import Coercions.Oopsla16.Frontend.Typer
import Coercions.Oopsla16.Frontend.Infer
import Coercions.Oopsla16.Frontend.Step
import Coercions.Oopsla16.Frontend.StepFC
import Coercions.FCdotR.SourceSafety
import Coercions.FCdotR.ElaborationFull
import Coercions.FCdotR.ElaborationErasure
import Coercions.FCdotR.CheckerCompleteness
import Coercions.FCdotR.Simulation
import Coercions.FCdotR.MethodInversion

/-!
# The pipeline

`compileE` takes a surface program through the resolver, the elaborator of
`Infer.lean` and the typer.  The theorems say what the result is worth.  The
safety theorems compose results of `Oopsla16` and `FCdotR`, so the front end
proves nothing about the calculus itself.

`compileE` returns the filled term and a `Compiled`: the synthesized type, the
`Oopsla16.HasType` derivation, and the fragment proof of the term when it is
in `FCdotR.TmFrag`.  The filled term is the resolved program with a self type
written into each literal the typer cannot take as it is.  Or `compileE`
returns the reason the program is rejected: a missing parameter type, a cyclic
reference, candidates with no least type, a mismatch, or the recursion limit.
`compile` forgets the reason (`compile_eq`).  `elaborate` translates the
derivation to an FCdotR term by `FCdotR.elabTm`.  `compileAndRun` and
`compileAndRunFC` run the program on the source machine of `Step.lean` and the
target machine of `StepFC.lean`, each at a step budget.

Every safety theorem takes `h : compile b Λ e = some ⟨a, c⟩`.  The content is
in the type of `c`, whose `deriv` field derives `a.erase`.  A run `r`, a budget
`m` or a fragment proof `f` names the subject of the statement.  For a concrete
program the premise `(compile b Λ e).isSome = true` closes by `decide +kernel`.

## Inference and the typer

`compileL` is the pipeline with no inference: the typer on the resolved term.

* `elabF_eq` says that the elaborator is the fill followed by the typer's
  synthesis on the filled term.  It holds by unfolding `elabF` and adds no
  completeness: a self type the fill does not find is not found.
* `compile_landed` says that a program the typer takes as it is compiles as
  the typer types it.  `compile_conservative` follows: every program that
  compiles without inference compiles with it, to the same result.
* `compile_spec` says that a compile returns the fill of the resolved program,
  with the typer's type and derivation for the fill from a full tank.
* `compileE_erase` says that the fill agrees with every written self type and
  erases to the resolved program.  So `a.erase` in the safety theorems is the
  program as written.
* `compileE_slot` says that a reason naming an empty slot comes only from a
  program the typer cannot take as it is.
* `elabTop?_stable` and `elabTop?_mono` say that an elaboration that ends
  unmarked gives the same verdict at more fuel, as `synthTop?_stable` and
  `synthTop?_mono` say of the typer.  `compile_rejects` follows: a rejection
  that ends unmarked is a rejection at every budget.

## Where the safety theorems come from

* `compile_safe` and `compile_not_stuck` are `Oopsla16.oopsla16_safety` and
  `Oopsla16.oopsla16_not_stuck`, applied to the derivation.
* `compile_checks` is `FCdotR.checkTm_complete` at the `typed` field of
  `FCdotR.elabTm`.  The checker takes no fuel, so its verdict is a theorem.
* `compile_corr` is the `corr` field of `FCdotR.elabTm`.  It relates the
  program and its elaboration up to annotations and `let` bindings.
* `compile_adequate` is `FCdotR.Rel.answer_iff_final` at `FCdotR.Rel.init`.
* `compile_target_safe` is `FCdotR.safety'`.
* `compile_frag_erase` and `compile_frag_checks` are `FCdotR.elabHasType_erase`
  and `FCdotR.checkTm_complete` at the fragment elaboration `FCdotR.elabHasType`.
* `compile_run_progress` and `compile_fcRun_progress` say that the state a
  driver returns is final or has a step.  `compile_drivers_agree` says that
  the two drivers terminate together.

The full elaboration binds every call operand with `let`, so it does not erase
to the program in general.  On the fragment, which `frag?` of `Decide.lean`
decides, the fragment elaboration does erase to the program.  `compile` records
the verdict in `Compiled.frag`.
-/

namespace Oopsla16Frontend

open FCdot (Sig)
open Oopsla16 (Ty Ctx Store Grows HasType Step Steps)

/-! ## The result of a compilation -/

/-- The result of `synthTop?` for a closed term, with the fragment proof of
the term when it is in `FCdotR.TmFrag`. -/
structure Compiled (t : Oopsla16.Tm [] []) where
  /-- The synthesized type. -/
  ty : Ty [] []
  /-- The derivation. -/
  deriv : HasType Store.nil Ctx.nil t ty
  /-- The fragment proof, as `frag?` decides it. -/
  frag : Option (FCdotR.TmFrag t)

/-! ## The pipeline -/

/-- Resolve, elaborate and decide the fragment.  The elaborator (`elabTopF`,
`Infer.lean`) writes a self type into every literal the typer cannot take as
it is and hands the filled term to the typer.  The answer is the filled term
with its type, its derivation and its fragment proof, or the reason the
program is rejected: a missing parameter type, a cyclic reference, candidates
with no least type, a mismatch, or the recursion limit.  A program with a free
name or with no label table has no resolution, and the reason is a mismatch,
which names no slot. -/
def compileE (b : Budget) (Λ : LabelTable) (e : STm) :
    Except EReason ((a : ATm []) × Compiled a.erase) :=
  match resolve Λ e with
  | none => .error .mismatch
  | some a =>
      match (elabTopF b.fuel a).1 with
      | .ok r => .ok ⟨r.1, ⟨r.2.ty, r.2.deriv, frag? r.1.erase⟩⟩
      | .error r => .error r

/-- Resolve, elaborate and decide the fragment, without the reason.  The result
is a dependent pair, since the derivation is about the erasure of the filled
term.  `none` means the program has a free name, has no label table, is
rejected, or has no type within the fuel of `b`. -/
def compile (b : Budget) (Λ : LabelTable) (e : STm) :
    Option ((a : ATm []) × Compiled a.erase) :=
  (compileE b Λ e).toOption

/-- The reason `compileE` gives, and `none` when the program compiles.  A
compiled program carries a derivation, which has no decidable equality, so a
verdict is stated through this function. -/
def reasonOf (b : Budget) (Λ : LabelTable) (e : STm) : Option EReason :=
  match compileE b Λ e with
  | .ok _ => none
  | .error r => some r

/-- Resolve and type with no inference: the typer on the resolved term.  This
is the pipeline without `Infer.lean`, the reference of
`compile_conservative`. -/
def compileL (b : Budget) (Λ : LabelTable) (e : STm) :
    Option ((a : ATm []) × Compiled a.erase) := do
  let a ← resolve Λ e
  let c ← synthTop? b a
  pure ⟨a, ⟨c.ty, c.deriv, frag? a.erase⟩⟩

/-- The target term of a compiled program: `FCdotR.elabTm` at the empty store. -/
def elaborate {t : Oopsla16.Tm [] []} (c : Compiled t) : FCdotR.Tm [] [] :=
  (FCdotR.elabTm FCdotR.emptyStoreTy c.deriv).tm

/-- The initial target state: empty store, empty continuation, the elaboration. -/
def initFC {t : Oopsla16.Tm [] []} (c : Compiled t) : FCdotR.State [] :=
  ⟨FCdotR.MachineStore.nil, .nil, elaborate c⟩

/-- Compile, then run the source machine for at most `m` steps. -/
def compileAndRun (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) : Option (Next []) :=
  (compile b Λ e).map fun r => run m Store.nil r.1.erase

/-- Compile, then run the target machine for at most `m` steps. -/
def compileAndRunFC (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) : Option (FNext []) :=
  (compile b Λ e).map fun r => fcRun m (initFC r.2)

/-! ## The elaborator at the top

What `elabTopF` returns, read through the typer.  `elabF` is the fill
followed by the typer's synthesis on the filled term (`elabF_eq`).  A term the
typer takes as it is goes to the typer unchanged (`elabTopF_landed`).  A
filled term that the elaborator types, the typer types from a full tank at the
same first candidate (`elabTopF_ok`). -/

section Top

open Frontend.Fuel

/-- **Inference is the typer on the filled term.**  The elaborator fills the
term with no goal and hands the filled term to the typer's synthesis, on the
tank the fill leaves.  This holds by unfolding `elabF`. -/
theorem elabF_eq {s : Sig} (Γ : Ctx [] s) (a : ATm s) (t : Tank) :
    elabF Γ a t = match fillF Γ none a t with
      | (.ok a', t1) => (.ok ⟨a', (synthF Γ a' t1).1⟩, (synthF Γ a' t1).2)
      | (.error r, t1) => (.error r, t1) := by
  unfold elabF
  simp only [Fu.bind]
  cases fillF Γ none a t with
  | mk r t1 => cases r <;> rfl

/-- The same at a goal: the fill at the goal, then the typer's check of the
filled term. -/
theorem elabChkF_eq {s : Sig} (Γ : Ctx [] s) (a : ATm s) (G : Ty [] s) (t : Tank) :
    elabChkF Γ a G t = match fillAtF Γ G a (fun g => fillF Γ g a) t with
      | (.ok a', t1) => (.ok ⟨a', (checkF Γ a' G t1).1⟩, (checkF Γ a' G t1).2)
      | (.error r, t1) => (.error r, t1) := by
  unfold elabChkF
  simp only [Fu.bind]
  cases fillAtF Γ G a (fun g => fillF Γ g a) t with
  | mk r t1 => cases r <;> rfl

/-- The verdict `elabTopF` gives a term the typer takes as it is, read off the
typer's first candidate: the candidate, else the recursion limit when the tank
ended marked, else a mismatch. -/
def topOf (a : ATm []) :
    Option (Cand Ctx.nil a.erase) × Tank → FillR ((a' : ATm []) × Cand Ctx.nil a'.erase)
  | (some c, _) => .ok ⟨a, c⟩
  | (none, t) => .error (if t.out then .limit else .mismatch)

/-- **A term the typer takes is elaborated as the typer types it.**  The
verdict is the typer's first candidate and the tank is the typer's tank. -/
theorem elabTopF_landed {a : ATm []} (hl : a.landed = true) (n : Nat) :
    elabTopF n a = (topOf a (synthTopF n a), (synthTopF n a).2) := by
  unfold elabTopF synthTopF synthInF
  rw [elabF_landed Ctx.nil a hl]
  simp only [Fu.bind, Fu.ret]
  cases synthF Ctx.nil a ⟨n, false⟩ with
  | mk cs t =>
    cases cs with
    | nil => cases ht : t.out <;> simp [firstCand, topOf, ht, Frontend.Reason.Reason.top]
    | cons c cs => cases ht : t.out <;> simp [firstCand, topOf, ht]

/-- A term the typer takes is rejected only for the recursion limit or a
mismatch, never for a reason that names a slot. -/
theorem elabTopF_landed_error {a : ATm []} (hl : a.landed = true) {n : Nat} {r : EReason}
    (h : (elabTopF n a).1 = .error r) : r = .limit ∨ r = .mismatch := by
  rw [elabTopF_landed hl n] at h
  revert h
  cases synthTopF n a with
  | mk o t =>
    cases o with
    | some c => intro h; cases h
    | none =>
      intro h
      simp only [topOf, Except.error.injEq] at h
      subst h
      cases t.out <;> simp

/-- The typer's synthesis on the filled term, read off a successful
elaboration.  The fill leaves an unmarked tank on which the typer's first
candidate is the elaborator's, and the filled term fills the input. -/
theorem elabTopF_ok {n : Nat} {a : ATm []} {r : (a' : ATm []) × Cand Ctx.nil a'.erase}
    (h : (elabTopF n a).1 = .ok r) :
    a.fills r.1 = true ∧ r.1.landed = true ∧ (synthTopF n r.1).1 = some r.2 := by
  unfold elabTopF at h
  rw [elabF_eq] at h
  cases hf : fillF Ctx.nil none a ⟨n, false⟩ with
  | mk res t1 =>
    rw [hf] at h
    cases res with
    | error e => simp at h
    | ok a' =>
      have hfill := fillF_fills (Γ := Ctx.nil) (g := none) (t := ⟨n, false⟩) (by rw [hf])
      simp only at h
      cases hs : synthF Ctx.nil a' t1 with
      | mk cs t =>
        rw [hs] at h
        cases cs with
        | nil => simp at h
        | cons c cs =>
          cases ht : t.out with
          | true => simp [ht] at h
          | false =>
            simp only [ht, Bool.false_eq_true, if_false, Except.ok.injEq] at h
            subst h
            refine ⟨hfill.1, hfill.2, ?_⟩
            have ht1 : t1.out = false := (synthF_framed Ctx.nil a').start hs ht
            have hle : t1.left ≤ n := (fillF_framed Ctx.nil none a).le hf
            have heq := Tank.eq_add (u := ⟨n, false⟩) ht1 rfl hle
            unfold synthTopF synthInF
            rw [heq, synthF_frame hs ht]
            simp [firstCand, Tank.add, ht]

/-- An elaboration that ends with a filled term ends unmarked. -/
theorem elabTopF_ok_out {n : Nat} {a : ATm []} {r : (a' : ATm []) × Cand Ctx.nil a'.erase}
    (h : (elabTopF n a).1 = .ok r) : (elabTopF n a).2.out = false := by
  unfold elabTopF at h ⊢
  cases hs : elabF Ctx.nil a ⟨n, false⟩ with
  | mk res t =>
    rw [hs] at h
    rcases res with e | ⟨a', _ | ⟨c, cs⟩⟩
    · simp at h
    · simp at h
    · cases ht : t.out with
      | false => rfl
      | true => simp [ht] at h

/-- **An elaboration that ends unmarked gives the same verdict at every larger
fuel.**  So a rejection that ends unmarked is a rejection by the rules.  This
is `elabF_framed`, as `synthTop?_stable` is `synthF_framed`. -/
theorem elabTop?_stable {n k : Nat} {a : ATm []}
    {r : FillR ((a' : ATm []) × Cand Ctx.nil a'.erase)}
    (h : elabTopF n a = (r, ⟨k, false⟩)) (j : Nat) : (elabTopF (n + j) a).1 = r := by
  unfold elabTopF at h ⊢
  cases hs : elabF Ctx.nil a ⟨n, false⟩ with
  | mk res t =>
    rw [hs] at h
    have ht : t = ⟨k, false⟩ := by
      rcases res with e | ⟨a', _ | ⟨c, cs⟩⟩ <;> exact (Prod.mk.inj h).2
    have hf := (elabF_framed Ctx.nil a).shift _ _ _ hs (by rw [ht]) j
    have hn : (⟨n + j, false⟩ : Tank) = (⟨n, false⟩ : Tank).add j := rfl
    rw [hn, hf]
    subst ht
    rcases res with e | ⟨a', _ | ⟨c, cs⟩⟩ <;> exact (Prod.mk.inj h).1

/-- **More fuel keeps the answer of an elaboration.** -/
theorem elabTop?_mono {n m : Nat} {a : ATm []} {r : (a' : ATm []) × Cand Ctx.nil a'.erase}
    (h : (elabTopF n a).1 = .ok r) (hnm : n ≤ m) : (elabTopF m a).1 = .ok r := by
  have ho := elabTopF_ok_out h
  have he : elabTopF n a = (.ok r, ⟨(elabTopF n a).2.left, false⟩) := by
    rw [← h, ← ho]
  have := elabTop?_stable he (m - n)
  rwa [Nat.add_sub_cancel' hnm] at this

end Top

/-! ## What `compile` returns -/

/-- A successful compile returns the fill of the resolved program: the
resolved program with a self type written into each literal that lacked one.
The type and derivation are the typer's on the fill, from a full tank. -/
theorem compile_spec {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []}
    {c : Compiled a.erase} (h : compile b Λ e = some ⟨a, c⟩) :
    ∃ a0, resolve Λ e = some a0 ∧ a0.fills a = true ∧
      synthTop? b a = some ⟨c.ty, c.deriv⟩ ∧ c.frag = frag? a.erase := by
  unfold compile compileE at h
  cases hr : resolve Λ e with
  | none => rw [hr] at h; cases h
  | some a0 =>
    rw [hr] at h
    dsimp only at h
    cases he : (elabTopF b.fuel a0).1 with
    | error r => rw [he] at h; cases h
    | ok r =>
      rw [he] at h
      cases h
      obtain ⟨hfill, _, hs⟩ := elabTopF_ok he
      exact ⟨a0, rfl, hfill, hs, rfl⟩

/-- The recorded fragment proof is the verdict of `frag?` on the program. -/
theorem compile_frag {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []}
    {c : Compiled a.erase} (h : compile b Λ e = some ⟨a, c⟩) : c.frag = frag? a.erase := by
  obtain ⟨_, _, _, _, hf⟩ := compile_spec h
  exact hf

/-- A program in the fragment has its fragment proof recorded, by
`frag?_complete`. -/
theorem compile_frag_isSome {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []}
    {c : Compiled a.erase} (h : compile b Λ e = some ⟨a, c⟩) (f : FCdotR.TmFrag a.erase) :
    c.frag.isSome = true := by
  rw [compile_frag h]; exact frag?_complete f

/-! ## Inference and the typer

A program the typer takes as it is compiles as the typer types it
(`compile_landed`).  So every program that compiles without inference compiles
with it, at the same term, type and derivation (`compile_conservative`).  The
filled term fills the resolved program and erases to it (`compileE_erase`), so
every theorem below speaks of the program as written.  The reasons that name
an empty slot come only from a program the typer cannot take as it is
(`compileE_slot`). -/

section Infer
variable {b : Budget} {Λ : LabelTable} {e : STm}

/-- `compile` is `compileE` without the reason. -/
theorem compile_eq (b : Budget) (Λ : LabelTable) (e : STm) :
    compile b Λ e = (compileE b Λ e).toOption := rfl

/-- **A program the typer takes compiles as the typer types it.**  When the
resolved program is one the typer takes as it is, inference changes nothing:
the pipeline is the typer on the resolved term. -/
theorem compile_landed {a : ATm []} (hr : resolve Λ e = some a) (hl : a.landed = true) :
    compile b Λ e = compileL b Λ e := by
  unfold compile compileE compileL
  rw [hr]
  dsimp only
  rw [elabTopF_landed hl]
  unfold synthTop?
  cases hs : synthTopF b.fuel a with
  | mk o t =>
    cases o with
    | some c => simp [hs, topOf, Except.toOption]
    | none => cases ht : t.out <;> simp [hs, topOf, ht, Except.toOption]

/-- **Conservativity.**  Every program that compiles without inference compiles
with it, to the same term, type, derivation and fragment proof.  A program the
typer types has a first candidate, so the typer takes it as it is
(`synthF_cons_landed`), and `compile_landed` applies. -/
theorem compile_conservative {r : (a : ATm []) × Compiled a.erase}
    (h : compileL b Λ e = some r) : compile b Λ e = some r := by
  have h' := h
  unfold compileL at h
  cases hr : resolve Λ e with
  | none => rw [hr] at h; cases h
  | some a =>
    cases hs : synthTop? b a with
    | none => simp [hr, hs] at h
    | some c =>
      have hl : a.landed = true := by
        unfold synthTop? synthTopF synthInF at hs
        cases hsf : synthF Ctx.nil a ⟨b.fuel, false⟩ with
        | mk cs t =>
          rw [hsf] at hs
          cases cs with
          | nil => simp [firstCand] at hs
          | cons c' cs => exact synthF_cons_landed (t := ⟨b.fuel, false⟩) (by rw [hsf])
      rw [compile_landed hr hl, h']

/-- **Inference fills only empty slots.**  The term a compile returns agrees
with the resolved program at every written self type, and erases to it.  So
the derivation is about the program as written. -/
theorem compileE_erase {a' : ATm []} {c : Compiled a'.erase} (h : compileE b Λ e = .ok ⟨a', c⟩) :
    ∃ a, resolve Λ e = some a ∧ a.fills a' = true ∧ a'.erase = a.erase := by
  unfold compileE at h
  cases hr : resolve Λ e with
  | none => rw [hr] at h; cases h
  | some a =>
    rw [hr] at h
    dsimp only at h
    cases he : (elabTopF b.fuel a).1 with
    | error r => rw [he] at h; cases h
    | ok r =>
      rw [he] at h
      cases h
      have hfill := (elabTopF_ok he).1
      exact ⟨a, rfl, hfill, fills_erase _ _ hfill⟩

/-- **The slot reasons arise only where a slot is empty.**  A program rejected
for a missing parameter type, a cyclic reference, a definition that needs a
written type, or candidates with no least type resolves to a term the typer
cannot take as it is. -/
theorem compileE_slot {r : EReason} (h : compileE b Λ e = .error r)
    (hr : r.isSlotReason = true) : ∃ a, resolve Λ e = some a ∧ a.landed = false := by
  unfold compileE at h
  cases hres : resolve Λ e with
  | none =>
    rw [hres] at h
    cases h
    cases hr
  | some a =>
    rw [hres] at h
    dsimp only at h
    refine ⟨a, rfl, ?_⟩
    cases hl : a.landed with
    | false => rfl
    | true =>
      cases he : (elabTopF b.fuel a).1 with
      | ok c => rw [he] at h; cases h
      | error r' =>
        rw [he] at h
        cases h
        rcases elabTopF_landed_error hl he with rfl | rfl <;> cases hr

/-- **A rejection that ends unmarked is a rejection at every budget.**  Above
the fuel of the rejection this is `elabTop?_stable`.  Below it, an answer would
be kept by `elabTop?_mono` and contradict the rejection.  This is the
counterpart of `typeAt_rejects` for a program of any kind, with or without the
self types the typer needs. -/
theorem compile_rejects {a : ATm []} {n : Nat} (hr : resolve Λ e = some a)
    (h : (elabTopF n a).1.isOk = false ∧ (elabTopF n a).2.out = false) (b : Budget) :
    compile b Λ e = none := by
  obtain ⟨hno, hout⟩ := h
  have hpair : elabTopF n a = ((elabTopF n a).1, ⟨(elabTopF n a).2.left, false⟩) := by
    rw [← hout]
  have hb : ∀ c, (elabTopF b.fuel a).1 ≠ .ok c := by
    intro c hc
    rcases Nat.le_total n b.fuel with hle | hle
    · have := elabTop?_stable hpair (b.fuel - n)
      rw [Nat.add_sub_cancel' hle, hc] at this
      rw [← this] at hno
      cases hno
    · have := elabTop?_mono hc hle
      rw [this] at hno
      cases hno
  unfold compile compileE
  rw [hr]
  dsimp only
  cases he : (elabTopF b.fuel a).1 with
  | ok c => exact absurd he (hb c)
  | error r' => rfl

end Infer

/-! ## The theorems -/

-- Most theorems do not use `h`.  The content is in the type of `c`.
set_option linter.unusedVariables false

section
variable {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []} {c : Compiled a.erase}

/-- **Safety on the source machine.**  No configuration reachable from the
program is stuck.  This is `Oopsla16.oopsla16_safety`. -/
theorem compile_safe (h : compile b Λ e = some ⟨a, c⟩) {σ : Sig} {g : Grows [] σ}
    {G' : Store σ σ} {t' : Oopsla16.Tm σ []} (r : Steps g Store.nil a.erase G' t') :
    ¬ FCdotR.SrcStuck G' t' :=
  Oopsla16.oopsla16_safety c.deriv r

/-- **Progress.**  Every reachable configuration is an answer or has a step.
This is `Oopsla16.oopsla16_not_stuck`. -/
theorem compile_not_stuck (h : compile b Λ e = some ⟨a, c⟩) {σ : Sig} {g : Grows [] σ}
    {G' : Store σ σ} {t' : Oopsla16.Tm σ []} (r : Steps g Store.nil a.erase G' t') :
    t'.IsAnswer ∨
      ∃ (σ' : Sig) (g' : Grows σ σ') (G'' : Store σ' σ') (t'' : Oopsla16.Tm σ' []),
        Step g' G' t' G'' t'' :=
  Oopsla16.oopsla16_not_stuck c.deriv r

/-- **The target checker accepts the elaboration.** -/
theorem compile_checks (h : compile b Λ e = some ⟨a, c⟩) :
    FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil (elaborate c) c.ty = true :=
  FCdotR.checkTm_complete (FCdotR.elabTm FCdotR.emptyStoreTy c.deriv).typed

/-- **The elaboration corresponds to the program** in the sense of
`FCdotR.Corr`: up to type annotations and the `let` bindings of call operands. -/
theorem compile_corr (h : compile b Λ e = some ⟨a, c⟩) : FCdotR.Corr a.erase (elaborate c) :=
  (FCdotR.elabTm FCdotR.emptyStoreTy c.deriv).corr

/-- **Adequacy.**  The program reaches an answer on the source machine exactly
when its elaboration reaches a final state on the target machine. -/
theorem compile_adequate (h : compile b Λ e = some ⟨a, c⟩) :
    (∃ (σ : Sig) (g : Grows [] σ) (G' : Store σ σ) (t' : Oopsla16.Tm σ []),
        Steps g Store.nil a.erase G' t' ∧ t'.IsAnswer) ↔
      (∃ (σ : Sig) (g : Grows [] σ) (st' : FCdotR.State σ),
        FCdotR.Steps g (initFC c) st' ∧ st'.Final) :=
  (FCdotR.Rel.init (compile_corr h)).answer_iff_final

/-- **Safety on the target machine.**  No state reachable from the initial
state is stuck. -/
theorem compile_target_safe (h : compile b Λ e = some ⟨a, c⟩) {σ : Sig} {g : Grows [] σ}
    {st' : FCdotR.State σ} (r : FCdotR.Steps g (initFC c) st') : ¬ st'.Stuck :=
  FCdotR.safety' (FCdotR.elabTm FCdotR.emptyStoreTy c.deriv).typed r

/-- **The source driver never stops at a stuck configuration.**  At every
budget `m`, the configuration `run` returns is an answer or has a step.  This
is `compile_not_stuck` at that configuration. -/
theorem compile_run_progress (h : compile b Λ e = some ⟨a, c⟩) (m : Nat) :
    isAnswer (run m Store.nil a.erase).t' = true ∨
      (step? (run m Store.nil a.erase).G' (run m Store.nil a.erase).t').isSome = true := by
  obtain ⟨g, r⟩ := run_steps m Store.nil a.erase
  rcases compile_not_stuck h r with ha | hs
  · exact Or.inl ((isAnswer_iff _).mpr ha)
  · refine Or.inr ?_
    cases hn : step? (run m Store.nil a.erase).G' (run m Store.nil a.erase).t' with
    | some _ => rfl
    | none => exact absurd hs (step?_eq_none_iff.mp hn)

/-- **The target driver never stops at a stuck state.**  At every budget `m`,
the state `fcRun` returns is final or has a step.  This is
`compile_target_safe` at that state. -/
theorem compile_fcRun_progress (h : compile b Λ e = some ⟨a, c⟩) (m : Nat) :
    fcFinal? (fcRun m (initFC c)).st' = true ∨ (fcStep? (fcRun m (initFC c)).st').isSome = true := by
  obtain ⟨g, r⟩ := fcRun_steps m (initFC c)
  cases hn : fcStep? (fcRun m (initFC c)).st' with
  | some _ => exact Or.inr rfl
  | none =>
      rcases fcStep?_none_classify hn with hf | hs
      · exact Or.inl ((fcFinal?_iff _).mpr hf)
      · exact absurd hs (compile_target_safe h r)

/-- **The two drivers terminate together.**  Some budget takes the source
driver to an answer exactly when some budget takes the target driver to a
final state.  This is `compile_adequate` with the completeness of the drivers,
`run_complete` and `fcRun_complete`. -/
theorem compile_drivers_agree (h : compile b Λ e = some ⟨a, c⟩) :
    (∃ m, isAnswer (run m Store.nil a.erase).t' = true) ↔
      (∃ m, fcFinal? (fcRun m (initFC c)).st' = true) := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨g, r⟩ := run_steps m Store.nil a.erase
    obtain ⟨σ, g', st', r', hfin⟩ :=
      (compile_adequate h).mp ⟨_, g, _, _, r, (isAnswer_iff _).mp hm⟩
    obtain ⟨k, hk⟩ := fcRun_complete r'
    exact ⟨k, by rw [hk]; exact (fcFinal?_iff _).mpr hfin⟩
  · rintro ⟨m, hm⟩
    obtain ⟨g, r⟩ := fcRun_steps m (initFC c)
    obtain ⟨σ, g', G', t', r', ha⟩ :=
      (compile_adequate h).mpr ⟨_, g, _, r, (fcFinal?_iff _).mp hm⟩
    obtain ⟨k, hk⟩ := run_complete r'
    exact ⟨k, by rw [hk]; exact (isAnswer_iff _).mpr ha⟩

/-- **On the fragment, the fragment elaboration erases to the program.** -/
theorem compile_frag_erase (h : compile b Λ e = some ⟨a, c⟩) {f : FCdotR.TmFrag a.erase}
    (hf : c.frag = some f) :
    (FCdotR.elabHasType FCdotR.emptyStoreTy c.deriv f).1.erase = a.erase :=
  FCdotR.elabHasType_erase FCdotR.emptyStoreTy c.deriv f

/-- **On the fragment, the target checker accepts the fragment
elaboration.** -/
theorem compile_frag_checks (h : compile b Λ e = some ⟨a, c⟩) {f : FCdotR.TmFrag a.erase}
    (hf : c.frag = some f) :
    FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
      (FCdotR.elabHasType FCdotR.emptyStoreTy c.deriv f).1 c.ty = true :=
  FCdotR.checkTm_complete (FCdotR.elabHasType FCdotR.emptyStoreTy c.deriv f).2

end

/-- **The checker accepts the elaboration, read off a successful compile.**
For a concrete program the premise closes by `decide +kernel`, which leaves a
theorem with no hypothesis. -/
theorem compile_checks_get {b : Budget} {Λ : LabelTable} {e : STm}
    (h : (compile b Λ e).isSome = true) :
    FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
      (elaborate ((compile b Λ e).get h).2) ((compile b Λ e).get h).2.ty = true :=
  compile_checks (Option.some_get h).symm

/-! ## Checks

`FCdotR.SourceSafety.RecursiveArg.prog`, written as `recArgSrc` in
`Notation.lean`, runs end to end in the kernel.  It compiles at type `⊤`.  The
source driver answers in three steps and the target driver is final in
thirteen.  It is outside the fragment, which calls variables on variables
only. -/

section Checks

/-- `RecursiveArg` compiles, at `⊤`. -/
example : ((compile {} recArgTable recArgSrc).map
    (·.2.ty)) = some .TTop := by
  decide +kernel

/-- The checker accepts the elaboration of `RecursiveArg`. -/
example : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate ((compile {} recArgTable recArgSrc).get
      (by decide +kernel)).2)
    ((compile {} recArgTable recArgSrc).get
      (by decide +kernel)).2.ty = true :=
  compile_checks_get _

/-- `RecursiveArg` is outside the fragment. -/
example : ((compile {} recArgTable recArgSrc).map
    (·.2.frag.isSome)) = some false := by
  decide +kernel

/-- The source driver answers in three steps and not in two. -/
example : (compileAndRun {} 3 recArgTable recArgSrc).map
      (fun n => isAnswer n.t') = some true ∧
    (compileAndRun {} 2 recArgTable recArgSrc).map
      (fun n => isAnswer n.t') = some false := by
  decide +kernel

/-- The target driver is final in thirteen steps and not in twelve.  The extra
steps are `let` and coercion steps. -/
example : (compileAndRunFC {} 13 recArgTable recArgSrc).map
      (fun n => fcFinal? n.st') = some true ∧
    (compileAndRunFC {} 12 recArgTable recArgSrc).map
      (fun n => fcFinal? n.st') = some false := by
  decide +kernel

/-! `ex1` of `FCdotR.CheckerExamples` is in the fragment, so
`compile_frag_erase` and `compile_frag_checks` apply to it. -/

/-- `ex1` compiles at the default budget. -/
private theorem ex1_isSome : (compile {} ex1Table ex1src).isSome = true := by
  decide +kernel

/-- The compiled `ex1`. -/
private abbrev ex1Compiled : (a : ATm []) × Compiled a.erase :=
  (compile {} ex1Table ex1src).get ex1_isSome

/-- `frag?` finds the fragment proof of `ex1`. -/
private theorem ex1_frag_isSome : ex1Compiled.2.frag.isSome = true := by
  decide +kernel

/-- The fragment proof of `ex1`. -/
private abbrev ex1Frag : FCdotR.TmFrag ex1Compiled.1.erase :=
  ex1Compiled.2.frag.get ex1_frag_isSome

/-- The compile of `ex1`. -/
private theorem ex1_compile :
    compile {} ex1Table ex1src = some ⟨ex1Compiled.1, ex1Compiled.2⟩ :=
  (Option.some_get ex1_isSome).symm

/-- The recorded fragment proof of `ex1`. -/
private theorem ex1_frag : ex1Compiled.2.frag = some ex1Frag :=
  (Option.some_get ex1_frag_isSome).symm

/-- The fragment elaboration of `ex1` erases to `ex1`. -/
example : (FCdotR.elabHasType FCdotR.emptyStoreTy ex1Compiled.2.deriv ex1Frag).1.erase =
    ex1Compiled.1.erase :=
  compile_frag_erase ex1_compile ex1_frag

/-- The checker accepts the fragment elaboration of `ex1`. -/
example : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (FCdotR.elabHasType FCdotR.emptyStoreTy ex1Compiled.2.deriv ex1Frag).1 ex1Compiled.2.ty = true :=
  compile_frag_checks ex1_compile ex1_frag

/-! ### Through inference

`fwd` of `Infer.lean` has two methods without a written result, so the typer
alone does not take it.  The pipeline fills its self type and compiles it, and
the target checker accepts the elaboration.  A method without a parameter type
and without a goal is the compiler's missing parameter type, and a method that
calls itself without a written result is a cyclic reference.  Both are
rejections of a program the typer cannot take as it is (`compileE_slot`). -/

open InferChecks in
/-- `fwd` does not compile without inference. -/
example : (compileL {} fwdTable fwdSrc).isSome = false := by decide +kernel

open InferChecks in
/-- `fwd` compiles through inference, outside the fragment. -/
theorem fwd_compiles : (compile {} fwdTable fwdSrc).isSome = true := by decide +kernel

open InferChecks in
/-- The checker accepts the elaboration of the filled `fwd`. -/
example : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate ((compile {} fwdTable fwdSrc).get fwd_compiles).2)
    ((compile {} fwdTable fwdSrc).get fwd_compiles).2.ty = true :=
  compile_checks_get fwd_compiles

open InferChecks in
/-- A method with no parameter type and no goal. -/
example : reasonOf {} [("f", 0)] noParamSrc = some (.missingParamType (some 0)) := by
  decide +kernel

open InferChecks in
/-- A method that calls itself with no written result. -/
example : reasonOf {} recTable recUSrc = some (.cyclicRef 0) := by decide +kernel

open InferChecks in
/-- The resolution of the recursive method. -/
private theorem recU_resolves : (resolve recTable recUSrc).isSome = true := by decide

open InferChecks in
/-- The cyclic reference ends with the tank unmarked, so the program is
rejected at every budget. -/
example (b : Budget) : compile b recTable recUSrc = none :=
  compile_rejects (a := (resolve recTable recUSrc).get recU_resolves)
    (Option.some_get recU_resolves).symm
    (n := Core.defaultFuel) (by decide +kernel) b

open InferChecks in
/-- A literal at a goal whose two domains have no common result for the
body. -/
example : reasonOf {} fTable ascIncSrc = some .mismatch := by decide +kernel

/-- A free name has no resolution, which is a mismatch. -/
example : reasonOf {} [] (o16% x) = some .mismatch := by decide +kernel

end Checks

end Oopsla16Frontend
