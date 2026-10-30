import Coercions.Nominal.Frontend.Typer
import Coercions.Nominal.Frontend.Elab
import Coercions.Nominal.Frontend.Sources
import Coercions.Nominal.Translation.Examples
import Coercions.Nominal.FCn.CheckerCompleteness

/-!
# The pipeline

`compileE` resolves a program to a partial term (`resolveP`, `Resolve.lean`)
and elaborates it (`elabTopF`, `Elab.lean`).  It returns the fill and a
`Compiled`, which holds the type and the annotated derivation `AHasTy`, or the
reason the program is rejected.  `compile` is `compileE` without the reason, and
`compileReason` is the reason alone.  The erasure `Compiled.deriv` is the
`Nominal.Source.HasTy` derivation of the erased term.  `compileLanded` synthesizes
the type of a resolved term with every slot written, and `checkAt` checks one
against a given type.  `compileAndRun` follows a compile with the source machine
of `Nominal.Source` at a fuel and a step budget.  `compileAndRunFC` translates the
derivation to FCn and runs its machine at a step budget.

A program with every slot written compiles as `compileLanded` types its
resolution (`compile_full`).  A fill agrees with every slot the program writes
(`compileE_fills`).  A reason that names a slot comes only from a program with
an empty slot (`compileE_slot`).  An elaboration that ends with the tank
unmarked gives the same verdict at more fuel (`elabTop?_stable`,
`elabTop?_mono`).  Every theorem of the Head other than `compile_full` is proved
from a successful compile alone, never by unfolding `compile`.  `compile_isSome`
goes through `compile_full` only.

The Head's theorems compose results about the calculus.  The front end proves
nothing new.

* `compile_checks` is `Nominal.FCn.checkTm_iff` applied to
  `Nominal.Source.HasTy.translate_typed`.  The checker takes no fuel, so its verdict
  on the translation is a theorem.  `compile_checks_get` states it for a compile
  known only to succeed, so that a program discharges it with one decided fact.
* `compile_erase` is `Nominal.Source.HasTy.translate_erase`.
* `compile_safe` is `Nominal.safety`.  `compile_run_progress` is its first half at
  the configuration the source driver returns.
* `compile_reachable` is `Nominal.reachable_typed`, and `compile_lockstep` is
  `Nominal.reachable_run`.

Each theorem takes the successful compile `h : compile b Λ e = some ⟨a, c⟩`.
The content is the type of `c`.  The siblings restate these at the drivers
(`compileAndRun_eq` to `compileAndRunFC_consistent`), state that `c.ann` erases
to `c.deriv` (`compile_ann`), and carry the stability of the typer in the fuel
to `checkAt` and `compileLanded` (`checkAt_mono`, `compileLanded_mono`).

The section `Checks` runs the nine hand programs E1 to E8 and E13 of
`Sources.lean`.  For each, `checkAt` types the resolved term at the type of its
hand derivation, `compileLanded` accepts it, and the FCn checker accepts the
image of the compiled derivation.  N1 to N3 are rejected with the tank
unmarked.  The refuter's program G1 compiles, since avoidance takes the meet of
the upper bounds.  E6 costs at most the plan's estimate of 11,000 units.

The namespace `ElabChecks` runs the elaborator.  The reasons of `compileE` on
small programs.  The nine programs with their self types and lambda domains
erased where a goal or the definitions give them, each compiled to a fill whose
erasure is the hand term.  The same programs with every slot erased, each
rejected with its reason.  N4 rejected with `selfSingleton`.  The plan's risk, a
three-level literal whose inner lambda field waits for an outer one, and the
same reached through a path field.  A nested literal at a field that a written
self type declares takes its declared self type.  Limit L9.
-/

namespace NominalFrontend

open Frontend.Fuel NominalFrontend.Core Frontend.Reason
open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)
open Nominal.Source (Ty Dec Tm Ctx HasTy Sub)

/-! ## The result of a compilation -/

/-- A type for a closed annotated term, with the annotated derivation. -/
structure Compiled (a : ATm []) where
  ty : Ty []
  ann : AHasTy .nil a ty

/-- The pDOT derivation of the erased term, the erasure of the annotated one. -/
def Compiled.deriv {a : ATm []} (c : Compiled a) : HasTy .nil a.erase c.ty := c.ann.erase

/-! ## The pipeline -/

/-- Check a closed annotated term against a type, with the tank. -/
def checkAtF (b : Budget) (a : ATm []) (T : Ty []) : Option (AHasTy .nil a T) × Tank :=
  checkTopF b.mode b.modules b.fuel a T
/-- Check a closed annotated term against a type.  A marked tank answers `none`. -/
def checkAt (b : Budget) (a : ATm []) (T : Ty []) : Option (AHasTy .nil a T) := (checkAtF b a T).1
/-- Synthesize the type of a closed annotated term, with the tank. -/
def compileLandedF (b : Budget) (a : ATm []) : Option (Compiled a) × Tank :=
  let r := synthTopF b.mode b.modules b.fuel a
  (r.1.map fun c => ⟨c.ty, c.deriv⟩, r.2)
/-- Synthesize the type of a closed annotated term.  A marked tank answers `none`. -/
def compileLanded (b : Budget) (a : ATm []) : Option (Compiled a) := (compileLandedF b a).1
/-- Resolve to a partial term, then elaborate at the budget's fuel and mode.  The answer is the
fill with its type and annotated derivation, or the reason the program is rejected.  A program
out of scope or out of the label table has no resolution, and the reason is a mismatch. -/
def compileE (b : Budget) (Λ : LabelTable) (e : STm) : Except PReason ((a : ATm []) × Compiled a) :=
  match resolveP Λ e with
  | none => .error .mismatch
  | some p =>
      match (elabTopF b.mode b.modules b.fuel p).1 with
      | .ok c => .ok ⟨c.a, ⟨c.ty, c.ann⟩⟩
      | .error r => .error r
/-- `compileE` without the reason. -/
def compile (b : Budget) (Λ : LabelTable) (e : STm) : Option ((a : ATm []) × Compiled a) :=
  (compileE b Λ e).toOption
/-- The reason of a rejected program, `none` for an accepted one. -/
def compileReason (b : Budget) (Λ : LabelTable) (e : STm) : Option PReason :=
  match compileE b Λ e with
  | .error r => some r
  | .ok _ => none

/-- Compile, then run the source machine. -/
def compileAndRun (b : Budget) (n m : Nat) (Λ : LabelTable) (e : STm) : Option Nominal.Source.Conf :=
  (compile b Λ e).map fun r => Nominal.Source.runFuel n m ⟨[], .nil, r.1.erase⟩
/-- Compile, translate to FCn, then run the FCn machine. -/
def compileAndRunFC (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) :
    Option ((s : Sig) × Nominal.FCn.State s) :=
  (compile b Λ e).map fun r => Nominal.Translation.runOf m ⟨[], ⟨.nil, .nil, r.2.deriv.translate⟩⟩

/-! ## The Head's theorems and their siblings -/

/-- A partial term with no empty slot elaborates as the typer types the term it stands for. -/
theorem elabN_full {md : Mode} {ms : List (List Label)} {k : Nat} {s : Sig} {Γ : Ctx s} {p : PTm s} {a : ATm s}
    (hp : p.full? = some a) : elabN md ms (k + 1) Γ p = fullSynthAt md ms Γ p a (PTm.fills_of_full? hp) := by
  rw [elabN]
  split
  · rename_i a' h
    rw [hp, Option.some.injEq] at h
    subst h
    rfl
  · rename_i h
    rw [hp] at h
    cases h

theorem elabTopF_full {md : Mode} {ms : List (List Label)} {n : Nat} {p : PTm []} {a : ATm []}
    (hp : p.full? = some a) :
    elabTopF md ms n p =
      match fullSynthAt md ms Ctx.nil p a (PTm.fills_of_full? hp) ⟨n, false⟩ with
      | ((c :: _, _), t) => (if t.out then .error .limit else .ok c, t)
      | (([], rs), t) => (.error (Reason.top t.out rs), t) := by
  unfold elabTopF
  obtain ⟨k, hk⟩ : ∃ k, p.size = k + 1 := ⟨p.size - 1, by have := PTm.size_pos p; omega⟩
  rw [hk, elabN_full hp]
  rfl

theorem compile_full {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []} (h : resolve Λ e = some a) :
    compile b Λ e = (compileLanded b a).map (⟨a, ·⟩) := by
  rw [resolve_eq] at h
  cases hp : resolveP Λ e with
  | none =>
    rw [hp] at h
    cases h
  | some p =>
    rw [hp, Option.bind_some] at h
    simp only [compile, compileE, hp, elabTopF_full h, compileLanded, compileLandedF, synthTopF, fullSynthAt,
      Fu.bind, Fu.ret]
    cases hs : synthF b.mode b.modules Ctx.nil a ⟨b.fuel, false⟩ with
    | mk cs t =>
      cases cs with
      | nil => simp [firstCand, Except.toOption]
      | cons c cs => cases ht : t.out <;> simp [firstCand, ht, Except.toOption]

/-- **Inference fills only empty slots.**  The fill agrees with every slot the program writes. -/
theorem compileE_fills {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []} {c : Compiled a}
    (h : compileE b Λ e = .ok ⟨a, c⟩) : ∃ p, resolveP Λ e = some p ∧ p.fills a = true := by
  unfold compileE at h
  cases hp : resolveP Λ e with
  | none =>
    rw [hp] at h
    cases h
  | some p =>
    rw [hp] at h
    dsimp only at h
    refine ⟨p, rfl, ?_⟩
    cases he : (elabTopF b.mode b.modules b.fuel p).1 with
    | error r =>
      rw [he] at h
      cases h
    | ok c' =>
      rw [he] at h
      cases h
      exact c'.fills

theorem whyR_notSlot {s : Sig} (a : ATm s) : ∀ r ∈ whyR a, r.isSlotReason = false := by
  intro r hr
  simp only [whyR, List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with ⟨_, _, rfl⟩ | rfl <;> rfl

theorem fullSynthAt_notSlot {md : Mode} {ms : List (List Label)} {s : Sig} {Γ : Ctx s} {p : PTm s}
    {a : ATm s} {h : p.fills a = true} (t : Tank) :
    ∀ r ∈ (fullSynthAt md ms Γ p a h t).1.2, r.isSlotReason = false := by
  intro r hr
  simp only [fullSynthAt, Fu.bind, Fu.ret] at hr
  split at hr
  · exact whyR_notSlot a r hr
  · simp at hr

theorem top_notSlot {out : Bool} {rs : List PReason} (h : ∀ r ∈ rs, r.isSlotReason = false) :
    (Reason.top out rs).isSlotReason = false := by
  unfold Reason.top
  cases out with
  | true => rfl
  | false =>
    cases rs with
    | nil => rfl
    | cons r rs => exact h r (List.mem_cons_self ..)

/-- **The slot reasons arise only where a slot is empty.** -/
theorem compileE_slot {b : Budget} {Λ : LabelTable} {e : STm} {r : PReason} (h : compileE b Λ e = .error r)
    (hr : r.isSlotReason = true) : ∃ p, resolveP Λ e = some p ∧ p.full? = none := by
  unfold compileE at h
  cases hp : resolveP Λ e with
  | none =>
    rw [hp] at h
    cases h
    cases hr
  | some p =>
    rw [hp] at h
    dsimp only at h
    refine ⟨p, rfl, ?_⟩
    cases hf : p.full? with
    | none => rfl
    | some a =>
      exfalso
      rw [elabTopF_full hf] at h
      have hrs := fullSynthAt_notSlot (md := b.mode) (ms := b.modules) (Γ := Ctx.nil) (p := p)
        (h := PTm.fills_of_full? hf) ⟨b.fuel, false⟩
      revert hrs h
      cases fullSynthAt b.mode b.modules Ctx.nil p a (PTm.fills_of_full? hf) ⟨b.fuel, false⟩ with
      | mk res t =>
        obtain ⟨cs, rs⟩ := res
        intro h hrs
        cases cs with
        | cons c cs =>
          cases ht : t.out <;> simp [ht] at h
          subst h
          cases hr
        | nil =>
          simp only [Except.error.injEq] at h
          subst h
          rw [top_notSlot hrs] at hr
          cases hr

/-- **A rejection that ends unmarked is stable.**  A closed elaboration that ends unmarked gives the
same verdict at every larger fuel. -/
theorem elabTop?_stable {b : Budget} {n k : Nat} {p : PTm []} {r : Except PReason (ECand Ctx.nil p)}
    (h : elabTopF b.mode b.modules n p = (r, ⟨k, false⟩)) (j : Nat) :
    (elabTopF b.mode b.modules (n + j) p).1 = r := by
  unfold elabTopF at h ⊢
  cases hs : elabN b.mode b.modules p.size Ctx.nil p ⟨n, false⟩ with
  | mk res t =>
    obtain ⟨cs, rs⟩ := res
    rw [hs] at h
    have ht : t = ⟨k, false⟩ := by
      cases cs with
      | nil => exact (Prod.mk.inj h).2
      | cons c cs => exact (Prod.mk.inj h).2
    have hf := (elabN_framed b.mode b.modules p.size Ctx.nil p).shift _ _ _ hs (by rw [ht]) j
    have hn : (⟨n + j, false⟩ : Tank) = (⟨n, false⟩ : Tank).add j := rfl
    rw [hn, hf]
    subst ht
    cases cs with
    | nil => exact (Prod.mk.inj h).1
    | cons c cs => exact (Prod.mk.inj h).1

theorem elabTopF_ok_out {md : Mode} {ms : List (List Label)} {n : Nat} {p : PTm []} {c : ECand Ctx.nil p}
    (h : (elabTopF md ms n p).1 = .ok c) : (elabTopF md ms n p).2.out = false := by
  unfold elabTopF at h ⊢
  cases hs : elabN md ms p.size Ctx.nil p ⟨n, false⟩ with
  | mk res t =>
    obtain ⟨cs, rs⟩ := res
    rw [hs] at h
    cases cs with
    | nil => cases h
    | cons c' cs =>
      cases ht : t.out with
      | false => rfl
      | true =>
        simp only [ht, if_true] at h
        cases h

/-- **More fuel keeps the answer of a closed elaboration.** -/
theorem elabTop?_mono {b : Budget} {n m : Nat} {p : PTm []} {c : ECand Ctx.nil p}
    (h : (elabTopF b.mode b.modules n p).1 = .ok c) (hnm : n ≤ m) :
    (elabTopF b.mode b.modules m p).1 = .ok c := by
  have ho := elabTopF_ok_out h
  have he : elabTopF b.mode b.modules n p = (.ok c, ⟨(elabTopF b.mode b.modules n p).2.left, false⟩) := by
    rw [← h, ← ho]
  have := elabTop?_stable he (m - n)
  rwa [Nat.add_sub_cancel' hnm] at this

section Head

set_option linter.unusedVariables false

variable {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []} {c : Compiled a}

theorem compile_checks (h : compile b Λ e = some ⟨a, c⟩) :
    Nominal.FCn.checkTm .nil c.deriv.translate c.ty.translate = true :=
  Nominal.FCn.checkTm_iff.mpr (Nominal.Source.HasTy.translate_typed c.deriv .nil)

theorem compile_checks_get (h : (compile b Λ e).isSome = true) :
    Nominal.FCn.checkTm .nil ((compile b Λ e).get h).2.deriv.translate
      ((compile b Λ e).get h).2.ty.translate = true :=
  compile_checks (Option.some_get h).symm

theorem compile_safe (h : compile b Λ e = some ⟨a, c⟩) {c' : Nominal.Source.Conf}
    (hc : Nominal.Source.Reds ⟨[], .nil, a.erase⟩ c') :
    (Nominal.Source.NormForm c'.tm ∨ ∃ c'', Nominal.Source.Step c' c'') ∧
    (∀ p, c'.tm = .path p → Nominal.Source.PathSafe c'.store p) :=
  Nominal.safety c.deriv hc

theorem compile_erase (h : compile b Λ e = some ⟨a, c⟩) :
    c.deriv.translate.erase = a.erase.erase :=
  Nominal.Source.HasTy.translate_erase c.deriv

theorem compile_reachable (h : compile b Λ e = some ⟨a, c⟩) {c' : Nominal.Source.Conf}
    (hc : Nominal.Source.Reds ⟨[], .nil, a.erase⟩ c') :
    ∃ (st : Nominal.FCn.State c'.s) (ρ : Rename [] c'.s),
      st.Typed (c.ty.translate.rename ρ) ∧ st.erase = c'.erase ∧
      ∀ Γ, Nominal.FCn.Store.Typed st.σ Γ → ¬ ∃ ev, Nominal.FCn.LeCo.HasType Γ ev Nominal.FCn.Ty.top Nominal.FCn.Ty.bot :=
  Nominal.reachable_typed c.deriv hc

theorem compile_lockstep (h : compile b Λ e = some ⟨a, c⟩) {c' : Nominal.Source.Conf}
    (hc : Nominal.Source.Reds ⟨[], .nil, a.erase⟩ c') :
    ∃ st : Nominal.FCn.State c'.s,
      Nominal.FCn.Steps Nominal.FCn.appView ⟨.nil, .nil, c.deriv.translate⟩ st ∧ st.erase = c'.erase :=
  Nominal.reachable_run c.deriv hc

theorem compile_run_progress (h : compile b Λ e = some ⟨a, c⟩) (n m : Nat) :
    let c' := Nominal.Source.runFuel n m ⟨[], .nil, a.erase⟩
    Nominal.Source.NormForm c'.tm ∨ ∃ c'', Nominal.Source.Step c' c'' :=
  (compile_safe h (Nominal.Source.Reds.of_runFuel n m _)).1

theorem compile_ann (h : compile b Λ e = some ⟨a, c⟩) : c.ann.erase = c.deriv := rfl

theorem compileAndRun_eq (h : compile b Λ e = some ⟨a, c⟩) (n m : Nat) :
    compileAndRun b n m Λ e = some (Nominal.Source.runFuel n m ⟨[], .nil, a.erase⟩) := by
  simp only [compileAndRun, h, Option.map_some]

theorem compileAndRun_progress (h : compile b Λ e = some ⟨a, c⟩) {n m : Nat} {c' : Nominal.Source.Conf}
    (hr : compileAndRun b n m Λ e = some c') :
    Nominal.Source.NormForm c'.tm ∨ ∃ c'', Nominal.Source.Step c' c'' := by
  rw [compileAndRun_eq h] at hr
  cases hr
  exact compile_run_progress h n m

theorem compileAndRunFC_eq (h : compile b Λ e = some ⟨a, c⟩) (m : Nat) :
    compileAndRunFC b m Λ e = some (Nominal.Translation.runOf m ⟨[], ⟨.nil, .nil, c.deriv.translate⟩⟩) := by
  simp only [compileAndRunFC, h, Option.map_some]

theorem compileAndRunFC_reaches (h : compile b Λ e = some ⟨a, c⟩) {m : Nat}
    {r : (s : Sig) × Nominal.FCn.State s} (hr : compileAndRunFC b m Λ e = some r) :
    Nominal.FCn.Steps Nominal.FCn.appView ⟨.nil, .nil, c.deriv.translate⟩ r.2 := by
  rw [compileAndRunFC_eq h] at hr
  cases hr
  exact Nominal.Translation.steps_of_runOf m ⟨[], ⟨.nil, .nil, c.deriv.translate⟩⟩

theorem compileAndRunFC_typed (h : compile b Λ e = some ⟨a, c⟩) {m : Nat}
    {r : (s : Sig) × Nominal.FCn.State s} (hr : compileAndRunFC b m Λ e = some r) :
    ∃ ρ : Rename [] r.1, r.2.Typed (c.ty.translate.rename ρ) :=
  Nominal.FCn.Steps.typed (Nominal.image_typed c.deriv) (compileAndRunFC_reaches h hr)

theorem compileAndRunFC_consistent (h : compile b Λ e = some ⟨a, c⟩) {m : Nat}
    {r : (s : Sig) × Nominal.FCn.State s} (hr : compileAndRunFC b m Λ e = some r) :
    ∃ Γ : Nominal.FCn.Ctx r.1, Nominal.FCn.Store.Typed r.2.σ Γ ∧
      ¬ ∃ ev, Nominal.FCn.LeCo.HasType Γ ev Nominal.FCn.Ty.top Nominal.FCn.Ty.bot :=
  Nominal.FCn.reachable_consistent (Nominal.Source.HasTy.translate_typed c.deriv .nil) (compileAndRunFC_reaches h hr)

theorem checkAt_mono {a : ATm []} {T : Ty []} {d : AHasTy .nil a T} (h : checkAt b a T = some d)
    {n : Nat} (hn : b.fuel ≤ n) : checkAt { b with fuel := n } a T = some d :=
  checkTopF_mono h hn

theorem compileLanded_mono {a : ATm []} {c : Compiled a} (h : compileLanded b a = some c)
    {n : Nat} (hn : b.fuel ≤ n) : compileLanded { b with fuel := n } a = some c := by
  unfold compileLanded compileLandedF at h ⊢
  simp only [Option.map_eq_some_iff] at h ⊢
  obtain ⟨c', h', rfl⟩ := h
  exact ⟨c', synthTopF_mono h' hn, rfl⟩

end Head

/-- A compile succeeds when `compileLanded` accepts the resolved term.  Proved from
`compile_full` alone, so it keeps its proof when XF3a replaces the body of `compile`. -/
theorem compile_isSome {b : Budget} {Λ : LabelTable} {e : STm}
    (h : (resolve Λ e).any (fun a => (compileLanded b a).isSome) = true) : (compile b Λ e).isSome = true := by
  cases hr : resolve Λ e with
  | none => simp [hr] at h
  | some a =>
    rw [compile_full hr]
    simp only [hr, Option.any_some] at h
    simpa [Option.isSome_map] using h

/-! ## Checks

The nine hand programs of `Sources.lean`, each checked at the type of its hand
derivation, compiled, and its image accepted by the FCn checker.  Then N1 to N3
rejected with the tank unmarked, N1 with no compile, the refuter's program G1,
and the cost of E6.  N1 and N2 are rejected by the shape of a path definition
under a declared type that is no singleton, at 0 units, so they do not exercise
the bad bounds their names suggest.  N3 is rejected at the first view of
`x.zz`. -/

section Checks

open NominalFrontend.Sources
open Nominal.Source (e1_Td e2_Tz compiler_T list_T sngl_T e13_T)

theorem E1_checkAt : (resolve Λ1 E1_src).any (fun a => (checkAt {} a (.mu e1_Td)).isSome) = true := by decide +kernel
theorem E1_landed : (resolve Λ1 E1_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E1_compiles : (compile {} Λ1 E1_src).isSome = true := compile_isSome E1_landed
theorem E1_checks : Nominal.FCn.checkTm .nil ((compile {} Λ1 E1_src).get E1_compiles).2.deriv.translate
    ((compile {} Λ1 E1_src).get E1_compiles).2.ty.translate = true := compile_checks_get E1_compiles

theorem E2_checkAt : (resolve Λ2 E2_src).any (fun a => (checkAt {} a (.mu e2_Tz)).isSome) = true := by decide +kernel
theorem E2_landed : (resolve Λ2 E2_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E2_compiles : (compile {} Λ2 E2_src).isSome = true := compile_isSome E2_landed
theorem E2_checks : Nominal.FCn.checkTm .nil ((compile {} Λ2 E2_src).get E2_compiles).2.deriv.translate
    ((compile {} Λ2 E2_src).get E2_compiles).2.ty.translate = true := compile_checks_get E2_compiles

theorem E3_checkAt : (resolve Λ3 E3_src).any (fun a => (checkAt {} a compiler_T).isSome) = true := by decide +kernel
theorem E3_landed : (resolve Λ3 E3_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E3_compiles : (compile {} Λ3 E3_src).isSome = true := compile_isSome E3_landed
theorem E3_checks : Nominal.FCn.checkTm .nil ((compile {} Λ3 E3_src).get E3_compiles).2.deriv.translate
    ((compile {} Λ3 E3_src).get E3_compiles).2.ty.translate = true := compile_checks_get E3_compiles

theorem E4_checkAt : (resolve Λ4 E4_src).any (fun a => (checkAt {} a list_T).isSome) = true := by decide +kernel
theorem E4_landed : (resolve Λ4 E4_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E4_compiles : (compile {} Λ4 E4_src).isSome = true := compile_isSome E4_landed
theorem E4_checks : Nominal.FCn.checkTm .nil ((compile {} Λ4 E4_src).get E4_compiles).2.deriv.translate
    ((compile {} Λ4 E4_src).get E4_compiles).2.ty.translate = true := compile_checks_get E4_compiles

theorem E5_checkAt : (resolve Λ5 E5_src).any (fun a => (checkAt {} a sngl_T).isSome) = true := by decide +kernel
theorem E5_landed : (resolve Λ5 E5_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E5_compiles : (compile {} Λ5 E5_src).isSome = true := compile_isSome E5_landed
theorem E5_checks : Nominal.FCn.checkTm .nil ((compile {} Λ5 E5_src).get E5_compiles).2.deriv.translate
    ((compile {} Λ5 E5_src).get E5_compiles).2.ty.translate = true := compile_checks_get E5_compiles

theorem E6_checkAt : (resolve Λ6 E6_src).any (fun a => (checkAt {} a .top).isSome) = true := by decide +kernel
theorem E6_landed : (resolve Λ6 E6_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E6_compiles : (compile {} Λ6 E6_src).isSome = true := compile_isSome E6_landed
theorem E6_checks : Nominal.FCn.checkTm .nil ((compile {} Λ6 E6_src).get E6_compiles).2.deriv.translate
    ((compile {} Λ6 E6_src).get E6_compiles).2.ty.translate = true := compile_checks_get E6_compiles

theorem E7_checkAt : (resolve Λ7 E7_src).any (fun a => (checkAt {} a .top).isSome) = true := by decide +kernel
theorem E7_landed : (resolve Λ7 E7_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E7_compiles : (compile {} Λ7 E7_src).isSome = true := compile_isSome E7_landed
theorem E7_checks : Nominal.FCn.checkTm .nil ((compile {} Λ7 E7_src).get E7_compiles).2.deriv.translate
    ((compile {} Λ7 E7_src).get E7_compiles).2.ty.translate = true := compile_checks_get E7_compiles

theorem E8_checkAt : (resolve Λ8 E8_src).any (fun a => (checkAt {} a .top).isSome) = true := by decide +kernel
theorem E8_landed : (resolve Λ8 E8_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E8_compiles : (compile {} Λ8 E8_src).isSome = true := compile_isSome E8_landed
theorem E8_checks : Nominal.FCn.checkTm .nil ((compile {} Λ8 E8_src).get E8_compiles).2.deriv.translate
    ((compile {} Λ8 E8_src).get E8_compiles).2.ty.translate = true := compile_checks_get E8_compiles

theorem E13_checkAt : (resolve Λ13 E13_src).any (fun a => (checkAt {} a (.mu e13_T)).isSome) = true := by decide +kernel
theorem E13_landed : (resolve Λ13 E13_src).any (fun a => (compileLanded {} a).isSome) = true := by decide +kernel
theorem E13_compiles : (compile {} Λ13 E13_src).isSome = true := compile_isSome E13_landed
theorem E13_checks : Nominal.FCn.checkTm .nil ((compile {} Λ13 E13_src).get E13_compiles).2.deriv.translate
    ((compile {} Λ13 E13_src).get E13_compiles).2.ty.translate = true := compile_checks_get E13_compiles
theorem N1_rejected : (resolve ΛN1 N1_src).any (fun a => rejected (compileLandedF {} a)) = true := by decide +kernel
theorem N2_rejected : (resolve ΛN2 N2_src).any (fun a => rejected (compileLandedF {} a)) = true := by decide +kernel
theorem N3_rejected : (resolve ΛN3 N3_src).any (fun a => rejected (compileLandedF {} a)) = true := by decide +kernel
theorem N1_compile : compile {} ΛN1 N1_src = none := by decide +kernel

/-- The labels of the refuter's program G1. -/
def ΛG : LabelTable := [("A", .typ 0), ("c", .trm 0)]
/-- G1: a binder with two upper bounds of `A`, typed through their meet. -/
def G1_src : STm := pdc%
  (λ(f : ∀(z : {A : ⊥..⊤} ∧ {A : ⊥..{c : ⊤}}) z.A). λ(x : {A : ⊥..⊤} ∧ {A : ⊥..{c : ⊤}}). let y = x in f y
    : ∀(f : ∀(z : {A : ⊥..⊤} ∧ {A : ⊥..{c : ⊤}}) z.A) ∀(x : ({A : ⊥..⊤} ∧ {A : ⊥..{c : ⊤}}) ∧ ⊤) {c : ⊤})
theorem G1_compiles : (compile {} ΛG G1_src).isSome = true := by decide +kernel

theorem E6_cost : (resolve Λ6 E6_src).any (fun a => used (checkAtF {} a .top) ≤ 11000) = true := by decide +kernel

end Checks

/-! ## The elaborator's checks -/

namespace ElabChecks

open NominalFrontend.Sources

/-! ### The reasons of `compileE` -/

section Reasons

/-- The labels of the small programs. -/
def ΛS : LabelTable := [("a", .trm 0), ("b", .trm 1), ("f", .trm 2), ("m", .trm 3)]
/-- A lambda with no goal and no callee. -/
def Miss_src : STm := pdc% λx. x
/-- Two lambda fields that read each other. -/
def Cyc_src : STm := pdc% ν(x) {a = λ(u : ⊤). x.b u, b = λ(u : ⊤). x.a u}
/-- A lambda field that reads itself. -/
def Rec_src : STm := pdc% ν(x) {f = λ(u : ⊤). x.f u}
/-- A lambda field whose candidates `r.type` and `{a : ⊤}` pDOT does not compare. -/
def Amb_src : STm := pdc% λ(r : {a : ⊤}). ν(x) {m = r, f = λ(u : ⊤). x.m}
/-- The class of XF2's item 7: a `widen` binding of an application at the singleton of a path that is
no module, in the Scala mode. -/
def Wd_src : STm := .lam "g" (some (.all "z" .top (.sngl (.var "z")))) (.lam "q" (some .top)
  (.obj "x" none (.trm .nil "f" none (.lam "u" (some .top) (.bind .widen "v" (.app (.var "g") (.var "q")) (.var "v"))))))
/-- A domain from an ascription. -/
def Dom_src : STm := pdc% (λx. x : ∀(z : ⊤) ⊤)
/-- A domain from the dominant formal of the callee of a call argument. -/
def Arg_src : STm := pdc% λ(f : ∀(g : ∀(z : ⊤) ⊤) ⊤). f (λx. x)
/-- A domain from the callee of the body, with no goal. -/
def Callee_src : STm := pdc% λ(g : ∀(z : ⊤) ⊤). let h = λx. g x in h

theorem Miss_reason : compileReason {} ΛS Miss_src = some (.missingParamType none) := by decide +kernel
theorem Cyc_reason : compileReason {} ΛS Cyc_src = some (.cyclicRef (.trm 0)) := by decide +kernel
theorem Rec_reason : compileReason {} ΛS Rec_src = some (.cyclicRef (.trm 2)) := by decide +kernel
theorem Amb_reason : compileReason {} ΛS Amb_src = some (.ambiguous (.trm 2)) := by decide +kernel
theorem Amb_scala : (compile { mode := .scala } ΛS Amb_src).isSome = true := by decide +kernel
theorem Wd_reason : compileReason { mode := .scala } ΛS Wd_src = some .mismatch := by decide +kernel
theorem Dom_ok : (compile {} ΛS Dom_src).isSome = true := by decide +kernel
theorem Arg_ok : (compile {} ΛS Arg_src).isSome = true := by decide +kernel
theorem Callee_ok : (compile {} ΛS Callee_src).isSome = true := by decide +kernel
/-- No fuel: the tank ends marked, and the reason is the limit. -/
theorem Amb_limit : compileReason { fuel := 0 } ΛS Amb_src = some .limit := by decide +kernel
/-- A program with every slot written: `compileE` agrees with `compileLanded` (`compile_full`). -/
theorem E1_full : (compile {} Λ1 E1_src).map (fun r => r.2.ty) =
    ((resolve Λ1 E1_src).bind fun a => (compileLanded {} a).map (·.ty)) := by decide +kernel

end Reasons

end ElabChecks

namespace ElabChecks

open NominalFrontend.Sources
open Nominal.Source (E1_prog E2_prog compiler_t list_t sngl_t E6_prog E7_prog E8_prog e13_lit)

/-! ### The programs with their slots erased

`Ek_srcI` is `Ek_src` of `Sources.lean` with every self type and every lambda domain erased that a
goal or the definitions give.  E1, E2 and E13 keep none.  The others keep a self type that gives a
lambda field its domain, or a declared type that differs from the least one, and a lambda domain
that no goal reaches.  `Ek_srcE` erases every one, `Ek_srcB` every self type and no domain. -/

section Fills

def E1_srcI : STm := pdc%
  let dotty = ν(d) {
    core = ν(c) {
      types = ν(t) {type «Type» = ⊤, type TypeRef = t.«Type» ∧ {symb : c.symbols.Symbol}},
      symbols = ν(s) {type Symbol = {tpe : c.types.«Type»}}}} in dotty

def E2_srcI : STm := pdc%
  let x = ν(z) {c = ν(w) {type A = z.B}, type B = z.c.A} in x

def E3_srcI : STm := pdc%
  ν(r : {DottyCore : μ(c. {types : μ(t. {Tpe : ⊥..⊤} ∧ {typeRef : ∀(s : c.symbols.Symbol) t.Tpe ∧ {symb : c.symbols.Symbol}})}
                         ∧ {symbols : μ(y. {Symbol : ⊥..⊤} ∧ {symbol : ∀(u : c.types.Tpe) y.Symbol ∧ {tpe : c.types.Tpe}})})
                 .. μ(c. {types : μ(t. {Tpe : ⊥..⊤} ∧ {typeRef : ∀(s : c.symbols.Symbol) t.Tpe ∧ {symb : c.symbols.Symbol}})}
                         ∧ {symbols : μ(y. {Symbol : ⊥..⊤} ∧ {symbol : ∀(u : c.types.Tpe) y.Symbol ∧ {tpe : c.types.Tpe}})})}
        ∧ {dottyCore : ∀(e : ⊤) r.DottyCore}) {
    type DottyCore = μ(c. {types : μ(t. {Tpe : ⊥..⊤} ∧ {typeRef : ∀(s : c.symbols.Symbol) t.Tpe ∧ {symb : c.symbols.Symbol}})}
                         ∧ {symbols : μ(y. {Symbol : ⊥..⊤} ∧ {symbol : ∀(u : c.types.Tpe) y.Symbol ∧ {tpe : c.types.Tpe}})}),
    dottyCore = λe. let k = ν(c) {
      types = ν(t : {Tpe : μ(o. {denotation : ∀(z : ⊤) ⊤})..μ(o. {denotation : ∀(z : ⊤) ⊤})}
                      ∧ {typeRef : ∀(s : c.symbols.Symbol) t.Tpe ∧ {symb : c.symbols.Symbol}}) {
        type Tpe = μ(o. {denotation : ∀(z : ⊤) ⊤}),
        typeRef = λs. let o = ν(o) {symb = s, denotation = λ(z : ⊤). z} in o},
      symbols = ν(y : {Symbol : μ(o. {srcPos : ∀(z : ⊤) ⊤})..μ(o. {srcPos : ∀(z : ⊤) ⊤})}
                      ∧ {symbol : ∀(u : c.types.Tpe) y.Symbol ∧ {tpe : c.types.Tpe}}) {
        type Symbol = μ(o. {srcPos : ∀(z : ⊤) ⊤}),
        symbol = λu. let o = ν(o) {tpe = u, srcPos = λ(z : ⊤). z} in o}} in k}

def E4_srcI : STm := pdc%
  ν(sci : ({List : μ(l. ({A : ⊥..⊤} ∧ {head : ∀(u : ⊤) l.A}) ∧ {tail : ∀(u : ⊤) sci.List ∧ {A : ⊥..l.A}})
                 .. μ(l. ({A : ⊥..⊤} ∧ {head : ∀(u : ⊤) l.A}) ∧ {tail : ∀(u : ⊤) sci.List ∧ {A : ⊥..l.A}})}
           ∧ {Nil : ∀(x : {A : ⊥..⊤}) sci.List ∧ {A : ⊥..⊥}})
          ∧ {Cons : ∀(x : {A : ⊥..⊤}) ∀(y : x.A) ∀(ys : sci.List ∧ {A : ⊥..x.A}) sci.List ∧ {A : ⊥..x.A}}) {
    type List = μ(l. ({A : ⊥..⊤} ∧ {head : ∀(u : ⊤) l.A}) ∧ {tail : ∀(u : ⊤) sci.List ∧ {A : ⊥..l.A}}),
    Nil = λx.
      let r = ν(r : ({A : ⊥..⊥} ∧ {head : ∀(u : ⊤) r.A}) ∧ {tail : ∀(u : ⊤) sci.List ∧ {A : ⊥..r.A}}) {
        type A = ⊥, head = λu. r.head u, tail = λu. r.tail u} in r,
    Cons = λx. λy. λys.
      let r = ν(r : ({A : x.A..x.A} ∧ {head : ∀(u : ⊤) r.A}) ∧ {tail : ∀(u : ⊤) sci.List ∧ {A : ⊥..x.A}}) {
        type A = x.A, head = λu. y, tail = λu. ys} in r}

def E5_srcI : STm := pdc%
  let x = ν(x : ({C : μ(c. {incr : c.type})..μ(c. {incr : c.type})}
                 ∧ {D : μ(d. x.C ∧ {decr : d.type})..μ(d. x.C ∧ {decr : d.type})})
                ∧ {d : ∀(u : ⊤) x.D}) {
    type C = μ(c. {incr : c.type}), type D = μ(d. x.C ∧ {decr : d.type}),
    d = λu. let o = ν(o) {incr = o, decr = o} in o} in
  let z = x.d x in z.incr.decr

def E6_srcI : STm := pdc%
  let options = ν(o) {type Option = ⊤} in
  let pcore = ν(p :
      {types : μ(t. ((({«Type» : ⊤..⊤} ∧ {TypeTop : t.«Type»..t.«Type»}) ∧ {newTypeTop : ∀(u : ⊤) t.TypeTop})
                     ∧ {TypeRef : t.«Type» ∧ {symb : p.symbols.Symbol} .. t.«Type» ∧ {symb : p.symbols.Symbol}})
                    ∧ {newTypeRef : ∀(s : p.symbols.Symbol) t.TypeRef})}
      ∧ {symbols : μ(y. {Symbol : {tpe : options.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}}
                           .. {tpe : options.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}}}
                       ∧ {newSymbol : ∀(u : options.Option ∧ {A : ⊥..p.types.«Type»}) ∀(i : {n : ⊤}) y.Symbol})}) {
    types = ν(t) {
      type «Type» = ⊤, type TypeTop = t.«Type», newTypeTop = λu. u,
      type TypeRef = t.«Type» ∧ {symb : p.symbols.Symbol},
      newTypeRef = λs. let r = ν(r) {symb = s} in r},
    symbols = ν(y) {
      type Symbol = {tpe : options.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}},
      newSymbol = λu. λi. let r = ν(r) {tpe = u, id = i} in r}} in
  let pc = pcore in pc

def E7_srcI : STm := pdc%
  let core = ν(c) {types = ν(t) {type A = ⊤, f = λ(u : ⊤). u}, m = c.types} in
  core.m.f core

def E8_srcI : STm := pdc%
  let g = λ(x : {A : ⊥..⊤} ∧ {f : ∀(u : ⊤) ⊤}). λ(y : x.type). λ(v : y.A). let w = y.f v in v in
  let o = ν(o) {type A = ⊤, f = λ(u : ⊤). u, me = o} in
  let h = g o in let k = h o.me in k o

def E13_srcI : STm := pdc% ν(x) {a = x.a}


def ΛN4 : LabelTable := [("A", .typ 0)]
def N4_src : STm := pdc% λ(x : {A : ⊤..⊤}). (x : x.type)

/-- The labels of the plan's risk and of the cross program. -/
def ΛR : LabelTable := [("o", .trm 0), ("p", .trm 1), ("g", .trm 2), ("f", .trm 3), ("h", .trm 4)]
def Risk_src : STm := pdc% ν(x) {o = ν(y) {p = ν(z) {g = λ(w : ⊤). x.f w}}, f = λ(u : ⊤). u}
def Cross_src : STm := pdc% ν(x) {o = ν(y) {h = λ(u : ⊤). u, g = λ(w : ⊤). x.f w}, f = λ(u : ⊤). x.o.h u}
/-- `Cross_src` with `h`'s declared type written: `o` still waits for `f`, and `f` for `o`. -/
def Cross_h : STm := pdc% ν(x) {o = ν(y) {h : ∀(u : ⊤) ⊤ = λ(u : ⊤). u, g = λ(w : ⊤). x.f w}, f = λ(u : ⊤). x.o.h u}

/-- The labels of the programs that reach a field through a path field. -/
def ΛA : LabelTable := [("m", .trm 0), ("f", .trm 1), ("g", .trm 2), ("o", .trm 3), ("p", .trm 4)]
/-- `g` reaches the pending field `f` through the path field `m`, known at once. -/
def A1_src : STm := pdc% ν(x) {m = x.f, f = λ(u : ⊤). u, g = λ(u : ⊤). x.m u}
/-- The same across three levels: the inner field `g` reaches the outer `f` through `m`. -/
def A4_src : STm := pdc% ν(x) {o = ν(y) {p = ν(z) {g = λ(w : ⊤). x.m w}}, m = x.f, f = λ(u : ⊤). u}
/-- The labels of the Scala shape. -/
def ΛA5 : LabelTable := [("o", .trm 0), ("h", .trm 1), ("m", .trm 2), ("g", .trm 3)]
/-- `object x { object o { def h(u: Any) = u }; val m: o.type = o; def g(u: Any) = m.h(u) }`. -/
def A5_src : STm := pdc% ν(x) {o = ν(y) {h = λ(u : ⊤). u}, m = x.o, g = λ(u : ⊤). x.m.h u}

/-- The labels of the declared nested literals. -/
def ΛB : LabelTable := [("c", .trm 0), ("f", .trm 1), ("A", .typ 0)]
/-- The declaration `{c : μ(y. U)}` gives the nested literal `U` and its field the domain `y.A`. -/
def B1_src : STm := pdc% ν(x : {c : μ(y. {A : ⊤..⊤} ∧ {f : ∀(z : y.A) y.A})}) {c = ν(y) {type A = ⊤, f = λz. z}}
/-- A declaration that differs from the self type the definitions would form. -/
def B2_src : STm := pdc% ν(x : {c : μ(y. {f : ∀(z : ⊤) ⊤})}) {c = ν(y) {f = λ(z : ⊤). x}}

def E3_srcE : STm := pdc%
  ν(r) {
    type DottyCore = μ(c. {types : μ(t. {Tpe : ⊥..⊤} ∧ {typeRef : ∀(s : c.symbols.Symbol) t.Tpe ∧ {symb : c.symbols.Symbol}})}
                         ∧ {symbols : μ(y. {Symbol : ⊥..⊤} ∧ {symbol : ∀(u : c.types.Tpe) y.Symbol ∧ {tpe : c.types.Tpe}})}),
    dottyCore = λe. let k = ν(c) {
      types = ν(t) {
        type Tpe = μ(o. {denotation : ∀(z : ⊤) ⊤}),
        typeRef = λs. let o = ν(o) {symb = s, denotation = λz. z} in o},
      symbols = ν(y) {
        type Symbol = μ(o. {srcPos : ∀(z : ⊤) ⊤}),
        symbol = λu. let o = ν(o) {tpe = u, srcPos = λz. z} in o}} in k}

def E3_srcB : STm := pdc%
  ν(r) {
    type DottyCore = μ(c. {types : μ(t. {Tpe : ⊥..⊤} ∧ {typeRef : ∀(s : c.symbols.Symbol) t.Tpe ∧ {symb : c.symbols.Symbol}})}
                         ∧ {symbols : μ(y. {Symbol : ⊥..⊤} ∧ {symbol : ∀(u : c.types.Tpe) y.Symbol ∧ {tpe : c.types.Tpe}})}),
    dottyCore = λ(e : ⊤). let k = ν(c) {
      types = ν(t) {
        type Tpe = μ(o. {denotation : ∀(z : ⊤) ⊤}),
        typeRef = λ(s : c.symbols.Symbol). let o = ν(o) {symb = s, denotation = λ(z : ⊤). z} in o},
      symbols = ν(y) {
        type Symbol = μ(o. {srcPos : ∀(z : ⊤) ⊤}),
        symbol = λ(u : c.types.Tpe). let o = ν(o) {tpe = u, srcPos = λ(z : ⊤). z} in o}} in k}

def E4_srcE : STm := pdc%
  ν(sci) {
    type List = μ(l. ({A : ⊥..⊤} ∧ {head : ∀(u : ⊤) l.A}) ∧ {tail : ∀(u : ⊤) sci.List ∧ {A : ⊥..l.A}}),
    Nil = λx.
      let r = ν(r) {type A = ⊥, head = λu. r.head u, tail = λu. r.tail u} in r,
    Cons = λx. λy. λys.
      let r = ν(r) {type A = x.A, head = λu. y, tail = λu. ys} in r}

def E4_srcB : STm := pdc%
  ν(sci) {
    type List = μ(l. ({A : ⊥..⊤} ∧ {head : ∀(u : ⊤) l.A}) ∧ {tail : ∀(u : ⊤) sci.List ∧ {A : ⊥..l.A}}),
    Nil = λ(x : {A : ⊥..⊤}).
      let r = ν(r) {type A = ⊥, head = λ(u : ⊤). r.head u, tail = λ(u : ⊤). r.tail u} in r,
    Cons = λ(x : {A : ⊥..⊤}). λ(y : x.A). λ(ys : sci.List ∧ {A : ⊥..x.A}).
      let r = ν(r) {type A = x.A, head = λ(u : ⊤). y, tail = λ(u : ⊤). ys} in r}

def E5_srcE : STm := pdc%
  let x = ν(x) {
    type C = μ(c. {incr : c.type}), type D = μ(d. x.C ∧ {decr : d.type}),
    d = λu. let o = ν(o) {incr = o, decr = o} in o} in
  let z = x.d x in z.incr.decr

def E5_srcB : STm := pdc%
  let x = ν(x) {
    type C = μ(c. {incr : c.type}), type D = μ(d. x.C ∧ {decr : d.type}),
    d = λ(u : ⊤). let o = ν(o) {incr = o, decr = o} in o} in
  let z = x.d x in z.incr.decr

def E6_srcE : STm := pdc%
  let options = ν(o) {type Option = ⊤} in
  let pcore = ν(p) {
    types = ν(t) {
      type «Type» = ⊤, type TypeTop = t.«Type», newTypeTop = λu. u,
      type TypeRef = t.«Type» ∧ {symb : p.symbols.Symbol},
      newTypeRef = λs. let r = ν(r) {symb = s} in r},
    symbols = ν(y) {
      type Symbol = {tpe : options.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}},
      newSymbol = λu. λi. let r = ν(r) {tpe = u, id = i} in r}} in
  let pc = pcore in pc

def E6_srcB : STm := pdc%
  let options = ν(o) {type Option = ⊤} in
  let pcore = ν(p) {
    types = ν(t) {
      type «Type» = ⊤, type TypeTop = t.«Type», newTypeTop = λ(u : ⊤). u,
      type TypeRef = t.«Type» ∧ {symb : p.symbols.Symbol},
      newTypeRef = λ(s : p.symbols.Symbol). let r = ν(r) {symb = s} in r},
    symbols = ν(y) {
      type Symbol = {tpe : options.Option ∧ {A : ⊥..p.types.«Type»}} ∧ {id : {n : ⊤}},
      newSymbol = λ(u : options.Option ∧ {A : ⊥..p.types.«Type»}). λ(i : {n : ⊤}). let r = ν(r) {tpe = u, id = i} in r}} in
  let pc = pcore in pc

def E7_srcE : STm := pdc%
  let core = ν(c) {types = ν(t) {type A = ⊤, f = λu. u}, m = c.types} in
  core.m.f core

def E8_srcE : STm := pdc%
  let g = λx. λy. λv. let w = y.f v in v in
  let o = ν(o) {type A = ⊤, f = λu. u, me = o} in
  let h = g o in let k = h o.me in k o

abbrev la : Label := .trm 0
abbrev lp : Label := .trm 1
abbrev lg : Label := .trm 2
abbrev lf : Label := .trm 3
/-- The type of the three-level literal. -/
def RiskT : Ty [] := .mu (.and (.rcd (.trm la (.mu (.rcd (.trm lp (.mu (.rcd (.trm lg (.all .top .top)))))))))
  (.rcd (.trm lf (.all .top .top))))

theorem E1_fill : (compile {} Λ1 E1_srcI).map (fun r => r.1.erase) = some E1_prog := by decide +kernel
theorem E2_fill : (compile {} Λ2 E2_srcI).map (fun r => r.1.erase) = some E2_prog := by decide +kernel
theorem E3_fill : (compile {} Λ3 E3_srcI).map (fun r => r.1.erase) = some compiler_t := by decide +kernel
theorem E4_fill : (compile {} Λ4 E4_srcI).map (fun r => r.1.erase) = some list_t := by decide +kernel
theorem E5_fill : (compile {} Λ5 E5_srcI).map (fun r => r.1.erase) = some sngl_t := by decide +kernel
theorem E6_fill : (compile {} Λ6 E6_srcI).map (fun r => r.1.erase) = some E6_prog := by decide +kernel
theorem E7_fill : (compile {} Λ7 E7_srcI).map (fun r => r.1.erase) = some E7_prog := by decide +kernel
theorem E8_fill : (compile {} Λ8 E8_srcI).map (fun r => r.1.erase) = some E8_prog := by decide +kernel
theorem E13_fill : (compile {} Λ13 E13_srcI).map (fun r => r.1.erase) = some (.val e13_lit) := by decide +kernel

theorem E1_compilesI : (compile {} Λ1 E1_srcI).isSome = true := by
  simpa [Option.isSome_map] using congrArg Option.isSome E1_fill
theorem E1_checksI : Nominal.FCn.checkTm .nil ((compile {} Λ1 E1_srcI).get E1_compilesI).2.deriv.translate
    ((compile {} Λ1 E1_srcI).get E1_compilesI).2.ty.translate = true := compile_checks_get E1_compilesI
theorem E2_compilesI : (compile {} Λ2 E2_srcI).isSome = true := by
  simpa [Option.isSome_map] using congrArg Option.isSome E2_fill
theorem E2_checksI : Nominal.FCn.checkTm .nil ((compile {} Λ2 E2_srcI).get E2_compilesI).2.deriv.translate
    ((compile {} Λ2 E2_srcI).get E2_compilesI).2.ty.translate = true := compile_checks_get E2_compilesI
theorem E3_compilesI : (compile {} Λ3 E3_srcI).isSome = true := by
  simpa [Option.isSome_map] using congrArg Option.isSome E3_fill
theorem E3_checksI : Nominal.FCn.checkTm .nil ((compile {} Λ3 E3_srcI).get E3_compilesI).2.deriv.translate
    ((compile {} Λ3 E3_srcI).get E3_compilesI).2.ty.translate = true := compile_checks_get E3_compilesI
theorem E4_compilesI : (compile {} Λ4 E4_srcI).isSome = true := by
  simpa [Option.isSome_map] using congrArg Option.isSome E4_fill
theorem E4_checksI : Nominal.FCn.checkTm .nil ((compile {} Λ4 E4_srcI).get E4_compilesI).2.deriv.translate
    ((compile {} Λ4 E4_srcI).get E4_compilesI).2.ty.translate = true := compile_checks_get E4_compilesI
theorem E5_compilesI : (compile {} Λ5 E5_srcI).isSome = true := by
  simpa [Option.isSome_map] using congrArg Option.isSome E5_fill
theorem E5_checksI : Nominal.FCn.checkTm .nil ((compile {} Λ5 E5_srcI).get E5_compilesI).2.deriv.translate
    ((compile {} Λ5 E5_srcI).get E5_compilesI).2.ty.translate = true := compile_checks_get E5_compilesI
theorem E6_compilesI : (compile {} Λ6 E6_srcI).isSome = true := by
  simpa [Option.isSome_map] using congrArg Option.isSome E6_fill
theorem E6_checksI : Nominal.FCn.checkTm .nil ((compile {} Λ6 E6_srcI).get E6_compilesI).2.deriv.translate
    ((compile {} Λ6 E6_srcI).get E6_compilesI).2.ty.translate = true := compile_checks_get E6_compilesI
theorem E7_compilesI : (compile {} Λ7 E7_srcI).isSome = true := by
  simpa [Option.isSome_map] using congrArg Option.isSome E7_fill
theorem E7_checksI : Nominal.FCn.checkTm .nil ((compile {} Λ7 E7_srcI).get E7_compilesI).2.deriv.translate
    ((compile {} Λ7 E7_srcI).get E7_compilesI).2.ty.translate = true := compile_checks_get E7_compilesI
theorem E8_compilesI : (compile {} Λ8 E8_srcI).isSome = true := by
  simpa [Option.isSome_map] using congrArg Option.isSome E8_fill
theorem E8_checksI : Nominal.FCn.checkTm .nil ((compile {} Λ8 E8_srcI).get E8_compilesI).2.deriv.translate
    ((compile {} Λ8 E8_srcI).get E8_compilesI).2.ty.translate = true := compile_checks_get E8_compilesI
theorem E13_compilesI : (compile {} Λ13 E13_srcI).isSome = true := by
  simpa [Option.isSome_map] using congrArg Option.isSome E13_fill
theorem E13_checksI : Nominal.FCn.checkTm .nil ((compile {} Λ13 E13_srcI).get E13_compilesI).2.deriv.translate
    ((compile {} Λ13 E13_srcI).get E13_compilesI).2.ty.translate = true := compile_checks_get E13_compilesI

theorem E3_erased : compileReason {} Λ3 E3_srcE = some (.missingParamType none) := by decide +kernel
theorem E4_erased : compileReason {} Λ4 E4_srcE = some (.missingParamType none) := by decide +kernel
theorem E5_erased : compileReason {} Λ5 E5_srcE = some (.missingParamType none) := by decide +kernel
theorem E6_erased : compileReason {} Λ6 E6_srcE = some (.cyclicRef (.trm 0)) := by decide +kernel
theorem E7_erased : compileReason {} Λ7 E7_srcE = some (.missingParamType none) := by decide +kernel
theorem E8_erased : compileReason {} Λ8 E8_srcE = some (.missingParamType none) := by decide +kernel
theorem E3_selfErased : compileReason {} Λ3 E3_srcB = some (.cyclicRef (.trm 1)) := by decide +kernel
theorem E4_selfErased : compileReason {} Λ4 E4_srcB = some (.cyclicRef (.trm 2)) := by decide +kernel
theorem E5_selfErased : compileReason {} Λ5 E5_srcB = some (.ambiguous (.trm 0)) := by decide +kernel
theorem E6_selfErased : compileReason {} Λ6 E6_srcB = some (.cyclicRef (.trm 0)) := by decide +kernel

theorem N4_reason : compileReason {} ΛN4 N4_src = some (.landed (.selfSingleton [])) := by decide +kernel
theorem Risk_ty : (compile {} ΛR Risk_src).map (fun r => r.2.ty) = some RiskT := by decide +kernel
theorem Cross_reason : compileReason {} ΛR Cross_src = some (.cyclicRef (.trm 0)) := by decide +kernel
theorem E3_limit : compileReason { fuel := 512 } Λ3 E3_srcI = some .limit := by decide +kernel
theorem Cross_h_reason : compileReason {} ΛR Cross_h = some (.cyclicRef (.trm 0)) := by decide +kernel
theorem A1_ok : (compile {} ΛA A1_src).isSome = true := by decide +kernel
theorem A4_ok : (compile {} ΛA A4_src).isSome = true := by decide +kernel
theorem A5_ok : (compile {} ΛA5 A5_src).isSome = true := by decide +kernel
theorem A5_scala : (compile { mode := .scala } ΛA5 A5_src).isSome = true := by decide +kernel
theorem B1_ok : (compile {} ΛB B1_src).isSome = true := by decide +kernel
theorem B2_ok : (compile {} ΛB B2_src).isSome = true := by decide +kernel

end Fills

end ElabChecks

end NominalFrontend
