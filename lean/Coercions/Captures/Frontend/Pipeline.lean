import Coercions.Captures.Frontend.Typer
import Coercions.Captures.Frontend.Elab
import Coercions.Captures.Frontend.Step
import Coercions.Captures.DotToFCdot.Prediction
import Coercions.Captures.FCdot.CheckerCompleteness

/-!
# The pipeline

`compile` takes a surface program through the whole front end.  The theorems
say what the result is worth.  Each composes results of the calculus.  The
front end proves nothing about the calculus.

`compileE` resolves a program over a platform to a partial term
(`resolvePTop`), whose empty slots are a lambda's domain, a literal's self
shape and a field's written type, and elaborates it at the platform's context
(`elabTopF`, `Elab.lean`).  A platform is a prefix of capture binders, one per
capability the program may use.  The elaborator returns the typer's own
candidate: the elaborated term, its use set, its type and the derivation of
its erasure.  Box inference may insert `□ x` and `C ⊸ x`, so the elaborated
term is not the program.  The fill is the program with its empty slots filled,
read off the elaborated term in lockstep (`PTm.fillFrom`).  `compileE` keeps
the result when the fill agrees with every slot the program writes and the
elaborated term has the fill's skeleton.  Or it returns the reason the program
is rejected: a missing parameter type, a cyclic reference, candidates with no
least type, a mismatch, or the recursion limit.  `compile` forgets the reason
(`compile_eq`).

`Compiled` holds the elaborated term, its use set, its type, the derivation
about its erasure and the proof that its skeleton is that of the fill.  So the
elaborated program is the fill up to what box inference adds.

The typer types under `platformCtx`.  `platformCtx_eq` equates it with the
calculus's `Platform.ctx`, and `compileE` moves the derivation across, so the
theorems name the calculus's context.

`compileAndRun` follows `compile` with the executable machine of `Step.lean`
from the platform's initial store, at a step budget.

## Theorems

`h : compile b Λ π e = some ⟨a, c⟩` is a successful compile, the platform is
`π.plat`, `a` is the fill and the compiled term is `c.tm.erase`.

* `compile_checks`.  The target checker accepts the translation of the
  derivation.
* `compile_uses_checks`.  It accepts the use set evidence as well.
* `compile_erase`.  The translation erases to the compiled term.
* `compile_faithful`.  The elaborated term has the skeleton of the fill.
* `compile_safe`.  Every state a run reaches is final or has a step.
  `DotMNF.dot_safety` is stated at the empty context only, so this is composed
  at the platform from `Platform.simulatedRun`, `FCdot.State.Typed.steps`,
  `Platform.initial_typed` and `Simulated.progress`.
* `compile_not_stuck`.  No reachable state is stuck.
* `compile_run_progress`.  The state the driver `run` returns is final or the
  executable machine finds a step from it.
* `compile_capture_prediction`.  Along any run, the target machine runs from
  the translation to a typed state with the same erasure, and that state uses
  no more than the translated use set the typer found, renamed along the store
  extension.
* `compile_effect_safety`.  A platform capability that is not in the use set
  is not a root, in that target state, of a variable a run reads.
* `compile_checks_get`, `compile_faithful_get` and `compile_effect_safety_get`.
  The same for a program whose compile succeeds by a decided test.  For a
  concrete program the kernel reduces the compile, so `decide +kernel` closes
  the premises.

The premise `h` is what a caller holds.  The content rides on the type of
`c`.  The other premises select what a theorem speaks of: a run, a variable,
a capability.  None is a hypothesis about the compiler.

The theorems that relate a compilation to the elaborator and to the typer.

* `compile_full`.  A program with every slot written compiles as the typer's
  synthesis on its resolution, at the same fuel (`compileLanded`).
* `compileE_fills`.  The fill agrees with every slot the program writes.
* `compileE_skel`.  The elaborated term has the skeleton of the partial term.
* `compileE_slot`.  The four reasons that name an empty slot come only from a
  program with an empty slot.
* `elabTop?_mono` and `elabTop?_stable`.  An elaboration that ends unmarked
  gives the same verdict at more fuel.
* `elab_complete_direct` and `compile_complete_direct`.  A program whose empty
  slots sit where the elaborator runs the typer's own clause on the fill is
  accepted from some fuel on, and compiles as the typer compiles its fill
  (`canon_lag`).  `compile_complete_canonAt` decides the premises at one fuel
  and concludes that an erased program compiles as its written form does.
-/

namespace CapturesFrontend

open Captures
open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (CapAtom CaptureSet Ty Tm Ctx HasTy State Step Steps Platform)

/-! ## Platform context -/

/-- The front end's platform context is the calculus's. -/
theorem platformCtx_eq {s : Sig} (P : Platform s) : platformCtx P = P.ctx := by
  induction P with
  | nil => rfl
  | cons P ih =>
      rw [platformCtx, ih]
      rfl

/-! ## Result -/

/-- A program typed over a platform, with the fill `a` it came from: the
program with its empty slots filled. -/
structure Compiled {s₀ : Sig} (P : Platform s₀) (a : ATm s₀) where
  /-- The elaborated term. -/
  tm : ATm s₀
  /-- The use set. -/
  uses : CaptureSet s₀
  /-- The type. -/
  ty : Ty s₀
  /-- The derivation. -/
  deriv : HasTy uses P.ctx tm.erase ty
  /-- The elaborated term has the skeleton of the fill. -/
  skel : ATm.skel tm = ATm.skel a

/-! ## The fill

The elaborator returns the typer's candidate, whose term holds what box
inference inserted and the least set the typer found for each literal.  The
fill keeps the program and takes from that term only the slots the program
leaves empty.  Box inference binds a variable at a leaf of the program, never
around a lambda, a literal, a `let` or an ascription, so the two terms walk in
lockstep down to the leaves. -/

mutual
/-- The fill of a partial term, read off its elaborated term.  A term with no
empty slot is its own fill.  An empty domain or self shape takes the one of
the elaborated term at the same place.  A literal keeps the set the program
writes, or none.  `none` when the two terms are out of step. -/
def PTm.fillFrom {s : Sig} (p : PTm s) (t : ATm s) : Option (ATm s) :=
  match p.full? with
  | some a => some a
  | none =>
      match p, t with
      | .lam o p', .lam T t' => (PTm.fillFrom p' t').map (.lam (o.getD T))
      | .obj o U d, .obj S _ e => (PDefs.fillFrom d e).map (.obj (o.getD S) U)
      | .let _ ann p1 p2, .let _ t1 t2 =>
          match PTm.fillFrom p1 t1, PTm.fillFrom p2 t2 with
          | some a1, some a2 => some (.let ann a1 a2)
          | _, _ => none
      | .asc p' T, .asc t' _ => (PTm.fillFrom p' t').map fun a => .asc a T
      | _, _ => none
termination_by structural p
/-- The fill of the definitions of a partial term.  A written field type has
no place in `ADefs` and is dropped, so the fill of `{a : T = t}` is the field
`{a = t'}`. -/
def PDefs.fillFrom {s : Sig} (d : PDefs s) (e : ADefs s) : Option (ADefs s) :=
  match d, e with
  | .typ A S, _ => some (.typ A S)
  | .cap C c, _ => some (.cap C c)
  | .trm a _ t, .trm _ b => (PTm.fillFrom t b).map (.trm a)
  | .and d1 d2, .and e1 e2 =>
      match PDefs.fillFrom d1 e1, PDefs.fillFrom d2 e2 with
      | some f1, some f2 => some (.and f1 f2)
      | _, _ => none
  | _, _ => none
termination_by structural d
end

/-- A partial term with no empty slot is its own fill. -/
theorem PTm.fillFrom_full {s : Sig} {p : PTm s} {a : ATm s} (h : p.full? = some a)
    (t : ATm s) : p.fillFrom t = some a := by
  unfold PTm.fillFrom
  rw [h]

/-! ## Pipeline -/

/-- Resolve over the platform to a partial term, elaborate it at the
platform's context and the budget's fuel, and read off the fill.  The result
is kept when the fill agrees with every written slot and the elaborated term
has its skeleton, and the answer is then the fill with the record.  Otherwise
it is the reason the program is rejected.  A program out of scope or out of
the label table has no resolution, and the reason is a mismatch, which names
no slot.  The result is a dependent pair, since the record speaks of the
fill. -/
def compileE (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) :
    Except EReason ((a : ATm π.sig) × Compiled π.plat a) :=
  match resolvePTop Λ π e with
  | none => .error .mismatch
  | some p =>
      match (elabTopF b.fuel π p).1 with
      | .error r => .error r
      | .ok r =>
          match p.fillFrom r.tm with
          | none => .error .mismatch
          | some a =>
              if p.fills a = true then
                if hs : ATm.skel r.tm = ATm.skel a then
                  .ok ⟨a, ⟨r.tm, r.uses, r.ty, platformCtx_eq π.plat ▸ r.deriv, hs⟩⟩
                else .error .mismatch
              else .error .mismatch

/-- Resolve, elaborate and fill, without the reason.  `none` carries no
reason.  The result is a dependent pair, since the record speaks of the
fill. -/
def compile (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) :
    Option ((a : ATm π.sig) × Compiled π.plat a) :=
  (compileE b Λ π e).toOption

/-- The typer's synthesis on a resolved term with every slot written, as a
compilation: the result is kept when the skeleton is the program's. -/
def compileLanded (b : Budget) (π : PlatformNames) (a : ATm π.sig) :
    Option ((a : ATm π.sig) × Compiled π.plat a) :=
  match synthTop? b π a with
  | none => none
  | some r =>
      if hs : ATm.skel r.tm = ATm.skel a then
        some ⟨a, ⟨r.tm, r.uses, r.ty, platformCtx_eq π.plat ▸ r.deriv, hs⟩⟩
      else none

/-- `compile`, then the machine of `Step.lean` for `m` steps. -/
def compileAndRun (b : Budget) (m : Nat) (Λ : LabelTable) (π : PlatformNames) (e : STm) :
    Option ((s : Sig) × State s) :=
  (compile b Λ π e).map fun r => run m π.sig ⟨π.plat.store, .nil, r.2.tm.erase⟩

/-! ## Effect premise on the source set -/

/-- A capability is in the translation of a set only if it is in the set. -/
theorem cvar_mem_translate {s : Sig} {κ : BVar s .cap} {C : CaptureSet s}
    (h : FCdot.CapAtom.cvar κ ∈ C.translate) : CapAtom.cvar κ ∈ C := by
  induction C with
  | nil => simp at h
  | cons a C ih =>
      cases a with
      | var x =>
          simp only [DotMNF.CaptureSet.translate_cons_var, List.mem_cons] at h
          rcases h with h | h
          · cases h
          · exact List.mem_cons_of_mem _ (ih h)
      | cvar κ' =>
          simp only [DotMNF.CaptureSet.translate_cons_cvar, List.mem_cons] at h
          rcases h with h | h
          · cases h; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih h)
      | sel x A =>
          simp only [DotMNF.CaptureSet.translate_cons_sel, List.mem_cons] at h
          rcases h with h | h
          · cases h
          · exact List.mem_cons_of_mem _ (ih h)
      | any =>
          simp only [DotMNF.CaptureSet.translate_cons_any] at h
          exact List.mem_cons_of_mem _ (ih h)

/-! ## Theorems -/

-- `h` is read only by the proof of `compile_faithful`.
set_option linter.unusedVariables false

section
variable {b : Budget} {Λ : LabelTable} {π : PlatformNames} {e : STm} {a : ATm π.sig}
  {c : Compiled π.plat a}

/-- **The target checker accepts the translation.** -/
theorem compile_checks (h : compile b Λ π e = some ⟨a, c⟩) :
    FCdot.checkTm π.plat.ctx.translate c.deriv.translate c.ty.translate = true :=
  FCdot.checkTm_complete (c.deriv.translate_typed (Platform.ctx_wf π.plat))

/-- **The target checker accepts the use set evidence.**  The evidence says
that the target term uses no more than the translated use set. -/
theorem compile_uses_checks (h : compile b Λ π e = some ⟨a, c⟩) :
    FCdot.checkCap π.plat.ctx.translate c.deriv.translateUses c.deriv.translate.uses
      c.uses.translate = true :=
  FCdot.checkCap_complete (c.deriv.translate_uses (Platform.ctx_wf π.plat))

/-- **The translation erases to the erasure of the compiled term.** -/
theorem compile_erase (h : compile b Λ π e = some ⟨a, c⟩) :
    FCdot.Tm.erase c.deriv.translate = Tm.erase c.tm.erase :=
  DotMNF.HasTy.translate_erase c.deriv

/-- **The compiled term is the fill up to box inference.** -/
theorem compile_faithful (h : compile b Λ π e = some ⟨a, c⟩) : ATm.skel c.tm = ATm.skel a :=
  c.skel

/-- **Safety of the compiled program.**  Every state of a run `r` from the
platform's initial store is final or has a step.  This is
`DotMNF.dot_safety_platform` at the compiled derivation. -/
theorem compile_safe (h : compile b Λ π e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st) :
    State.Final st ∨ ∃ (s' : Sig) (st' : State s'), Step st st' :=
  DotMNF.dot_safety_platform π.plat c.deriv r

/-- **No reachable state of the compiled program is stuck.** -/
theorem compile_not_stuck (h : compile b Λ π e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st) : ¬ State.Stuck st := by
  intro ⟨hnf, hns⟩
  rcases compile_safe h r with hf | hs
  · exact hnf hf
  · exact hns hs

/-- **The driver never answers at a stuck state.**  At every step budget the
state `run` returns is final or the executable machine finds a step. -/
theorem compile_run_progress (h : compile b Λ π e = some ⟨a, c⟩) (m : Nat) :
    let st := (run m π.sig ⟨π.plat.store, .nil, c.tm.erase⟩).2
    State.Final st ∨ (step? st).isSome := by
  intro st
  have hr : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st := run_steps m _
  rcases compile_safe h hr with hfin | hstep
  · exact Or.inl hfin
  · refine Or.inr ?_
    cases hs : step? st with
    | some _ => rfl
    | none => exact absurd hstep (step?_eq_none_iff.mp hs)

/-- **Capture prediction.**  For a run `r` from the platform's initial store,
the target machine runs from the translation of the derivation to a typed
state with the same erasure.  Its store extends the platform's along a
renaming `ρ`, and its use set is below the translation of the typer's use
set, renamed by `ρ`. -/
theorem compile_capture_prediction (h : compile b Λ π e = some ⟨a, c⟩) {s : Sig}
    {st : State s} (r : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename π.sig s),
      FCdot.Steps (⟨π.plat.targetStore, .nil, c.deriv.translate⟩ : FCdot.State π.sig) stt ∧
        (∃ V, FCdot.State.Typed stt V) ∧
        FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext π.plat.targetStore stt.σ ρ ∧
          FCdot.CapLe Γ' stt.uses (c.uses.translate.rename ρ) :=
  DotMNF.dot_capture_prediction π.plat c.deriv r

/-- **Effect safety.**  Let `κ` be a platform capability that the typer's use
set lacks (`hκ`), `r` a run from the platform's initial store and `x` a
variable the reached state reads.  Then the target machine runs from the
translation of the derivation to a typed state with the same erasure, and `κ`
is not a root of `x` in it.  The premise of `DotMNF.dot_effect_safety` on the
translated set follows from `hκ` by `cvar_mem_translate`. -/
theorem compile_effect_safety (h : compile b Λ π e = some ⟨a, c⟩) {κ : BVar π.sig .cap}
    (hκ : c.uses.elem (.cvar κ) = false)
    {s : Sig} {st : State s} (r : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename π.sig s),
      FCdot.Steps (⟨π.plat.targetStore, .nil, c.deriv.translate⟩ : FCdot.State π.sig) stt ∧
        (∃ V, FCdot.State.Typed stt V) ∧
        FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext π.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var κ)) [FCdot.CapAtom.var x] := by
  refine DotMNF.dot_effect_safety π.plat c.deriv (fun hm => ?_) r hin
  have hmem := (DotMNF.CaptureSet.elem_iff c.uses).mpr (cvar_mem_translate hm)
  rw [hκ] at hmem
  exact Bool.noConfusion hmem

end

/-! ## Theorems at a decided compile

For a concrete program the kernel decides whether the compile succeeds.  These
forms take that test and speak of the record the compile returns. -/

section
variable {b : Budget} {Λ : LabelTable} {π : PlatformNames} {e : STm}

/-- **The target checker accepts the translation of a program that compiles.** -/
theorem compile_checks_get (h : (compile b Λ π e).isSome = true) :
    FCdot.checkTm π.plat.ctx.translate ((compile b Λ π e).get h).2.deriv.translate
      ((compile b Λ π e).get h).2.ty.translate = true :=
  compile_checks (Option.some_get h).symm

/-- **`compile_faithful` at a program that compiles.** -/
theorem compile_faithful_get (h : (compile b Λ π e).isSome = true) :
    resolveTop Λ π e = some ((compile b Λ π e).get h).1 ∧
      (∃ r : Elab (platformCtx π.plat), synthTop? b π ((compile b Λ π e).get h).1 = some r ∧
        r.tm = ((compile b Λ π e).get h).2.tm ∧ r.uses = ((compile b Λ π e).get h).2.uses ∧
          r.ty = ((compile b Λ π e).get h).2.ty) ∧
      ATm.skel ((compile b Λ π e).get h).2.tm = ATm.skel ((compile b Λ π e).get h).1 :=
  compile_faithful (Option.some_get h).symm

/-- **Effect safety of a program that compiles.**  `compile_effect_safety` at
the returned record. -/
theorem compile_effect_safety_get (h : (compile b Λ π e).isSome = true)
    {κ : BVar π.sig .cap} (hκ : ((compile b Λ π e).get h).2.uses.elem (.cvar κ) = false)
    {s : Sig} {st : State s}
    (r : Steps (⟨π.plat.store, .nil, ((compile b Λ π e).get h).2.tm.erase⟩ : State π.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename π.sig s),
      FCdot.Steps (⟨π.plat.targetStore, .nil, ((compile b Λ π e).get h).2.deriv.translate⟩ :
          FCdot.State π.sig) stt ∧
        (∃ V, FCdot.State.Typed stt V) ∧
        FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext π.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var κ)) [FCdot.CapAtom.var x] :=
  compile_effect_safety (Option.some_get h).symm hκ r hin

end

/-! ## Inference and the typer

The theorems that relate a compilation to the elaborator and to the typer. -/

section
variable {b : Budget} {Λ : LabelTable} {π : PlatformNames} {e : STm}

open Frontend.Fuel

/-- `compile` is `compileE` without the reason. -/
theorem compile_eq (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) :
    compile b Λ π e = (compileE b Λ π e).toOption := rfl

/-- **Every slot written: the typer, at the same fuel.**  A program that
resolves with every slot written compiles as the typer's synthesis on its
resolution. -/
theorem compile_full {a : ATm π.sig} (h : resolveTop Λ π e = some a) :
    compile b Λ π e = compileLanded b π a := by
  rw [resolve_eq] at h
  cases hp : resolvePTop Λ π e with
  | none =>
    rw [hp] at h
    cases h
  | some p =>
    rw [hp, Option.bind_some] at h
    have hfill := PTm.fillFrom_full h
    have hfills := PTm.fills_of_full? h
    simp only [compile, compileE, hp, compileLanded, synthTop?, synthTopF, synthInF, elabTopF,
      elabF_full _ h, fullInfer, withR, synthF, Fu.bind, Fu.ret]
    cases hs : inferF (platformCtx π.plat) a none ⟨b.fuel, false⟩ with
    | mk cs t =>
      cases cs with
      | nil => simp [firstCand, Except.toOption]
      | cons c cs =>
        cases ht : t.out with
        | true => simp [firstCand, ht, Except.toOption]
        | false =>
          simp only [firstCand, ht, Bool.false_eq_true, if_false, hfill, hfills, if_true]
          by_cases hk : ATm.skel c.tm = ATm.skel a
          · simp [hk, Except.toOption]
          · simp [hk, Except.toOption]

/-- **Inference fills only empty slots.**  The fill of a compiled program
agrees with every slot its partial term writes. -/
theorem compileE_fills {a : ATm π.sig} {c : Compiled π.plat a}
    (h : compileE b Λ π e = .ok ⟨a, c⟩) :
    ∃ p, resolvePTop Λ π e = some p ∧ p.fills a = true := by
  unfold compileE at h
  cases hp : resolvePTop Λ π e with
  | none =>
    rw [hp] at h
    cases h
  | some p =>
    rw [hp] at h
    dsimp only at h
    refine ⟨p, rfl, ?_⟩
    cases he : (elabTopF b.fuel π p).1 with
    | error r =>
      rw [he] at h
      cases h
    | ok r =>
      rw [he] at h
      dsimp only at h
      cases hf : p.fillFrom r.tm with
      | none =>
        rw [hf] at h
        cases h
      | some a' =>
        rw [hf] at h
        dsimp only at h
        by_cases hfa : p.fills a' = true
        · by_cases hk : ATm.skel r.tm = ATm.skel a'
          · rw [if_pos hfa, dif_pos hk] at h
            cases h
            exact hfa
          · rw [if_pos hfa, dif_neg hk] at h
            cases h
        · rw [if_neg hfa] at h
          cases h

/-- **The skeleton of the program.**  The elaborated term of a compiled program
has the skeleton of the partial term it was resolved to, which forgets every
slot. -/
theorem compileE_skel {a : ATm π.sig} {c : Compiled π.plat a}
    (h : compileE b Λ π e = .ok ⟨a, c⟩) :
    ∃ p, resolvePTop Λ π e = some p ∧ ATm.skel c.tm = PTm.skel p := by
  obtain ⟨p, hp, hf⟩ := compileE_fills h
  exact ⟨p, hp, c.skel.trans (PTm.skel_of_fills hf).symm⟩

/-- The reasons of the typer on a term with no empty slot: a mismatch, or
none. -/
theorem fullInfer_reasons {s : Sig} {Γ : Ctx s} {a : ATm s} {G : Option (Ty s)} (t : Tank) :
    ∀ r ∈ (fullInfer Γ a G t).1.2, r = .mismatch := by
  intro r hr
  simp only [fullInfer, withR, Fu.bind, Fu.ret] at hr
  split at hr
  · simp at hr
    exact hr
  · simp at hr

/-- The reason `elabTopF` reports when the typer rejects a program with no
empty slot: the recursion limit or a mismatch. -/
theorem elabTopF_full_error {p : PTm π.sig} {a : ATm π.sig} (hp : p.full? = some a) {n : Nat}
    {r : EReason} (h : (elabTopF n π p).1 = .error r) : r = .limit ∨ r = .mismatch := by
  unfold elabTopF at h
  have hrs := fullInfer_reasons (Γ := platformCtx π.plat) (a := a) (G := none) ⟨n, false⟩
  rw [← elabF_full _ hp] at hrs
  revert hrs h
  cases elabF (platformCtx π.plat) p none ⟨n, false⟩ with
  | mk res t =>
    obtain ⟨cs, rs⟩ := res
    intro h hrs
    cases cs with
    | cons c cs =>
      cases ht : t.out <;> simp [ht] at h
      exact Or.inl h.symm
    | nil =>
      simp only [Except.error.injEq] at h
      subst h
      unfold Frontend.Reason.Reason.top
      cases ht : t.out with
      | true => exact Or.inl rfl
      | false =>
        cases rs with
        | nil => exact Or.inr rfl
        | cons r rs => exact Or.inr (hrs r (List.mem_cons_self ..))

/-- **The slot reasons arise only where a slot is empty.**  A program rejected
for a missing parameter type, a cyclic reference, a definition that needs a
written type, or candidates with no least type resolves to a partial term with
an empty slot. -/
theorem compileE_slot {r : EReason} (h : compileE b Λ π e = .error r)
    (hr : r.isSlotReason = true) :
    ∃ p, resolvePTop Λ π e = some p ∧ p.full? = none := by
  unfold compileE at h
  cases hp : resolvePTop Λ π e with
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
      cases he : (elabTopF b.fuel π p).1 with
      | error r' =>
        rw [he] at h
        cases h
        rcases elabTopF_full_error hf he with rfl | rfl <;> cases hr
      | ok c =>
        rw [he] at h
        dsimp only at h
        split at h
        · cases h
          cases hr
        · split at h
          · split at h
            · cases h
            · cases h
              cases hr
          · cases h
            cases hr

end

/-! ## The tank of an elaboration

`elabF` is framed (`elabF_framed`, `Elab.lean`), so an elaboration that ends
unmarked does the same with more fuel. -/

section
open Frontend.Fuel

/-- A closed elaboration that ends unmarked gives the same verdict at every
larger fuel.  So a rejection that ends unmarked is a rejection by the rules. -/
theorem elabTop?_stable {n k : Nat} {π : PlatformNames} {p : PTm π.sig}
    {r : Except EReason (Elab (platformCtx π.plat))}
    (h : elabTopF n π p = (r, ⟨k, false⟩)) (j : Nat) : (elabTopF (n + j) π p).1 = r := by
  unfold elabTopF at h ⊢
  cases hs : elabF (platformCtx π.plat) p none ⟨n, false⟩ with
  | mk res t =>
    obtain ⟨cs, rs⟩ := res
    rw [hs] at h
    have ht : t = ⟨k, false⟩ := by
      cases cs with
      | nil => exact (Prod.mk.inj h).2
      | cons c cs => exact (Prod.mk.inj h).2
    have hf := (elabF_framed (platformCtx π.plat) p none).shift _ _ _ hs (by rw [ht]) j
    have hn : (⟨n + j, false⟩ : Tank) = (⟨n, false⟩ : Tank).add j := rfl
    rw [hn, hf]
    subst ht
    cases cs with
    | nil => exact (Prod.mk.inj h).1
    | cons c cs => exact (Prod.mk.inj h).1

/-- An elaborated program ends unmarked. -/
theorem elabTopF_ok_out {n : Nat} {π : PlatformNames} {p : PTm π.sig}
    {c : Elab (platformCtx π.plat)}
    (h : (elabTopF n π p).1 = .ok c) : (elabTopF n π p).2.out = false := by
  unfold elabTopF at h ⊢
  cases hs : elabF (platformCtx π.plat) p none ⟨n, false⟩ with
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
theorem elabTop?_mono {n m : Nat} {π : PlatformNames} {p : PTm π.sig}
    {c : Elab (platformCtx π.plat)}
    (h : (elabTopF n π p).1 = .ok c) (hnm : n ≤ m) : (elabTopF m π p).1 = .ok c := by
  have ho := elabTopF_ok_out h
  have he : elabTopF n π p = (.ok c, ⟨(elabTopF n π p).2.left, false⟩) := by
    rw [← h, ← ho]
  have := elabTop?_stable he (m - n)
  rwa [Nat.add_sub_cancel' hnm] at this

end

/-! ## Completeness at the direct sites

The elaborator fills a lambda's domain from its goal and hands the filled term
to the typer.  At some sites this is the typer's own clause on the filled
program, after the lookups that read the goal.  At those sites inference loses
no program whose fill the typer types.

`Canon Γ p G a` says that `a` is the canonical fill of `p` at the goal `G`:
every empty slot of `p` is at such a site and holds what the elaborator reads
there.  The sites are a lambda without a domain whose body has no empty slot,
at a goal with a function part, the body `g x` of a lambda at a goal without
one, a lambda whose body has an empty slot at a function type, a call
argument, an ascription, a field of a literal with a written self shape, and a
literal without a self shape at a goal that dealiases to a `μ`.  The path from
the root to a slot runs through lambdas, `let`s, ascriptions and literals.  A
slot under a `let` binder is filled alike in every context a candidate of the
bound term gives.

Some sites carry a premise about the typer on the fill.  At a call argument
and at a field of a literal the elaborator hands the typer the term its check
of the fill returns.  So the typer's check must answer first with the fill
itself.  At a call argument and at a literal typed by its goal the elaborator
stops at the first try that answers, so the typer must accept the filled term
there.  A clause that checks first and falls back to synthesis needs the body
canonical with no goal as well, unless the typer's check answers, so that
neither falls back.

`Lag R c c'` says that `c'` does what `c` does, with enough fuel.  From a tank
on which `c` ends unmarked, `c'` reaches a related answer.  `Reaches c x` says
that `c` ends unmarked at `x` from some full tank, and from every larger one
with as many more units left.  The elaborator may spend more fuel than the
typer, where it reads a goal.  `canon_lag` proves the lag for the typer on the
fill against the elaborator on the partial term, with the same candidates in
the same order, derivations included (`SameCands`).  `elab_complete_direct` reads
it at the top: the elaborator accepts a program whose canonical fill the typer
types, from some fuel on, with the typer's first candidate
(`elab_complete_direct_fill`).  Some fuel, and not the typer's, since the
elaborator reads the goal on the same tank.  `compile_complete_direct` adds
the fill: when the elaborated term gives the fill back and the fill agrees
with every written slot, the program compiles as the typer compiles the fill,
record included (`compileLanded`).  `canonB` and `canonAt` decide the premises
from one fuel, and `compile_complete_canonAt` says that an erased program
compiles as its written form does.

Out of reach are a lambda whose body has an empty slot at a goal whose
function part is reached through an intersection, an alias or a box, where the
elaborator checks the body against the result part and the typer synthesizes
it, a literal whose self shape the rounds form, and a field of a literal that
is itself a literal, since the typer writes the least set it finds into the
inner literal. -/

section Complete

open Frontend.Fuel CapturesFrontend.Core Frontend.Reason
open Captures.DotMNF (Shape)
open scoped Captures.DotMNF

/-! ### Computations that reach an answer -/

/-- A computation that ends unmarked with `x` from a full tank of `n` units,
and from every larger full tank with as many more units left. -/
def Reaches {α : Type} (c : Fu α) (x : α) : Prop :=
  ∃ n m, ∀ k, c ⟨n + k, false⟩ = (x, ⟨m + k, false⟩)

/-- `c'` does what `c` does, with enough fuel.  From a tank on which `c` ends
unmarked with `r`, `c'` reaches an answer related to `r`.  The fuel `c'` needs
is not tied to the fuel `c` spends. -/
def Lag {α β : Type} (R : α → β → Prop) (c : Fu α) (c' : Fu β) : Prop :=
  ∀ t r t', c t = (r, t') → t'.out = false → ∃ r', R r r' ∧ Reaches c' r'

/-- A computation that ends unmarked with `x` from some full tank.  A framed
one then reaches `x`. -/
def SettlesTo {α : Type} (c : Fu α) (x : α) : Prop :=
  ∃ n m, c ⟨n, false⟩ = (x, ⟨m, false⟩)

section LagLemmas

variable {α β γ δ : Type}

/-- Two tanks with the same fuel and the same mark are equal. -/
theorem tank_eq {t u : Tank} (hl : t.left = u.left) (ho : t.out = u.out) : t = u := by
  cases t
  cases u
  simp_all

/-- An answer returned at no cost is reached. -/
theorem reaches_ret (x : α) : Reaches (Fu.ret x) x :=
  ⟨0, 0, fun _ => rfl⟩

/-- Reaching composes along a `bind`. -/
theorem reaches_bind {c : Fu α} {f : α → Fu β} {x : α} {y : β} (hc : Reaches c x)
    (hf : Reaches (f x) y) : Reaches (Fu.bind c f) y := by
  obtain ⟨n1, m1, h1⟩ := hc
  obtain ⟨n2, m2, h2⟩ := hf
  refine ⟨n1 + n2, m2 + m1, fun k => ?_⟩
  have e1 : (⟨n1 + n2 + k, false⟩ : Tank) = ⟨n1 + (n2 + k), false⟩ := by rw [Nat.add_assoc]
  have e2 : (⟨m1 + (n2 + k), false⟩ : Tank) = ⟨n2 + (m1 + k), false⟩ := by
    rw [Tank.mk.injEq]
    exact ⟨by omega, rfl⟩
  have e3 : (⟨m2 + (m1 + k), false⟩ : Tank) = ⟨m2 + m1 + k, false⟩ := by rw [Nat.add_assoc]
  show (match c ⟨n1 + n2 + k, false⟩ with | (a, t1) => f a t1) = _
  rw [e1, h1]
  show f x ⟨m1 + (n2 + k), false⟩ = _
  rw [e2, h2, e3]

/-- A framed computation that ends unmarked reaches its answer. -/
theorem reaches_of_run {c : Fu α} (hc : Framed c) {t : Tank} {x : α} {t' : Tank}
    (h : c t = (x, t')) (ho : t'.out = false) : Reaches c x := by
  have hto : t.out = false := hc.start h ho
  refine ⟨t.left, t'.left, fun k => ?_⟩
  have hs := hc.shift t x t' h ho k
  have e1 : t.add k = ⟨t.left + k, false⟩ := tank_eq rfl (by simp [Tank.add, hto])
  have e2 : t'.add k = ⟨t'.left + k, false⟩ := tank_eq rfl (by simp [Tank.add, ho])
  rw [e1, e2] at hs
  exact hs

/-- A framed computation that settles reaches its answer. -/
theorem reaches_settles {c : Fu α} {x : α} (hc : Framed c) (hs : SettlesTo c x) : Reaches c x := by
  obtain ⟨n, m, h⟩ := hs
  exact reaches_of_run hc h rfl

/-- A first try whose answer `ok` accepts ends `stopOr` at once. -/
theorem reaches_stop {a : β} {c : Fu β} : Reaches (stopOr true a c) a :=
  ⟨0, 0, fun _ => rfl⟩

/-- Two answers returned at no cost lag by nothing. -/
theorem lag_ret {R : α → β → Prop} {x : α} {y : β} (h : R x y) : Lag R (Fu.ret x) (Fu.ret y) := by
  intro t r t' hr _
  simp only [Fu.ret, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨y, h, reaches_ret y⟩

/-- Lags compose along a `bind`.  The continuations need to lag only at answers
the first computation gives on a tank it leaves unmarked. -/
theorem lag_bind {R1 : α → β → Prop} {R2 : γ → δ → Prop} {c : Fu α} {c' : Fu β}
    {f : α → Fu γ} {f' : β → Fu δ} (hc : Lag R1 c c') (hf : ∀ x, Framed (f x))
    (hff : ∀ t x t1, c t = (x, t1) → t1.out = false → ∀ y, R1 x y → Lag R2 (f x) (f' y)) :
    Lag R2 (Fu.bind c f) (Fu.bind c' f') := by
  intro t r t' h ho
  simp only [Fu.bind] at h
  cases hct : c t with
  | mk x t1 =>
    rw [hct] at h
    have ht1 : t1.out = false := (hf x).start h ho
    obtain ⟨y, hR1, h1⟩ := hc t x t1 hct ht1
    obtain ⟨r', hR2, h2⟩ := hff t x t1 hct ht1 y hR1 t1 r t' h ho
    exact ⟨r', hR2, reaches_bind h1 h2⟩

/-- The answer of `c`, mapped. -/
theorem lag_map {R : α → β → Prop} {c : Fu α} {g : α → β} (hc : Framed c) (h : ∀ x, R x (g x)) :
    Lag R c (Fu.bind c fun x => Fu.ret (g x)) := by
  intro t r t' hr ho
  exact ⟨g r, h r, reaches_bind (reaches_of_run hc hr ho) (reaches_ret _)⟩

/-- The answer of `c'`, mapped. -/
theorem lag_map_right {R R' : α → β → Prop} {c : Fu α} {c' : Fu β} {g : β → β}
    (h : Lag R c c') (hg : ∀ x y, R x y → R' x (g y)) :
    Lag R' c (Fu.bind c' fun y => Fu.ret (g y)) := by
  intro t r t' hr ho
  obtain ⟨r', hR, hk⟩ := h t r t' hr ho
  exact ⟨g r', hg _ _ hR, reaches_bind hk (reaches_ret _)⟩

/-- A computation that reaches an answer, run first, keeps the lag. -/
theorem lag_prefix {R : α → γ → Prop} {k : Fu α} {c : Fu β} {f : β → Fu γ} {x : β}
    (hs : Reaches c x) (hf : Lag R k (f x)) : Lag R k (Fu.bind c f) := by
  intro t r t' h ho
  obtain ⟨r', hR, hd⟩ := hf t r t' h ho
  exact ⟨r', hR, reaches_bind hs hd⟩

/-- A framed computation that settles at `x` answers `x` on every tank on which
it ends unmarked. -/
theorem settles_unique {c : Fu α} {x : α} (hc : Framed c) (hs : SettlesTo c x) {t : Tank} {r : α}
    {t' : Tank} (h : c t = (r, t')) (ho : t'.out = false) : r = x := by
  obtain ⟨n, m, hn⟩ := hs
  have hto : t.out = false := hc.start h ho
  by_cases hle : t.left ≤ n
  · have ht : (⟨n, false⟩ : Tank) = t.add (n - t.left) :=
      tank_eq (by simp [Tank.add]; omega) (by simp [Tank.add, hto])
    have := hc.shift t r t' h ho (n - t.left)
    rw [← ht, hn] at this
    exact (Prod.mk.inj this).1.symm
  · have ht : t = (⟨n, false⟩ : Tank).add (t.left - n) :=
      tank_eq (by simp [Tank.add]; omega) (by simp [Tank.add, hto])
    have := hc.shift ⟨n, false⟩ x ⟨m, false⟩ hn rfl (t.left - n)
    rw [← ht, h] at this
    exact (Prod.mk.inj this).1

/-- A computation that lags behind one that settles reaches a related answer. -/
theorem settles_lag {R : α → β → Prop} {c : Fu α} {c' : Fu β} {x : α} (h : Lag R c c')
    (hs : SettlesTo c x) : ∃ y, R x y ∧ Reaches c' y := by
  obtain ⟨n, m, hn⟩ := hs
  exact h ⟨n, false⟩ x ⟨m, false⟩ hn rfl

/-- A `bind` whose first computation is a `bind`, reassociated. -/
theorem bind_bind {c : Fu α} {f : α → Fu β} {g : β → Fu γ} :
    Fu.bind (Fu.bind c f) g = Fu.bind c (fun x => Fu.bind (f x) g) := by
  funext t
  simp only [Fu.bind]

/-- A `bind` whose first computation returns at no cost. -/
theorem bind_ret {x : α} {f : α → Fu β} : Fu.bind (Fu.ret x) f = f x := by
  funext t
  rfl

/-- A first try whose answer `ok` accepts stops `orElseW`, when the
computation it lags behind settles at an answer that the relation carries to
an accepted one. -/
theorem lag_stop {ρ : Type} {R : α → β × List ρ → Prop} {k : Fu α} {X : Fu (β × List ρ)}
    {ok : β → Bool} {Z : β × List ρ → Fu (β × List ρ)} {x : α}
    (hk : Framed k) (hX : Lag R k X) (hs : SettlesTo k x)
    (hR : ∀ y, R x y → ok y.1 = true) :
    Lag R k (Fu.bind X fun r => stopOr (ok r.1) r (Z r)) := by
  intro t r t' h ho
  have hr := settles_unique hk hs h ho
  subst hr
  obtain ⟨r', hR', hd⟩ := hX t r t' h ho
  refine ⟨r', hR', reaches_bind hd ?_⟩
  rw [hR r' hR']
  exact reaches_stop

/-- Without `stop`, `stopOr` on an unmarked tank is its second computation. -/
theorem reaches_go {a : β} {c : Fu β} {y : β} (h : Reaches c y) :
    Reaches (stopOr false a c) y := by
  obtain ⟨n, m, h⟩ := h
  exact ⟨n, m, fun k => h k⟩

end LagLemmas

/-! ### The same candidates -/

/-- The elaborator's candidates are the typer's, in the same order. -/
def SameCands {s : Sig} {Γ : Ctx s} (cs : List (Elab Γ)) (r : Out Γ) : Prop := r.1 = cs

section LagLists

variable {α γ ρ : Type}

/-- The typer on a term with no empty slot, with its reasons, lags behind the
typer. -/
theorem lag_full {s : Sig} (Γ : Ctx s) (a : ATm s) (G : Option (Ty s)) :
    Lag SameCands (inferF Γ a G) (fullInfer Γ a G) := by
  unfold fullInfer withR
  exact lag_map (R := SameCands) (inferF_framed Γ a G) fun _ => rfl

/-- A list step of the typer after an elaboration lags behind the same step
after the typer. -/
theorem lag_thenL {s s' : Sig} {Γ : Ctx s} {Δ : Ctx s'} {c : Fu (List (Elab Δ))}
    {c' : Fu (Out Δ)} {f : List (Elab Δ) → Fu (List (Elab Γ))} (h : Lag SameCands c c')
    (hf : ∀ l, Framed (f l)) : Lag SameCands (Fu.bind c f) (thenL c' f) := by
  unfold thenL
  refine lag_bind h hf ?_
  intro _ x _ _ _ y hxy
  simp only [SameCands] at hxy
  rw [hxy]
  exact lag_map (hf x) fun _ => rfl

/-- The typer's `orElseL` against the elaborator's `orElseO`. -/
theorem lag_orElse {s : Sig} {Γ : Ctx s} {a b : Fu (List (Elab Γ))} {a' b' : Fu (Out Γ)}
    (ha : Lag SameCands a a') (hb : Lag SameCands b b') (hbf : Framed b) :
    Lag SameCands (orElseL a b) (orElseO a' b') := by
  unfold orElseL orElseO
  refine lag_bind ha (fun l => ?_) ?_
  · cases l with
    | nil => exact hbf
    | cons _ _ => exact ret_framed _
  · intro _ x _ _ _ y hxy
    obtain ⟨l, rs⟩ := y
    simp only [SameCands] at hxy
    subst hxy
    cases l with
    | nil => exact lag_map_right hb fun _ _ h => h
    | cons c cs => exact lag_ret rfl

/-- The typer's first success over a list against the elaborator's, over the
same list. -/
theorem lag_firstSome {f : α → Fu (Option γ)} {f' : α → Fu (Option γ × List ρ)} :
    ∀ l : List α, (∀ x ∈ l, Lag (fun o r => r.1 = o) (f x) (f' x)) →
      Lag (fun o r => r.1 = o) (Fu.firstSome f l) (firstSomeR f' l)
  | [], _ => by
    simp only [Fu.firstSome, firstSomeR]
    exact lag_ret rfl
  | x :: xs, hf => by
    have ih := lag_firstSome xs fun x' hx' => hf x' (List.mem_cons_of_mem _ hx')
    have hx := hf x (List.mem_cons_self ..)
    intro t r t' hr ho
    simp only [Fu.firstSome, Fu.orElse] at hr
    cases hat : f x t with
    | mk o1 t1 =>
      rw [hat] at hr
      cases o1 with
      | some v =>
        simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨r1, hR, hd⟩ := hx t (some v) t1 hat ho
        refine ⟨r1, hR, ?_⟩
        simp only [firstSomeR, orElseW]
        refine reaches_bind hd ?_
        rw [hR]
        exact reaches_stop
      | none =>
        cases ht1 : t1.out with
        | true =>
          simp only [ht1, if_true, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          simp [ht1] at ho
        | false =>
          simp only [ht1, Bool.false_eq_true, if_false] at hr
          obtain ⟨r1, hR1, hd1⟩ := hx t none t1 hat ht1
          obtain ⟨r2, hR2, hd2⟩ := ih t1 r t' hr ho
          refine ⟨(r2.1, r1.2 ++ r2.2), hR2, ?_⟩
          simp only [firstSomeR, orElseW]
          refine reaches_bind hd1 ?_
          rw [hR1]
          exact reaches_go (reaches_bind hd2 (reaches_ret _))

/-- The typer's answers over a list against the elaborator's, over the same
list. -/
theorem lag_flatMap {f : α → Fu (List γ)} {f' : α → Fu (List γ × List ρ)}
    (hfr : ∀ x, Framed (f x)) :
    ∀ l : List α, (∀ x ∈ l, Lag (fun ys r => r.1 = ys) (f x) (f' x)) →
      Lag (fun ys r => r.1 = ys) (Fu.flatMapL f l) (flatMapR f' l)
  | [], _ => by
    simp only [Fu.flatMapL, flatMapR]
    exact lag_ret rfl
  | x :: xs, hf => by
    have ih := lag_flatMap hfr xs fun x' hx' => hf x' (List.mem_cons_of_mem _ hx')
    simp only [Fu.flatMapL, flatMapR]
    refine lag_bind (hf x (List.mem_cons_self ..))
      (fun _ => bind_framed (flatMapL_framed hfr xs) fun _ => ret_framed _) ?_
    intro _ ys1 _ _ _ r1 h1
    refine lag_bind ih (fun _ => ret_framed _) ?_
    intro _ zs _ _ _ r2 h2
    exact lag_ret (by simp only [h1, h2])

/-- The typer's `orElseL` against the elaborator's `orElseO`, when the typer's
first try settles at a candidate, so that neither runs its second try. -/
theorem lag_orElse_stop {s : Sig} {Γ : Ctx s} {a b : Fu (List (Elab Γ))} {a' b' : Fu (Out Γ)}
    {c : Elab Γ} {l : List (Elab Γ)} (ha : Lag SameCands a a') (haf : Framed a) (hbf : Framed b)
    (hs : SettlesTo a (c :: l)) : Lag SameCands (orElseL a b) (orElseO a' b') := by
  intro t r t' h ho
  unfold orElseL at h
  simp only [Fu.bind] at h
  cases hat : a t with
  | mk x t1 =>
    rw [hat] at h
    have ht1 : t1.out = false := by
      cases x with
      | nil => exact hbf.start h ho
      | cons _ _ =>
        simp only [Fu.ret, Prod.mk.injEq] at h
        rw [h.2]
        exact ho
    have hx := settles_unique haf hs hat ht1
    subst hx
    simp only [Fu.ret, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨y, hy, hry⟩ := ha t (c :: l) t1 hat ht1
    refine ⟨y, hy, ?_⟩
    unfold orElseO
    refine reaches_bind hry ?_
    obtain ⟨yl, rs⟩ := y
    simp only [SameCands] at hy
    subst hy
    exact reaches_ret _

end LagLists

/-! ### The `let` clause -/

/-- The goals at which the body of a `let` is checked: the written type, or
the goal.  With neither the body is synthesized. -/
def letGoals {s : Sig} : Option (Ty s) → Option (Ty s) → List (Option (Ty (s,x)))
  | some A, _ => [some A.weaken]
  | none, some T => [some T.weaken]
  | none, none => [none]

section LetLag

variable {s : Sig} {Γ : Ctx s}

/-- The typer's `let` at a type against the elaborator's, over the same
candidates of the bound term. -/
theorem lag_letCheck (ann : Option (Ty s)) (A : Ty s) (r1s : List (Elab Γ))
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))}
    {body' : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))}
    (hb : ∀ r1 ∈ r1s, Lag SameCands (body' r1 (some A.weaken)) (body r1 (some A.weaken))) :
    Lag SameCands (mapL (letCheckF Γ ann A r1s body') id) (letCheckO Γ ann A r1s body) := by
  unfold mapL letCheckF letCheckO
  refine lag_bind (lag_firstSome r1s fun r1 hr1 => ?_) (fun _ => ret_framed _) ?_
  · refine lag_bind (hb r1 hr1) (fun r2s => ?_) ?_
    · split
      · exact letAtF_framed _ _ _ _ _
      · exact ret_framed _
    · intro _ x _ _ _ y hxy
      simp only [SameCands] at hxy
      subst hxy
      cases firstChecked y.1 A.weaken with
      | some c => exact lag_map (letAtF_framed _ _ _ _ _) fun _ => rfl
      | none => exact lag_ret rfl
  · intro _ o _ _ _ r hr
    refine lag_ret ?_
    simp only [SameCands, hr]
    cases o <;> rfl

/-- The typer's synthesis of a `let` without a type against the
elaborator's, over the same candidates of the bound term. -/
theorem lag_letPairs (r1s : List (Elab Γ))
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))}
    {body' : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))}
    (hbf : ∀ r1 o, Framed (body' r1 o))
    (hb : ∀ r1 ∈ r1s, Lag SameCands (body' r1 none) (body r1 none)) :
    Lag SameCands (letGenF Γ none r1s body') (letGenO Γ none r1s body) := by
  unfold letGenF letGenO
  refine lag_bind (lag_flatMap (fun r1 => letPairsF_framed _ _ (hbf _ _)) r1s
    fun r1 hr1 => ?_) (fun _ => ret_framed _) ?_
  · unfold letPairsF
    refine lag_bind (hb r1 hr1)
      (fun _ => flatMapL_framed (fun _ => mapL_framed _ (letFinishF_framed _ _ _)) _) ?_
    intro _ x _ _ _ y hxy
    simp only [SameCands] at hxy
    subst hxy
    exact lag_map (flatMapL_framed (fun _ => mapL_framed _ (letFinishF_framed _ _ _)) _)
      fun _ => rfl
  · intro _ cs _ _ _ r hr
    exact lag_ret (by simp only [SameCands, hr])

/-- The typer's `let` clause on no candidate of the bound term answers no
candidate and draws nothing. -/
theorem typer_let_nil (ann : Option (Ty s)) (G : Option (Ty s))
    (body' : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))) (t : Tank) :
    orElseL (letSpecialF Γ ann G [] body') (Fu.bind (letGenF Γ ann [] body') (finishF Γ G)) t =
      ([], t) := by
  cases ann with
  | some A =>
    cases G <;> simp [orElseL, letSpecialF, letGenF, mapL, letCheckF, Fu.firstSome, finishF,
      Fu.flatMapL, Fu.bind, Fu.ret, listO]
  | none =>
    cases G with
    | none => simp [orElseL, letSpecialF, letGenF, finishF, Fu.flatMapL, Fu.bind, Fu.ret, dedupE]
    | some T =>
      by_cases hw : tyWf? T = true <;>
        simp [orElseL, letSpecialF, letGenF, mapL, letCheckF, Fu.firstSome, finishF, Fu.flatMapL,
          Fu.bind, Fu.ret, listO, dedupE, hw]

/-- **The `let` clause.**  The typer's `let` lags behind the elaborator's when
the bound terms do and, for every candidate of the bound term, the bodies do at
the goal the clause checks them against.  A `let` without a type at a goal
falls back to synthesizing its body.  There the bodies lag with no goal, or the
typer's check answers, so that neither falls back. -/
theorem lag_letO (ann : Option (Ty s)) (G : Option (Ty s)) {a1 : ATm s} {bound : Fu (Out Γ)}
    {body : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (Out (Γ.cons r1.ty))}
    {body' : (r1 : Elab Γ) → Option (Ty (s,x)) → Fu (List (Elab (Γ.cons r1.ty)))}
    (hbf : ∀ r1 o, Framed (body' r1 o))
    (h1 : Lag SameCands (inferF Γ a1 none) bound)
    (hb : ∀ t r1s t1, inferF Γ a1 none t = (r1s, t1) → t1.out = false → ∀ r1 ∈ r1s,
      ∀ G' ∈ letGoals ann G, Lag SameCands (body' r1 G') (body r1 G'))
    (hfb : ∀ t r1s t1, inferF Γ a1 none t = (r1s, t1) → t1.out = false → ∀ T, ann = none →
      G = some T → (∀ r1 ∈ r1s, Lag SameCands (body' r1 none) (body r1 none)) ∨
        ∃ c l, SettlesTo (letSpecialF Γ none (some T) r1s body') (c :: l)) :
    Lag SameCands
      (Fu.bind (inferF Γ a1 none) fun r1s =>
        orElseL (letSpecialF Γ ann G r1s body') (Fu.bind (letGenF Γ ann r1s body') (finishF Γ G)))
      (letO Γ ann G bound body) := by
  unfold letO
  refine lag_bind h1 (fun r1s => orElseL_framed (letSpecialF_framed _ _ _ _ hbf)
    (bind_framed (letGenF_framed _ _ _ hbf) fun _ => finishF_framed _ _ _)) ?_
  intro t r1s t1 hrun ho y hy
  simp only [SameCands] at hy
  have hb' := hb t r1s t1 hrun ho
  have hfb' := hfb t r1s t1 hrun ho
  obtain ⟨l, rs⟩ := y
  simp only at hy
  subst hy
  cases l with
  | nil =>
    intro t2 r t' h _
    rw [typer_let_nil] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨([], rs), rfl, reaches_ret _⟩
  | cons r0 l =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
    have hbf2 : Framed (Fu.bind (letGenF Γ ann (r0 :: l) body') (finishF Γ G)) :=
      bind_framed (letGenF_framed _ _ _ hbf) fun _ => finishF_framed _ _ _
    cases ann with
    | some A =>
      refine lag_orElse (lag_ret rfl) ?_ hbf2
      exact lag_thenL (lag_letCheck (some A) A _ fun r1 hr1 => hb' r1 hr1 _ (by simp [letGoals]))
        fun _ => finishF_framed _ _ _
    | none =>
      cases G with
      | none =>
        refine lag_orElse (lag_ret rfl) ?_ hbf2
        exact lag_thenL (lag_letPairs _ hbf fun r1 hr1 => hb' r1 hr1 _ (by simp [letGoals]))
          fun _ => finishF_framed _ _ _
      | some T =>
        have hspec : Lag SameCands (letSpecialF Γ none (some T) (r0 :: l) body')
            (letSpecialO Γ none (some T) (r0 :: l) body) := by
          simp only [letSpecialF, letSpecialO]
          split
          · exact lag_letCheck none T _ fun r1 hr1 => hb' r1 hr1 _ (by simp [letGoals])
          · exact lag_ret rfl
        rcases hfb' T rfl rfl with hl | ⟨c, cs, hs⟩
        · exact lag_orElse hspec (lag_thenL (lag_letPairs _ hbf hl) fun _ => finishF_framed _ _ _)
            hbf2
        · exact lag_orElse_stop hspec (letSpecialF_framed _ _ _ _ hbf) hbf2 hs

end LetLag

/-! ### The canonical fill -/

/-- The domain a function part gives a lambda. -/
def FunPart.dom? {s : Sig} : FunPart s → Option (Ty s)
  | .direct _ T1 _ => some T1
  | .side T1 _ => some T1
  | _ => Option.none

/-- `T` is the type of a candidate of `a` in a run of the typer with no goal
that ends unmarked. -/
def CandTy {s : Sig} (Γ : Ctx s) (a : ATm s) (T : Ty s) : Prop :=
  ∃ t cs t', inferF Γ a none t = (cs, t') ∧ t'.out = false ∧ T ∈ cs.map (·.ty)

/-- The typer checks the body `a` of `λ(x : T). a` against the codomain of the
function type `(∀(x : T1) T2) ^ C` and answers, so that it does not fall back
to synthesis. -/
def LamChecks {s : Sig} (Γ : Ctx s) (T : Ty s) (a : ATm (s,x)) (C : CaptureSet s) (T1 : Ty s)
    (T2 : Ty (s,x)) : Prop :=
  ∀ hwf : Ty.Wf T, ∃ c l,
    SettlesTo (Fu.bind (inferF (Γ.cons T) a (some T2)) (lamCheckF Γ T hwf C T1 T2)) (c :: l)

/-- `e` fills the definitions `d` against the self shape `S` in lockstep, as
`elabDefsF` fills them.  A type or capture member stays.  A field whose
written type, if any, is the shape's keeps its term when that has no empty
slot, and holds some term otherwise. -/
inductive DefsFill : {s : Sig} → PDefs s → Shape s → ADefs s → Prop where
  | typ {s : Sig} {A : Label} {S0 S : Shape s} : DefsFill (.typ A S0) S (.typ A S0)
  | cap {s : Sig} {C : Label} {c : CaptureSet s} {S : Shape s} : DefsFill (.cap C c) S (.cap C c)
  | trmFull {s : Sig} {a c : Label} {o : Option (Ty s)} {t : PTm s} {T : Ty s} {b : ATm s} :
      optAgree o T = true → t.full? = some b → DefsFill (.trm a o t) (.fld c T) (.trm a b)
  | trmSlot {s : Sig} {a c : Label} {o : Option (Ty s)} {t : PTm s} {T : Ty s} {b : ATm s} :
      optAgree o T = true → t.full? = none → DefsFill (.trm a o t) (.fld c T) (.trm a b)
  | and {s : Sig} {d1 d2 : PDefs s} {S1 S2 : Shape s} {e1 e2 : ADefs s} :
      DefsFill d1 S1 e1 → DefsFill d2 S2 e2 → DefsFill (.and d1 d2) (.and S1 S2) (.and e1 e2)

/-- `t`, at the type `T` in the shape, filled by `b`, is a field of `d` with an
empty slot. -/
inductive SlotField : {s : Sig} → PDefs s → Shape s → ADefs s → PTm s → Ty s → ATm s → Prop where
  | here {s : Sig} {a c : Label} {o : Option (Ty s)} {t : PTm s} {T : Ty s} {b : ATm s} :
      t.full? = none → SlotField (.trm a o t) (.fld c T) (.trm a b) t T b
  | left {s : Sig} {d1 d2 : PDefs s} {S1 S2 : Shape s} {e1 e2 : ADefs s} {t : PTm s} {T : Ty s}
      {b : ATm s} :
      SlotField d1 S1 e1 t T b → SlotField (.and d1 d2) (.and S1 S2) (.and e1 e2) t T b
  | right {s : Sig} {d1 d2 : PDefs s} {S1 S2 : Shape s} {e1 e2 : ADefs s} {t : PTm s} {T : Ty s}
      {b : ATm s} :
      SlotField d2 S2 e2 t T b → SlotField (.and d1 d2) (.and S1 S2) (.and e1 e2) t T b

/-- `a` fills the partial term `p`, elaborated in `Γ` at the goal `G`, with
the domains the elaborator reads, and every empty slot is at a direct site. -/
inductive Canon : {s : Sig} → Ctx s → PTm s → Option (Ty s) → ATm s → Prop where
  /-- Every slot written. -/
  | full {s : Sig} {Γ : Ctx s} {p : PTm s} {G : Option (Ty s)} {a : ATm s} :
      p.full? = some a → Canon Γ p G a
  /-- A lambda without a domain whose body has no empty slot: the domain of the
  goal's function part. -/
  | lamGoal {s : Sig} {Γ : Ctx s} {G : Option (Ty s)} {b : PTm (s,x)} {b' : ATm (s,x)}
      {T : Ty s} {fp : FunPart s} :
      b.full? = some b' → SettlesTo (funPartOf Γ G) fp → fp.dom? = some T →
      Canon Γ (.lam none b) G (.lam T b')
  /-- The body `g x` at a goal with no function part: the dominant formal of
  `g`. -/
  | callee {s : Sig} {Γ : Ctx s} {G : Option (Ty s)} {g : BVar s .var} {S : Ty s} :
      SettlesTo (funPartOf Γ G) .none → SettlesTo (argGoalF Γ g) (some S) →
      Canon Γ (.lam none (.app (.there g) .here)) G (.lam S (.app (.there g) .here))
  /-- A lambda whose body has an empty slot at a function type, with its
  written domain or the goal's: its body checked against the codomain, and
  synthesized. -/
  | lamFun {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {T1 : Ty s} {T2 : Ty (s,x)} {T : Ty s}
      {o : Option (Ty s)} {t : PTm (s,x)} {a : ATm (s,x)} :
      t.full? = none → o.getD T1 = T → Canon (Γ.cons T) t (some T2) a →
      Canon (Γ.cons T) t none a →
      Canon Γ (.lam o t) (some ((Shape.all T1 T2) ^ C)) (.lam T a)
  /-- The same, where the typer's check of the body answers, so that neither
  synthesizes it. -/
  | lamFunChk {s : Sig} {Γ : Ctx s} {C : CaptureSet s} {T1 : Ty s} {T2 : Ty (s,x)} {T : Ty s}
      {o : Option (Ty s)} {t : PTm (s,x)} {a : ATm (s,x)} :
      t.full? = none → o.getD T1 = T → Canon (Γ.cons T) t (some T2) a →
      LamChecks Γ T a C T1 T2 →
      Canon Γ (.lam o t) (some ((Shape.all T1 T2) ^ C)) (.lam T a)
  /-- A lambda with a written domain at a goal that is no function type and
  whose function part gives no domain: its body synthesized. -/
  | lamSyn {s : Sig} {Γ : Ctx s} {G : Option (Ty s)} {T : Ty s} {t : PTm (s,x)}
      {a : ATm (s,x)} {fp : FunPart s} :
      t.full? = none → funGoal? G = none → SettlesTo (funPartOf Γ G) fp → fp.dom? = none →
      Canon (Γ.cons T) t none a → Canon Γ (.lam (some T) t) G (.lam T a)
  /-- A `let` that is no call argument: its body at the goal the clause checks
  it against, and synthesized when the clause falls back to that, in the
  context of every candidate of the bound term. -/
  | letGen {s : Sig} {Γ : Ctx s} {G : Option (Ty s)} {tag : LetTag} {ann : Option (Ty s)}
      {t : PTm s} {u : PTm (s,x)} {a1 : ATm s} {a2 : ATm (s,x)} :
      (PTm.let tag ann t u).full? = none → argCallee? tag ann u = none → Canon Γ t none a1 →
      (∀ T0, CandTy Γ a1 T0 → ∀ G' ∈ letGoals ann G, Canon (Γ.cons T0) u G' a2) →
      (∀ T, ann = none → G = some T → ∀ T0, CandTy Γ a1 T0 → Canon (Γ.cons T0) u none a2) →
      Canon Γ (.let tag ann t u) G (.let ann a1 a2)
  /-- A `let` without a type at a goal whose body the typer checks against the
  goal and answers, so that neither synthesizes the body. -/
  | letChk {s : Sig} {Γ : Ctx s} {T : Ty s} {tag : LetTag} {t : PTm s} {u : PTm (s,x)}
      {a1 : ATm s} {a2 : ATm (s,x)} {cs : List (Elab Γ)} {c : Elab Γ} {l : List (Elab Γ)} :
      (PTm.let tag none t u).full? = none → argCallee? tag none u = none → Canon Γ t none a1 →
      (∀ T0, CandTy Γ a1 T0 → Canon (Γ.cons T0) u (some T.weaken) a2) →
      SettlesTo (inferF Γ a1 none) cs →
      SettlesTo (letSpecialF Γ none (some T) cs fun r1 o => inferF (Γ.cons r1.ty) a2 o) (c :: l) →
      Canon Γ (.let tag none t u) (some T) (.let none a1 a2)
  /-- A call argument `let z = t in g z`: `t` checked at the dominant formal
  `F` of `g`, with its box stripped.  The typer's check of the fill at `F`
  answers first with the fill itself, and the typer accepts the filled
  `let`. -/
  | arg {s : Sig} {Γ : Ctx s} {G : Option (Ty s)} {g : BVar s .var} {t : PTm s} {F : Ty s}
      {a1 : ATm s} :
      t.full? = none → SettlesTo (argGoalF Γ g) (some F) → Canon Γ t (some (stripBox F)) a1 →
      (∃ c cs, SettlesTo (inferF Γ a1 (some (stripBox F))) (c :: cs) ∧ c.tm = a1) →
      (∃ c cs, SettlesTo (inferF Γ (.let none a1 (.app (.there g) .here)) G) (c :: cs)) →
      Canon Γ (.let .arg none t (.app (.there g) .here)) G (.let none a1 (.app (.there g) .here))
  /-- An ascription `(t : T)`: `t` checked at `T`. -/
  | asc {s : Sig} {Γ : Ctx s} {G : Option (Ty s)} {t : PTm s} {T : Ty s} {a1 : ATm s} :
      t.full? = none → Canon Γ t (some T) a1 → Canon Γ (.asc t T) G (.asc a1 T)
  /-- A literal with a written self shape: each field with an empty slot
  checked at its type in the shape, in the context that binds the self at `μ`
  of the shape (`probeCtx`).  The typer's check of each field's fill there
  answers first with the fill itself. -/
  | obj {s : Sig} {Γ : Ctx s} {G : Option (Ty s)} {S : Shape (s,x)} {U0 : Option (CaptureSet s)}
      {d : PDefs (s,x)} {e : ADefs (s,x)} :
      d.full? = none → DefsFill d S e →
      (∀ t T b, SlotField d S e t T b → Canon (probeCtx Γ S U0) t (some T) b) →
      (∀ t T b, SlotField d S e t T b →
        ∃ c cs, SettlesTo (inferF (probeCtx Γ S U0) b (some T)) (c :: cs) ∧ c.tm = b) →
      Canon Γ (.obj (some S) U0 d) G (.obj S U0 e)
  /-- A literal without a self shape at a goal that dealiases to `μ` of a
  shape: that shape as the self shape, the fields as for a written one, and
  the typer accepts the filled literal at the goal. -/
  | objGoal {s : Sig} {Γ : Ctx s} {T : Ty s} {S : Shape (s,x)} {U0 : Option (CaptureSet s)}
      {d : PDefs (s,x)} {e : ADefs (s,x)} :
      SettlesTo (selfGoalF Γ T) (some S) → DefsFill d S e →
      (∀ t T' b, SlotField d S e t T' b → Canon (probeCtx Γ S U0) t (some T') b) →
      (∀ t T' b, SlotField d S e t T' b →
        ∃ c cs, SettlesTo (inferF (probeCtx Γ S U0) b (some T')) (c :: cs) ∧ c.tm = b) →
      (∃ c cs, SettlesTo (inferF Γ (.obj S U0 e) (some T)) (c :: cs)) →
      Canon Γ (.obj none U0 d) (some T) (.obj S U0 e)

/-! ### Unfoldings of the elaborator -/

/-- A lambda with a written domain and an empty slot in its body, unfolded. -/
theorem elabF_lam_some {s : Sig} (Γ : Ctx s) (T : Ty s) {t : PTm (s,x)} (ht : t.full? = none)
    (G : Option (Ty s)) :
    elabF Γ (.lam (some T) t) G = lamSomeF Γ T G (fun o => elabF (Γ.cons T) t o) := by
  rw [elabF]
  simp only [PTm.full?, ht, Option.map_none]

/-- A lambda whose body has an empty slot at a function type, unfolded to the
clause of a lambda with a domain. -/
theorem elabF_lam_fun {s : Sig} (Γ : Ctx s) {o : Option (Ty s)} {t : PTm (s,x)}
    (ht : t.full? = none) (C : CaptureSet s) (T1 : Ty s) (T2 : Ty (s,x)) :
    elabF Γ (.lam o t) (some ((Shape.all T1 T2) ^ C)) =
      lamAtF Γ (o.getD T1) (some ((Shape.all T1 T2) ^ C)) (.direct C T1 T2)
        (fun o' => elabF (Γ.cons (o.getD T1)) t o') := by
  cases o with
  | some T =>
    rw [elabF_lam_some _ _ ht]
    rfl
  | none =>
    rw [elabF_lam_none]
    simp only [lamNoneF, funPartOf, bind_ret, ht]
    rfl

/-- A `let` with an empty slot, unfolded. -/
theorem elabF_let {s : Sig} (Γ : Ctx s) {tag : LetTag} {ann : Option (Ty s)} {t : PTm s}
    {u : PTm (s,x)} (hp : (PTm.let tag ann t u).full? = none) (G : Option (Ty s)) :
    elabF Γ (.let tag ann t u) G =
      letF Γ tag ann u G (fun F => elabF Γ t (some F))
        (fun _ => letO Γ ann G (elabF Γ t none) (fun r1 o => elabF (Γ.cons r1.ty) u o)) := by
  rw [elabF, hp]

/-- A `let` that is no call argument goes to the clause of any `let`. -/
theorem letF_gen {s : Sig} {Γ : Ctx s} {tag : LetTag} {ann : Option (Ty s)} {u : PTm (s,x)}
    {G : Option (Ty s)} {arg : Ty s → Fu (Out Γ)} {gen : Unit → Fu (Out Γ)}
    (h : argCallee? tag ann u = none) : letF Γ tag ann u G arg gen = gen () := by
  unfold letF
  rw [h]

/-- A literal with a written self shape and an empty slot, unfolded. -/
theorem elabF_obj_some {s : Sig} (Γ : Ctx s) {S : Shape (s,x)} {U0 : Option (CaptureSet s)}
    {d : PDefs (s,x)} (hd : d.full? = none) (G : Option (Ty s)) :
    elabF Γ (.obj (some S) U0 d) G = objSelfF Γ S U0 G (elabDefsF (probeCtx Γ S U0) d S) := by
  rw [elabF]
  simp only [PTm.full?, hd, Option.map_none]

/-- The definitions of a literal filled in lockstep reach their fill when
the elaboration of every field with an empty slot reaches a first candidate
at the field's fill. -/
theorem elabDefsF_reaches {s : Sig} {Γ : Ctx s} {d : PDefs s} {S : Shape s} {e : ADefs s}
    (hd : DefsFill d S e)
    (hf : ∀ t T b, SlotField d S e t T b → ∃ y : Out Γ,
      (∃ c cs, y.1 = c :: cs ∧ c.tm = b) ∧ Reaches (elabF Γ t (some T)) y) :
    ∃ rs, Reaches (elabDefsF Γ d S) (some e, rs) := by
  induction hd with
  | typ =>
    rw [elabDefsF]
    exact ⟨[], reaches_ret _⟩
  | cap =>
    rw [elabDefsF]
    exact ⟨[], reaches_ret _⟩
  | @trmFull a c o t T b ho ht =>
    rw [elabDefsF]
    simp only [ho, ht]
    exact ⟨[], reaches_ret _⟩
  | @trmSlot a c o t T b ho ht =>
    rw [elabDefsF]
    simp only [ho, ht, ↓reduceIte]
    obtain ⟨y, ⟨c', cs, hy, hct⟩, hry⟩ := hf t T b (.here ht)
    refine ⟨y.2, reaches_bind hry ?_⟩
    rw [hy]
    simp only [List.head?_cons, Option.map_some, hct]
    exact reaches_ret _
  | @and d1 d2 S1 S2 e1 e2 _ _ ih1 ih2 =>
    obtain ⟨rs1, h1⟩ := ih1 fun t T b h => hf t T b (.left h)
    obtain ⟨rs2, h2⟩ := ih2 fun t T b h => hf t T b (.right h)
    rw [elabDefsF]
    refine ⟨rs2, reaches_bind h1 ?_⟩
    exact reaches_bind h2 (reaches_ret _)

/-! ### The elaborator at the direct sites -/

/-- **The elaborator at the direct sites is the typer on the fill.**  When the
typer's run on the canonical fill ends unmarked, the elaborator gives the same
candidates in the same order, with enough fuel. -/
theorem canon_lag {s : Sig} {Γ : Ctx s} {p : PTm s} {G : Option (Ty s)} {a : ATm s}
    (h : Canon Γ p G a) : Lag SameCands (inferF Γ a G) (elabF Γ p G) := by
  induction h with
  | full hp =>
    rw [elabF_full _ hp]
    exact lag_full _ _ _
  | @lamGoal s Γ G b b' T fp hb hs hd =>
    rw [elabF_lam_none]
    unfold lamNoneF
    refine lag_prefix (reaches_settles (funPartOf_framed _ _) hs) ?_
    cases fp with
    | direct C T1 T2 =>
      simp only [FunPart.dom?, Option.some.injEq] at hd
      subst hd
      simp only [hb]
      exact lag_full _ _ _
    | side T1 V =>
      simp only [FunPart.dom?, Option.some.injEq] at hd
      subst hd
      simp only [hb]
      exact lag_full _ _ _
    | none => cases hd
    | bad => cases hd
  | @callee s Γ G g S hf hg =>
    rw [elabF_lam_none]
    unfold lamNoneF
    refine lag_prefix (reaches_settles (funPartOf_framed _ _) hf) ?_
    simp only [lamCalleeF, calleeOf?_app]
    refine lag_prefix (reaches_settles (argGoalF_framed _ _) hg) ?_
    exact lag_full _ _ _
  | @lamFun s Γ C T1 T2 T o t a ht hT _ _ ih2 ih1 =>
    rw [elabF_lam_fun _ ht, hT, inferF]
    unfold lamAtF
    by_cases hwf : Ty.Wf T
    · simp only [dif_pos hwf, funGoal?]
      exact lag_orElse (lag_thenL ih2 fun _ => lamCheckF_framed _ _ _ _ _ _ _)
        (lag_thenL ih1 fun _ => lamGenFin_framed _ _ _ _ _)
        (bind_framed (inferF_framed _ _ _) fun _ => lamGenFin_framed _ _ _ _ _)
    · simp only [dif_neg hwf]
      exact lag_ret rfl
  | @lamFunChk s Γ C T1 T2 T o t a ht hT _ hchk ih2 =>
    rw [elabF_lam_fun _ ht, hT, inferF]
    unfold lamAtF
    by_cases hwf : Ty.Wf T
    · simp only [dif_pos hwf, funGoal?]
      obtain ⟨c, l, hs⟩ := hchk hwf
      exact lag_orElse_stop (lag_thenL ih2 fun _ => lamCheckF_framed _ _ _ _ _ _ _)
        (bind_framed (inferF_framed _ _ _) fun _ => lamCheckF_framed _ _ _ _ _ _ _)
        (bind_framed (inferF_framed _ _ _) fun _ => lamGenFin_framed _ _ _ _ _) hs
    · simp only [dif_neg hwf]
      exact lag_ret rfl
  | @lamSyn s Γ G T t a fp ht hG hs hd _ ih =>
    rw [elabF_lam_some _ _ ht]
    unfold lamSomeF
    refine lag_prefix (reaches_settles (funPartOf_framed _ _) hs) ?_
    rw [inferF]
    unfold lamAtF
    by_cases hwf : Ty.Wf T
    · simp only [dif_pos hwf, hG]
      cases fp with
      | direct => cases hd
      | side => cases hd
      | none =>
        exact lag_orElse (lag_ret rfl) (lag_thenL ih fun _ => lamGenFin_framed _ _ _ _ _)
          (bind_framed (inferF_framed _ _ _) fun _ => lamGenFin_framed _ _ _ _ _)
      | bad =>
        exact lag_orElse (lag_ret rfl) (lag_thenL ih fun _ => lamGenFin_framed _ _ _ _ _)
          (bind_framed (inferF_framed _ _ _) fun _ => lamGenFin_framed _ _ _ _ _)
    · simp only [dif_neg hwf]
      exact lag_ret rfl
  | @letGen s Γ G tag ann t u a1 a2 hp hc _ _ _ ih1 ih2 ih3 =>
    rw [elabF_let _ hp, letF_gen hc, inferF]
    refine lag_letO ann G (fun _ _ => inferF_framed _ _ _) ih1
      (fun t r1s t1 hrun ho r1 hr1 G' hG' =>
        ih2 r1.ty ⟨t, r1s, t1, hrun, ho, List.mem_map_of_mem hr1⟩ G' hG') ?_
    intro t r1s t1 hrun ho T hann hG
    exact .inl fun r1 hr1 => ih3 T hann hG r1.ty ⟨t, r1s, t1, hrun, ho, List.mem_map_of_mem hr1⟩
  | @letChk s Γ T tag t u a1 a2 cs c l hp hc _ _ hcs hsp ih1 ih2 =>
    rw [elabF_let _ hp, letF_gen hc, inferF]
    refine lag_letO none (some T) (fun _ _ => inferF_framed _ _ _) ih1
      (fun t r1s t1 hrun ho r1 hr1 G' hG' => ?_) ?_
    · simp only [letGoals, List.mem_singleton] at hG'
      subst hG'
      exact ih2 r1.ty ⟨t, r1s, t1, hrun, ho, List.mem_map_of_mem hr1⟩
    · intro t r1s t1 hrun ho T' _ hG
      simp only [Option.some.injEq] at hG
      subst hG
      have hr := settles_unique (inferF_framed _ _ _) hcs hrun ho
      subst hr
      exact .inr ⟨c, l, hsp⟩
  | @arg s Γ G g t F a1 ht hF _ hchk hacc ih =>
    rw [elabF_arg _ ht]
    unfold argLetF
    refine lag_prefix (reaches_settles (argGoalF_framed _ _) hF) ?_
    obtain ⟨c, cs, hcs, hct⟩ := hchk
    obtain ⟨y, hy, hry⟩ := settles_lag ih hcs
    simp only [SameCands] at hy
    unfold orElseW
    dsimp only
    rw [bind_bind]
    refine lag_prefix hry ?_
    simp only [hy, hct]
    obtain ⟨c', cs', hacc'⟩ := hacc
    refine lag_stop (ok := fun cs => !cs.isEmpty) (inferF_framed _ _ _) (lag_full _ _ _) hacc' ?_
    intro y hy
    simp only [SameCands] at hy
    simp [hy]
  | @asc s Γ G t T a1 ht _ ih =>
    rw [elabF_asc _ ht, inferF]
    unfold ascO
    exact lag_thenL ih fun _ => finishF_framed _ _ _
  | @obj s Γ G S U0 d e hd hfill _ htyp ih =>
    rw [elabF_obj_some _ hd]
    unfold objSelfF
    obtain ⟨rs, hr⟩ := elabDefsF_reaches hfill fun t T b hsf => by
      obtain ⟨c, cs, hs, hct⟩ := htyp t T b hsf
      obtain ⟨y, hy, hry⟩ := settles_lag (ih t T b hsf) hs
      exact ⟨y, ⟨c, cs, hy, hct⟩, hry⟩
    refine lag_prefix hr ?_
    exact lag_full _ _ _
  | @objGoal s Γ T S U0 d e hS hfill _ htyp hacc ih =>
    rw [elabF]
    simp only [PTm.full?]
    refine lag_prefix (reaches_settles (selfGoalF_framed _ _) hS) ?_
    obtain ⟨rs, hr⟩ := elabDefsF_reaches hfill fun t T' b hsf => by
      obtain ⟨c, cs, hs, hct⟩ := htyp t T' b hsf
      obtain ⟨y, hy, hry⟩ := settles_lag (ih t T' b hsf) hs
      exact ⟨y, ⟨c, cs, hy, hct⟩, hry⟩
    unfold orElseW objSelfF
    dsimp only
    rw [bind_bind]
    refine lag_prefix hr ?_
    obtain ⟨c, cs, hacc'⟩ := hacc
    refine lag_stop (ok := fun cs => !cs.isEmpty) (inferF_framed _ _ _) (lag_full _ _ _) hacc' ?_
    intro y hy
    simp only [SameCands] at hy
    simp [hy]

/-! ### At the top -/

/-- **Completeness at the direct sites, with the candidate.**  A program
whose canonical fill the typer types elaborates, from some fuel on, to the
typer's first candidate on that fill. -/
theorem elab_complete_direct_fill {π : PlatformNames} {p : PTm π.sig} {a : ATm π.sig} {n : Nat}
    {c0 : Elab (platformCtx π.plat)} (hc : Canon (platformCtx π.plat) p none a)
    (hl : (synthTopF n π a).1 = some c0) :
    ∃ n0, ∀ m, n0 ≤ m → (elabTopF m π p).1 = .ok c0 := by
  unfold synthTopF synthInF synthF at hl
  cases hs : inferF (platformCtx π.plat) a none ⟨n, false⟩ with
  | mk cs t' =>
    rw [hs] at hl
    cases cs with
    | nil => simp [firstCand] at hl
    | cons c cs =>
      cases ho : t'.out with
      | true => simp [firstCand, ho] at hl
      | false =>
        simp only [firstCand, ho, Bool.false_eq_true, if_false, Option.some.injEq] at hl
        subst hl
        obtain ⟨r', hR, n1, m1, hk⟩ := canon_lag hc ⟨n, false⟩ (c :: cs) t' hs ho
        refine ⟨n1, fun m hm => ?_⟩
        have hrun := hk (m - n1)
        have htk : (⟨n1 + (m - n1), false⟩ : Tank) = ⟨m, false⟩ := by
          rw [Tank.mk.injEq]
          exact ⟨by omega, rfl⟩
        rw [htk] at hrun
        obtain ⟨es, rs⟩ := r'
        simp only [SameCands] at hR
        subst hR
        unfold elabTopF
        rw [hrun]
        rfl

/-- **Completeness at the direct sites.**  A program whose canonical fill the
typer types is accepted by the elaborator from some fuel on. -/
theorem elab_complete_direct {π : PlatformNames} {p : PTm π.sig} {a : ATm π.sig} {n : Nat}
    (hc : Canon (platformCtx π.plat) p none a) (hl : (synthTopF n π a).1.isSome = true) :
    ∃ n0, ∀ m, n0 ≤ m → (elabTopF m π p).1.isOk = true := by
  obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨n0, h⟩ := elab_complete_direct_fill hc hc0
  refine ⟨n0, fun m hm => ?_⟩
  rw [h m hm]
  rfl

/-- **Completeness at the direct sites, through the pipeline.**  A program
that resolves to a partial term whose canonical fill the typer types, and
whose fill the elaborated term gives back, compiles as the typer compiles the
fill, record included, at every budget from some fuel on. -/
theorem compile_complete_direct {Λ : LabelTable} {π : PlatformNames} {e : STm} {p : PTm π.sig}
    {a : ATm π.sig} {n : Nat} {c0 : Elab (platformCtx π.plat)}
    (hp : resolvePTop Λ π e = some p) (hc : Canon (platformCtx π.plat) p none a)
    (hl : (synthTopF n π a).1 = some c0) (hf : p.fillFrom c0.tm = some a)
    (hfa : p.fills a = true) :
    ∃ n0, ∀ b : Budget, n0 ≤ b.fuel → compile b Λ π e = compileLanded b π a := by
  obtain ⟨n0, h⟩ := elab_complete_direct_fill hc hl
  refine ⟨max n0 n, fun b hb => ?_⟩
  have he := h b.fuel (Nat.le_trans (Nat.le_max_left _ _) hb)
  have hs := synthTop?_mono hl (Nat.le_trans (Nat.le_max_right _ _) hb)
  simp only [compile, compileE, hp, he, hf, hfa, if_true, compileLanded, synthTop?, hs]
  by_cases hk : ATm.skel c0.tm = ATm.skel a
  · simp [hk, Except.toOption]
  · simp [hk, Except.toOption]

/-- A candidate type of a term in a run that ends unmarked is one of the types
any run that ends unmarked gives. -/
theorem candTy_of {s : Sig} {Γ : Ctx s} {a : ATm s} {cs : List (Elab Γ)}
    (hs : SettlesTo (inferF Γ a none) cs) {T : Ty s} (hT : CandTy Γ a T) : T ∈ cs.map (·.ty) := by
  obtain ⟨t, cs', t', hrun, ho, hmem⟩ := hT
  rw [settles_unique (inferF_framed Γ a none) hs hrun ho] at hmem
  exact hmem

/-! ### Deciding the canonical fill -/

/-- The answer of a computation from a full tank of `n` units, when the tank
ends unmarked. -/
def settledAt {α : Type} (c : Fu α) (n : Nat) : Option α :=
  match c ⟨n, false⟩ with
  | (x, t) => if t.out then none else some x

/-- An answer read by `settledAt` is where the computation settles. -/
theorem settlesTo_of_settledAt {α : Type} {c : Fu α} {x : α} {n : Nat}
    (h : settledAt c n = some x) : SettlesTo c x := by
  unfold settledAt at h
  cases hc : c ⟨n, false⟩ with
  | mk y t =>
    rw [hc] at h
    cases ho : t.out with
    | true => simp [ho] at h
    | false =>
      simp only [ho, Bool.false_eq_true, if_false, Option.some.injEq] at h
      subst h
      exact ⟨n, t.left, by rw [hc]; exact Prod.ext rfl (tank_eq rfl ho)⟩

/-- Whether a computation settles at a nonempty list from a full tank of `n`
units. -/
def settlesNonempty {α : Type} (c : Fu (List α)) (n : Nat) : Bool :=
  match settledAt c n with
  | some (_ :: _) => true
  | _ => false

theorem settlesNonempty_sound {α : Type} {c : Fu (List α)} {n : Nat}
    (h : settlesNonempty c n = true) : ∃ x l, SettlesTo c (x :: l) := by
  unfold settlesNonempty at h
  split at h
  · rename_i x l hs
    exact ⟨x, l, settlesTo_of_settledAt hs⟩
  · cases h

/-- Whether the typer's check of the body `a` of `λ(x : T). a` against the
codomain `T2` answers, from a full tank of `n` units. -/
def lamChecksB {s : Sig} (n : Nat) (Γ : Ctx s) (T : Ty s) (a : ATm (s,x)) (C : CaptureSet s)
    (T1 : Ty s) (T2 : Ty (s,x)) : Bool :=
  if hwf : Ty.Wf T then
    settlesNonempty (Fu.bind (inferF (Γ.cons T) a (some T2)) (lamCheckF Γ T hwf C T1 T2)) n
  else true

theorem lamChecksB_sound {s : Sig} {n : Nat} {Γ : Ctx s} {T : Ty s} {a : ATm (s,x)}
    {C : CaptureSet s} {T1 : Ty s} {T2 : Ty (s,x)} (h : lamChecksB n Γ T a C T1 T2 = true) :
    LamChecks Γ T a C T1 T2 := by
  intro hwf
  unfold lamChecksB at h
  rw [dif_pos hwf] at h
  exact settlesNonempty_sound h

mutual
/-- Whether `a` is the canonical fill of `p` elaborated in `Γ` at the goal
`G`, with the readings of the goal and the runs of the typer taken from a full
tank of `n` units. -/
def canonB {s : Sig} (n : Nat) (Γ : Ctx s) (p : PTm s) (G : Option (Ty s)) (a : ATm s) : Bool :=
  if p.full? = some a then true
  else
    match p, a with
    | .lam o t, .lam S a' =>
        match o, t.full? with
        | none, some b =>
            match settledAt (funPartOf Γ G) n with
            | some fp =>
                match fp.dom? with
                | some T => decide (T = S) && decide (b = a')
                | none =>
                    match fp, calleeOf? t with
                    | .none, some g =>
                        decide (t = .app (.there g) .here) && decide (a' = .app (.there g) .here) &&
                          decide (settledAt (argGoalF Γ g) n = some (some S))
                    | _, _ => false
            | none => false
        | _, none =>
            match G with
            | some (.capt C (.all T1 T2)) =>
                decide (o.getD T1 = S) && canonB n (Γ.cons S) t (some T2) a' &&
                  (canonB n (Γ.cons S) t none a' || lamChecksB n Γ S a' C T1 T2)
            | _ =>
                decide (o = some S) && canonB n (Γ.cons S) t none a' &&
                  match settledAt (funPartOf Γ G) n with
                  | some fp => fp.dom?.isNone
                  | none => false
        | some _, some _ => false
    | .let tag ann t u, .let ann' a1 a2 =>
        match argCallee? tag ann u with
        | none =>
            decide (ann = ann') && decide ((PTm.let tag ann t u).full? = none) &&
              canonB n Γ t none a1 &&
              match settledAt (inferF Γ a1 none) n with
              | some cs =>
                  (cs.map (·.ty)).all (fun T0 =>
                    (letGoals ann G).all fun G' => canonB n (Γ.cons T0) u G' a2) &&
                  match ann, G with
                  | none, some T =>
                      (cs.map (·.ty)).all (fun T0 => canonB n (Γ.cons T0) u none a2) ||
                        settlesNonempty
                          (letSpecialF Γ none (some T) cs fun r1 o => inferF (Γ.cons r1.ty) a2 o) n
                  | _, _ => true
              | none => false
        | some g =>
            decide (tag = .arg) && decide (ann = none) && decide (ann' = none) &&
              decide (u = .app (.there g) .here) && decide (a2 = .app (.there g) .here) &&
              decide (t.full? = none) &&
              match settledAt (argGoalF Γ g) n with
              | some (some F) =>
                  canonB n Γ t (some (stripBox F)) a1 &&
                    (match settledAt (inferF Γ a1 (some (stripBox F))) n with
                      | some (c :: _) => decide (c.tm = a1)
                      | _ => false) &&
                    settlesNonempty (inferF Γ (.let none a1 (.app (.there g) .here)) G) n
              | _ => false
    | .asc t T, .asc a1 T' =>
        decide (T = T') && decide (t.full? = none) && canonB n Γ t (some T) a1
    | .obj (some S) U0 d, .obj S' U0' e =>
        decide (S = S') && decide (U0 = U0') && decide (d.full? = none) &&
          canonDefsB n (probeCtx Γ S U0) d S e
    | .obj none U0 d, .obj S U0' e =>
        match G with
        | some T =>
            decide (U0 = U0') && decide (settledAt (selfGoalF Γ T) n = some (some S)) &&
              canonDefsB n (probeCtx Γ S U0) d S e &&
              settlesNonempty (inferF Γ (.obj S U0 e) (some T)) n
        | none => false
    | _, _ => false
termination_by structural p

/-- Whether `e` fills the definitions `d` against the self shape `S` in
lockstep, each field with an empty slot at a direct site whose fill the
typer's check gives back, read from a full tank of `n` units. -/
def canonDefsB {s : Sig} (n : Nat) (Γ : Ctx s) (d : PDefs s) (S : Shape s) (e : ADefs s) :
    Bool :=
  match d, S, e with
  | .typ A S0, _, .typ A' S0' => decide (A = A') && decide (S0 = S0')
  | .cap C c, _, .cap C' c' => decide (C = C') && decide (c = c')
  | .trm a o t, .fld _ T, .trm a' b =>
      decide (a = a') && optAgree o T &&
        match t.full? with
        | some b' => decide (b' = b)
        | none =>
            canonB n Γ t (some T) b &&
              match settledAt (inferF Γ b (some T)) n with
              | some (c :: _) => decide (c.tm = b)
              | _ => false
  | .and d1 d2, .and S1 S2, .and e1 e2 => canonDefsB n Γ d1 S1 e1 && canonDefsB n Γ d2 S2 e2
  | _, _, _ => false
termination_by structural d
end

/-- A goal that is no function type has no function goal. -/
theorem funGoal?_none {s : Sig} {G : Option (Ty s)}
    (h : ∀ C T1 T2, G = some ((Shape.all T1 T2) ^ C) → False) : funGoal? G = none := by
  cases G with
  | none => rfl
  | some T =>
    obtain ⟨C, S⟩ := T
    cases S with
    | all T1 T2 => exact (h C T1 T2 rfl).elim
    | _ => rfl

mutual
/-- `canonB` decides `Canon` soundly. -/
theorem canonB_sound {n : Nat} : {s : Sig} → {Γ : Ctx s} → (p : PTm s) → (G : Option (Ty s)) →
    (a : ATm s) → canonB n Γ p G a = true → Canon Γ p G a
  | _, Γ, .lam o t, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · rename_i hnf
      cases a with
      | lam S a' =>
        simp only at h
        split at h
        · rename_i b hb
          split at h
          · rename_i fp hfp
            split at h
            · rename_i T hT
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .lamGoal hb (settlesTo_of_settledAt hfp) hT
            · split at h
              · rename_i g _
                simp only [Bool.and_eq_true, decide_eq_true_eq] at h
                obtain ⟨⟨rfl, rfl⟩, ha⟩ := h
                exact .callee (settlesTo_of_settledAt hfp) (settlesTo_of_settledAt ha)
              · cases h
          · cases h
        · rename_i o ht
          split at h
          · rename_i C T1 T2
            simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨hT, h1⟩, h2 | h2⟩ := h
            · exact .lamFun ht hT (canonB_sound t _ a' h1) (canonB_sound t none a' h2)
            · exact .lamFunChk ht hT (canonB_sound t _ a' h1) (lamChecksB_sound h2)
          · rename_i hG
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨rfl, h1⟩, h2⟩ := h
            split at h2
            · rename_i fp hfp
              exact .lamSyn ht (funGoal?_none hG) (settlesTo_of_settledAt hfp) (by simpa using h2)
                (canonB_sound t none a' h1)
            · cases h2
        · cases h
      | _ => simp at h
  | _, Γ, .let tag ann t u, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · cases a with
      | «let» ann' a1 a2 =>
        simp only at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨rfl, hp⟩, h1⟩, h2⟩ := h
          split at h2
          · rename_i cs hcs
            simp only [Bool.and_eq_true] at h2
            obtain ⟨h3, h4⟩ := h2
            have hgoals : ∀ T0, CandTy Γ a1 T0 → ∀ G' ∈ letGoals ann G,
                Canon (Γ.cons T0) u G' a2 := by
              intro T0 hT G' hG'
              have hm := candTy_of (settlesTo_of_settledAt hcs) hT
              rw [List.all_eq_true] at h3
              have h5 := h3 T0 hm
              rw [List.all_eq_true] at h5
              exact canonB_sound u G' a2 (h5 G' hG')
            split at h4
            · rename_i T
              simp only [Bool.or_eq_true, List.all_eq_true] at h4
              rcases h4 with h4 | h4
              · refine .letGen hp hc (canonB_sound t none a1 h1) hgoals ?_
                intro T' _ hG T0 hT
                exact canonB_sound u none a2 (h4 T0 (candTy_of (settlesTo_of_settledAt hcs) hT))
              · obtain ⟨c, l, hs⟩ := settlesNonempty_sound h4
                exact .letChk hp hc (canonB_sound t none a1 h1)
                  (fun T0 hT => hgoals T0 hT _ (by simp [letGoals])) (settlesTo_of_settledAt hcs) hs
            · rename_i hne
              refine .letGen hp hc (canonB_sound t none a1 h1) hgoals ?_
              intro T' hann hG
              exact (hne T' hann hG).elim
          · cases h2
        · rename_i g hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, ht⟩, h5⟩ := h
          split at h5
          · rename_i F hF
            simp only [Bool.and_eq_true] at h5
            obtain ⟨⟨h6, h7⟩, h8⟩ := h5
            split at h7
            · rename_i c cs hcs
              simp only [decide_eq_true_eq] at h7
              obtain ⟨c', cs', hacc⟩ := settlesNonempty_sound h8
              exact .arg ht (settlesTo_of_settledAt hF) (canonB_sound t _ a1 h6)
                ⟨c, cs, settlesTo_of_settledAt hcs, h7⟩ ⟨c', cs', hacc⟩
            · cases h7
          · cases h5
      | _ => simp at h
  | _, Γ, .asc t T, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · cases a with
      | asc a1 T' =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, ht⟩, h1⟩ := h
        exact .asc ht (canonB_sound t _ a1 h1)
      | _ => simp at h
  | _, Γ, .path _, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
  | _, Γ, .obj o U0 d, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · cases o with
      | none =>
        cases a with
        | obj S U0' e =>
          simp only at h
          split at h
          · rename_i T
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨rfl, hS⟩, h1⟩, h2⟩ := h
            obtain ⟨hfill, hc, ht⟩ := canonDefsB_sound d S e h1
            obtain ⟨c, cs, hacc⟩ := settlesNonempty_sound h2
            exact .objGoal (settlesTo_of_settledAt hS) hfill hc ht ⟨c, cs, hacc⟩
          · cases h
        | _ => simp at h
      | some S =>
        cases a with
        | obj S' U0' e =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨rfl, rfl⟩, hd⟩, h1⟩ := h
          obtain ⟨hfill, hc, ht⟩ := canonDefsB_sound d S e h1
          exact .obj hd hfill hc ht
        | _ => simp at h
  | _, Γ, .app _ _, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
  | _, Γ, .proj _ _, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
  | _, Γ, .box _, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
  | _, Γ, .unbox _ _, G, a, h => by
    unfold canonB at h
    split at h
    · rename_i hf
      exact .full hf
    · simp at h
termination_by structural _ _ p => p

/-- `canonDefsB` decides the lockstep fill of a literal's definitions and the
premises of its fields soundly. -/
theorem canonDefsB_sound {n : Nat} : {s : Sig} → {Γ : Ctx s} → (d : PDefs s) → (S : Shape s) →
    (e : ADefs s) → canonDefsB n Γ d S e = true →
    DefsFill d S e ∧ (∀ t T b, SlotField d S e t T b → Canon Γ t (some T) b) ∧
      (∀ t T b, SlotField d S e t T b →
        ∃ c cs, SettlesTo (inferF Γ b (some T)) (c :: cs) ∧ c.tm = b)
  | _, Γ, .typ A S0, S, e, h => by
    cases e with
    | typ A' S0' =>
      simp only [canonDefsB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨.typ, ?_, ?_⟩ <;> intro _ _ _ hs <;> cases hs
    | _ => simp [canonDefsB] at h
  | _, Γ, .cap C c, S, e, h => by
    cases e with
    | cap C' c' =>
      simp only [canonDefsB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨.cap, ?_, ?_⟩ <;> intro _ _ _ hs <;> cases hs
    | _ => simp [canonDefsB] at h
  | _, Γ, .trm a o t, S, e, h => by
    cases S with
    | fld c T =>
      cases e with
      | trm a' b =>
        unfold canonDefsB at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, ho⟩, h1⟩ := h
        split at h1
        · rename_i b' hb
          simp only [decide_eq_true_eq] at h1
          subst h1
          refine ⟨.trmFull ho hb, fun _ _ _ hs => ?_, fun _ _ _ hs => ?_⟩
          · cases hs with
            | here ht => rw [hb] at ht; cases ht
          · cases hs with
            | here ht => rw [hb] at ht; cases ht
        · rename_i hb
          simp only [Bool.and_eq_true] at h1
          obtain ⟨h2, h3⟩ := h1
          split at h3
          · rename_i c' cs hcs
            simp only [decide_eq_true_eq] at h3
            refine ⟨.trmSlot ho hb, fun _ _ _ hs => ?_, fun _ _ _ hs => ?_⟩
            · cases hs with
              | here _ => exact canonB_sound t _ b h2
            · cases hs with
              | here _ => exact ⟨c', cs, settlesTo_of_settledAt hcs, h3⟩
          · cases h3
      | _ => simp [canonDefsB] at h
    | _ => cases e <;> simp [canonDefsB] at h
  | _, Γ, .and d1 d2, S, e, h => by
    cases S with
    | and S1 S2 =>
      cases e with
      | and e1 e2 =>
        simp only [canonDefsB, Bool.and_eq_true] at h
        obtain ⟨f1, c1, t1⟩ := canonDefsB_sound d1 S1 e1 h.1
        obtain ⟨f2, c2, t2⟩ := canonDefsB_sound d2 S2 e2 h.2
        refine ⟨.and f1 f2, fun t T b hs => ?_, fun t T b hs => ?_⟩
        · cases hs with
          | left hs => exact c1 t T b hs
          | right hs => exact c2 t T b hs
        · cases hs with
          | left hs => exact t1 t T b hs
          | right hs => exact t2 t T b hs
      | _ => simp [canonDefsB] at h
    | _ => cases e <;> simp [canonDefsB] at h
termination_by structural _ _ d => d
end

/-- Whether the erased program `e` resolves to a partial term whose canonical
fill is the resolution of the written program `w`, the typer types that fill,
and the elaborated term gives the fill back, all read from a full tank of `n`
units. -/
def canonAt (Λ : LabelTable) (π : PlatformNames) (e w : STm) (n : Nat := defaultFuel) : Bool :=
  match resolvePTop Λ π e, resolveTop Λ π w with
  | some p, some a =>
      canonB n (platformCtx π.plat) p none a &&
        match (synthTopF n π a).1 with
        | some c0 => decide (p.fillFrom c0.tm = some a) && p.fills a
        | none => false
  | _, _ => false

/-- **Completeness at the direct sites, decided.**  An erased program that
`canonAt` relates to a written one compiles as the written program does,
record included, at every budget from some fuel on. -/
theorem compile_complete_canonAt {Λ : LabelTable} {π : PlatformNames} {e w : STm} {n : Nat}
    (h : canonAt Λ π e w n = true) :
    ∃ n0, ∀ b : Budget, n0 ≤ b.fuel → compile b Λ π e = compile b Λ π w := by
  unfold canonAt at h
  split at h
  · rename_i p a hp ha
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    split at h2
    · rename_i c0 hc0
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      obtain ⟨n0, h0⟩ := compile_complete_direct hp (canonB_sound p none a h1) hc0 h2.1 h2.2
      exact ⟨n0, fun b hb => by rw [compile_full ha]; exact h0 b hb⟩
    · cases h2
  · cases h

end Complete

end CapturesFrontend
