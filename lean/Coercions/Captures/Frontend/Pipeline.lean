import Coercions.Captures.Frontend.Typer
import Coercions.Captures.Frontend.Step
import Coercions.Captures.DotToFCdot.Prediction
import Coercions.Captures.FCdot.CheckerCompleteness

/-!
# The pipeline

`compile` takes a surface program through the whole front end.  The theorems
say what the result is worth.  Each composes results of the calculus.  The
front end proves nothing about the calculus.

`compile` resolves a program over a platform, types it at the platform's
context and checks that the typer kept the program's skeleton.  A platform is
a prefix of capture binders, one per capability the program may use.  Box
inference may insert `□ x` and `C ⊸ x`, so the typed term is not the resolved
one.  `Compiled` holds the elaborated term, its use set, its type, the
derivation about its erasure and the proof that its skeleton is that of the
resolved term.  `ATm.skel` forgets annotations, ascriptions, boxes and
unboxings, and inlines a `let` of a variable.  So the check says that the
elaborated program has the skeleton of the resolved one.

The typer types under `platformCtx`.  `platformCtx_eq` equates it with the
calculus's `Platform.ctx`, and `compile` moves the derivation across, so the
theorems name the calculus's context.

`compileAndRun` follows `compile` with the executable machine of `Step.lean`
from the platform's initial store, at a step budget.

## Theorems

`h : compile b Λ π e = some ⟨a, c⟩` is a successful compile, the platform is
`π.plat` and the compiled term is `c.tm.erase`.

* `compile_checks`.  The target checker accepts the translation of the
  derivation.
* `compile_uses_checks`.  It accepts the use set evidence as well.
* `compile_erase`.  The translation erases to the erasure of the compiled term.
* `compile_faithful`.  The elaborated term has the skeleton of the resolved one.
* `compile_safe`.  Every state a run reaches is final or has a step.
  `DotMNF.dot_safety` is stated at the empty context only, so this is composed
  at the platform from `Platform.simulatedRun`, `FCdot.State.Typed.steps`,
  `Platform.initial_typed` and `Simulated.progress`.
* `compile_not_stuck`.  No reachable state is stuck.
* `compile_run_progress`.  The state the driver `run` returns is final or the
  executable machine finds a step from it.
* `compile_capture_prediction`.  Along any run, a target state with the same
  erasure and a typed store exists, and it uses no more than the translated
  use set the typer found, renamed along the store extension.
* `compile_effect_safety`.  A platform capability that is not in the use set
  is not a root, in the matched target state, of a variable a run reads.
* `compile_checks_get` and `compile_effect_safety_get`.  The same for a
  program whose compile succeeds by a decided test.  For a concrete program
  the kernel reduces the compile, so `decide +kernel` closes the premises.

The premise `h` is what a caller holds.  The content rides on the type of
`c`.  The other premises select what a theorem speaks of: a run, a variable,
a capability.  None is a hypothesis about the compiler.
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

/-- A program typed over a platform, with the resolved term `a` it came from. -/
structure Compiled {s₀ : Sig} (P : Platform s₀) (a : ATm s₀) where
  /-- The elaborated term. -/
  tm : ATm s₀
  /-- The use set. -/
  uses : CaptureSet s₀
  /-- The type. -/
  ty : Ty s₀
  /-- The derivation. -/
  deriv : HasTy uses P.ctx tm.erase ty
  /-- The elaborated term has the skeleton of the resolved one. -/
  skel : ATm.skel tm = ATm.skel a

/-! ## Pipeline -/

/-- Resolve over the platform, type at the platform's context, and keep the
result when the skeleton is the program's.  `none` carries no reason.  The
result is a dependent pair, since the record speaks of the resolved term. -/
def compile (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) :
    Option ((a : ATm π.sig) × Compiled π.plat a) :=
  match resolveTop Λ π e with
  | none => none
  | some a =>
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

-- `h` is read by no proof.
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

/-- **The compiled term has the skeleton of the resolved one.**  This names the
field `Compiled.skel`.  The check is in `compile`, which builds the record only
when the skeletons agree. -/
theorem compile_faithful (h : compile b Λ π e = some ⟨a, c⟩) : ATm.skel c.tm = ATm.skel a :=
  c.skel

/-- **Safety of the compiled program.**  Every state of a run `r` from the
platform's initial store is final or has a step.  The matched target run stays
typed, and `Simulated.progress` reads progress back. -/
theorem compile_safe (h : compile b Λ π e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st) :
    State.Final st ∨ ∃ (s' : Sig) (st' : State s'), Step st st' := by
  obtain ⟨stt, hrun, he, -⟩ := π.plat.simulatedRun c.deriv r
  obtain ⟨U, hU⟩ := FCdot.State.Typed.steps ⟨_, π.plat.initial_typed c.deriv⟩ hrun
  exact DotMNF.Simulated.progress ⟨stt, U, hU, he⟩

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

/-- **Capture prediction.**  For a run `r` from the platform's initial store, a
target state with the same erasure and a typed store exists, its store extends the
platform's along a renaming `ρ`, and its use set is below the translation of
the typer's use set, renamed by `ρ`. -/
theorem compile_capture_prediction (h : compile b Λ π e = some ⟨a, c⟩) {s : Sig}
    {st : State s} (r : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename π.sig s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext π.plat.targetStore stt.σ ρ ∧
          FCdot.CapLe Γ' stt.uses (c.uses.translate.rename ρ) :=
  DotMNF.dot_capture_prediction π.plat c.deriv r

/-- **Effect safety.**  Let `κ` be a platform capability that the typer's use
set lacks (`hκ`), `r` a run from the platform's initial store and `x` a
variable the reached state reads.  Then `κ` is not a root of `x` in the
matched target state.  The premise of `DotMNF.dot_effect_safety` on the
translated set follows from `hκ` by `cvar_mem_translate`. -/
theorem compile_effect_safety (h : compile b Λ π e = some ⟨a, c⟩) {κ : BVar π.sig .cap}
    (hκ : c.uses.elem (.cvar κ) = false)
    {s : Sig} {st : State s} (r : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename π.sig s),
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

/-- **Effect safety of a program that compiles.**  `compile_effect_safety` at
the returned record. -/
theorem compile_effect_safety_get (h : (compile b Λ π e).isSome = true)
    {κ : BVar π.sig .cap} (hκ : ((compile b Λ π e).get h).2.uses.elem (.cvar κ) = false)
    {s : Sig} {st : State s}
    (r : Steps (⟨π.plat.store, .nil, ((compile b Λ π e).get h).2.tm.erase⟩ : State π.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename π.sig s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext π.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var κ)) [FCdot.CapAtom.var x] :=
  compile_effect_safety (Option.some_get h).symm hκ r hin

end

end CapturesFrontend
