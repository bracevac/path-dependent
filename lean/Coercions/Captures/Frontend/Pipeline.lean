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
* `compile_faithful`.  The resolved term is what `resolveTop` makes of the
  program, the record holds what `synthTop?` answers on it, and the elaborated
  term has the skeleton of the resolved one.  They differ only in types,
  capture sets, boxes, unboxings, ascriptions and a `let` of a variable.
* `compile_safe`.  Every state a run reaches is final or has a step.  It is
  `DotMNF.dot_safety_platform` at the compiled derivation.
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
`c`, except in `compile_faithful`, which reads `h` to name where `a` and `c`
come from.  The other premises select what a theorem speaks of: a run, a
variable, a capability.  None is a hypothesis about the compiler.
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

/-- **The compiled term is the typer's answer on the resolved program, with its
skeleton.**  `a` is what `resolveTop` makes of `e`.  `synthTop?` answers on `a`
with the term, use set and type of the record.  The elaborated term has the
skeleton of `a`.  So it differs from `a` only where `ATm.skel` forgets: types
and capture sets, boxes `□ x` and unboxings `C ⊸ x`, ascriptions, and a `let`
whose bound term has a variable as its skeleton, which the skeleton inlines.
An application, a projection, a lambda, an object literal with its members and
any other `let` stay. -/
theorem compile_faithful (h : compile b Λ π e = some ⟨a, c⟩) :
    resolveTop Λ π e = some a ∧
      (∃ r : Elab (platformCtx π.plat), synthTop? b π a = some r ∧
        r.tm = c.tm ∧ r.uses = c.uses ∧ r.ty = c.ty) ∧
      ATm.skel c.tm = ATm.skel a := by
  unfold compile at h
  split at h
  · cases h
  · rename_i a' ha'
    split at h
    · cases h
    · rename_i r hr
      split at h
      · rename_i hs
        cases h
        exact ⟨ha', ⟨r, hr, rfl, rfl, rfl⟩, hs⟩
      · cases h

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

end CapturesFrontend
