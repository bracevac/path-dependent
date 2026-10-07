import Coercions.Captures.Frontend.Typer
import Coercions.Captures.Frontend.Step
import Coercions.Captures.DotToFCdot.Prediction
import Coercions.Captures.FCdot.CheckerCompleteness

/-!
# The pipeline

One function takes a surface program through the whole front end.  Eleven
theorems say what the result is worth.  Each one composes results of the
version.  The front end proves nothing about the calculus.

## The function

`compile` resolves a program over a platform, types it at the platform's
context and checks that the typer kept the program's skeleton.  A platform is
a prefix of capture binders, one per capability the program may use.  The
typer elaborates: box inference may insert `□ x` and `C ⊸ x`, and a few of
those are bound by a new `let`.  So the typed term is not the resolved one.
`Compiled` holds the elaborated term, its use set, its type, the derivation
about its erasure, and the proof that its skeleton is the skeleton of the
resolved term.  `ATm.skel` forgets annotations, capture sets, boxes,
unboxings and ascriptions, and inlines a `let` of a variable.  So a check on
skeletons says that the elaborated program is the written one up to what box
inference adds.

The derivation is a field.  A caller holds the typing, not an answer.  The
typer types under `platformCtx`, the front end's copy of the version's
`Platform.ctx`.  The two are equal by `platformCtx_eq`, and `compile` moves
the derivation across that equation, so every statement below names the
version's context.

`compileAndRun` follows `compile` with the executable source machine of
`Step.lean`, from the platform's initial store, at a step budget.

## The theorems

Throughout, `h : compile b Λ π e = some ⟨a, c⟩` is the successful compile.
The platform is `π.plat` and the compiled term is `c.tm.erase`.

* `compile_checks`.  The target checker accepts the translation of the
  derivation.  `FCdot.checkTm_complete` at `HasTy.translate_typed` and
  `Platform.ctx_wf`.
* `compile_uses_checks`.  The target checker accepts the use set evidence
  the translation emits.  `FCdot.checkCap_complete` at `HasTy.translate_uses`.
* `compile_erase`.  The translation erases to the compiled term.
  `HasTy.translate_erase`.
* `compile_faithful`.  The elaborated term has the skeleton of the resolved
  term.  It is the `skel` field.
* `compile_safe`.  Every state a run of the compiled term reaches is final or
  has a step.  `DotMNF.dot_safety` is stated at the empty context only, so
  this is composed at the platform from the pieces it is built from:
  `Platform.simulatedRun`, `FCdot.State.Typed.steps`,
  `Platform.initial_typed` and `Simulated.progress`.
* `compile_not_stuck`.  No reachable state is stuck.  From `compile_safe`.
* `compile_run_progress`.  The state the driver `run` returns is final or the
  executable machine finds a step from it.  From `compile_safe`, `run_steps`
  and `step?_eq_none_iff`.
* `compile_capture_prediction`.  Along any run, the matched target state uses
  no more than the translation of the use set the typer found.
  `DotMNF.dot_capture_prediction`.
* `compile_effect_safety`.  A platform capability `κ` that is not in the use
  set the typer found is never the root of a variable a run reads.
  `DotMNF.dot_effect_safety`, with `cvar_mem_translate` to state the premise
  on the source set, where it is decided.
* `compile_checks_get` and `compile_effect_safety_get`.  The same, stated for
  a program whose compile succeeds by a decided test.  For a concrete
  program the kernel reduces the compile, so `(compile b Λ π e).isSome = true`
  and the premise on the use set both close by `decide +kernel`.

The premise `h` is written in every statement because it is what a caller
holds.  The content rides on the type of `c`.  The other premises select
what a theorem speaks of: a run `r`, a read variable `hin`, a capability
`κ` with `hκ`.  None of them is a hypothesis about the compiler.

Everything here lives in `namespace CapturesFrontend`.  No definition is
placed in a namespace of the version, and no file of the version is touched.
-/

namespace CapturesFrontend

open Captures
open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (CapAtom CaptureSet Ty Tm Ctx HasTy State Step Steps Platform)

/-! ## The platform context -/

/-- The front end's platform context is the version's. -/
theorem platformCtx_eq {s : Sig} (P : Platform s) : platformCtx P = P.ctx := by
  induction P with
  | nil => rfl
  | cons P ih =>
      rw [platformCtx, ih]
      rfl

/-! ## The result of a compilation -/

/-- A program typed over a platform.  The elaborated term, its use set and
type, the derivation about its erasure under the platform's context, and the
proof that the elaborated term is the resolved term `a` up to what box
inference adds. -/
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

/-! ## The pipeline -/

/-- The front end end to end: resolve over the platform, type at the
platform's context, and keep the result when the skeleton is the program's.
`none` is returned when the program is out of scope, out of the label table,
out of the typer's reach, or elaborated to another skeleton.  A failure
carries no reason.  The result is a dependent pair, since the record speaks
of the resolved term. -/
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

/-- The front end followed by the source machine of `Step.lean`, from the
platform's initial store, at a step budget `m`. -/
def compileAndRun (b : Budget) (m : Nat) (Λ : LabelTable) (π : PlatformNames) (e : STm) :
    Option ((s : Sig) × State s) :=
  (compile b Λ π e).map fun r => run m π.sig ⟨π.plat.store, .nil, r.2.tm.erase⟩

/-! ## A source reading of the effect premise -/

/-- A capability is in the translation of a set only if it is in the set.
`CaptureSet.translate` keeps the variables and capabilities of a set, maps
a selection to its own atom and drops `any`, so no capability appears that
was not there. -/
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

/-! ## The theorems -/

-- The premise `h` is read by no proof.  It is written because it is what a
-- caller holds.  The content rides on the type of `c`.
set_option linter.unusedVariables false

section
variable {b : Budget} {Λ : LabelTable} {π : PlatformNames} {e : STm} {a : ATm π.sig}
  {c : Compiled π.plat a}

/-- **The target checker accepts the translation.**  `FCdot.checkTm_complete`
at the typedness of the translation under the platform's context. -/
theorem compile_checks (h : compile b Λ π e = some ⟨a, c⟩) :
    FCdot.checkTm π.plat.ctx.translate c.deriv.translate c.ty.translate = true :=
  FCdot.checkTm_complete (c.deriv.translate_typed (Platform.ctx_wf π.plat))

/-- **The target checker accepts the use set evidence.**  The translation
emits evidence that the target term uses no more than the translated use set.
`FCdot.checkCap_complete` at `HasTy.translate_uses`. -/
theorem compile_uses_checks (h : compile b Λ π e = some ⟨a, c⟩) :
    FCdot.checkCap π.plat.ctx.translate c.deriv.translateUses c.deriv.translate.uses
      c.uses.translate = true :=
  FCdot.checkCap_complete (c.deriv.translate_uses (Platform.ctx_wf π.plat))

/-- **The translation erases to the compiled term.**  `HasTy.translate_erase`. -/
theorem compile_erase (h : compile b Λ π e = some ⟨a, c⟩) :
    FCdot.Tm.erase c.deriv.translate = Tm.erase c.tm.erase :=
  DotMNF.HasTy.translate_erase c.deriv

/-- **The compiled term is the written one up to box inference.**  The
elaborated term has the skeleton of the resolved term. -/
theorem compile_faithful (h : compile b Λ π e = some ⟨a, c⟩) : ATm.skel c.tm = ATm.skel a :=
  c.skel

/-- **Safety of the compiled program over its platform.**  The subject is a run
`r` from the platform's initial store.  Every state it reaches is final or
has a step.  The matched target run of `Platform.simulatedRun` stays typed by
`FCdot.State.Typed.steps`, and `Simulated.progress` reads progress back. -/
theorem compile_safe (h : compile b Λ π e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st) :
    State.Final st ∨ ∃ (s' : Sig) (st' : State s'), Step st st' := by
  obtain ⟨stt, hrun, he, -⟩ := π.plat.simulatedRun c.deriv r
  obtain ⟨U, hU⟩ := FCdot.State.Typed.steps ⟨_, π.plat.initial_typed c.deriv⟩ hrun
  exact DotMNF.Simulated.progress ⟨stt, U, hU, he⟩

/-- **No reachable state of the compiled program is stuck.**  The subject is a
run `r` from the platform's initial store. -/
theorem compile_not_stuck (h : compile b Λ π e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st) : ¬ State.Stuck st := by
  intro ⟨hnf, hns⟩
  rcases compile_safe h r with hf | hs
  · exact hnf hf
  · exact hns hs

/-- **The driver never answers at a stuck state.**  At every step budget the
state `run` returns is final or the executable machine finds a step.
`compile_safe` at the reached state, with `run_steps` for the run and
`step?_eq_none_iff` for the executable half. -/
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

/-- **Capture prediction of the compiled program.**  The subject is a run `r`
from the platform's initial store.  A typed target state with the same
erasure exists, its store extends the platform's along a renaming `ρ`, and
its use set is below the translation of the use set the typer found, renamed
by `ρ`.  `DotMNF.dot_capture_prediction`. -/
theorem compile_capture_prediction (h : compile b Λ π e = some ⟨a, c⟩) {s : Sig}
    {st : State s} (r : Steps (⟨π.plat.store, .nil, c.tm.erase⟩ : State π.sig) st) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename π.sig s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext π.plat.targetStore stt.σ ρ ∧
          FCdot.CapLe Γ' stt.uses (c.uses.translate.rename ρ) :=
  DotMNF.dot_capture_prediction π.plat c.deriv r

/-- **Effect safety of the compiled program.**  The subjects are a platform
capability `κ`, selected by `hκ` as one the use set the typer found does not
hold, a run `r` from the platform's initial store, and a variable `x` the
reached state reads.  Then `κ` is not a root of `x` in the matched target
state.  `DotMNF.dot_effect_safety`, whose premise on the translated set
follows from `hκ` by `cvar_mem_translate` and `CaptureSet.elem_iff`. -/
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

/-! ## The theorems at a decided compile

A concrete program is compiled by the kernel, so its success is a decided
test and needs no hypothesis.  These two forms take that test and speak of
the record the compile returns. -/

section
variable {b : Budget} {Λ : LabelTable} {π : PlatformNames} {e : STm}

/-- **The target checker accepts the translation of a program that compiles.**
`compile_checks` at the record `compile` returns.  For a concrete program the
premise closes by `decide +kernel`. -/
theorem compile_checks_get (h : (compile b Λ π e).isSome = true) :
    FCdot.checkTm π.plat.ctx.translate ((compile b Λ π e).get h).2.deriv.translate
      ((compile b Λ π e).get h).2.ty.translate = true :=
  compile_checks (Option.some_get h).symm

/-- **Effect safety of a program that compiles.**  `compile_effect_safety` at
the record `compile` returns.  The subjects are as there: a capability `κ`
that `hκ` selects as absent from the use set the typer found, a run `r` and a
read variable `x`.  For a concrete program both `h` and `hκ` close by
`decide +kernel`. -/
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
