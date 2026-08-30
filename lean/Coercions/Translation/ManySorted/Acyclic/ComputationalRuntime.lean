import Coercions.Translation.ManySorted.Acyclic.SourceErasure
import Coercions.DOT.Captures.Acyclic.ComputationalExamples

/-!
# Runtime behavior of the captured-DOT computational examples

The source programs are erased directly to the ordinary untyped runtime.
Opening an object and binding its selected payload are both genuine runtime
lets.  The returned payload can therefore be a function rather than unit,
and the application example performs the expected two zeta steps followed
by beta reduction.
-/

namespace DOTCaptureToManySortedFC.Acyclic.ComputationalRuntime

namespace SourceExamples

export DOTCapture.Acyclic.ComputationalExamples
  (returnSelected returnSelectedTyping applySelected applySelectedTyping)

end SourceExamples

namespace Runtime

export ManySortedFC.Runtime (Tm IsValue Step Steps)

end Runtime

/-! ## Exact closed erasures -/

/-- Erased identity payload `lambda z. z`. -/
def identity : Runtime.Tm 0 :=
  .lam (.var 0)

/-- Runtime state after opening the object in `returnSelected`. -/
def returnSelectedAfterObject : Runtime.Tm 0 :=
  .let' identity (.var 0)

/-- The complete erased `returnSelected` program. -/
def returnSelectedRuntime : Runtime.Tm 0 :=
  .let' identity (.let' (.var 0) (.var 0))

theorem returnSelected_erases_exactly :
    SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        SourceExamples.returnSelected =
      returnSelectedRuntime := by
  rfl

/-- Runtime state after opening the object in `applySelected`. -/
def applySelectedAfterObject : Runtime.Tm 0 :=
  .let' identity (.app (.var 0) .unit)

/-- Runtime state after additionally binding the selected payload. -/
def applySelectedAfterSelection : Runtime.Tm 0 :=
  .app identity .unit

/-- The complete erased `applySelected` program. -/
def applySelectedRuntime : Runtime.Tm 0 :=
  .let' identity
    (.let' (.var 0) (.app (.var 0) .unit))

theorem applySelected_erases_exactly :
    SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
        SourceExamples.applySelected =
      applySelectedRuntime := by
  rfl

/-! ## Exact runtime reductions -/

theorem returnSelected_zeta_object :
    Runtime.Step returnSelectedRuntime returnSelectedAfterObject := by
  exact .zeta .lam

theorem returnSelected_zeta_payload :
    Runtime.Step returnSelectedAfterObject identity := by
  exact .zeta .lam

/-- The closed source program returns its function payload after exactly the
two lets introduced by object opening and payload binding are eliminated. -/
theorem returnSelected_steps_to_identity :
    Runtime.Steps returnSelectedRuntime identity :=
  .tail (.single returnSelected_zeta_object)
    returnSelected_zeta_payload

/-- A small, syntax-directed normal-form predicate for the runtime result. -/
def IsNormal {scope : Nat} (term : Runtime.Tm scope) : Prop :=
  ∀ {next}, ¬ Runtime.Step term next

theorem identity_is_normal : IsNormal identity := by
  intro next step
  cases step

theorem identity_is_not_unit :
    identity ≠ (.unit : Runtime.Tm 0) := by
  intro equality
  cases equality

theorem applySelected_zeta_object :
    Runtime.Step applySelectedRuntime applySelectedAfterObject := by
  exact .zeta .lam

theorem applySelected_zeta_payload :
    Runtime.Step applySelectedAfterObject applySelectedAfterSelection := by
  exact .zeta .lam

theorem applySelected_beta :
    Runtime.Step applySelectedAfterSelection .unit := by
  exact .beta .unit

/-- The closed application exposes two object/payload zeta steps and then
the beta step of the selected identity function. -/
theorem applySelected_steps_to_unit :
    Runtime.Steps applySelectedRuntime .unit :=
  .tail
    (.tail (.single applySelected_zeta_object)
      applySelected_zeta_payload)
    applySelected_beta

end DOTCaptureToManySortedFC.Acyclic.ComputationalRuntime
