import LambdaPToFCo.Full.RecordFirstValueStaticRegression
import LambdaPToFCo.Full.LetPlanning

/-!
# Second Record let-boundary regression

After the implementation package is opened, the first record value is bound
at its compiled `firstRecord` plan.  This leaf retains that actual resulting
scope as the input for compiling `secondValue`.

The overall result remains the outer `Top` demand.  Its positive and negative
models are transported under the implementation binder explicitly, rather
than replacing the proof-relevant outer demand with a fresh opaque `Top`
model merely because the target plans happen to coincide.
-/

namespace LambdaPToFCo.Full.RecordSecondLetPlanningRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

noncomputable section

abbrev SourceContext :=
  RecordFirstValueStaticRegression.SourceContext

abbrev TargetContext :=
  RecordFirstValueStaticRegression.TargetContext

abbrev BodyScope :=
  RecordFirstValueStaticRegression.BodyScope

/-- The actual scope obtained by opening the compiled first record value. -/
noncomputable def secondBodyScope :=
  LetPlanning.bodyScope BodyScope
    RecordFirstValueStaticRegression.compiled

/-- The adapted package retained exactly the positive model selected by the
certified `firstRecord` result. -/
theorem compiled_model_eq :
    RecordFirstValueStaticRegression.compiled.modeled =
      RecordFirstValueStaticRegression.targetResult.model.producer := by
  rfl

/-- The outer `Top` result, with both polarities retained through the actual
compiled implementation binder. -/
noncomputable def outerResult : WfPlan.Proper SourceContext TargetContext
    BodyScope .Top where
  wf := .top
  plan := RecordImplementationStaticRegression.bodyDemand.plan
  model := .both
    (.underBinding RecordImplementationStaticRegression.compiled.modeled
      RecordImplementationStaticRegression.rootResult.model.producer)
    RecordImplementationStaticRegression.bodyDemand.model.2

/-- Exact demand for the remainder of the program after binding
`RecordRegression.firstValue`. -/
noncomputable def plannedBodyDemand :=
  LetPlanning.bodyDemand BodyScope
    RecordFirstValueStaticRegression.compiled outerResult

end

end LambdaPToFCo.Full.RecordSecondLetPlanningRegression
