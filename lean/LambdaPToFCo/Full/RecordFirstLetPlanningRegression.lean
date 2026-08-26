import LambdaPToFCo.Full.RecordImplementationStaticRegression
import LambdaPToFCo.Full.RecordIntroductionStaticRegression

/-!
# First Record let-boundary regression

The implementation abstraction and the first record-value development were
compiled independently.  This leaf checks that opening the actual compiled
implementation package produces exactly the source/target scope used by the
record constructors.  The equality is definitional: no scope alignment,
renaming, or target-package equality is supplied by a caller.
-/

namespace LambdaPToFCo.Full.RecordFirstLetPlanningRegression

open TranslationInterfaces

/-- The first nested-let body starts in the exact scope obtained by opening
the compiled implementation package. -/
theorem bodyScope_eq :
    RecordImplementationStaticRegression.letBodyScope =
      RecordIntroductionStaticRegression.context1Scope := by
  rfl

/-- Consequently the already-certified first-record plan is available under
the actual implementation binder, without transport through an unrelated
scope model. -/
noncomputable def firstRecordResult :
    WfPlan.Proper RecordIntroductionStaticRegression.Source.context1
      (RecordImplementationStaticRegression.compiled.plan.context
        SystemFCoExt.Ctx.empty)
      RecordImplementationStaticRegression.letBodyScope
      LambdaPFC.RecordRegression.firstRecord := by
  rw [bodyScope_eq]
  exact RecordIntroductionStaticRegression.firstRecordResult

end LambdaPToFCo.Full.RecordFirstLetPlanningRegression
