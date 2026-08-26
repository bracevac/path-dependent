import LambdaPToFCo.OperationalApplicationStep
import LambdaPToFCo.OperationalImageSafety
import LambdaPToFCo.OperationalRegression

/-!
# Unconditional one-step operational preservation

Every native CK constructor is now covered by a concrete image transition.
The non-application dispatcher handles path normalization, let push,
allocation, and return; the wrapper-aware application lift handles beta
steps through recursively retained function provenance.
-/

namespace LambdaPToFCo
namespace OperationalOneStepPreservation

open OperationalStateImage

/-- Every source CK step preserves the operational image and is simulated by
zero or more target reductions. -/
theorem preservation : OperationalImageSafety.OneStepPreservation := by
  intro sourceSize targetSize source target before step
  cases OperationalNonApplicationStep.StepClass.classify step with
  | application evidence =>
      let lifted := OperationalApplicationStep.ApplicationStep.lift before
        evidence
      exact ⟨lifted.after,
        OperationalImageSafety.ImageStep.ofEvidence before lifted.after step
          lifted.targetSteps⟩
  | nonApplication evidence =>
      let lifted := OperationalNonApplicationStep.NonApplicationStep.lift
        before evidence
      exact ⟨lifted.after,
        OperationalImageSafety.ImageStep.ofEvidence before lifted.after step
          lifted.targetSteps⟩

/-- Closed well-typed programs in the executable fragment cannot reach a
stuck CK state.  No preservation premise remains at this public boundary. -/
theorem source_not_goesWrong
    {term : LambdaPFC.Tm 0} {sourceType : LambdaPFC.Ty 0}
    (typing : Fragment.HasType LambdaPFC.Ctx.nil term sourceType)
    (admissible :
      OperationalAdmissibility.OperationallyAdmissible typing) :
    Not (OperationalSafety.GoesWrong term) :=
  OperationalImageSafety.not_goesWrong typing admissible preservation

/-- The concrete exact-member application regression is covered by the
generic theorem, including its wrapper-aware application transition. -/
theorem regression_not_goesWrong :
    Not (OperationalSafety.GoesWrong OperationalRegression.program) :=
  source_not_goesWrong OperationalRegression.programTyping
    OperationalRegression.programAdmissible

end OperationalOneStepPreservation
end LambdaPToFCo
