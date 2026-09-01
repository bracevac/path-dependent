import Coercions.Translation.ManySorted.Intersections.Metrics
import Coercions.Translation.ManySorted.Intersections.ObjectInterfaceExamples

/-!
# M11 static metrics regressions
-/

namespace DOTCaptureToManySortedFC.Intersections.MetricsExamples

open DOTCaptureToManySortedFC.Intersections
open ObjectInterfaceExamples

/-- Six raw declarations normalize to four shared names.  All six intervals
remain, each contributes two directed constraints, and the object retains one
runtime representation payload. -/
def expectedMultiMemberReport : Metrics.StaticMetrics :=
  { rawDeclarationOccurrences := 6
    normalizedAllocatedNames := 4
    retainedIntervals := 6
    retainedMixedConstraints := 0
    emittedConstraints := 12
    runtimePayloads := 1 }

def multiMemberReport? : Option Metrics.StaticMetrics :=
  (Metrics.prepareObject
    (Preparation.emptyLayout ([] : ManySortedFC.Sig)) multiObject).toOption

theorem multi_member_report_is_exact :
    multiMemberReport? = some expectedMultiMemberReport := by
  native_decide

theorem multi_member_has_four_names_six_occurrences_twelve_constraints_one_payload :
    (multiMemberReport?.map fun report =>
      (report.normalizedAllocatedNames,
        report.rawDeclarationOccurrences,
        report.retainedIntervals,
        report.emittedConstraints,
        report.runtimePayloads)) =
      some (4, 6, 6, 12, 1) := by
  native_decide

theorem multi_member_constraint_formula :
    expectedMultiMemberReport.emittedConstraints =
      2 * expectedMultiMemberReport.retainedIntervals +
        expectedMultiMemberReport.retainedMixedConstraints := by
  decide

end DOTCaptureToManySortedFC.Intersections.MetricsExamples
