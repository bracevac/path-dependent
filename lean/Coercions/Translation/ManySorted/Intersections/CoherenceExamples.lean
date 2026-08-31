import Coercions.DOT.Captures.Intersections.SourceExamples
import Coercions.Translation.ManySorted.Intersections.Coherence

/-!
# Association-coherence regression

The two source trees differ only in intersection association. Their complete
names-first target preparation is literally identical.
-/

namespace DOTCaptureToManySortedFC.Intersections.CoherenceExamples

open DOTCaptureToManySortedFC.Intersections.Preparation

namespace SourceExamples

export DOTCapture.Intersections.Source.Examples
  (leftAssociated rightAssociated association_variants_collect_identically)

end SourceExamples

theorem associated_intersections_prepare_identically :
    collectAndPrepare (emptyLayout []) SourceExamples.leftAssociated =
      collectAndPrepare (emptyLayout []) SourceExamples.rightAssociated :=
  collectAndPrepare_eq_of_collect_eq (emptyLayout [])
    SourceExamples.leftAssociated SourceExamples.rightAssociated
    SourceExamples.association_variants_collect_identically

theorem associated_intersections_allocate_identical_signature
    {leftPrepared rightPrepared : Encoding.PreparedSignature []}
    (leftSuccess :
      collectAndPrepare (emptyLayout []) SourceExamples.leftAssociated =
        .ok leftPrepared)
    (rightSuccess :
      collectAndPrepare (emptyLayout []) SourceExamples.rightAssociated =
        .ok rightPrepared) :
    leftPrepared = rightPrepared :=
  prepared_eq_of_collect_eq (emptyLayout [])
    SourceExamples.leftAssociated SourceExamples.rightAssociated
    SourceExamples.association_variants_collect_identically leftSuccess
    rightSuccess

end DOTCaptureToManySortedFC.Intersections.CoherenceExamples
