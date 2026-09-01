import Coercions.Translation.ManySorted.Classifiers.SourceErasure
import Coercions.ManySortedFC.Syntax

/-!
# Direct lowering of `.only` and `.except`

Every nonempty surface chain becomes one `ManySortedFC.Capture.project` node.
The base capture is translated once, and the closed kind algebra computes the
single filter carried by that node.  No administrative term, kind variable,
or runtime operation is introduced.
-/

namespace DOTCaptureToManySortedFC.Classifiers.Lowering

namespace Source

export DOTCaptureToManySortedFC.Classifiers.Source
  (Classifier Kind Filter ProjectedCapture Term Program)

end Source

/-- Lower a source capture chain using the caller's translation for its
unfiltered base.  A plain capture remains plain; every actual filter chain is
collapsed to exactly one target projection. -/
def capture {Base : Type} {targetScope : ManySortedFC.Sig}
    (translateBase : Base -> ManySortedFC.Capture targetScope) :
    Source.ProjectedCapture Base -> ManySortedFC.Capture targetScope
  | .base source => translateBase source
  | projected@(.only preceding _) =>
      .project (translateBase preceding.root) projected.kind
  | projected@(.except preceding _) =>
      .project (translateBase preceding.root) projected.kind

@[simp]
theorem capture_base {Base : Type} {targetScope : ManySortedFC.Sig}
    (translateBase : Base -> ManySortedFC.Capture targetScope)
    (source : Base) :
    capture translateBase (.base source) = translateBase source := rfl

@[simp]
theorem capture_only {Base : Type} {targetScope : ManySortedFC.Sig}
    (translateBase : Base -> ManySortedFC.Capture targetScope)
    (preceding : Source.ProjectedCapture Base)
    (classifier : Source.Classifier) :
    capture translateBase (preceding.only classifier) =
      .project (translateBase preceding.root)
        (ManySortedFC.Classifier.Kind.intersect preceding.kind
          (ManySortedFC.Classifier.Kind.classifier classifier)) := by
  simp [capture]

@[simp]
theorem capture_except {Base : Type} {targetScope : ManySortedFC.Sig}
    (translateBase : Base -> ManySortedFC.Capture targetScope)
    (preceding : Source.ProjectedCapture Base)
    (classifier : Source.Classifier) :
    capture translateBase (preceding.except classifier) =
      .project (translateBase preceding.root)
        (ManySortedFC.Classifier.Kind.subtract preceding.kind
          (ManySortedFC.Classifier.Kind.classifier classifier)) := by
  simp [capture]

end DOTCaptureToManySortedFC.Classifiers.Lowering
