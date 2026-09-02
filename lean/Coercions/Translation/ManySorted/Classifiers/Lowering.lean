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

/-- Collapse a surface filter chain through caller-supplied base and
projection constructors.  An unfiltered base is translated directly; every
nonempty `.only`/`.except` chain invokes `project` exactly once with the
chain's root and computed ground kind. -/
def lowerWith {Base Target : Type} (translateBase : Base -> Target)
    (project : Target -> ManySortedFC.Classifier.Kind -> Target) :
    Source.ProjectedCapture Base -> Target
  | .base source => translateBase source
  | projected@(.only preceding _) =>
      project (translateBase preceding.root) projected.kind
  | projected@(.except preceding _) =>
      project (translateBase preceding.root) projected.kind

@[simp]
theorem lowerWith_base {Base Target : Type} (translateBase : Base -> Target)
    (project : Target -> ManySortedFC.Classifier.Kind -> Target)
    (source : Base) :
    lowerWith translateBase project (.base source) = translateBase source :=
  rfl

@[simp]
theorem lowerWith_only {Base Target : Type} (translateBase : Base -> Target)
    (project : Target -> ManySortedFC.Classifier.Kind -> Target)
    (preceding : Source.ProjectedCapture Base)
    (classifier : Source.Classifier) :
    lowerWith translateBase project (preceding.only classifier) =
      project (translateBase preceding.root)
        (ManySortedFC.Classifier.Kind.intersect preceding.kind
          (ManySortedFC.Classifier.Kind.classifier classifier)) := by
  simp [lowerWith]

@[simp]
theorem lowerWith_except {Base Target : Type}
    (translateBase : Base -> Target)
    (project : Target -> ManySortedFC.Classifier.Kind -> Target)
    (preceding : Source.ProjectedCapture Base)
    (classifier : Source.Classifier) :
    lowerWith translateBase project (preceding.except classifier) =
      project (translateBase preceding.root)
        (ManySortedFC.Classifier.Kind.subtract preceding.kind
          (ManySortedFC.Classifier.Kind.classifier classifier)) := by
  simp [lowerWith]

/-- Lower a source capture chain using the caller's translation for its
unfiltered base.  A plain capture remains plain; every actual filter chain is
collapsed to exactly one target projection. -/
def capture {Base : Type} {targetScope : ManySortedFC.Sig}
    (translateBase : Base -> ManySortedFC.Capture targetScope) :
    Source.ProjectedCapture Base -> ManySortedFC.Capture targetScope :=
  lowerWith translateBase fun base kind => .project base kind

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
