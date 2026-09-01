import Coercions.ManySortedFC.BindableClassifierExamples
import Coercions.ManySortedFC.Consistency
import Coercions.ManySortedFC.SeparationConsistency

/-!
# Semantic regressions for bindable classifiers

One classifier symbol is interpreted as the closed kind `onlyIO`.  The
Boolean valuation observes one classifier-tree node, while the access
valuation observes one concrete capability.  Both validate the same scoped
projection and classifier-exclusion facts without identifying the two
semantic models.
-/

namespace ManySortedFC.BindableClassifierSemanticsExamples

open BindableClassifierExamples

/-- One bindable classifier followed by one term capability. -/
abbrev Scope : Sig := ([] ▹ .symbol .classifier) ▹ .term

def boundClassifier : ClassifierExpr Scope :=
  .var (.there .here)

def capability : Capture Scope :=
  .singleton .here

def projected : Capture Scope :=
  .project capability boundClassifier

/-! ## Boolean observation -/

def boolAtIO : BoolValuation Scope where
  term := fun
    | .here => true
    | .there older => nomatch older
  typeSymbol := fun
    | .there (.there older) => nomatch older
  captureSymbol := fun
    | .there (.there older) => nomatch older
  classifierSymbol := fun
    | .there .here => onlyIO
    | .there (.there older) => nomatch older
  classifier := io

def boolAtControl : BoolValuation Scope :=
  { boolAtIO with classifier := control }

theorem bool_classifier_inclusion :
    BoolSemantics.LE (boundClassifier.eval boolAtIO)
      ((ClassifierExpr.ground onlyShared).eval boolAtIO) := by
  intro _
  native_decide

theorem bool_classifier_disjoint :
    ClassifierExpr.DisjointAt boolAtIO boundClassifier
      (.ground onlyControl) := by
  change Classifier.Kind.Contains onlyIO io ->
    Classifier.Kind.Contains onlyControl io -> False
  exact io_is_not_control.not_both

theorem bool_capture_has_kind :
    (Proposition.captureHasKind capability boundClassifier).Holds boolAtIO := by
  change BoolSemantics.LE (capability.eval boolAtIO)
    (boundClassifier.eval boolAtIO)
  intro _
  native_decide

theorem bool_projected_at_io :
    projected.eval boolAtIO = true := by
  native_decide

/-- The same present capability is filtered out when the observation moves to
`Control`, which does not belong to the bound `onlyIO` kind. -/
theorem bool_projected_at_control :
    projected.eval boolAtControl = false := by
  native_decide

theorem bool_classifier_exclude_sound :
    BoolSemantics.LE (boundClassifier.eval boolAtIO)
      ((ClassifierExpr.ground sharedWithoutControl).eval boolAtIO) :=
  ClassifierExpr.eval_exclude bool_classifier_inclusion
    bool_classifier_disjoint

/-! ## Access observation -/

def accessAtIO : AccessValuation Scope Unit where
  term := fun
    | .here => fun _ => .writable
    | .there older => nomatch older
  captureSymbol := fun
    | .there (.there older) => nomatch older
  classifierSymbol := fun
    | .there .here => onlyIO
    | .there (.there older) => nomatch older
  classOf := fun _ => io

theorem access_classifier_inclusion :
    SeparationSemantics.Subclassifier accessAtIO boundClassifier
      (.ground onlyShared) := by
  exact io_is_shared

theorem access_classifier_disjoint :
    SeparationSemantics.ClassifierDisjoint accessAtIO boundClassifier
      (.ground onlyControl) := by
  exact io_is_not_control

theorem access_capture_has_kind :
    SeparationSemantics.HasClassifier accessAtIO capability
      boundClassifier := by
  intro observed _
  cases observed
  exact Classifier.Kind.Contains.classifier (Classifier.le_refl io)

theorem access_projected_at_io :
    projected.access accessAtIO () = .writable := by
  native_decide

theorem access_classifier_exclude_sound :
    SeparationSemantics.Subclassifier accessAtIO boundClassifier
      (.ground sharedWithoutControl) :=
  SeparationSemantics.subclassifier_exclude access_classifier_inclusion
    access_classifier_disjoint

/-- The larger `onlyShared` kind overlaps `onlyControl`; the semantic
disjointness relation therefore rejects that pair. -/
theorem shared_and_control_are_not_disjoint :
    ¬ SeparationSemantics.ClassifierDisjoint accessAtIO
      (.ground onlyShared) (.ground onlyControl) := by
  intro disjoint
  exact disjoint.not_both
    (Classifier.Kind.Contains.classifier
      (Classifier.Subclass.child .refl))
    (Classifier.Kind.Contains.classifier (Classifier.le_refl control))

end ManySortedFC.BindableClassifierSemanticsExamples
