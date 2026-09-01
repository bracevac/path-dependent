import Coercions.ManySortedFC.Classifier.Basic
import Coercions.ManySortedFC.EvidenceChecker
import Coercions.ManySortedFC.TermChecker

/-!
# Checked classifier-projection examples

These regressions exercise every logical-evidence constructor added for
closed classifier projection.  Each positive certificate is checked by the
executable target checker and is also given its exact declarative endpoint.
The negative cases isolate the four ground side conditions recomputed by the
checker: subkinding, kind equivalence, emptiness, and disjointness.
-/

namespace ManySortedFC.ClassifierProjectionExamples

/-! ## A small open classifier tree -/

/-- A known classifier below the universal root. -/
def classifierA : Classifier := .child 0 .top

/-- One known child of `classifierA`. -/
def classifierB : Classifier := .child 0 classifierA

/-- A distinct child, standing for a sibling that may be added later. -/
def classifierLater : Classifier := .child 1 classifierA

def onlyA : Classifier.Kind := Classifier.Kind.classifier classifierA

def onlyB : Classifier.Kind := Classifier.Kind.classifier classifierB

def onlyLater : Classifier.Kind := Classifier.Kind.classifier classifierLater

def exceptTop : Classifier.Kind :=
  Classifier.Kind.subtract Classifier.Kind.top Classifier.Kind.top

def onlyAExceptB : Classifier.Kind := Classifier.Kind.subtract onlyA onlyB

theorem classifierB_below_classifierA : classifierB ≤ classifierA :=
  .child .refl

theorem classifierLater_below_classifierA :
    classifierLater ≤ classifierA :=
  .child .refl

theorem sibling_classifier_roots_are_disjoint :
    Classifier.Disjoint classifierB classifierLater := by
  native_decide

theorem sibling_kinds_are_disjoint :
    Classifier.Kind.Disjoint onlyB onlyLater :=
  Classifier.Kind.Disjoint.classifiers
    sibling_classifier_roots_are_disjoint

theorem onlyB_is_a_subkind_of_onlyA :
    Classifier.Kind.Subkind onlyB onlyA := by
  apply Classifier.Kind.Subkind.semantics.mpr
  intro item inB
  exact Classifier.Kind.Contains.classifier
    (Classifier.le_trans
      (Classifier.Kind.Contains.classifier_iff.mp inB)
      classifierB_below_classifierA)

theorem except_top_is_empty : Classifier.Kind.IsEmpty exceptTop := by
  apply Classifier.Kind.IsEmpty.of_not_contains
  intro item inDifference
  have difference := Classifier.Kind.Contains.subtract.mp inDifference
  exact difference.2 Classifier.Kind.Contains.top

/-! ## Shared evidence context -/

abbrev TestScope : Sig := [] ▹ .term

/-- The projection laws do not inspect the term binding.  It supplies a
nonempty capture expression so the endpoint tests are not vacuous. -/
def testContext : Ctx TestScope :=
  Ctx.nil.extendTerm .one

def testCapture : Capture TestScope := .singleton .here

/-! ## Kind-equivalent projection -/

def equivalentProjection : Evidence (.equality .capture) TestScope :=
  .equalityCaptureProject
    (.equalityRefl (.capture testCapture))
    (Classifier.Kind.intersect onlyA Classifier.Kind.top) onlyA

def equivalentProjectionEndpoint :
    Proposition (.equality .capture) TestScope :=
  .equality
    (.capture
      (.project testCapture
        (Classifier.Kind.intersect onlyA Classifier.Kind.top)))
    (.capture (.project testCapture onlyA))

def equivalent_projection_is_declaratively_typed :
    Evidence.Proves testContext equivalentProjection
      equivalentProjectionEndpoint :=
  .equalityCaptureProject
    (.equalityRefl (.capture testCapture))
    (Classifier.Kind.Equivalent.intersectTopRight onlyA)

theorem equivalent_projection_is_checked :
    (Evidence.check testContext equivalentProjection).map
        Evidence.Checked.proposition =
      some equivalentProjectionEndpoint := by
  native_decide

/-! ## Projection through top -/

def topIdentity : Evidence (.equality .capture) TestScope :=
  .equalityCaptureProjectTop testCapture

def topIdentityEndpoint : Proposition (.equality .capture) TestScope :=
  .equality (.capture (.project testCapture Classifier.Kind.top))
    (.capture testCapture)

def top_identity_is_declaratively_typed :
    Evidence.Proves testContext topIdentity topIdentityEndpoint :=
  .equalityCaptureProjectTop testCapture

theorem top_identity_is_checked :
    (Evidence.check testContext topIdentity).map
        Evidence.Checked.proposition =
      some topIdentityEndpoint := by
  native_decide

/-! ## Projection through an empty `except top` filter -/

def emptyProjection : Evidence (.equality .capture) TestScope :=
  .equalityCaptureProjectEmpty testCapture exceptTop

def emptyProjectionEndpoint :
    Proposition (.equality .capture) TestScope :=
  .equality (.capture (.project testCapture exceptTop)) (.capture .empty)

def empty_projection_is_declaratively_typed :
    Evidence.Proves testContext emptyProjection emptyProjectionEndpoint :=
  .equalityCaptureProjectEmpty testCapture exceptTop except_top_is_empty

theorem empty_projection_is_checked :
    (Evidence.check testContext emptyProjection).map
        Evidence.Checked.proposition =
      some emptyProjectionEndpoint := by
  native_decide

/-! ## Nested projection composition -/

def nestedComposition : Evidence (.equality .capture) TestScope :=
  .equalityCaptureProjectCompose testCapture onlyA onlyB

def nestedCompositionEndpoint :
    Proposition (.equality .capture) TestScope :=
  .equality
    (.capture (.project (.project testCapture onlyA) onlyB))
    (.capture
      (.project testCapture (Classifier.Kind.intersect onlyB onlyA)))

def nested_composition_is_declaratively_typed :
    Evidence.Proves testContext nestedComposition
      nestedCompositionEndpoint :=
  .equalityCaptureProjectCompose testCapture onlyA onlyB

theorem nested_composition_is_checked :
    (Evidence.check testContext nestedComposition).map
        Evidence.Checked.proposition =
      some nestedCompositionEndpoint := by
  native_decide

/-! ## Projection is bounded by its source -/

def projectToSource : Evidence (.inclusion .capture) TestScope :=
  .captureProjectSource testCapture onlyAExceptB

def projectToSourceEndpoint :
    Proposition (.inclusion .capture) TestScope :=
  .inclusion (.capture (.project testCapture onlyAExceptB))
    (.capture testCapture)

def project_to_source_is_declaratively_typed :
    Evidence.Proves testContext projectToSource projectToSourceEndpoint :=
  .captureProjectSource testCapture onlyAExceptB

theorem project_to_source_is_checked :
    (Evidence.check testContext projectToSource).map
        Evidence.Checked.proposition =
      some projectToSourceEndpoint := by
  native_decide

/-! ## Monotonicity in the capture and classifier kind -/

def subclassMonotonicity : Evidence (.inclusion .capture) TestScope :=
  .captureProjectMono
    (.inclusionRefl (.capture testCapture)) onlyB onlyA

def subclassMonotonicityEndpoint :
    Proposition (.inclusion .capture) TestScope :=
  .inclusion (.capture (.project testCapture onlyB))
    (.capture (.project testCapture onlyA))

def subclass_monotonicity_is_declaratively_typed :
    Evidence.Proves testContext subclassMonotonicity
      subclassMonotonicityEndpoint :=
  .captureProjectMono
    (.inclusionRefl (.capture testCapture)) onlyB_is_a_subkind_of_onlyA

theorem subclass_monotonicity_is_checked :
    (Evidence.check testContext subclassMonotonicity).map
        Evidence.Checked.proposition =
      some subclassMonotonicityEndpoint := by
  native_decide

/-! ## Projection through a kind union -/

def unionMerge : Evidence (.inclusion .capture) TestScope :=
  .captureProjectMerge testCapture onlyB onlyLater

def unionMergeEndpoint : Proposition (.inclusion .capture) TestScope :=
  .inclusion
    (.capture (.project testCapture (onlyB ++ onlyLater)))
    (.capture (.union (.project testCapture onlyB)
      (.project testCapture onlyLater)))

def union_merge_is_declaratively_typed :
    Evidence.Proves testContext unionMerge unionMergeEndpoint :=
  .captureProjectMerge testCapture onlyB onlyLater

theorem union_merge_is_checked :
    (Evidence.check testContext unionMerge).map
        Evidence.Checked.proposition =
      some unionMergeEndpoint := by
  native_decide

/-! ## Sibling projections are disjoint, hence separate -/

def siblingDisjoint : Evidence .disjoint TestScope :=
  .disjointCaptureProject testCapture onlyB testCapture onlyLater

def siblingDisjointEndpoint : Proposition .disjoint TestScope :=
  .disjoint (.project testCapture onlyB)
    (.project testCapture onlyLater)

def sibling_disjoint_is_declaratively_typed :
    Evidence.Proves testContext siblingDisjoint siblingDisjointEndpoint :=
  .disjointCaptureProject testCapture onlyB testCapture onlyLater
    sibling_kinds_are_disjoint

theorem sibling_disjoint_is_checked :
    (Evidence.check testContext siblingDisjoint).map
        Evidence.Checked.proposition =
      some siblingDisjointEndpoint := by
  native_decide

def siblingSeparate : Evidence .separate TestScope :=
  .separateOfDisjoint siblingDisjoint

def siblingSeparateEndpoint : Proposition .separate TestScope :=
  .separate (.project testCapture onlyB)
    (.project testCapture onlyLater)

def disjoint_projection_is_declaratively_separate :
    Evidence.Proves testContext siblingSeparate siblingSeparateEndpoint :=
  .separateOfDisjoint sibling_disjoint_is_declaratively_typed

theorem disjoint_projection_is_checked_as_separate :
    (Evidence.check testContext siblingSeparate).map
        Evidence.Checked.proposition =
      some siblingSeparateEndpoint := by
  native_decide

/-! ## Rejected ground side conditions -/

/-- The parent kind is not a subkind of its known child. -/
def bogusSubkind : Evidence (.inclusion .capture) TestScope :=
  .captureProjectMono
    (.inclusionRefl (.capture testCapture)) onlyA onlyB

theorem bogus_subkind_is_rejected :
    (Evidence.check testContext bogusSubkind).isNone = true := by
  native_decide

/-- A parent subtree and a proper child subtree are not equivalent. -/
def bogusEquivalent : Evidence (.equality .capture) TestScope :=
  .equalityCaptureProject
    (.equalityRefl (.capture testCapture)) onlyA onlyB

theorem bogus_equivalence_is_rejected :
    (Evidence.check testContext bogusEquivalent).isNone = true := by
  native_decide

/-- `only A` contains at least `A`, so it cannot discharge the emptiness
side condition. -/
def bogusEmpty : Evidence (.equality .capture) TestScope :=
  .equalityCaptureProjectEmpty testCapture onlyA

theorem nonempty_kind_as_empty_is_rejected :
    (Evidence.check testContext bogusEmpty).isNone = true := by
  native_decide

/-- A parent kind overlaps its child kind. -/
def bogusDisjoint : Evidence .disjoint TestScope :=
  .disjointCaptureProject testCapture onlyA testCapture onlyB

theorem overlapping_kinds_as_disjoint_are_rejected :
    (Evidence.check testContext bogusDisjoint).isNone = true := by
  native_decide

/-! ## Open-world exclusion -/

theorem later_sibling_is_in_onlyA :
    Classifier.Kind.Contains onlyA classifierLater :=
  Classifier.Kind.Contains.classifier classifierLater_below_classifierA

theorem later_sibling_is_not_in_onlyB :
    ¬ Classifier.Kind.Contains onlyB classifierLater := by
  intro inB
  exact sibling_classifier_roots_are_disjoint.2
    (Classifier.Kind.Contains.classifier_iff.mp inB)

/-- Excluding one known child from `only A` leaves later siblings. -/
theorem later_sibling_survives_known_child_exclusion :
    Classifier.Kind.Contains onlyAExceptB classifierLater :=
  Classifier.Kind.Contains.subtract.mpr
    ⟨later_sibling_is_in_onlyA, later_sibling_is_not_in_onlyB⟩

theorem onlyA_except_known_child_is_not_empty :
    ¬ Classifier.Kind.IsEmpty onlyAExceptB := by
  intro emptyClaim
  exact emptyClaim.not_contains
    later_sibling_survives_known_child_exclusion

def bogusOpenWorldEmpty : Evidence (.equality .capture) TestScope :=
  .equalityCaptureProjectEmpty testCapture onlyAExceptB

theorem open_world_exclusion_is_not_checked_as_empty :
    (Evidence.check testContext bogusOpenWorldEmpty).isNone = true := by
  native_decide

/-! ## Projected captures in checked terms -/

/-- A closed function may advertise a projected capture annotation.  The
body is pure, and the ordinary capture-inclusion certificate discharges that
empty use against the annotated closure plus its argument root. -/
def projectedClosureFunction : Tm [] :=
  .lam .one .one (.project .empty onlyA) .unit
    (.captureEmpty
      (.union (.project .empty onlyA) (.singleton .here)))

theorem projected_capture_term_is_accepted :
    (Tm.check Ctx.nil projectedClosureFunction).isSome = true := by
  native_decide

theorem projected_capture_term_has_expected_type :
    Tm.synth Ctx.nil projectedClosureFunction =
      some (.empty,
        .capturing (.project .empty onlyA) (.arr .one .one)) := by
  native_decide

end ManySortedFC.ClassifierProjectionExamples
