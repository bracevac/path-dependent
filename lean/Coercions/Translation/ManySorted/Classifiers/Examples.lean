import Coercions.Translation.ManySorted.Classifiers.Lowering
import Coercions.ManySortedFC.SeparationConsistency

/-!
# Classifier-filter regressions

The first group mirrors the paper artifact's ground-kind `.only`/`.except`
examples. The final group interprets a capture with two concrete capabilities:
an IO capability survives `only[Shared].except[Control]`, while a Control
capability does not. Checked capture-kinding and term-level regressions live in
`CaptureKindingExamples`.
-/

namespace DOTCaptureToManySortedFC.Classifiers.Examples

namespace Source

export DOTCaptureToManySortedFC.Classifiers.Source
  (Classifier Kind Filter ProjectedCapture Term Program)

end Source

/-! ## A closed classifier hierarchy used by the paper-derived checks -/

def shared : Source.Classifier := .child 0 .top
def control : Source.Classifier := .child 0 shared
def io : Source.Classifier := .child 1 shared
def net : Source.Classifier := .child 0 io
def unscoped : Source.Classifier := .child 1 .top

def openA : Source.Classifier := .child 2 .top
def knownB : Source.Classifier := .child 0 openA

abbrev BaseCapture := Nat

def any : Source.ProjectedCapture BaseCapture := .base 0

def sharedWithoutControl : Source.ProjectedCapture BaseCapture :=
  (any.only shared).except control

def sharedWithoutControlAndIo : Source.ProjectedCapture BaseCapture :=
  ((any.only shared).except control).except io

def withoutControlAndIo : Source.ProjectedCapture BaseCapture :=
  (any.except control).except io

def withoutIoAndControl : Source.ProjectedCapture BaseCapture :=
  (any.except io).except control

def withoutIoAndNet : Source.ProjectedCapture BaseCapture :=
  (any.except io).except net

def onlyIo : Source.ProjectedCapture BaseCapture :=
  any.only io

def onlyOpenAButNotB : Source.ProjectedCapture BaseCapture :=
  (any.only openA).except knownB

/-- A sibling declared after the filter that excluded `knownB`. -/
def laterD : Source.Classifier := .child 1 openA

example : sharedWithoutControl.filters =
    [.only shared, .except control] := rfl

example : withoutControlAndIo.filters =
    [.except control, .except io] := rfl

example : sharedWithoutControl.kind =
    ManySortedFC.Classifier.Kind.subtract
      (ManySortedFC.Classifier.Kind.intersect
        ManySortedFC.Classifier.Kind.top
        (ManySortedFC.Classifier.Kind.classifier shared))
      (ManySortedFC.Classifier.Kind.classifier control) := by
  simp [sharedWithoutControl, any]

/-! ## Paper-derived semantic checks

These are closed decidable propositions over the classifier algebra.  The
positive checks follow `effect-exclusion-basics.scala`,
`kinds-multi-exclusion.scala`, and the two open-world modules.  The negative
checks follow the rejected reverse-subsumption examples from the artifact.
-/

/-- Each extra exclusion shrinks the allowed classifier kind. -/
example : ManySortedFC.Classifier.Kind.Subkind
    sharedWithoutControlAndIo.kind sharedWithoutControl.kind := by
  native_decide

example : ManySortedFC.Classifier.Kind.Subkind
    withoutControlAndIo.kind (any.except control).kind := by
  native_decide

example : ManySortedFC.Classifier.Kind.Subkind
    withoutControlAndIo.kind (any.except io).kind := by
  native_decide

example : ManySortedFC.Classifier.Kind.Subkind
    withoutControlAndIo.kind any.kind := by
  native_decide

/-- Exclusion order changes the executable representation, if at all, but not
the denoted kind. -/
example : ManySortedFC.Classifier.Kind.Equivalent
    withoutControlAndIo.kind withoutIoAndControl.kind := by
  native_decide

/-- Removing `io` already removes its descendant `net`. -/
example : ManySortedFC.Classifier.Kind.Equivalent
    withoutIoAndNet.kind (any.except io).kind := by
  native_decide

/-- A classifier on another root branch survives both exclusions. -/
example : ManySortedFC.Classifier.Kind.Contains
    withoutControlAndIo.kind unscoped := by
  native_decide

/-- `only Shared; except Control` removes the named child while retaining its
sibling from the same parent classifier. -/
example : ManySortedFC.Classifier.Kind.Contains
    sharedWithoutControl.kind io := by
  native_decide

example : ¬ ManySortedFC.Classifier.Kind.Contains
    sharedWithoutControl.kind control := by
  native_decide

/-- A later sibling under `openA` remains admitted without recompiling the
kind that excluded the previously known `knownB` subtree. -/
example : ManySortedFC.Classifier.Kind.Contains
    onlyOpenAButNotB.kind laterD := by
  native_decide

example : ¬ ManySortedFC.Classifier.Kind.Contains
    onlyOpenAButNotB.kind knownB := by
  native_decide

/-- Reverse monotonicity is rejected: dropping an exclusion grows the kind. -/
example : ¬ ManySortedFC.Classifier.Kind.Subkind
    (any.except control).kind withoutControlAndIo.kind := by
  native_decide

example : ¬ ManySortedFC.Classifier.Kind.Subkind
    any.kind withoutControlAndIo.kind := by
  native_decide

example : ¬ ManySortedFC.Classifier.Kind.Subkind
    any.kind (any.except io).kind := by
  native_decide

/-- The part explicitly removed by the second exclusion cannot flow into the
double-excluded view. -/
example : ¬ ManySortedFC.Classifier.Kind.Subkind
    onlyIo.kind withoutControlAndIo.kind := by
  native_decide

/-- Excluding only the descendant `net` is not strong enough to establish the
view that excludes all of `io`. -/
example : ¬ ManySortedFC.Classifier.Kind.Subkind
    (any.except net).kind (any.except io).kind := by
  native_decide

/-- Exclusions of sibling branches do not subsume one another. -/
example : ¬ ManySortedFC.Classifier.Kind.Subkind
    (any.except control).kind (any.except io).kind := by
  native_decide

example : ¬ ManySortedFC.Classifier.Kind.Subkind
    (any.except io).kind (any.except control).kind := by
  native_decide

/-! ## A nonempty concrete projection

The logical checks above concern the closed kind algebra.  This valuation
also gives the filter an actual capture to operate on: `file` is classified
under `IO`, while `thrower` is classified under `Control`.
-/

inductive ConcreteCapability where
  | file
  | thrower
deriving DecidableEq

abbrev ConcreteScope : ManySortedFC.Sig :=
  ([] : ManySortedFC.Sig) ▹ .term ▹ .term

/-- The older term variable denotes `file`; the newer one denotes `thrower`.
Both are genuinely present and writable in this semantic instance. -/
def concreteValuation :
    ManySortedFC.AccessValuation ConcreteScope ConcreteCapability where
  term := fun
    | .here => fun capability =>
        if capability = .thrower then .writable else .absent
    | .there .here => fun capability =>
        if capability = .file then .writable else .absent
    | .there (.there older) => nomatch older
  captureSymbol := fun
    | .there (.there older) => nomatch older
  classOf := fun
    | .file => io
    | .thrower => control

def concreteAll : ManySortedFC.Capture ConcreteScope :=
  .union (.singleton (.there .here)) (.singleton .here)

def concreteFiltered : ManySortedFC.Capture ConcreteScope :=
  .project concreteAll sharedWithoutControl.kind

theorem concrete_all_contains_file :
    concreteAll.access concreteValuation .file = .writable := by
  native_decide

theorem concrete_all_contains_thrower :
    concreteAll.access concreteValuation .thrower = .writable := by
  native_decide

/-- `only[Shared].except[Control]` retains the IO capability. -/
theorem concrete_filter_retains_file :
    concreteFiltered.access concreteValuation .file = .writable := by
  native_decide

/-- The same filter removes the Control capability. -/
theorem concrete_filter_removes_thrower :
    concreteFiltered.access concreteValuation .thrower = .absent := by
  native_decide

theorem concrete_filter_is_not_empty :
    ¬ ManySortedFC.SeparationSemantics.Equivalent concreteValuation
      concreteFiltered .empty := by
  intro equivalent
  have atFile := equivalent .file
  rw [concrete_filter_retains_file] at atFile
  simp only [ManySortedFC.Capture.access] at atFile
  cases atFile

theorem concrete_filter_is_not_all :
    ¬ ManySortedFC.SeparationSemantics.Equivalent concreteValuation
      concreteFiltered concreteAll := by
  intro equivalent
  have atThrower := equivalent .thrower
  rw [concrete_filter_removes_thrower,
    concrete_all_contains_thrower] at atThrower
  cases atThrower

end DOTCaptureToManySortedFC.Classifiers.Examples
