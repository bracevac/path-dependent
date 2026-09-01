import Coercions.Translation.ManySorted.Classifiers.Lowering
import Coercions.ManySortedFC.TermChecker
import Coercions.ManySortedFC.Erasure
import Coercions.ManySortedFC.StaticExamples

/-!
# Classifier-filter regressions

The first group mirrors the paper artifact's ground-kind `.only`/`.except`
examples.  Capability-level cases that require kind inference are outside this
closed layer.  The final group places the lowered projection in the checked
capture type of a real ManySortedFC lambda, checks the complete annotated term
with the standalone checker, proves literal agreement with the independent
source erasure, and executes its beta/zeta runtime spine.
-/

namespace DOTCaptureToManySortedFC.Classifiers.Examples

namespace Source

export DOTCaptureToManySortedFC.Classifiers.Source
  (Classifier Kind Filter ProjectedCapture Term Program)

end Source

namespace Target

export ManySortedFC
  (BVar Capture Ctx Evidence EvidenceArgs Sig StaticScope SymbolArgs Theory Tm Ty)

end Target

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

/-! ## One independently checked source/target pair -/

/-- The source program has a genuine beta redex whose argument first performs
a genuine zeta step.  Its advertised capture uses the paper's
`only[Shared].except[Control]` chain. -/
def sourceProgram : Source.Program BaseCapture 0 where
  capture := sharedWithoutControl
  term := .app
    (.lam (.var 0))
    (.let' .unit (.var 0))

abbrev MixedScope : Target.Sig :=
  Target.StaticScope [] [.type, .capture]
    [.equality .type, .equality .capture]

/-- The capture name allocated by `exactMixedTheory`, below its two exported
evidence binders and the type name in the same symbol block. -/
def mixedCapture : Target.Capture MixedScope :=
  .cvar (.there (.there (.there .here)))

/-- This case study maps its one source base to an abstract target capture.
The model later supplied at static application instantiates that name with the
empty capture, but the lambda is checked while the name is still abstract. -/
def abstractBase (_ : BaseCapture) : Target.Capture MixedScope :=
  mixedCapture

/-- The full surface chain has become one target projection node. -/
def projectedClosure : Target.Capture MixedScope :=
  DOTCaptureToManySortedFC.Classifiers.Lowering.capture
    abstractBase sourceProgram.capture

example : projectedClosure =
    .project mixedCapture sourceProgram.capture.kind := rfl

/-- A real target lambda whose checked result type retains `projectedClosure`.
The lambda body is pure, so its declared closure is a safe over-approximation. -/
def projectedIdentity : Target.Tm MixedScope :=
  .lam .one .one projectedClosure (.var .here)
    (.captureEmpty
      (.union projectedClosure.weaken (.singleton .here)))

/-- The capture equality exported by `exactMixedTheory`. -/
def mixedCaptureEqualsEmpty :
    Target.Evidence (.equality .capture) MixedScope :=
  .var (.there .here)

/-- Projection is bounded by its abstract source, and the opened theory fixes
that source to the empty capture.  Both steps are explicit target evidence. -/
def projectedClosureIsEmpty :
    Target.Evidence (.inclusion .capture) MixedScope :=
  .inclusionTrans
    (.captureProjectSource mixedCapture sourceProgram.capture.kind)
    (.equalityToInclusion mixedCaptureEqualsEmpty)

/-- The erased static wrapper is accepted only because the projection is
explicitly discharged to its empty source capture.  This exercises the
projection certificate inside the checked term rather than merely checking a
standalone proposition. -/
def polymorphicIdentity : Target.Tm [] :=
  .slam ManySortedFC.StaticExamples.exactMixedTheory .empty
    projectedIdentity projectedClosureIsEmpty

def instantiatedIdentity : Target.Tm [] :=
  .sapp ManySortedFC.StaticExamples.exactMixedTheory polymorphicIdentity
    ManySortedFC.StaticExamples.exactMixedWitnesses
    ManySortedFC.StaticExamples.exactMixedEvidence

/-- The argument is a computation rather than a value.  Its zeta reduction
precedes the surrounding beta reduction under the shared CBV runtime. -/
def computedUnit : Target.Tm [] :=
  .let' .one .empty .unit (.var .here)
    (.captureEmpty .empty)

def targetProgram : Target.Tm [] :=
  .app instantiatedIdentity computedUnit

theorem target_program_is_independently_accepted :
    (ManySortedFC.Tm.check (.nil : ManySortedFC.Ctx [])
      targetProgram).isSome = true := by
  native_decide

theorem projected_closure_survives_target_synthesis :
    (ManySortedFC.Tm.check (.nil : ManySortedFC.Ctx [])
      instantiatedIdentity).map
        (fun checked => checked.type) =
      some (ManySortedFC.Ty.capturing
        (.project .empty sourceProgram.capture.kind)
        (.arr .one .one)) := by
  native_decide

/-- For this representative checked pair, target erasure agrees literally
with the source erasure defined without reference to target syntax.  This is
an execution regression, not a claim that this file compiles arbitrary source
terms. -/
theorem representative_exact_erasure :
    targetProgram.erase = sourceProgram.erase := rfl

def afterZeta : ManySortedFC.Runtime.Tm 0 :=
  .app (.lam (.var 0)) .unit

theorem runtime_zeta :
    ManySortedFC.Runtime.Step targetProgram.erase afterZeta :=
  .appArgument .lam (.zeta .unit)

theorem runtime_beta :
    ManySortedFC.Runtime.Step afterZeta .unit :=
  .beta .unit

theorem runtime_executes :
    ManySortedFC.Runtime.Steps targetProgram.erase .unit :=
  .tail (.single runtime_zeta) runtime_beta

end DOTCaptureToManySortedFC.Classifiers.Examples
