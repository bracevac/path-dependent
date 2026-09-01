import Coercions.Translation.ManySorted.ModalIntersections.Compiler
import Coercions.Translation.ManySorted.Classifiers.Lowering

/-!
# Checked compilation with bindable classifier kinds

The source object below combines a type member, a capture member, and two
declarations of one classifier member.  Its classifier theory records
`K <= Shared`, `K # Control`, and `C hasKind K`; the second declaration
records the paper-style view `only[Shared].except[Control]` without allocating
another `K`.

The runtime payload is a real callback.  A source `objectLet` opens the package
once, a cross-shape object argument drops the extra type/member occurrence,
and the negative consumer invokes the selected callback.  Static classifier
names, constraints, the theory map, and evidence all erase.
-/

namespace DOTCaptureToManySortedFC.BindableClassifiers.CompilerExamples

open DOTCaptureToManySortedFC.ModalIntersections.Compiler
open DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext

private def success? {alpha : Type} : Except Error alpha -> Option alpha
  | .ok value => some value
  | .error _ => none

namespace Source

open DOTCapture.ModalIntersections

/-! ## Classifier tree and source signature -/

def sharedNode : ManySortedFC.Classifier := .child 0 .top
def controlNode : ManySortedFC.Classifier := .child 0 sharedNode
def ioNode : ManySortedFC.Classifier := .child 1 sharedNode

def shared : ClassifierKind :=
  ManySortedFC.Classifier.Kind.classifier sharedNode

def control : ClassifierKind :=
  ManySortedFC.Classifier.Kind.classifier controlNode

def io : ClassifierKind :=
  ManySortedFC.Classifier.Kind.classifier ioNode

/-- The paper syntax is retained at the source boundary and collapsed before
the cumulative compiler sees the ground kind. -/
def paperFilter :
    DOTCaptureToManySortedFC.Classifiers.Source.ProjectedCapture Unit :=
  ((DOTCaptureToManySortedFC.Classifiers.Source.ProjectedCapture.base ()).only
    sharedNode).except controlNode

def sharedWithoutControl : ClassifierKind :=
  paperFilter.kind

/-- The ground kind after the `only[Shared]` prefix and before exclusion. -/
def paperAllowed : ClassifierKind :=
  ((DOTCaptureToManySortedFC.Classifiers.Source.ProjectedCapture.base ()).only
    sharedNode).kind

def loweredPaperFilter : ManySortedFC.Capture [] :=
  DOTCaptureToManySortedFC.Classifiers.Lowering.capture
    (fun _ => .empty) paperFilter

theorem paper_filter_lowers_to_one_projection :
    loweredPaperFilter =
      .project .empty (.ground sharedWithoutControl) := rfl

theorem ioInShared : ManySortedFC.Classifier.Kind.Subkind io shared := by
  native_decide

theorem ioInPaperAllowed :
    ManySortedFC.Classifier.Kind.Subkind io paperAllowed := by
  native_decide

theorem ioAvoidsControl : ManySortedFC.Classifier.Kind.Disjoint io control := by
  native_decide

theorem ioInSharedWithoutControl :
    ManySortedFC.Classifier.Kind.Subkind io sharedWithoutControl := by
  native_decide

/-- The source derivation that forces the cumulative evidence compiler through
its exclusion case: the two premises are supplied separately rather than as a
precomputed inclusion in the filtered kind. -/
def ioInSharedWithoutControlByExclusion :
    ClassifierIncludes TypingEnv.nil.bindings (.ground io)
      (.ground sharedWithoutControl) :=
  .exclude (.ground ioInPaperAllowed) (.ground ioAvoidsControl)

def typeLabel : Label := 41
def captureLabel : Label := 42
def classifierLabel : Label := 43

def localCapture {scope : Sig} : Capture scope :=
  .ref (.localCaptureMember captureLabel)

def localClassifier {scope : Sig} : ClassifierExpr scope :=
  .ref (.localMember classifierLabel)

/-- Surface `.only` and `.except` operands must already denote closed kinds.
An abstract member remains available to ordinary `Capture.project`, but it
cannot be fed to the ground filter-chain preprocessor. -/
inductive FilterBoundaryError : Type where
  | groundClassifierRequired
deriving DecidableEq

/-- An executable model of the ground-filter source boundary.  This helper is
not a compiler diagnostic: the production `ProjectedCapture` syntax admits
only closed classifier kinds, so a symbolic operand is unrepresentable there.
The actual chain collapse remains `Classifiers.Lowering.lowerWith`. -/
def requireGroundFilter {scope : Sig} :
    ClassifierExpr scope -> Except FilterBoundaryError ClassifierKind
  | .ground kind => .ok kind
  | .ref _ => .error .groundClassifierRequired

/-- At the source boundary, a symbolic `except[K]` operand cannot be reified
as the closed kind required by the production filter syntax. -/
def symbolicExceptAttempt : Except FilterBoundaryError ClassifierKind :=
  requireGroundFilter (localClassifier (scope := []))

theorem symbolic_except_requires_ground_classifier :
    symbolicExceptAttempt = .error .groundClassifierRequired := by
  rfl

/-- Collapse the surface `only[Shared].except[Control]` chain into one actual
source capture projection.  This is the same generic lowering used by the
standalone classifier examples, instantiated at cumulative captured-DOT
syntax. -/
def groundFilteredCapture {scope : Sig} : Capture scope :=
  DOTCaptureToManySortedFC.Classifiers.Lowering.lowerWith
    (fun _ : Unit => localCapture)
    (fun capture kind => .project capture (.ground kind)) paperFilter

theorem ground_filter_is_one_source_projection {scope : Sig} :
    groundFilteredCapture (scope := scope) =
      .project localCapture (.ground paperFilter.kind) :=
  rfl

def callbackCapture {scope : Sig} : Capture scope :=
  .union (.project localCapture localClassifier) groundFilteredCapture

def callbackRepresentation {scope : Sig} : Ty scope :=
  .capturing callbackCapture (.arr .one .one)

/-- The view required by the consumer. -/
def expectedInterface {scope : Sig} : Interface scope :=
  .inter
    (.captureMember captureLabel .empty .empty)
    (.inter
      (.classifierMember classifierLabel (.ground io)
        (.ground sharedWithoutControl))
      (.inter
        (.classifierDisjoint localClassifier (.ground control))
        (.captureHasKind localCapture localClassifier)))

/-- The available object is stronger: it also exports `A = One` and another
upper bound `K <= Shared`.  Both classifier declarations share one label. -/
def availableInterface {scope : Sig} : Interface scope :=
  .inter
    (.typeMember typeLabel .one .one)
    (.inter
      (.classifierMember classifierLabel (.ground io) (.ground shared))
      expectedInterface)

private def collectedEntryCount (interface : Interface []) : Nat :=
  match interface.collect with
  | .ok signature => signature.entries.length
  | .error _ => 0

private def collectedConstraintCount (interface : Interface []) : Nat :=
  match interface.collect with
  | .ok signature => signature.constraints.length
  | .error _ => 0

private def collectedSingleClassifierOccurrences
    (interface : Interface []) : Nat :=
  match interface.collect with
  | .ok { entries := [.classifier _ intervals], .. } => intervals.length
  | _ => 0

private def collectionSucceeds (interface : Interface []) : Bool :=
  match interface.collect with
  | .ok _ => true
  | .error _ => false

theorem repeated_classifier_label_has_one_name_and_two_intervals :
    collectedSingleClassifierOccurrences
      (.inter
        (.classifierMember classifierLabel (.ground io) (.ground shared))
        (.classifierMember classifierLabel (.ground io)
          (.ground sharedWithoutControl))) = 2 := by
  native_decide

theorem two_classifier_labels_remain_distinct :
    collectedEntryCount
      (.inter
        (.classifierMember classifierLabel (.ground io) (.ground shared))
        (.classifierMember (classifierLabel + 1) (.ground io)
          (.ground shared))) = 2 := by
  native_decide

theorem mixed_constraints_are_retained :
    collectedConstraintCount (availableInterface (scope := [])) = 2 := by
  native_decide

theorem type_classifier_label_conflict_is_rejected :
    collectionSucceeds
      (.inter
        (.typeMember classifierLabel .one .one)
        (.classifierMember classifierLabel (.ground io) (.ground shared))) =
      false := by
  native_decide

theorem capture_classifier_label_conflict_is_rejected :
    collectionSucceeds
      (.inter
        (.captureMember classifierLabel .empty .empty)
        (.classifierMember classifierLabel (.ground io) (.ground shared))) =
      false := by
  native_decide

theorem association_does_not_change_normalization :
    (Interface.inter (scope := [])
      (Interface.inter
        (Interface.typeMember typeLabel .one .one)
        (Interface.classifierMember classifierLabel (.ground io)
          (.ground shared)))
      (Interface.captureMember captureLabel .empty .empty)).collect =
    (Interface.inter (scope := [])
      (Interface.typeMember typeLabel .one .one)
      (Interface.inter
        (Interface.classifierMember classifierLabel (.ground io)
          (.ground shared))
        (Interface.captureMember captureLabel .empty .empty))).collect := by
  rfl

def availableObject {scope : Sig} : ObjectType scope :=
  .mk availableInterface callbackRepresentation .empty

def expectedObject {scope : Sig} : ObjectType scope :=
  .mk expectedInterface callbackRepresentation .empty

def model {scope : Sig} : LocalModel.Model scope where
  typeMember := fun _ => .one
  captureMember := fun _ => .empty
  classifierMember := fun _ => .ground io

def realization {scope : Sig} (environment : TypingEnv scope) :
    ObjectType.Realization environment.bindings
      (availableObject (scope := scope)) where
  model := model
  constraints :=
    .inter
      (.typeMember .refl .refl)
      (.inter
        (.classifierMember .refl (.ground ioInShared))
        (.inter
          (.captureMember .refl .refl)
          (.inter
            (.classifierMember .refl (.ground ioInSharedWithoutControl))
            (.inter
              (.classifierDisjoint (.ground ioAvoidsControl))
              (.captureHasKind .empty)))))

/-! ## Cross-shape source view -/

def availableCaptureOccurrence {scope : Sig} :
    (availableInterface (scope := scope)).HasCaptureOccurrence
      captureLabel .empty .empty :=
  .right (.right (.left .here))

def availableFilteredClassifierOccurrence {scope : Sig} :
    (availableInterface (scope := scope)).HasClassifierOccurrence
      classifierLabel (.ground io) (.ground sharedWithoutControl) :=
  .right (.right (.right (.left .here)))

def availableDisjointOccurrence {scope : Sig} :
    (availableInterface (scope := scope)).HasClassifierDisjointOccurrence
      localClassifier (.ground control) :=
  .right (.right (.right (.right (.left .here))))

def availableCaptureKindOccurrence {scope : Sig} :
    (availableInterface (scope := scope)).HasCaptureKindOccurrence
      localCapture localClassifier :=
  .right (.right (.right (.right (.right .here))))

def viewAdaptation {scope : Sig} (context : Ctx scope) :
    ObjectType.Adapts context (availableObject (scope := scope))
      (expectedObject (scope := scope)) where
  mapping := LocalModel.Mapping.identity
  theory :=
    .inter
      (.captureMember
        (by simpa using
          (LocalTheory.Includes.captureLower
            (availableCaptureOccurrence (scope := scope))))
        (by simpa using
          (LocalTheory.Includes.captureUpper
            (availableCaptureOccurrence (scope := scope)))))
      (.inter
        (.classifierMember
          (by simpa using
            (LocalTheory.ClassifierIncludes.lower
              (availableFilteredClassifierOccurrence (scope := scope))))
          (by simpa using
            (LocalTheory.ClassifierIncludes.upper
              (availableFilteredClassifierOccurrence (scope := scope)))))
        (.inter
          (.classifierDisjoint
            (by simpa using
              (LocalTheory.ClassifiersDisjoint.assumption
                (availableDisjointOccurrence (scope := scope)))))
          (.captureHasKind
            (by simpa using
              (LocalTheory.CaptureHasKind.assumption
                (availableCaptureKindOccurrence (scope := scope)))))))
  outerCapture := .refl
  packageCapture := .refl

/-! ## Callback payload and positive object -/

def concreteCallbackCapture {scope : Sig} : Capture scope :=
  .union (.project .empty (.ground io))
    (.project .empty (.ground sharedWithoutControl))

def callback {scope : Sig} : Value scope :=
  .lam .one .one (.ret .unit)

def callbackTyping {scope : Sig} {environment : TypingEnv scope} :
    Value.HasType environment (callback (scope := scope))
      (.capturing concreteCallbackCapture (.arr .one .one)) :=
  .lam (by trivial) (.ret .unit) .captureEmpty

def literal {scope : Sig} : Value scope :=
  .object availableObject callback

def literalTyping {scope : Sig} {environment : TypingEnv scope} :
    Value.HasType environment (literal (scope := scope))
      (availableObject (scope := scope)).formedType :=
  .object (realization environment) callbackTyping .refl .refl
    (.captureUnionElim .captureProjectSource .captureProjectSource)

/-! ## Negative consumer that invokes the selected payload -/

abbrev ConsumerScope (scope : Sig) : Sig := scope ▹ .term

def consumerObject {scope : Sig} : ObjectType (ConsumerScope scope) :=
  (expectedObject (scope := scope)).weaken (kind := .term)

def consumerEnvironment {scope : Sig} (environment : TypingEnv scope) :
    TypingEnv (ConsumerScope scope) :=
  environment.extendTerm (expectedObject (scope := scope)).formedType

def consumerExposure {scope : Sig} (environment : TypingEnv scope) :
    ExposesObject (consumerEnvironment environment).bindings (.var .here)
      (consumerObject (scope := scope)) :=
  .variable rfl

def openedCallbackCapture {scope : Sig} : Capture (ConsumerScope scope) :=
  .union
    (.project
      (.ref (.captureMember (.var .here) captureLabel))
      (.ref (.member (.var .here) classifierLabel)))
    (.project
      (.ref (.captureMember (.var .here) captureLabel))
      (.ground sharedWithoutControl))

def openedCaptureUpper {scope : Sig} (environment : TypingEnv scope) :
    CaptureIncludes (consumerEnvironment environment).bindings
      (.ref (.captureMember (.var .here) captureLabel)) .empty :=
  by
    simpa [Capture.openAt] using
      (Includes.upper (.captureMember (consumerExposure environment)
        (by simpa [consumerObject, expectedObject] using
          (Interface.HasCaptureOccurrence.left
            (Interface.HasCaptureOccurrence.here
              (scope := ConsumerScope scope)
              (label := captureLabel) (lower := .empty) (upper := .empty))))))

def openedCallbackIsEmpty {scope : Sig} (environment : TypingEnv scope) :
    CaptureIncludes (consumerEnvironment environment).bindings
      (openedCallbackCapture (scope := scope)) .empty :=
  .captureUnionElim
    (.trans .captureProjectSource (openedCaptureUpper environment))
    (.trans .captureProjectSource (openedCaptureUpper environment))

def callbackBody {scope : Sig} : Term (ConsumerScope scope) :=
  .app (.select (.var .here) .payload) (.ret .unit)

def callbackBodyRawTyping {scope : Sig} (environment : TypingEnv scope) :
    Term.HasType (consumerEnvironment environment)
      (callbackBody (scope := scope))
      (.union openedCallbackCapture
        (.union openedCallbackCapture .empty)) .one :=
  .app (consumerExposure environment).payload rfl (by trivial) (.ret .unit)

def callbackBodyTyping {scope : Sig} (environment : TypingEnv scope) :
    Term.HasType (consumerEnvironment environment)
      (callbackBody (scope := scope)) .empty .one :=
  .use (callbackBodyRawTyping environment)
    (.captureUnionElim (openedCallbackIsEmpty environment)
      (.captureUnionElim (openedCallbackIsEmpty environment) .captureEmpty))

def consumer {scope : Sig} : Value scope :=
  .objectConsumer expectedObject .one callbackBody

def consumerTyping {scope : Sig} {environment : TypingEnv scope} :
    Value.HasType environment (consumer (scope := scope))
      (.capturing .empty (.objectArrow expectedObject .one)) :=
  .objectConsumer (callbackBodyTyping environment) .captureEmpty

/-! ## One explicit open, one cross-shape argument, one callback invocation -/

abbrev OpenedScope : Sig := [] ▹ .term

def openedEnvironment : TypingEnv OpenedScope :=
  TypingEnv.nil.extendTerm (availableObject (scope := [])).formedType

def openedAvailable : ObjectType OpenedScope :=
  (availableObject (scope := [])).weaken (kind := .term)

def openedExpected : ObjectType OpenedScope :=
  (expectedObject (scope := [])).weaken (kind := .term)

def openedExposure : ExposesObject openedEnvironment.bindings (.var .here)
    openedAvailable :=
  .variable rfl

def openedAdaptation : ObjectType.Adapts openedEnvironment.bindings
    openedAvailable openedExpected := by
  simpa [openedAvailable, openedExpected, availableObject, expectedObject,
    availableInterface, expectedInterface, callbackRepresentation,
    callbackCapture, localCapture, localClassifier, ObjectType.weaken,
    Interface.weaken, Ty.weaken, Capture.weaken, ClassifierExpr.weaken] using
      (viewAdaptation (scope := OpenedScope) openedEnvironment.bindings)

def openedRepresentation : TypeIncludes openedEnvironment.bindings
    (ObjectType.realizedRepresentation openedAvailable
      (LocalModel.atPath (.var .here)))
    (ObjectType.realizedRepresentation openedExpected
      (openedAdaptation.mapping.apply (LocalModel.atPath (.var .here)))) := by
  simp [openedAvailable, openedExpected, openedAdaptation,
    ObjectType.realizedRepresentation]
  exact .refl

def openedExpectedCapture : CaptureIncludes openedEnvironment.bindings
    (ObjectType.realizedRepresentation openedExpected
      (openedAdaptation.mapping.apply (LocalModel.atPath (.var .here)))).outerCapture
    (openedExpected.realizedOuterCapture
      (openedAdaptation.mapping.apply (LocalModel.atPath (.var .here)))) := by
  have availableUpper : CaptureIncludes openedEnvironment.bindings
      (.ref (.captureMember (.var .here) captureLabel)) .empty := by
    simpa [Capture.openAt] using
      (Includes.upper (.captureMember openedExposure
        (by simpa [openedAvailable, availableObject, availableInterface] using
          (availableCaptureOccurrence (scope := OpenedScope)))))
  simpa [openedAvailable, openedExpected, openedAdaptation,
    ObjectType.realizedRepresentation, ObjectType.realizedOuterCapture,
    callbackRepresentation, callbackCapture, localCapture, localClassifier,
    groundFilteredCapture,
    Capture.openAt,
    LocalModel.Mapping.mapCapture_identity,
    LocalModel.Mapping.mapClassifier_identity] using
      (Includes.captureUnionElim
        (Includes.trans
          (Includes.captureProjectSource
            (context := openedEnvironment.bindings)
            (capture := .ref (.captureMember (.var .here) captureLabel))
            (classifier := .ref (.member (.var .here) classifierLabel)))
          availableUpper)
        (Includes.trans
          (Includes.captureProjectSource
            (context := openedEnvironment.bindings)
            (capture := .ref (.captureMember (.var .here) captureLabel))
            (classifier := .ground sharedWithoutControl))
          availableUpper))

def stableArgument : ObjectArgument.HasType openedEnvironment
    (.ret (.var .here)) openedExpected
    (openedAdaptation.mapping.apply (LocalModel.atPath (.var .here))) :=
  .stable rfl openedAdaptation openedRepresentation openedExpectedCapture

def openedApplication : Term OpenedScope :=
  .objectApp openedExpected (.ret consumer) (.ret (.var .here))

def openedApplicationRawTyping : Term.HasType openedEnvironment
    openedApplication (.union .empty .empty) .one := by
  simpa [openedApplication, openedExpected, expectedObject,
    ObjectType.realizedOuterCapture, Capture.seq] using
      (Term.HasType.objectApp
        (resultTemplate := (.one : Ty OpenedScope))
        (.ret (consumerTyping (scope := OpenedScope)
          (environment := openedEnvironment))) rfl stableArgument)

def openedApplicationTyping : Term.HasType openedEnvironment
    openedApplication .empty .one :=
  .use openedApplicationRawTyping
    (.captureUnionElim .captureEmpty .captureEmpty)

def program : Term [] :=
  .objectLet availableObject .one (.ret literal) openedApplication

def programRawTyping : Term.HasType TypingEnv.nil program
    (.union .empty .empty) .one :=
  .objectLet (.ret literalTyping) openedApplicationTyping .captureEmpty

def programTyping : Term.HasType TypingEnv.nil program .empty .one :=
  .use programRawTyping (.captureUnionElim .captureEmpty .captureEmpty)

end Source

/-! ## Structural exclusion evidence elaboration -/

/-- Run the real cumulative source-evidence compiler on an `exclude`
derivation, independently of the direct filtered interval used later by the
larger object example. -/
def exclusionCompiled? :=
  DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration.compileClassifierIncludes?
    Core.nil Source.ioInSharedWithoutControlByExclusion

def exclusionCompiled := exclusionCompiled?.get (by native_decide)

theorem exclusion_compiles_to_target_classifierExclude :
    exclusionCompiled.evidence =
      .classifierExclude (.ground Source.io) Source.paperAllowed Source.control
        (.classifierGroundInclusion Source.io Source.paperAllowed)
        (.classifierGroundDisjoint Source.io Source.control) := by
  native_decide

theorem compiled_exclusion_is_independently_checked :
    (ManySortedFC.Evidence.check Core.nil.target
      exclusionCompiled.evidence).map
        ManySortedFC.Evidence.Checked.proposition =
      some
        (.inclusion (.classifier (.ground Source.io))
          (.classifier (.ground Source.sharedWithoutControl))) := by
  native_decide

def compiled? := success? (compileTerm Context.nil Source.programTyping)

def compiled := compiled?.get (by native_decide)

theorem compiler_succeeds : compiled?.isSome = true := by
  native_decide

theorem standalone_checker_accepts :
    ManySortedFC.Tm.check Core.nil.target compiled.term =
      some compiled.checked :=
  compiled.accepted

theorem exact_erasure :
    compiled.term.erase = Core.nil.eraseTerm Source.program := by
  native_decide

def expectedRuntime : ManySortedFC.Runtime.Tm 0 :=
  .let' (.lam .unit)
    (.app (.lam (.app (.var 0) .unit)) (.var 0))

theorem erasure_is_callback_program :
    compiled.term.erase = expectedRuntime := by
  native_decide

theorem callback_executes :
    ManySortedFC.Runtime.Steps compiled.term.erase .unit := by
  rw [erasure_is_callback_program]
  exact .tail
    (.tail (.single (.zeta .lam)) (.beta .lam))
    (.beta .unit)

end DOTCaptureToManySortedFC.BindableClassifiers.CompilerExamples
