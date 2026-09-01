import Coercions.Translation.ManySorted.ModalIntersections.Compiler

/-!
# Capybara-inspired read-only separation benchmark

This is an access-only compiler benchmark.  It models the static spine of
Capybara's `runParallel` example: two abstract callback captures are required
to be separate, and two read-only views of one stable root satisfy that
requirement.  The shared runtime has no concurrency, allocation, mutation, or
freshness operation, so the benchmark makes none of those claims.
-/

namespace DOTCaptureToManySortedFC.CertificateStudy.ReadOnlyBenchmark

namespace Source

open DOTCapture.ModalIntersections

def unboundedCaptureInterval {scope : Sig} : Interval .capture scope :=
  .bounds .none .none

def abstractCapture {scope : Sig} : Capture (scope ▹ .static .capture) :=
  .ref (.bound .here)

def callbackType {scope : Sig} (capture : Capture scope) : Ty scope :=
  .capturing capture (.arr .one .one)

def firstCaptureAtSecondBinder {scope : Sig} :
    Capture
      (scope ▹ .static .capture ▹ .term ▹ .static .capture) :=
  ((abstractCapture (scope := scope)).weaken (kind := .term)).weaken
    (kind := .static .capture)

def secondCapture {scope : Sig} :
    Capture
      (scope ▹ .static .capture ▹ .term ▹ .static .capture) :=
  abstractCapture

def callbackRequirements {scope : Sig} :
    ModalRequirements 2 []
      (scope ▹ .static .capture ▹ .term ▹ .static .capture) :=
  .mk
    (.cons (.cons .nil firstCaptureAtSecondBinder) secondCapture)
    .nil

def modalResultType {scope : Sig} :
    Ty (scope ▹ .static .capture ▹ .term ▹ .static .capture) :=
  .capturing (.union firstCaptureAtSecondBinder secondCapture)
    (.modal callbackRequirements .one)

/-! The same interface at the type level does not contain the first callback's
term binder.  Weakening this interface below that binder produces the
term-level definitions above. -/

def firstCaptureAtSecondTypeBinder {scope : Sig} :
    Capture (scope ▹ .static .capture ▹ .static .capture) :=
  (abstractCapture (scope := scope)).weaken (kind := .static .capture)

def secondTypeCapture {scope : Sig} :
    Capture (scope ▹ .static .capture ▹ .static .capture) :=
  abstractCapture

def callbackTypeRequirements {scope : Sig} :
    ModalRequirements 2 []
      (scope ▹ .static .capture ▹ .static .capture) :=
  .mk
    (.cons (.cons .nil firstCaptureAtSecondTypeBinder) secondTypeCapture)
    .nil

def callbackModalType {scope : Sig} :
    Ty (scope ▹ .static .capture ▹ .static .capture) :=
  .capturing (.union firstCaptureAtSecondTypeBinder secondTypeCapture)
    (.modal callbackTypeRequirements .one)

def secondStageType {scope : Sig} : Ty (scope ▹ .static .capture) :=
  .capturing .empty
    (.forallI unboundedCaptureInterval
      (.capturing .empty
        (.arr (callbackType secondTypeCapture) callbackModalType)))

abbrev CallbackBodyScope (scope : Sig) : Sig :=
  scope ▹ .static .capture ▹ .term ▹ .static .capture ▹ .term

def firstCallbackVariable {scope : Sig} :
    BVar (CallbackBodyScope scope) .term :=
  .there (.there .here)

def secondCallbackVariable {scope : Sig} :
    BVar (CallbackBodyScope scope) .term :=
  .here

def firstRuntimeCapture {scope : Sig} : Capture (CallbackBodyScope scope) :=
  firstCaptureAtSecondBinder.weaken (kind := .term)

def secondRuntimeCapture {scope : Sig} : Capture (CallbackBodyScope scope) :=
  secondCapture.weaken (kind := .term)

def firstInvocation {scope : Sig} : Term (CallbackBodyScope scope) :=
  .app (.ret (.var firstCallbackVariable)) (.ret .unit)

def secondInvocationAfterLet {scope : Sig} :
    Term (CallbackBodyScope scope ▹ .term) :=
  .app (.ret (.var (.there secondCallbackVariable))) (.ret .unit)

/-- The callbacks run in source order.  The first result is bound and ignored
before the second callback is invoked. -/
def callbackExecution {scope : Sig} : Term (CallbackBodyScope scope) :=
  .let' .one firstInvocation secondInvocationAfterLet

def callbackExecutionTyping {scope : Sig} {environment : TypingEnv scope} :
    Term.HasType
      (((((environment.extendStatic unboundedCaptureInterval).extendTerm
          (callbackType abstractCapture)).extendStatic
            unboundedCaptureInterval).extendTerm
              (callbackType secondCapture)).push
                (callbackRequirements.weaken (kind := .term)))
      (callbackExecution (scope := scope))
      (.union (.union firstRuntimeCapture .empty)
        (.union secondRuntimeCapture .empty)) .one := by
  apply Term.HasType.letPlain
      (bound := (.one : Ty (CallbackBodyScope scope)))
      (bodyOuterUse := .union secondRuntimeCapture .empty)
      (by trivial)
  · exact .app
      (.ret (Value.HasType.declaredVar (name := firstCallbackVariable))) rfl
      (by trivial) (.ret .unit)
  · exact .app
      (.ret (Value.HasType.declaredVar
        (name := (.there secondCallbackVariable)))) rfl
      (by trivial) (.ret .unit)
  · exact .refl

def callbackExecutionCaptured {scope : Sig} {environment : TypingEnv scope} :
    CaptureIncludes
      (((((environment.extendStatic unboundedCaptureInterval).extendTerm
          (callbackType abstractCapture)).extendStatic
            unboundedCaptureInterval).extendTerm
              (callbackType secondCapture)).push
                (callbackRequirements.weaken (kind := .term))).bindings
      (.union (.union firstRuntimeCapture .empty)
        (.union secondRuntimeCapture .empty))
      (.union firstRuntimeCapture secondRuntimeCapture) :=
  .captureUnionElim
    (.captureUnionElim .captureUnionLeft .captureEmpty)
    (.captureUnionElim .captureUnionRight .captureEmpty)

def secondCallback {scope : Sig} :
    Value (scope ▹ .static .capture ▹ .term ▹ .static .capture) :=
  .lam (callbackType secondCapture) modalResultType
    (.ret
      (.lock (callbackRequirements.weaken (kind := .term)) .one
        (.union firstRuntimeCapture secondRuntimeCapture)
        callbackExecution))

def secondCallbackTyping {scope : Sig} {environment : TypingEnv scope} :
    Value.HasType
      (((environment.extendStatic unboundedCaptureInterval).extendTerm
        (callbackType abstractCapture)).extendStatic
          unboundedCaptureInterval)
      (secondCallback (scope := scope))
      (.capturing .empty
        (.arr (callbackType secondCapture) modalResultType)) := by
  apply Value.HasType.lam
  · trivial
  · exact .ret (.lock callbackExecutionTyping callbackExecutionCaptured)
  · exact .captureEmpty

def secondStaticCallback {scope : Sig} :
    Value (scope ▹ .static .capture ▹ .term) :=
  .staticLam unboundedCaptureInterval secondCallback

def secondStaticCallbackTyping {scope : Sig}
    {environment : TypingEnv scope} :
    Value.HasType
      ((environment.extendStatic unboundedCaptureInterval).extendTerm
        (callbackType abstractCapture))
      (secondStaticCallback (scope := scope))
      ((secondStageType (scope := scope)).weaken (kind := .term)) := by
  simpa [secondStageType, firstCaptureAtSecondTypeBinder, secondTypeCapture,
    callbackTypeRequirements, callbackModalType, callbackRequirements,
    firstCaptureAtSecondBinder, secondCapture, Ty.weaken, Capture.weaken,
    ModalRequirements.weaken] using
      (Value.HasType.staticLam secondCallbackTyping
        (.refl : CaptureIncludes _ (.empty : Capture _) .empty))

def firstCallback {scope : Sig} : Value (scope ▹ .static .capture) :=
  .lam (callbackType abstractCapture)
    secondStageType
    (.ret secondStaticCallback)

def firstCallbackTyping {scope : Sig} {environment : TypingEnv scope} :
    Value.HasType (environment.extendStatic unboundedCaptureInterval)
      (firstCallback (scope := scope))
      (.capturing .empty
        (.arr (callbackType abstractCapture)
          secondStageType)) := by
  apply Value.HasType.lam
  · trivial
  · exact .ret secondStaticCallbackTyping
  · exact .captureEmpty

/-- The static/modal spine of Capybara's two-callback combinator.  Static
capture parameters and evidence erase; the locked body invokes both supplied
callbacks in source order and returns the second callback's unit result. -/
def runReadPair {scope : Sig} : Value scope :=
  .staticLam unboundedCaptureInterval firstCallback

def runReadPairType {scope : Sig} : Ty scope :=
  .capturing .empty
    (.forallI unboundedCaptureInterval
      (.capturing .empty
        (.arr (callbackType abstractCapture)
          secondStageType)))

def runReadPairTyping {scope : Sig} {environment : TypingEnv scope} :
    Value.HasType environment (runReadPair (scope := scope)) runReadPairType :=
  .staticLam firstCallbackTyping .refl

/-! ## One normalized object with a repeated capture-member label -/

def typeLabel : Label := 31
def captureLabel : Label := 32

def repeatedInterface {scope : Sig} : Interface scope :=
  .inter
    (.typeMember typeLabel .one .one)
    (.inter
      (.captureMember captureLabel .empty
        (.ref (.localCaptureMember captureLabel)))
      (.captureMember captureLabel .empty
        (.ref (.localCaptureMember captureLabel))))

/-- The runtime shape depends on the shared type member.  The repeated capture
member remains a static separation/classification coordinate; the target's
generated `C_rep` still records the payload's actual capture explicitly. -/
def objectType {scope : Sig} : ObjectType scope :=
  .mk repeatedInterface (.ref (.localTypeMember typeLabel)) .empty

def objectModel {scope : Sig} : LocalModel.Model scope where
  typeMember := fun _ => .one
  captureMember := fun _ => .empty

def objectRealization {scope : Sig} (environment : TypingEnv scope) :
    ObjectType.Realization environment.bindings
      (objectType (scope := scope)) where
  model := objectModel
  constraints := .inter
    (.typeMember .refl .refl)
    (.inter
      (.captureMember .refl .refl)
      (.captureMember .refl .refl))

def objectLiteral {scope : Sig} : Value scope :=
  .object objectType .unit

def objectLiteralTyping {scope : Sig} {environment : TypingEnv scope} :
    Value.HasType environment (objectLiteral (scope := scope))
      (objectType (scope := scope)).formedType :=
  .object (objectRealization environment) .unit .refl .refl .refl

def objectConsumer {scope : Sig} : Value scope :=
  .objectConsumer objectType .one (.ret .unit)

def objectConsumerTyping {scope : Sig} {environment : TypingEnv scope} :
    Value.HasType environment (objectConsumer (scope := scope))
      (.capturing .empty (.objectArrow objectType .one)) :=
  .objectConsumer (.ret .unit) .captureEmpty

/-! ## Stable-root read-only instantiation -/

abbrev OpenedScope (scope : Sig) : Sig := scope ▹ .term

def openedRoot {scope : Sig} : Path (OpenedScope scope) := .var .here

def openedRootCapture {scope : Sig} : Capture (OpenedScope scope) :=
  .singleton openedRoot

def openedReadOnlyCapture {scope : Sig} : Capture (OpenedScope scope) :=
  .readOnly openedRootCapture

def concreteCallback {scope : Sig} : Value (OpenedScope scope) :=
  .lam .one .one (.ret .unit)

/-- The callback type deliberately records a read-only dependency on the
opened root.  Its unit body is the abstract runtime stand-in for a read-only
operation; capture typing permits this sound over-approximation. -/
def concreteCallbackTyping {scope : Sig} {environment : TypingEnv scope} :
    Value.HasType
      (environment.extendTerm (objectType (scope := scope)).formedType)
      (concreteCallback (scope := scope))
      (callbackType openedReadOnlyCapture) := by
  apply Value.HasType.lam
  · trivial
  · exact .ret .unit
  · exact .captureEmpty

def instantiatedFirst {scope : Sig} : Term (OpenedScope scope) :=
  .staticApp unboundedCaptureInterval (.ret runReadPair)
    (.capture openedReadOnlyCapture)

def instantiatedFirstTyping {scope : Sig} {environment : TypingEnv scope} :=
  Term.HasType.staticApp
    (environment := environment.extendTerm
      (objectType (scope := scope)).formedType)
    (argument := .capture openedReadOnlyCapture)
    (.ret runReadPairTyping) rfl .unbounded

def appliedFirst {scope : Sig} : Term (OpenedScope scope) :=
  .app instantiatedFirst (.ret concreteCallback)

def appliedFirstTyping {scope : Sig} {environment : TypingEnv scope} :=
  Term.HasType.app (instantiatedFirstTyping (environment := environment)) rfl
    (by change True; trivial)
    (.ret concreteCallbackTyping)

def instantiatedSecond {scope : Sig} : Term (OpenedScope scope) :=
  .staticApp unboundedCaptureInterval appliedFirst
    (.capture openedReadOnlyCapture)

def instantiatedSecondTyping {scope : Sig} {environment : TypingEnv scope} :=
  Term.HasType.staticApp
    (argument := .capture openedReadOnlyCapture)
    (appliedFirstTyping (environment := environment)) rfl .unbounded

def appliedSecond {scope : Sig} : Term (OpenedScope scope) :=
  .app instantiatedSecond (.ret concreteCallback)

def appliedSecondTyping {scope : Sig} {environment : TypingEnv scope} :=
  Term.HasType.app
    (instantiatedSecondTyping (environment := environment)) rfl
    (by change True; trivial)
    (.ret concreteCallbackTyping)

def concreteRequirements {scope : Sig} :
    ModalRequirements 2 [] (OpenedScope scope) :=
  .mk
    (.cons (.cons .nil openedReadOnlyCapture) openedReadOnlyCapture)
    .nil

def sharedReadOnlySeparation {scope : Sig} {environment : TypingEnv scope} :
    Separate
      (environment.extendTerm (objectType (scope := scope)).formedType).bindings
      (environment.extendTerm (objectType (scope := scope)).formedType).locks
      openedReadOnlyCapture openedReadOnlyCapture :=
  .readOnly (.readOnly openedRootCapture) (.readOnly openedRootCapture)

def concreteSatisfaction {scope : Sig} {environment : TypingEnv scope} :
    Satisfies
      (environment.extendTerm (objectType (scope := scope)).formedType).bindings
      (environment.extendTerm (objectType (scope := scope)).formedType).locks
      (concreteRequirements (scope := scope)) :=
  .mk
    (fun occurrence => nomatch occurrence)
    (fun left right distinct => by
      cases distinct with
      | hereThere older =>
          cases older with
          | here => exact sharedReadOnlySeparation
          | there impossible => nomatch impossible
      | thereHere older =>
          cases older with
          | here => exact .symm sharedReadOnlySeparation
          | there impossible => nomatch impossible
      | thereThere inner =>
          cases inner with
          | hereThere older => nomatch older
          | thereHere older => nomatch older
          | thereThere impossible => nomatch impossible)

def releasedPair {scope : Sig} : Term (OpenedScope scope) :=
  .unlock concreteRequirements appliedSecond

def releasedPairTyping {scope : Sig} {environment : TypingEnv scope} :=
  Term.HasType.unlock
    (appliedSecondTyping (environment := environment)) rfl
    (concreteSatisfaction (environment := environment))

/-! A separate stable negative-use regression reuses the same opened model and
passes the one runtime payload directly. -/
def stableObjectApplication {scope : Sig} : Term (OpenedScope scope) :=
  .objectApp objectType (.ret objectConsumer) (.ret (.var .here))

def stableObjectArgument {scope : Sig} {environment : TypingEnv scope} :
    ObjectArgument.HasType
      (environment.extendTerm (objectType (scope := scope)).formedType)
      (.ret (.var .here)) (objectType (scope := OpenedScope scope))
      (LocalModel.atPath (.var .here)) := by
  exact .stable rfl (ObjectType.Adapts.refl objectType) .refl .captureEmpty

def stableObjectApplicationTyping {scope : Sig}
    {environment : TypingEnv scope} :=
  Term.HasType.objectApp
    (environment := environment.extendTerm
      (objectType (scope := scope)).formedType)
    (.ret objectConsumerTyping) rfl
    (stableObjectArgument (environment := environment))

/-- Focused companion artifact for the stable negative-use path.  Keeping it
separate avoids inventing a source sequencing construct solely to splice it
into the modal result. -/
def stableUseProgram : Term [] :=
  .objectLet objectType .one (.ret objectLiteral) stableObjectApplication

def stableUseProgramTypingRaw :
    Term.HasType TypingEnv.nil stableUseProgram (.union .empty .empty) .one :=
  .objectLet (.ret (objectLiteralTyping (environment := TypingEnv.nil)))
    (stableObjectApplicationTyping (environment := TypingEnv.nil))
    (.captureUnionElim .captureEmpty .captureEmpty)

def stableUseProgramTyping :
    Term.HasType TypingEnv.nil stableUseProgram .empty .one :=
  .use stableUseProgramTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

/-- Closed benchmark: one object package/open, two
capture instantiations, two callback applications, and one checked release. -/
def program : Term [] :=
  .objectLet objectType .one (.ret objectLiteral) releasedPair

def programTypingRaw :
    Term.HasType TypingEnv.nil program (.union .empty .empty) .one := by
  apply Term.HasType.objectLet
      (bodyOuterUse := (.empty : Capture []))
      (.ret (objectLiteralTyping (environment := TypingEnv.nil)))
      (releasedPairTyping (environment := TypingEnv.nil))
  simp [runReadPairType, secondStageType, callbackModalType,
    callbackTypeRequirements, firstCaptureAtSecondTypeBinder,
    secondTypeCapture, callbackType, openedReadOnlyCapture,
    openedRootCapture, openedRoot, Capture.seq, Ty.outerCapture,
    Ty.instantiateStatic, Ty.substitute, Capture.substitute]
  exact .captureUnionElim
    (.captureUnionElim
      (.captureUnionElim
        (.captureUnionElim .captureEmpty
          (.trans .captureReadOnly .captureUnionRight))
        .captureEmpty)
      (.captureUnionElim .captureEmpty
        (.trans .captureReadOnly .captureUnionRight)))
    (.captureUnionElim
      (.trans .captureReadOnly .captureUnionRight)
      (.trans .captureReadOnly .captureUnionRight))

def programTyping : Term.HasType TypingEnv.nil program .empty .one :=
  .use programTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

end Source

end DOTCaptureToManySortedFC.CertificateStudy.ReadOnlyBenchmark
