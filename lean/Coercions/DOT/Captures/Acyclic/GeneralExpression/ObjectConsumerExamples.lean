import Coercions.DOT.Captures.Acyclic.GeneralExpression.Typing
import Coercions.DOT.Captures.Acyclic.GeneralExpression.Erasure

/-!
# Source regressions for negative object consumers

These examples exercise only the source boundary.  Object values retain
their ordinary positive formed-object type.  A negative consumer instead
uses `ObjectArgument.HasType` to receive an already available model and
payload without manufacturing and immediately opening an existential.
-/

namespace DOTCapture.Acyclic.GeneralExpression.ObjectConsumerExamples

def exactSignature {scope : Scope} : ObjectSig scope :=
  .bounds .one .one .empty .empty

def broadSignature {scope : Scope} : ObjectSig scope :=
  .bounds .bot .top .empty .empty

def exactAdaptsBroad {scope : Scope} (context : Ctx scope) :
    ObjectSig.Adapts context exactSignature broadSignature where
  typeLower := .typeBottom
  typeUpper := .typeTop
  captureLower := .refl
  captureUpper := .refl

/-! ## Canonical literals in negative position -/

def literal {scope : Scope} : Value scope :=
  .object exactSignature .one .empty .unit

def literalTyping {scope : Scope} (context : Ctx scope) :
    Value.HasType context (literal (scope := scope))
      (ObjectSig.formedType exactSignature) :=
  .object .refl .refl .refl .refl .unit .refl .refl

/-- The literal's exact model also realizes the broader consumer signature.
The four-field certificate is explicit in this derivation. -/
def literalArgument {scope : Scope} (context : Ctx scope) :
    ObjectArgument.HasType context (.ret (literal (scope := scope)))
      broadSignature :=
  .literal .refl .refl .refl .refl .unit .refl .refl
    (exactAdaptsBroad context)

def broadConsumer {scope : Scope} : Value scope :=
  .lam (ObjectSig.formedType broadSignature) .one (.ret .unit)

def broadConsumerTyping {scope : Scope} (context : Ctx scope) :
    Value.HasType context (broadConsumer (scope := scope))
      (.capturing .empty
        (.arr (ObjectSig.formedType broadSignature) .one)) :=
  .objectLam (.ret .unit) .captureEmpty

/-- The same introduction, recorded at the dedicated negative interface.
Unlike an arbitrary ordinary arrow proof, this witness determines the
consumer's universal target representation. -/
def broadConsumerFunction {scope : Scope} (context : Ctx scope) :
    ObjectFunction.HasType context (.ret (broadConsumer (scope := scope)))
      .empty broadSignature .one .empty :=
  .returned (.ret .unit) .captureEmpty

def literalApplication : Term 0 :=
  .app (.ret broadConsumer) (.ret literal)

private def literalApplicationRaw :
    Term.HasType Ctx.nil literalApplication (.union .empty .empty) .one :=
  .objectApp (broadConsumerFunction Ctx.nil) (literalArgument Ctx.nil)

def literalApplicationTyping :
    Term.HasType Ctx.nil literalApplication .empty .one :=
  .use literalApplicationRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

theorem literal_is_classified_directly :
    ObjectArgument.classify (.ret (literal (scope := 0))) =
      .canonicalLiteral := rfl

/-! ## Stable roots and explicit opening -/

def exactObjectContext : Ctx 1 :=
  Ctx.nil.extendTerm (ObjectSig.formedType exactSignature)

def stableArgument : ObjectArgument.HasType exactObjectContext
    (.ret (.var .here)) (broadSignature (scope := 1)) :=
  .stable rfl (exactAdaptsBroad exactObjectContext)

def stableApplication : Term 1 :=
  .app (.ret broadConsumer) (.ret (.var .here))

private def stableApplicationRaw :
    Term.HasType exactObjectContext stableApplication
      (.union .empty .empty) .one :=
  .objectApp (broadConsumerFunction exactObjectContext) stableArgument

def stableApplicationTyping :
    Term.HasType exactObjectContext stableApplication .empty .one :=
  .use stableApplicationRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

theorem stable_variable_is_classified_directly :
    ObjectArgument.classify
        (.ret (.var (.here : Var 1))) = .stableVariable :=
  rfl

/-! ## Member identity inside an object consumer -/

def receiver : Path 1 :=
  .var .here

def exactExposure : DOTCapture.Acyclic.ExposesObject exactObjectContext
    receiver (exactSignature (scope := 1)) :=
  .variable rfl

def selectedPure : Term.HasType exactObjectContext
    (.select receiver .v) .empty receiver.valueMemberType :=
  .use (ExposesObject.valueMember exactExposure) exactExposure.captureUpper

def resultType {scope : Scope} : Ty scope :=
  .capturing .empty .one

def selectedContext : Ctx 2 :=
  exactObjectContext.extendTerm receiver.valueMemberType

def olderReceiver : Path 2 :=
  .var (.there .here)

def olderExposure : DOTCapture.Acyclic.ExposesObject selectedContext
    olderReceiver (exactSignature (scope := 2)) :=
  .variable rfl

/-- The selected payload is converted through the assumptions attached to
the very model introduced for the object parameter. -/
def selectedPayloadTyping : Value.HasType selectedContext (.var .here)
    (resultType (scope := 2)) :=
  .adapt .var
    (.typeCapturing olderExposure.captureUpper olderExposure.typeUpper)

def selectingBody : Term 1 :=
  .let' resultType (.select receiver .v) (.ret (.var .here))

private def selectingBodyRaw : Term.HasType exactObjectContext selectingBody
    (.union .empty .empty) (resultType (scope := 1)) :=
  .letPlain (bound := receiver.valueMemberType) rfl selectedPure
    (.ret selectedPayloadTyping) .captureEmpty

def selectingBodyTyping : Term.HasType exactObjectContext selectingBody
    .empty (resultType (scope := 1)) :=
  .use selectingBodyRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

def selectingConsumer : Value 0 :=
  .lam (ObjectSig.formedType exactSignature) resultType selectingBody

/-- `objectLam` installs its parameter with the exact formed-object binding,
which is why both `x.A` and `x.C` in `selectingBody` expose one stable model. -/
def selectingConsumerTyping : Value.HasType Ctx.nil selectingConsumer
    (.capturing .empty
      (.arr (ObjectSig.formedType exactSignature) resultType)) :=
  .objectLam selectingBodyTyping .captureEmpty

def selectingConsumerFunction : ObjectFunction.HasType Ctx.nil
    (.ret selectingConsumer) .empty exactSignature resultType .empty :=
  .returned selectingBodyTyping .captureEmpty

/-! ## A genuinely computed negative consumer -/

def broadConsumerType {scope : Scope} : Ty scope :=
  .capturing .empty
    (.arr (ObjectSig.formedType broadSignature) .one)

/-- The function computation performs a real source let before yielding the
object lambda.  Its erasure is therefore a runtime zeta redex; the computation
is not manufactured by an erasing `use` node. -/
def computedBroadConsumer : Term 0 :=
  .let' broadConsumerType (.ret .unit) (.ret broadConsumer)

private def computedBroadConsumerRaw : ObjectFunction.HasType Ctx.nil
    computedBroadConsumer (.union .empty .empty) broadSignature .one .empty :=
  .letPlain (bound := .one) rfl (.ret .unit)
    (broadConsumerFunction (Ctx.nil.extendTerm .one)) .captureEmpty

def computedBroadConsumerTyping : ObjectFunction.HasType Ctx.nil
    computedBroadConsumer .empty broadSignature .one .empty :=
  .use computedBroadConsumerRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

/-- Forgetting the negative witness retains ordinary typing for the actual
let computation. -/
def computedBroadConsumerTermTyping : Term.HasType Ctx.nil
    computedBroadConsumer .empty broadConsumerType :=
  computedBroadConsumerTyping.toTermTyping

def computedConsumerApplication : Term 0 :=
  .app computedBroadConsumer (.ret literal)

private def computedConsumerApplicationRaw : Term.HasType Ctx.nil
    computedConsumerApplication (.union .empty .empty) .one :=
  .objectApp computedBroadConsumerTyping (literalArgument Ctx.nil)

def computedConsumerApplicationTyping : Term.HasType Ctx.nil
    computedConsumerApplication .empty .one :=
  .use computedConsumerApplicationRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

theorem computed_consumer_is_a_source_let :
    computedBroadConsumer =
      .let' broadConsumerType (.ret .unit) (.ret broadConsumer) :=
  rfl

theorem computed_consumer_runtime_shape :
    Erasure.eraseTerm computedBroadConsumer =
      ManySortedFC.Runtime.Tm.let' .unit (.lam .unit) :=
  rfl

/-- The computation takes a genuine zeta step before it exposes the object
consumer value. -/
theorem computed_consumer_takes_zeta :
    ManySortedFC.Runtime.Step (Erasure.eraseTerm computedBroadConsumer)
      (.lam .unit) := by
  rw [computed_consumer_runtime_shape]
  exact .zeta .unit

/-! ## Computed positive objects require an explicit open -/

/-- A positive, well-typed object-producing computation whose syntax does
not expose a reusable model and payload. -/
def computedObject : Term 0 :=
  .let' (ObjectSig.formedType exactSignature)
    (.ret literal) (.ret (.var .here))

private def computedObjectRaw : Term.HasType Ctx.nil computedObject
    (.union .empty .empty) (ObjectSig.formedType exactSignature) :=
  .letObject (.ret (literalTyping Ctx.nil)) (.ret .var) .captureEmpty

def computedObjectTyping : Term.HasType Ctx.nil computedObject .empty
    (ObjectSig.formedType exactSignature) :=
  .use computedObjectRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

/-- This is a compiler diagnostic only: `computedObjectTyping` above proves
that the positive expression is not rejected by source typing. -/
theorem computed_object_requires_explicit_open :
    ObjectArgument.classify computedObject =
      .unsupported .requiresExplicitOpen :=
  rfl

def openedApplication : Term 0 :=
  .let' .one computedObject stableApplication

private def openedApplicationRaw : Term.HasType Ctx.nil openedApplication
    (.union .empty .empty) .one :=
  .letObject computedObjectTyping stableApplicationTyping .captureEmpty

/-- The explicit object let establishes the stable root consumed by
`stableApplication`; no second package/open boundary is needed there. -/
def openedApplicationTyping :
    Term.HasType Ctx.nil openedApplication .empty .one :=
  .use openedApplicationRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

end DOTCapture.Acyclic.GeneralExpression.ObjectConsumerExamples
