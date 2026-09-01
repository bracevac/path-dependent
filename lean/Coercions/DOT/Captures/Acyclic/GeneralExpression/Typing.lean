import Coercions.DOT.Captures.Acyclic.GeneralExpression.Structural
import Coercions.DOT.Captures.Acyclic.ObjectTyping

/-!
# Typing of general acyclic captured-DOT expressions

The rules retain the value-MNF core's static judgments and exact formed-object
boundary.  The differences are computational: applications type two terms,
and object-opening lets may evaluate an arbitrary term before exposing its
existential members and payload.
-/

namespace DOTCapture.Acyclic.GeneralExpression

namespace ObjectSig

/-- Proof-relevant weakening from an available object signature to the
signature expected by a negative consumer.

A model of `available` realizes `expected` when the expected lower bounds
are below the available lower bounds and the available upper bounds are
below the expected upper bounds.  The four fields deliberately follow the
two member sorts uniformly; compilation may translate them as a telescope
morphism without inspecting particular endpoint syntax. -/
structure Adapts {scope : Scope} (context : Ctx scope)
    (available expected : ObjectSig scope) : Type where
  typeLower : DOTCapture.Acyclic.TypeIncludes context
    expected.typeLower available.typeLower
  typeUpper : DOTCapture.Acyclic.TypeIncludes context
    available.typeUpper expected.typeUpper
  captureLower : DOTCapture.Acyclic.CaptureIncludes context
    expected.captureLower available.captureLower
  captureUpper : DOTCapture.Acyclic.CaptureIncludes context
    available.captureUpper expected.captureUpper

namespace Adapts

/-- Every signature is an admissible view of itself. -/
def refl {scope : Scope} {context : Ctx scope}
    (signature : ObjectSig scope) : Adapts context signature signature where
  typeLower := .refl
  typeUpper := .refl
  captureLower := .refl
  captureUpper := .refl

/-- Signature weakening composes in the same direction as model reuse. -/
def trans {scope : Scope} {context : Ctx scope}
    {first second third : ObjectSig scope}
    (firstToSecond : Adapts context first second)
    (secondToThird : Adapts context second third) :
    Adapts context first third where
  typeLower := .trans secondToThird.typeLower firstToSecond.typeLower
  typeUpper := .trans firstToSecond.typeUpper secondToThird.typeUpper
  captureLower := .trans secondToThird.captureLower firstToSecond.captureLower
  captureUpper := .trans firstToSecond.captureUpper secondToThird.captureUpper

end Adapts

end ObjectSig

mutual

/-- Declarative typing of surface values.  Adaptation remains value-only and
logical, so compilation never hides evaluation beneath an adapter. -/
inductive Value.HasType : {scope : Scope} → Ctx scope →
    Value scope → Ty scope → Type where
  | var {scope : Scope} {context : Ctx scope} {name : Var scope} :
      Value.HasType context (.var name) (context.lookup name)
  | unit {scope : Scope} {context : Ctx scope} :
      Value.HasType context .unit .one
  | lam {scope : Scope} {context : Ctx scope}
      {domain codomain : Ty scope} {body : Term (scope + 1)}
      {bodyUse : Capture (scope + 1)} {closure : Capture scope}
      (domainPlain : domain.IsPlain)
      (bodyTyping : Term.HasType (context.extendTerm domain) body
        bodyUse codomain.weaken)
      (captures : DOTCapture.Acyclic.CaptureIncludes
        (context.extendTerm domain) bodyUse
        (.union closure.weaken (.singleton (.var .here)))) :
      Value.HasType context (.lam domain codomain body)
        (.capturing closure (.arr domain codomain))
  /-- Negative object consumer.

  The source arrow remains nondependent in this fixed-signature core.  Its
  parameter is nevertheless installed as a canonical stable object root, so
  every selection in `body` refers to the one model abstracted by target
  compilation.  The target elaboration is polarized: it turns this source
  lambda into static model abstraction followed by an ordinary runtime
  lambda over the representation. -/
  | objectLam {scope : Scope} {context : Ctx scope}
      {signature : ObjectSig scope} {codomain : Ty scope}
      {body : Term (scope + 1)}
      {bodyUse : Capture (scope + 1)} {closure : Capture scope}
      (bodyTyping : Term.HasType
        (context.extendTerm signature.formedType) body
        bodyUse codomain.weaken)
      (captures : DOTCapture.Acyclic.CaptureIncludes
        (context.extendTerm signature.formedType) bodyUse
        (.union closure.weaken (.singleton (.var .here)))) :
      Value.HasType context
        (.lam signature.formedType codomain body)
        (.capturing closure (.arr signature.formedType codomain))
  | object {scope : Scope} {context : Ctx scope}
      {signature : ObjectSig scope} {typeWitness : Ty scope}
      {captureWitness : Capture scope} {payload : Value scope}
      {payloadType : Ty scope}
      (typeLower : DOTCapture.Acyclic.TypeIncludes context
        signature.typeLower typeWitness)
      (typeUpper : DOTCapture.Acyclic.TypeIncludes context
        typeWitness signature.typeUpper)
      (captureLower : DOTCapture.Acyclic.CaptureIncludes context
        signature.captureLower captureWitness)
      (captureUpper : DOTCapture.Acyclic.CaptureIncludes context
        captureWitness signature.captureUpper)
      (payloadTyping : Value.HasType context payload payloadType)
      (payloadShape : DOTCapture.Acyclic.TypeIncludes context
        payloadType.stripCapture typeWitness)
      (payloadCapture : DOTCapture.Acyclic.CaptureIncludes context
        payloadType.outerCapture captureWitness) :
      Value.HasType context
        (.object signature typeWitness captureWitness payload)
        (.capturing signature.captureUpper (.object signature))
  | adapt {scope : Scope} {context : Ctx scope} {value : Value scope}
      {source target : Ty scope}
      (valueTyping : Value.HasType context value source)
      (inclusion : DOTCapture.Acyclic.TypeIncludes context source target) :
      Value.HasType context value target

/-- Direct negative use of an object.

The judgment is deliberately smaller than ordinary term typing.  It exposes
the model and representation without evaluating an existential package, so
only a canonical literal or an already-open stable variable is admitted.
`expected` is the consumer's signature.  `adaptation` records how the
argument's available model realizes that expected telescope. -/
inductive ObjectArgument.HasType : {scope : Scope} → Ctx scope →
    Term scope → ObjectSig scope → Type where
  | literal {scope : Scope} {context : Ctx scope}
      {available expected : ObjectSig scope} {typeWitness : Ty scope}
      {captureWitness : Capture scope} {payload : Value scope}
      {payloadType : Ty scope}
      (typeLower : DOTCapture.Acyclic.TypeIncludes context
        available.typeLower typeWitness)
      (typeUpper : DOTCapture.Acyclic.TypeIncludes context
        typeWitness available.typeUpper)
      (captureLower : DOTCapture.Acyclic.CaptureIncludes context
        available.captureLower captureWitness)
      (captureUpper : DOTCapture.Acyclic.CaptureIncludes context
        captureWitness available.captureUpper)
      (payloadTyping : Value.HasType context payload payloadType)
      (payloadShape : DOTCapture.Acyclic.TypeIncludes context
        payloadType.stripCapture typeWitness)
      (payloadCapture : DOTCapture.Acyclic.CaptureIncludes context
        payloadType.outerCapture captureWitness)
      (adaptation : available.Adapts context expected) :
      ObjectArgument.HasType context
        (.ret (.object available typeWitness captureWitness payload)) expected
  | stable {scope : Scope} {context : Ctx scope}
      {name : Var scope} {available expected : ObjectSig scope}
      (canonical : context.lookup name = available.formedType)
      (adaptation : available.Adapts context expected) :
      ObjectArgument.HasType context (.ret (.var name)) expected

/-- A computation whose result is a negative object consumer.

This judgment makes the polarity of an object-domain function explicit.  An
ordinary source arrow derivation is not enough: its target may be an ordinary
function consuming a positive existential package.  A negative consumer is
instead introduced by `objectLam`, or computed by administrative source
constructs whose final value is recursively known to be such a consumer.

The indices record the source computation use and the three components of its
unambiguous negative type.  Compilation may therefore assign it the target
type `forall Σ. Rep(Σ) -> R` without guessing from an ordinary arrow proof. -/
inductive ObjectFunction.HasType : {scope : Scope} → Ctx scope →
    Term scope → Capture scope → ObjectSig scope → Ty scope →
      Capture scope → Type where
  /-- A returned object lambda is the introduction form for a negative
  consumer. -/
  | returned {scope : Scope} {context : Ctx scope}
      {signature : ObjectSig scope} {codomain : Ty scope}
      {body : Term (scope + 1)}
      {bodyUse : Capture (scope + 1)} {closure : Capture scope}
      (bodyTyping : Term.HasType
        (context.extendTerm signature.formedType) body
        bodyUse codomain.weaken)
      (captures : DOTCapture.Acyclic.CaptureIncludes
        (context.extendTerm signature.formedType) bodyUse
        (.union closure.weaken (.singleton (.var .here)))) :
      ObjectFunction.HasType context
        (.ret (.lam signature.formedType codomain body)) .empty
        signature codomain closure
  /-- A plain source let may compute before producing a negative consumer.
  The RHS retains the ordinary term-typing judgment; only the let body is
  recursively checked at the negative function interface. -/
  | letPlain {scope : Scope} {context : Ctx scope}
      {signature : ObjectSig scope} {codomain bound : Ty scope}
      {closure : Capture scope} {rhs : Term scope}
      {body : Term (scope + 1)} {rhsUse : Capture scope}
      {bodyUse : Capture (scope + 1)} {bodyOuterUse : Capture scope}
      (boundPlain : bound.IsPlain)
      (rhsTyping : Term.HasType context rhs rhsUse bound)
      (bodyTyping : ObjectFunction.HasType (context.extendTerm bound) body
        bodyUse signature.weaken codomain.weaken closure.weaken)
      (discharge : DOTCapture.Acyclic.CaptureIncludes
        (context.extendTerm bound) bodyUse bodyOuterUse.weaken) :
      ObjectFunction.HasType context
        (.let'
          (.capturing closure (.arr signature.formedType codomain)) rhs body)
        (.union rhsUse bodyOuterUse) signature codomain closure
  /-- Immediate-use widening does not change the negative function
  interface. -/
  | use {scope : Scope} {context : Ctx scope}
      {function : Term scope} {sourceUse targetUse : Capture scope}
      {signature : ObjectSig scope} {codomain : Ty scope}
      {closure : Capture scope}
      (functionTyping : ObjectFunction.HasType context function sourceUse
        signature codomain closure)
      (inclusion : DOTCapture.Acyclic.CaptureIncludes context
        sourceUse targetUse) :
      ObjectFunction.HasType context function targetUse signature codomain
        closure

/-- Declarative typing of general computations.

Application evaluates its function and argument from left to right and then
charges both returned values' retained captures.  The capture index is a set
prediction, so sequencing is represented by `Capture.seq` and union rather
than by an effect-ordering judgment. -/
inductive Term.HasType : {scope : Scope} → Ctx scope →
    Term scope → Capture scope → Ty scope → Type where
  | ret {scope : Scope} {context : Ctx scope} {value : Value scope}
      {type : Ty scope} (valueTyping : Value.HasType context value type) :
      Term.HasType context (.ret value) .empty type
  | select {scope : Scope} {context : Ctx scope}
      {receiver : Path scope} {signature : ObjectSig scope}
      (exposes : DOTCapture.Acyclic.ExposesObject context receiver signature) :
      Term.HasType context (.select receiver .v) (.singleton receiver)
        receiver.valueMemberType
  | app {scope : Scope} {context : Ctx scope}
      {function argument : Term scope}
      {functionUse argumentUse : Capture scope}
      {functionType domain codomain : Ty scope}
      (functionTyping : Term.HasType context function functionUse functionType)
      (functionShape : functionType.stripCapture = .arr domain codomain)
      (domainPlain : domain.IsPlain)
      (argumentTyping : Term.HasType context argument argumentUse domain) :
      Term.HasType context (.app function argument)
        (Capture.seq functionUse
          (Capture.seq argumentUse
            (.union functionType.outerCapture domain.outerCapture)))
        codomain
  /-- Apply a negative object consumer to a directly available model and
  runtime representation.

  Unlike ordinary application, this premise does not compile the argument
  positively and then open a package.  Its two admissible forms erase to the
  source argument itself, so target static application followed by runtime
  application preserves literal erasure. -/
  | objectApp {scope : Scope} {context : Ctx scope}
      {function argument : Term scope} {functionUse closure : Capture scope}
      {codomain : Ty scope} {signature : ObjectSig scope}
      (functionTyping : ObjectFunction.HasType context function functionUse
        signature codomain closure)
      (argumentTyping : ObjectArgument.HasType context argument signature) :
      Term.HasType context (.app function argument)
        (Capture.seq functionUse
          (.union closure signature.captureUpper))
        codomain
  | letPlain {scope : Scope} {context : Ctx scope}
      {result bound : Ty scope} {rhs : Term scope}
      {body : Term (scope + 1)} {rhsUse : Capture scope}
      {bodyUse : Capture (scope + 1)} {bodyOuterUse : Capture scope}
      (boundPlain : bound.IsPlain)
      (rhsTyping : Term.HasType context rhs rhsUse bound)
      (bodyTyping : Term.HasType (context.extendTerm bound) body
        bodyUse result.weaken)
      (discharge : DOTCapture.Acyclic.CaptureIncludes
        (context.extendTerm bound) bodyUse bodyOuterUse.weaken) :
      Term.HasType context (.let' result rhs body)
        (.union rhsUse bodyOuterUse) result
  | letObject {scope : Scope} {context : Ctx scope}
      {signature : ObjectSig scope} {result : Ty scope}
      {rhs : Term scope} {rhsUse : Capture scope}
      {body : Term (scope + 1)}
      {bodyUse : Capture (scope + 1)} {bodyOuterUse : Capture scope}
      (rhsTyping : Term.HasType context rhs rhsUse
        (.capturing signature.captureUpper (.object signature)))
      (bodyTyping : Term.HasType
        (context.extendTerm
          (.capturing signature.captureUpper (.object signature)))
        body bodyUse result.weaken)
      (discharge : DOTCapture.Acyclic.CaptureIncludes
        (context.extendTerm
          (.capturing signature.captureUpper (.object signature)))
        bodyUse
        (.union bodyOuterUse.weaken (.singleton (.var .here)))) :
      Term.HasType context (.let' result rhs body)
        (Capture.seq rhsUse
          (.union signature.captureUpper bodyOuterUse)) result
  | use {scope : Scope} {context : Ctx scope} {term : Term scope}
      {sourceUse targetUse : Capture scope} {type : Ty scope}
      (termTyping : Term.HasType context term sourceUse type)
      (inclusion : DOTCapture.Acyclic.CaptureIncludes context
        sourceUse targetUse) :
      Term.HasType context term targetUse type

end

namespace ObjectFunction.HasType

/-- Forget the negative-use witness and recover ordinary source typing at the
corresponding captured arrow.  The converse is intentionally unavailable: an
ordinary arrow proof does not determine whether its object argument is
represented positively or negatively. -/
def toTermTyping {scope : Scope} {context : Ctx scope}
    {function : Term scope} {use : Capture scope}
    {signature : ObjectSig scope} {codomain : Ty scope}
    {closure : Capture scope}
    (typing : ObjectFunction.HasType context function use signature codomain
      closure) :
    Term.HasType context function use
      (.capturing closure (.arr signature.formedType codomain)) :=
  match typing with
  | .returned bodyTyping captures =>
      .ret (.objectLam bodyTyping captures)
  | @ObjectFunction.HasType.letPlain scope context signature codomain bound
      closure rhs body rhsUse bodyUse bodyOuterUse boundPlain rhsTyping
      bodyTyping discharge => by
      have bodyOrdinary : Term.HasType (context.extendTerm bound) body bodyUse
          ((Ty.capturing closure (Ty.arr signature.formedType codomain)).weaken) := by
        simpa using toTermTyping bodyTyping
      exact Term.HasType.letPlain boundPlain rhsTyping bodyOrdinary discharge
  | .use functionTyping inclusion =>
      .use (toTermTyping functionTyping) inclusion

end ObjectFunction.HasType

namespace ExposesObject

/-- Read the fixed payload and account for its receiver through `x.C`. -/
def valueMember {scope : Scope} {context : Ctx scope}
    {receiver : Path scope} {signature : ObjectSig scope}
    (exposes : DOTCapture.Acyclic.ExposesObject context receiver signature) :
    Term.HasType context (.select receiver .v) receiver.selectedCapture
      receiver.valueMemberType :=
  .use (.select exposes) exposes.payloadRoot

end ExposesObject

end DOTCapture.Acyclic.GeneralExpression
