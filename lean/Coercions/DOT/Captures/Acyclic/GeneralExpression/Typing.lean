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
      (argumentTyping : Term.HasType context argument argumentUse domain) :
      Term.HasType context (.app function argument)
        (Capture.seq functionUse
          (Capture.seq argumentUse
            (.union functionType.outerCapture domain.outerCapture)))
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
