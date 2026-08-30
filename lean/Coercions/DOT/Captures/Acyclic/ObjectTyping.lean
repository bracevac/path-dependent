import Coercions.DOT.Captures.Acyclic.MemberTyping

/-!
# Object and value-member typing

Object formation realizes the two abstract members with concrete witnesses.
All four endpoint certificates and the payload typing derivation live in the
ambient context: the object being constructed is never added as a self
assumption.  Thus a syntactically valid bad-bounds signature can be assumed
after opening a path, but it cannot construct itself by discharging its own
obligations.
-/

namespace DOTCapture.Acyclic

mutual

/-- Declarative value typing for the computational acyclic object layer.

Values retain capabilities in the outer capture of their type.  Adaptation
is deliberately limited to logical source inclusion, so its eventual target
adapter is runtime-transparent; structural function adaptation is not hidden
in this rule. -/
inductive Value.HasType : {scope : Scope} → Ctx scope →
    Value scope → Ty scope → Type where
  | var {scope : Scope} {context : Ctx scope} {name : Var scope} :
      Value.HasType context (.var name) (context.lookup name)
  | unit {scope : Scope} {context : Ctx scope} :
      Value.HasType context .unit .one
  /-- A lambda has a plain parameter binding, so its body introduces exactly
  one ordinary source/runtime coordinate.  Body use may be retained by the
  ambient closure or discharged to the parameter singleton. -/
  | lam {scope : Scope} {context : Ctx scope}
      {domain codomain : Ty scope} {body : Term (scope + 1)}
      {bodyUse : Capture (scope + 1)} {closure : Capture scope}
      (domainPlain : domain.IsPlain)
      (bodyTyping : Term.HasType (context.extendTerm domain) body
        bodyUse codomain.weaken)
      (captures : CaptureIncludes (context.extendTerm domain) bodyUse
        (.union closure.weaken (.singleton (.var .here)))) :
      Value.HasType context (.lam domain codomain body)
        (.capturing closure (.arr domain codomain))
  /-- Construct
  `{ A = typeWitness; C = captureWitness; v = payload }`.

  The four bounds are ambient premises, not a consistency field on the
  signature and not assumptions made available by the object itself.  The
  resulting object's retained closure is exactly the capture upper endpoint
  `E`. -/
  | object {scope : Scope} {context : Ctx scope}
      {signature : ObjectSig scope} {typeWitness : Ty scope}
      {captureWitness : Capture scope} {payload : Value scope}
      {payloadType : Ty scope}
      (typeLower : TypeIncludes context signature.typeLower typeWitness)
      (typeUpper : TypeIncludes context typeWitness signature.typeUpper)
      (captureLower : CaptureIncludes context signature.captureLower
        captureWitness)
      (captureUpper : CaptureIncludes context captureWitness
        signature.captureUpper)
      (payloadTyping : Value.HasType context payload payloadType)
      -- The payload's actual shape is admissible at concrete witness `A`.
      (payloadShape : TypeIncludes context payloadType.stripCapture
        typeWitness)
      -- The payload's actual retained capture is covered by witness `C`.
      (payloadCapture : CaptureIncludes context payloadType.outerCapture
        captureWitness) :
      Value.HasType context
        (.object signature typeWitness captureWitness payload)
        (.capturing signature.captureUpper (.object signature))
  /-- Implicit source conversion backed by one logical type-inclusion proof.
  Since this layer has no structural arrow-inclusion constructor, compilation
  can realize the rule with an erasing logical cast. -/
  | adapt {scope : Scope} {context : Ctx scope} {value : Value scope}
      {source target : Ty scope}
      (valueTyping : Value.HasType context value source)
      (inclusion : TypeIncludes context source target) :
      Value.HasType context value target

/-- Typing of the computational ANF layer.

The capture index describes capabilities used immediately.  A value-member
read first exposes the runtime receiver root `{x}`; the separate `use` rule
can apply the warranted `{x} ≤ x.C` member rule.  Plain lets compile as
ordinary sequencing; canonical object-value lets expose the object's static
theory and payload in one value-only boundary. -/
inductive Term.HasType : {scope : Scope} → Ctx scope →
    Term scope → Capture scope → Ty scope → Type where
  | ret {scope : Scope} {context : Ctx scope} {value : Value scope}
      {type : Ty scope} (valueTyping : Value.HasType context value type) :
      Term.HasType context (.ret value) .empty type
  | select {scope : Scope} {context : Ctx scope}
      {receiver : Path scope} {signature : ObjectSig scope}
      (exposes : ExposesObject context receiver signature) :
      Term.HasType context (.select receiver .v) (.singleton receiver)
        receiver.valueMemberType
  /-- Call-by-value application consumes two source values.  Any logical
  conversion needed to expose an arrow is made explicit in the function's
  `Value.HasType` derivation via `adapt`; this rule itself requires an exact
  callable shape. -/
  | app {scope : Scope} {context : Ctx scope}
      {function argument : Value scope}
      {functionType domain codomain : Ty scope}
      (functionTyping : Value.HasType context function functionType)
      (functionShape : functionType.stripCapture = .arr domain codomain)
      (argumentTyping : Value.HasType context argument domain) :
      Term.HasType context (.app function argument)
        (.union functionType.outerCapture domain.outerCapture) codomain
  /-- An ordinary let extends the body with exactly one plain binding.  The
  ambient result annotation prevents that binder from escaping. -/
  | letPlain {scope : Scope} {context : Ctx scope}
      {result bound : Ty scope} {rhs : Term scope}
      {body : Term (scope + 1)} {rhsUse : Capture scope}
      {bodyUse : Capture (scope + 1)} {bodyOuterUse : Capture scope}
      (boundPlain : bound.IsPlain)
      (rhsTyping : Term.HasType context rhs rhsUse bound)
      (bodyTyping : Term.HasType (context.extendTerm bound) body
        bodyUse result.weaken)
      (discharge : CaptureIncludes (context.extendTerm bound) bodyUse
        bodyOuterUse.weaken) :
      Term.HasType context (.let' result rhs body)
        (.union rhsUse bodyOuterUse) result
  /-- Bind and immediately expose one canonical object value.

  The source binding is the exact formation type produced by `object`.  Its
  retained upper capture is charged when the representation is opened.  The
  newest source singleton denotes the opened payload coordinate and may be
  discharged locally alongside the weakened ambient body use. -/
  | letObject {scope : Scope} {context : Ctx scope}
      {signature : ObjectSig scope} {result : Ty scope}
      {rhs : Value scope} {body : Term (scope + 1)}
      {bodyUse : Capture (scope + 1)} {bodyOuterUse : Capture scope}
      (rhsTyping : Value.HasType context rhs
        (.capturing signature.captureUpper (.object signature)))
      (bodyTyping : Term.HasType
        (context.extendTerm
          (.capturing signature.captureUpper (.object signature)))
        body bodyUse result.weaken)
      (discharge : CaptureIncludes
        (context.extendTerm
          (.capturing signature.captureUpper (.object signature)))
        bodyUse
        (.union bodyOuterUse.weaken (.singleton (.var .here)))) :
      Term.HasType context (.let' result (.ret rhs) body)
        (.union signature.captureUpper bodyOuterUse) result
  | use {scope : Scope} {context : Ctx scope} {term : Term scope}
      {sourceUse targetUse : Capture scope} {type : Ty scope}
      (termTyping : Term.HasType context term sourceUse type)
      (inclusion : CaptureIncludes context sourceUse targetUse) :
      Term.HasType context term targetUse type

end

namespace ExposesObject

/-- Reading `x.v` has the signature-declared result `(x.A)^{x.C}` and may
account for its receiver use through the selected capture `x.C`. -/
def valueMember {scope : Scope} {context : Ctx scope}
    {receiver : Path scope} {signature : ObjectSig scope}
    (exposes : ExposesObject context receiver signature) :
    Term.HasType context (.select receiver .v) receiver.selectedCapture
      receiver.valueMemberType :=
  .use (.select exposes) exposes.payloadRoot

end ExposesObject

end DOTCapture.Acyclic
