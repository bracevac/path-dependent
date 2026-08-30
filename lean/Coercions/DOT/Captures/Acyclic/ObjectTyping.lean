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

namespace Value

/-- Declarative value typing for the first acyclic object layer. -/
inductive HasType : {scope : Scope} → Ctx scope →
    Value scope → Ty scope → Type where
  | var {scope : Scope} {context : Ctx scope} {name : Var scope} :
      HasType context (.var name) (context.lookup name)
  | unit {scope : Scope} {context : Ctx scope} :
      HasType context .unit .one
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
      (payloadTyping : HasType context payload payloadType)
      -- The payload's actual shape is admissible at concrete witness `A`.
      (payloadShape : TypeIncludes context payloadType.stripCapture
        typeWitness)
      -- The payload's actual retained capture is covered by witness `C`.
      (payloadCapture : CaptureIncludes context payloadType.outerCapture
        captureWitness) :
      HasType context
        (.object signature typeWitness captureWitness payload)
        (.capturing signature.captureUpper (.object signature))

end Value

namespace Term

/-- Typing of the small ANF computation layer.

The capture index describes capabilities used immediately.  A value-member
read first exposes the runtime receiver root `{x}`; the separate `use` rule
can apply the warranted `{x} ≤ x.C` member rule. -/
inductive HasType : {scope : Scope} → Ctx scope →
    Term scope → Capture scope → Ty scope → Type where
  | ret {scope : Scope} {context : Ctx scope} {value : Value scope}
      {type : Ty scope} (valueTyping : Value.HasType context value type) :
      HasType context (.ret value) .empty type
  | select {scope : Scope} {context : Ctx scope}
      {receiver : Path scope} {signature : ObjectSig scope}
      (exposes : ExposesObject context receiver signature) :
      HasType context (.select receiver .v) (.singleton receiver)
        receiver.valueMemberType
  | use {scope : Scope} {context : Ctx scope} {term : Term scope}
      {sourceUse targetUse : Capture scope} {type : Ty scope}
      (termTyping : HasType context term sourceUse type)
      (inclusion : CaptureIncludes context sourceUse targetUse) :
      HasType context term targetUse type

end Term

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
