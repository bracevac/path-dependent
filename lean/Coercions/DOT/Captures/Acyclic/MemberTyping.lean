import Coercions.DOT.Captures.Acyclic.Context

/-!
# Selected-member typing and inclusion

An object path exposes four independent assumptions:
`L ≤ x.A ≤ U` and `D ≤ x.C ≤ E`.  The fixed value member has
declared type `(x.A)^{x.C}`.  Reading that payload warrants the directed root
contraction `{x} ≤ x.C`; there is deliberately no constructor for the
reverse direction.
-/

namespace DOTCapture.Acyclic

/-- A path exposes an object signature when the shape of its context binding
is that object type.  The retained outer capture, if any, is irrelevant to
member lookup. -/
inductive ExposesObject {scope : Scope} (context : Ctx scope) :
    Path scope → ObjectSig scope → Type where
  | variable {name : Var scope} {signature : ObjectSig scope}
      (found : (context.lookup name).stripCapture = .object signature) :
      ExposesObject context (.var name) signature

/-- A selected member supplies its lower endpoint.  Type and capture members
remain intrinsically sort-correct. -/
inductive HasLower {scope : Scope} (context : Ctx scope) :
    {sort : StaticSort} → StaticRef sort scope →
      StaticExpr sort scope → Type where
  | typeMember {receiver : Path scope} {signature : ObjectSig scope}
      (exposes : ExposesObject context receiver signature) :
      HasLower context receiver.typeMember (.type signature.typeLower)
  | captureMember {receiver : Path scope} {signature : ObjectSig scope}
      (exposes : ExposesObject context receiver signature) :
      HasLower context receiver.captureMember
        (.capture signature.captureLower)

/-- A selected member independently supplies its upper endpoint. -/
inductive HasUpper {scope : Scope} (context : Ctx scope) :
    {sort : StaticSort} → StaticRef sort scope →
      StaticExpr sort scope → Type where
  | typeMember {receiver : Path scope} {signature : ObjectSig scope}
      (exposes : ExposesObject context receiver signature) :
      HasUpper context receiver.typeMember (.type signature.typeUpper)
  | captureMember {receiver : Path scope} {signature : ObjectSig scope}
      (exposes : ExposesObject context receiver signature) :
      HasUpper context receiver.captureMember
        (.capture signature.captureUpper)

/-- Proof-relevant, sort-preserving inclusion. -/
inductive Includes {scope : Scope} (context : Ctx scope) :
    {sort : StaticSort} → StaticExpr sort scope →
      StaticExpr sort scope → Type where
  | refl {sort : StaticSort} {expression : StaticExpr sort scope} :
      Includes context expression expression
  | trans {sort : StaticSort} {source middle target : StaticExpr sort scope}
      (first : Includes context source middle)
      (second : Includes context middle target) :
      Includes context source target
  | lower {sort : StaticSort} {reference : StaticRef sort scope}
      {endpoint : StaticExpr sort scope}
      (bound : HasLower context reference endpoint) :
      Includes context endpoint reference.expression
  | upper {sort : StaticSort} {reference : StaticRef sort scope}
      {endpoint : StaticExpr sort scope}
      (bound : HasUpper context reference endpoint) :
      Includes context reference.expression endpoint
  | typeTop {type : Ty scope} :
      Includes context (.type type) (.type .top)
  | typeBottom {type : Ty scope} :
      Includes context (.type .bot) (.type type)
  | typeCapturing {sourceCaptures targetCaptures : Capture scope}
      {sourceShape targetShape : Ty scope}
      (captures : Includes context (.capture sourceCaptures)
        (.capture targetCaptures))
      (shape : Includes context (.type sourceShape) (.type targetShape)) :
      Includes context (.type (.capturing sourceCaptures sourceShape))
        (.type (.capturing targetCaptures targetShape))
  | captureEmpty {captures : Capture scope} :
      Includes context (.capture .empty) (.capture captures)
  | captureUnionLeft {left right : Capture scope} :
      Includes context (.capture left) (.capture (.union left right))
  | captureUnionRight {left right : Capture scope} :
      Includes context (.capture right) (.capture (.union left right))
  | captureUnionElim {left right target : Capture scope}
      (fromLeft : Includes context (.capture left) (.capture target))
      (fromRight : Includes context (.capture right) (.capture target)) :
      Includes context (.capture (.union left right)) (.capture target)
  /-- Reading the fixed payload of an exposed receiver contracts the runtime
  receiver root to the receiver's abstract capture member. -/
  | payloadRoot {receiver : Path scope} {signature : ObjectSig scope}
      (exposes : ExposesObject context receiver signature) :
      Includes context (.capture (.singleton receiver))
        (.capture receiver.selectedCapture)

/-- Type-specialized inclusion. -/
abbrev TypeIncludes {scope : Scope} (context : Ctx scope)
    (source target : Ty scope) : Type :=
  Includes context (.type source) (.type target)

/-- Capture-specialized inclusion. -/
abbrev CaptureIncludes {scope : Scope} (context : Ctx scope)
    (source target : Capture scope) : Type :=
  Includes context (.capture source) (.capture target)

namespace ExposesObject

/-- Every exposed object supplies `L ≤ x.A`. -/
def typeLower {scope : Scope} {context : Ctx scope}
    {receiver : Path scope} {signature : ObjectSig scope}
    (exposes : ExposesObject context receiver signature) :
    TypeIncludes context signature.typeLower receiver.selectedType :=
  .lower (.typeMember exposes)

/-- Every exposed object independently supplies `x.A ≤ U`. -/
def typeUpper {scope : Scope} {context : Ctx scope}
    {receiver : Path scope} {signature : ObjectSig scope}
    (exposes : ExposesObject context receiver signature) :
    TypeIncludes context receiver.selectedType signature.typeUpper :=
  .upper (.typeMember exposes)

/-- Every exposed object supplies `D ≤ x.C`. -/
def captureLower {scope : Scope} {context : Ctx scope}
    {receiver : Path scope} {signature : ObjectSig scope}
    (exposes : ExposesObject context receiver signature) :
    CaptureIncludes context signature.captureLower receiver.selectedCapture :=
  .lower (.captureMember exposes)

/-- Every exposed object independently supplies `x.C ≤ E`. -/
def captureUpper {scope : Scope} {context : Ctx scope}
    {receiver : Path scope} {signature : ObjectSig scope}
    (exposes : ExposesObject context receiver signature) :
    CaptureIncludes context receiver.selectedCapture signature.captureUpper :=
  .upper (.captureMember exposes)

/-- The warranted, one-way payload-root rule `{x} ≤ x.C`. -/
def payloadRoot {scope : Scope} {context : Ctx scope}
    {receiver : Path scope} {signature : ObjectSig scope}
    (exposes : ExposesObject context receiver signature) :
    CaptureIncludes context (.singleton receiver) receiver.selectedCapture :=
  .payloadRoot exposes

end ExposesObject

end DOTCapture.Acyclic
