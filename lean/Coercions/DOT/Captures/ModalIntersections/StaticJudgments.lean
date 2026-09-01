import Coercions.DOT.Captures.ModalIntersections.Context

/-!
# Static judgments for cumulative captured DOT

Lexical interval lookup and stable member lookup feed one proof-relevant,
sort-indexed inclusion judgment. Bounds remain independent: neither a lexical
binder nor an object member needs a consistent interval to expose one of its
endpoints.
-/

namespace DOTCapture.ModalIntersections

namespace StaticRef

def expression {scope : Sig} {sort : StaticSort}
    (reference : StaticRef sort scope) : StaticExpr sort scope :=
  reference.asExpression

@[simp]
theorem expression_eq_asExpression {scope : Sig} {sort : StaticSort}
    (reference : StaticRef sort scope) :
    reference.expression = reference.asExpression := rfl

end StaticRef

/-! ## Stable opening of local interface references -/

mutual

def Capture.openAt {scope : Sig} (receiver : Path scope) :
    Capture scope → Capture scope
  | .empty => .empty
  | .union left right => .union (left.openAt receiver) (right.openAt receiver)
  | .readOnly capture => .readOnly (capture.openAt receiver)
  | .singleton path => .singleton path
  | .ref (.localCaptureMember label) =>
      .ref (.captureMember receiver label)
  | .ref reference => .ref reference

def Ty.openAt {scope : Sig} (receiver : Path scope) : Ty scope → Ty scope
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .ref (.localTypeMember label) => .ref (.typeMember receiver label)
  | .ref reference => .ref reference
  | .arr domain codomain =>
      .arr (domain.openAt receiver) (codomain.openAt receiver)
  | .capturing capture shape =>
      .capturing (capture.openAt receiver) (shape.openAt receiver)
  | @Ty.forallI _ sort interval body =>
      .forallI (interval.openAt receiver)
        (body.openAt (receiver.weaken (kind := .static sort)))
  | @Ty.existsI _ sort interval body =>
      .existsI (interval.openAt receiver)
        (body.openAt (receiver.weaken (kind := .static sort)))
  | .object object => .object object

def StaticExpr.openAt {scope : Sig} {sort : StaticSort}
    (expression : StaticExpr sort scope) (receiver : Path scope) :
    StaticExpr sort scope :=
  match expression with
  | .type type => .type (type.openAt receiver)
  | .capture capture => .capture (capture.openAt receiver)

def Endpoint.openAt {scope : Sig} {sort : StaticSort}
    (endpoint : Endpoint sort scope) (receiver : Path scope) :
    Endpoint sort scope :=
  match endpoint with
  | .none => .none
  | .some expression => .some (expression.openAt receiver)

def Interval.openAt {scope : Sig} {sort : StaticSort}
    (interval : Interval sort scope) (receiver : Path scope) :
    Interval sort scope :=
  match interval with
  | .bounds lower upper =>
      .bounds (lower.openAt receiver) (upper.openAt receiver)

end

namespace ObjectType

def interface {scope : Sig} : ObjectType scope → Interface scope
  | .mk interface _ _ => interface

def representation {scope : Sig} : ObjectType scope → Ty scope
  | .mk _ representation _ => representation

def outerCapture {scope : Sig} : ObjectType scope → Capture scope
  | .mk _ _ outerCapture => outerCapture

def representationAt {scope : Sig} (object : ObjectType scope)
    (receiver : Path scope) : Ty scope :=
  object.representation.openAt receiver

end ObjectType

namespace Interface

/-- One exact type-member occurrence in an unnormalized intersection tree. -/
inductive HasTypeOccurrence {scope : Sig} : Interface scope →
    Label → Ty scope → Ty scope → Type where
  | here {label : Label} {lower upper : Ty scope} :
      HasTypeOccurrence (.typeMember label lower upper) label lower upper
  | left {left right : Interface scope} {label : Label}
      {lower upper : Ty scope}
      (occurrence : HasTypeOccurrence left label lower upper) :
      HasTypeOccurrence (.inter left right) label lower upper
  | right {left right : Interface scope} {label : Label}
      {lower upper : Ty scope}
      (occurrence : HasTypeOccurrence right label lower upper) :
      HasTypeOccurrence (.inter left right) label lower upper

/-- One exact capture-member occurrence in an unnormalized intersection. -/
inductive HasCaptureOccurrence {scope : Sig} : Interface scope →
    Label → Capture scope → Capture scope → Type where
  | here {label : Label} {lower upper : Capture scope} :
      HasCaptureOccurrence (.captureMember label lower upper)
        label lower upper
  | left {left right : Interface scope} {label : Label}
      {lower upper : Capture scope}
      (occurrence : HasCaptureOccurrence left label lower upper) :
      HasCaptureOccurrence (.inter left right) label lower upper
  | right {left right : Interface scope} {label : Label}
      {lower upper : Capture scope}
      (occurrence : HasCaptureOccurrence right label lower upper) :
      HasCaptureOccurrence (.inter left right) label lower upper

end Interface

/-- A stable variable exposes the complete object stored in its binding. -/
inductive ExposesObject {scope : Sig} (context : Ctx scope) :
    Path scope → ObjectType scope → Type where
  | variable {name : BVar scope .term} {object : ObjectType scope}
      (found : (context.lookupTerm name).stripCapture = .object object) :
      ExposesObject context (.var name) object

/-- A lexical interval or stable member supplies one lower endpoint. -/
inductive HasLower {scope : Sig} (context : Ctx scope) :
    {sort : StaticSort} → StaticRef sort scope → StaticExpr sort scope →
      Type where
  | bound {sort : StaticSort} {index : BVar scope (.static sort)}
      {lower : StaticExpr sort scope} {upper : Endpoint sort scope}
      (found : context.lookupStatic index = .bounds (.some lower) upper) :
      HasLower context (.bound index) lower
  | typeMember {receiver : Path scope} {object : ObjectType scope}
      {label : Label} {lower upper : Ty scope}
      (exposes : ExposesObject context receiver object)
      (occurrence : object.interface.HasTypeOccurrence label lower upper) :
      HasLower context (.typeMember receiver label)
        (.type (lower.openAt receiver))
  | captureMember {receiver : Path scope} {object : ObjectType scope}
      {label : Label} {lower upper : Capture scope}
      (exposes : ExposesObject context receiver object)
      (occurrence : object.interface.HasCaptureOccurrence label lower upper) :
      HasLower context (.captureMember receiver label)
        (.capture (lower.openAt receiver))

/-- A lexical interval or stable member supplies one upper endpoint. -/
inductive HasUpper {scope : Sig} (context : Ctx scope) :
    {sort : StaticSort} → StaticRef sort scope → StaticExpr sort scope →
      Type where
  | bound {sort : StaticSort} {index : BVar scope (.static sort)}
      {lower : Endpoint sort scope} {upper : StaticExpr sort scope}
      (found : context.lookupStatic index = .bounds lower (.some upper)) :
      HasUpper context (.bound index) upper
  | typeMember {receiver : Path scope} {object : ObjectType scope}
      {label : Label} {lower upper : Ty scope}
      (exposes : ExposesObject context receiver object)
      (occurrence : object.interface.HasTypeOccurrence label lower upper) :
      HasUpper context (.typeMember receiver label)
        (.type (upper.openAt receiver))
  | captureMember {receiver : Path scope} {object : ObjectType scope}
      {label : Label} {lower upper : Capture scope}
      (exposes : ExposesObject context receiver object)
      (occurrence : object.interface.HasCaptureOccurrence label lower upper) :
      HasUpper context (.captureMember receiver label)
        (.capture (upper.openAt receiver))

/-! ## Proof-relevant inclusion -/

inductive Includes {scope : Sig} (context : Ctx scope) :
    {sort : StaticSort} → StaticExpr sort scope → StaticExpr sort scope →
      Type where
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
  | typeArrow {sourceDomain targetDomain sourceCodomain targetCodomain :
        Ty scope}
      (domain : Includes context (.type targetDomain) (.type sourceDomain))
      (codomain : Includes context (.type sourceCodomain)
        (.type targetCodomain)) :
      Includes context (.type (.arr sourceDomain sourceCodomain))
        (.type (.arr targetDomain targetCodomain))
  | typeCapturing {sourceCaptures targetCaptures : Capture scope}
      {sourceShape targetShape : Ty scope}
      (captures : Includes context (.capture sourceCaptures)
        (.capture targetCaptures))
      (shape : Includes context (.type sourceShape) (.type targetShape)) :
      Includes context (.type (.capturing sourceCaptures sourceShape))
        (.type (.capturing targetCaptures targetShape))
  | captureEmpty {capture : Capture scope} :
      Includes context (.capture .empty) (.capture capture)
  | captureUnionLeft {left right : Capture scope} :
      Includes context (.capture left) (.capture (.union left right))
  | captureUnionRight {left right : Capture scope} :
      Includes context (.capture right) (.capture (.union left right))
  | captureUnionElim {left right target : Capture scope}
      (fromLeft : Includes context (.capture left) (.capture target))
      (fromRight : Includes context (.capture right) (.capture target)) :
      Includes context (.capture (.union left right)) (.capture target)
  | captureReadOnly {capture : Capture scope} :
      Includes context (.capture (.readOnly capture)) (.capture capture)
  | captureReadOnlyMono {lower upper : Capture scope}
      (subcapture : Includes context (.capture lower) (.capture upper)) :
      Includes context (.capture (.readOnly lower))
        (.capture (.readOnly upper))
  | captureVariable {name : BVar scope .term}
      {captures : Capture scope} {shape : Ty scope}
      (found : context.lookupTerm name = .capturing captures shape) :
      Includes context (.capture (.singleton (.var name)))
        (.capture captures)
  | payloadRoot {receiver : Path scope} {object : ObjectType scope}
      (exposes : ExposesObject context receiver object) :
      Includes context (.capture (.singleton receiver))
        (.capture (object.representationAt receiver).outerCapture)

abbrev TypeIncludes {scope : Sig} (context : Ctx scope)
    (source target : Ty scope) : Type :=
  Includes context (.type source) (.type target)

abbrev CaptureIncludes {scope : Sig} (context : Ctx scope)
    (source target : Capture scope) : Type :=
  Includes context (.capture source) (.capture target)

/-- Ordinary term binders exclude precisely object-shaped values; an object
must be opened by `objectLet` before it can become a stable member root. -/
def Plain {scope : Sig} (type : Ty scope) : Prop :=
  match type.stripCapture with
  | .object _ => False
  | _ => True

end DOTCapture.ModalIntersections
