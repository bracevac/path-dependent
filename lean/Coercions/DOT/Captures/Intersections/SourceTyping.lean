import Coercions.DOT.Captures.Intersections.SourceMetatheory

/-!
# Static typing for captured intersection objects

The M11 source context stores ordinary term bindings.  An object binding
exposes every retained interval occurrence in its interface.  Repeated
declarations therefore justify several lower and upper rules for one stable
`(path, label)` selection; the selection itself remains unique.
-/

namespace DOTCapture.Intersections.Source

namespace Capture

/-- Sequence a computation's immediate use before its continuation use. -/
def seq {scope : Scope} : Capture scope -> Capture scope -> Capture scope
  | .empty, continuation => continuation
  | immediate, continuation => .union immediate continuation

end Capture

namespace Ty

/-- Remove only the outer capture annotation. -/
def stripCapture {scope : Scope} : Ty scope -> Ty scope
  | .capturing _ shape => shape
  | type => type

/-- The capture retained by a value of this type. -/
def outerCapture {scope : Scope} : Ty scope -> Capture scope
  | .capturing captures _ => captures
  | _ => .empty

/-- Ordinary runtime binders cannot introduce a stable member root. -/
inductive IsPlain {scope : Scope} : Ty scope -> Prop where
  | top : IsPlain .top
  | bot : IsPlain .bot
  | one : IsPlain .one
  | ref {reference : StaticRef .type scope} : IsPlain (.ref reference)
  | arr {domain codomain : Ty scope} : IsPlain (.arr domain codomain)
  | capturing {captures : Capture scope} {shape : Ty scope}
      (shapePlain : IsPlain shape) : IsPlain (.capturing captures shape)

end Ty

mutual

/-- Open local capture-member references at one stable object root. -/
def Capture.openAt {scope : Scope} (receiver : Path scope) :
    Capture scope -> Capture scope
  | .empty => .empty
  | .union left right =>
      .union (Capture.openAt receiver left) (Capture.openAt receiver right)
  | .singleton path => .singleton path
  | .ref (.localCaptureMember label) =>
      .ref (.captureMember receiver label)
  | .ref (.captureMember path label) => .ref (.captureMember path label)

/-- Open local type- and capture-member references at one stable object root. -/
def Ty.openAt {scope : Scope} (receiver : Path scope) : Ty scope -> Ty scope
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .ref (.localTypeMember label) => .ref (.typeMember receiver label)
  | .ref (.typeMember path label) => .ref (.typeMember path label)
  | .arr domain codomain =>
      .arr (Ty.openAt receiver domain) (Ty.openAt receiver codomain)
  | .capturing captures shape =>
      .capturing (Capture.openAt receiver captures) (Ty.openAt receiver shape)
  | .object object => .object object

end

namespace ObjectType

/-- Positive object types retain the declared ambient capture outside the
existential static interface. -/
def formedType {scope : Scope} (object : ObjectType scope) : Ty scope :=
  .capturing (match object with | .mk _ _ capture => capture) (.object object)

def interface {scope : Scope} : ObjectType scope -> Interface scope
  | .mk interface _ _ => interface

def representation {scope : Scope} : ObjectType scope -> Ty scope
  | .mk _ representation _ => representation

def outerCapture {scope : Scope} : ObjectType scope -> Capture scope
  | .mk _ _ outerCapture => outerCapture

end ObjectType

/-! ## Source contexts and stable object exposure -/

/-- A source context aligned with its term-variable scope. -/
inductive Ctx : Scope -> Type where
  | nil : Ctx 0
  | extend {scope : Scope} (outer : Ctx scope) (type : Ty scope) :
      Ctx (scope + 1)
deriving DecidableEq

namespace Ctx

def extendTerm {scope : Scope} (context : Ctx scope) (type : Ty scope) :
    Ctx (scope + 1) :=
  .extend context type

/-- Lookup weakens the stored type into the complete ambient term scope. -/
def lookup {scope : Scope} (context : Ctx scope) (name : Var scope) : Ty scope :=
  match context, name with
  | .extend _ type, .here => type.rename DOTCapture.Acyclic.Rename.succ
  | .extend outer _, .there older =>
      (lookup outer older).rename DOTCapture.Acyclic.Rename.succ

@[simp]
theorem lookup_here {scope : Scope} (context : Ctx scope) (type : Ty scope) :
    (context.extendTerm type).lookup (.here : Var (scope + 1)) =
      type.rename DOTCapture.Acyclic.Rename.succ := rfl

@[simp]
theorem lookup_there {scope : Scope} (context : Ctx scope) (type : Ty scope)
    (name : Var scope) :
    (context.extendTerm type).lookup (.there name) =
      (context.lookup name).rename DOTCapture.Acyclic.Rename.succ := rfl

end Ctx

namespace Interface

/-- One exact type-member occurrence in an unnormalized intersection tree. -/
inductive HasTypeOccurrence {scope : Scope} : Interface scope ->
    Label -> Ty scope -> Ty scope -> Type where
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

/-- One exact capture-member occurrence in an unnormalized intersection
tree. -/
inductive HasCaptureOccurrence {scope : Scope} : Interface scope ->
    Label -> Capture scope -> Capture scope -> Type where
  | here {label : Label} {lower upper : Capture scope} :
      HasCaptureOccurrence (.captureMember label lower upper) label lower upper
  | left {left right : Interface scope} {label : Label}
      {lower upper : Capture scope}
      (occurrence : HasCaptureOccurrence left label lower upper) :
      HasCaptureOccurrence (.inter left right) label lower upper
  | right {left right : Interface scope} {label : Label}
      {lower upper : Capture scope}
      (occurrence : HasCaptureOccurrence right label lower upper) :
      HasCaptureOccurrence (.inter left right) label lower upper

end Interface

namespace StaticRef

/-- The intrinsically sorted selection expression named by a reference. -/
def expression {sort : StaticSort} {scope : Scope}
    (reference : StaticRef sort scope) : StaticExpr sort scope := by
  cases reference with
  | typeMember receiver label =>
      exact .type (.ref (.typeMember receiver label))
  | captureMember receiver label =>
      exact .capture (.ref (.captureMember receiver label))
  | localTypeMember label =>
      exact .type (.ref (.localTypeMember label))
  | localCaptureMember label =>
      exact .capture (.ref (.localCaptureMember label))

end StaticRef

/-- A stable path exposes the complete object metadata stored in its context
binding. -/
inductive ExposesObject {scope : Scope} (context : Ctx scope) :
    Path scope -> ObjectType scope -> Type where
  | variable {name : Var scope} {object : ObjectType scope}
      (found : (context.lookup name).stripCapture = .object object) :
      ExposesObject context (.var name) object

/-- A selected member supplies each retained lower endpoint independently. -/
inductive HasLower {scope : Scope} (context : Ctx scope) :
    {sort : StaticSort} -> StaticRef sort scope -> StaticExpr sort scope ->
      Type where
  | typeMember {receiver : Path scope} {object : ObjectType scope}
      {label : Label} {lower upper : Ty scope}
      (exposes : ExposesObject context receiver object)
      (occurrence : object.interface.HasTypeOccurrence label lower upper) :
      HasLower context (.typeMember receiver label)
        (.type (Ty.openAt receiver lower))
  | captureMember {receiver : Path scope} {object : ObjectType scope}
      {label : Label} {lower upper : Capture scope}
      (exposes : ExposesObject context receiver object)
      (occurrence : object.interface.HasCaptureOccurrence label lower upper) :
      HasLower context (.captureMember receiver label)
        (.capture (Capture.openAt receiver lower))

/-- A selected member supplies each retained upper endpoint independently. -/
inductive HasUpper {scope : Scope} (context : Ctx scope) :
    {sort : StaticSort} -> StaticRef sort scope -> StaticExpr sort scope ->
      Type where
  | typeMember {receiver : Path scope} {object : ObjectType scope}
      {label : Label} {lower upper : Ty scope}
      (exposes : ExposesObject context receiver object)
      (occurrence : object.interface.HasTypeOccurrence label lower upper) :
      HasUpper context (.typeMember receiver label)
        (.type (Ty.openAt receiver upper))
  | captureMember {receiver : Path scope} {object : ObjectType scope}
      {label : Label} {lower upper : Capture scope}
      (exposes : ExposesObject context receiver object)
      (occurrence : object.interface.HasCaptureOccurrence label lower upper) :
      HasUpper context (.captureMember receiver label)
        (.capture (Capture.openAt receiver upper))

/-! ## Proof-relevant inclusion -/

/-- Sort-preserving inclusion for the M11 source layer.  Bounds are selected
from exact occurrences rather than from synthesized merged endpoints. -/
inductive Includes {scope : Scope} (context : Ctx scope) :
    {sort : StaticSort} -> StaticExpr sort scope -> StaticExpr sort scope ->
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

abbrev TypeIncludes {scope : Scope} (context : Ctx scope)
    (source target : Ty scope) : Type :=
  Includes context (.type source) (.type target)

abbrev CaptureIncludes {scope : Scope} (context : Ctx scope)
    (source target : Capture scope) : Type :=
  Includes context (.capture source) (.capture target)

end DOTCapture.Intersections.Source
