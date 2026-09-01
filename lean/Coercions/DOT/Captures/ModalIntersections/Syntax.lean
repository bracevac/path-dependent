import Coercions.DOT.Captures.ModalIntersections.Scope
import Coercions.DOT.Captures.Intersections.Signature

/-!
# Static and object syntax for modal captured intersections

The syntax combines lexical static binders with the labeled stable selections
and intersection interfaces of captured DOT.  Intervals keep their lower and
upper endpoints independently optional; object interfaces retain every raw
declaration and leave normalization to a later layer.
-/

namespace DOTCapture.ModalIntersections

abbrev Label := Nat

/-- Stable paths are term variables. -/
inductive Path : Sig → Type where
  | var {scope : Sig} (name : BVar scope .term) : Path scope
deriving DecidableEq

/-- A static reference is either lexical or selected from a stable object
root.  Local references connect declarations inside one raw interface before
its names have been allocated. -/
inductive StaticRef : StaticSort → Sig → Type where
  | bound {scope : Sig} {sort : StaticSort}
      (name : BVar scope (.static sort)) : StaticRef sort scope
  | typeMember {scope : Sig} (receiver : Path scope) (label : Label) :
      StaticRef .type scope
  | captureMember {scope : Sig} (receiver : Path scope) (label : Label) :
      StaticRef .capture scope
  | localTypeMember {scope : Sig} (label : Label) : StaticRef .type scope
  | localCaptureMember {scope : Sig} (label : Label) :
      StaticRef .capture scope
deriving DecidableEq

/-- Access modes in the source separation fragment.  Consumption and killed
bindings are intentionally absent from this access-only layer. -/
inductive CaptureMode : Type where
  | writable
  | readOnly
deriving DecidableEq, Repr

/-- Capture expressions.  `readOnly` restricts access without changing
capability identity; it does not establish resource freshness. -/
inductive Capture : Sig → Type where
  | empty {scope : Sig} : Capture scope
  | union {scope : Sig} (left right : Capture scope) : Capture scope
  | readOnly {scope : Sig} (capture : Capture scope) : Capture scope
  | singleton {scope : Sig} (path : Path scope) : Capture scope
  | ref {scope : Sig} (reference : StaticRef .capture scope) : Capture scope

/-- Captures at distinct list positions are assumed pairwise separate while
checking a modal body.  Equal capture expressions at distinct positions are
still distinct requirements. -/
inductive SeparationContext : Nat → Sig → Type where
  | nil {scope : Sig} : SeparationContext 0 scope
  | cons {scope : Sig} {count : Nat}
      (rest : SeparationContext count scope) (capture : Capture scope) :
      SeparationContext (count + 1) scope

/-- Positional access-mode assumptions carried by a modal requirement. -/
inductive ModeContext : List CaptureMode → Sig → Type where
  | nil {scope : Sig} : ModeContext [] scope
  | cons {scope : Sig} {modes : List CaptureMode} {mode : CaptureMode}
      (rest : ModeContext modes scope) (capture : Capture scope) :
      ModeContext (mode :: modes) scope

/-- The access-only source modal interface: pairwise separation assumptions
and access-mode assumptions. -/
inductive ModalRequirements : Nat → List CaptureMode → Sig → Type where
  | mk {scope : Sig} {separationCount : Nat} {modes : List CaptureMode}
      (separation : SeparationContext separationCount scope)
      (mode : ModeContext modes scope) :
      ModalRequirements separationCount modes scope

mutual

/-- Types with lexical static intervals and labeled captured-DOT objects. -/
inductive Ty : Sig → Type where
  | top {scope : Sig} : Ty scope
  | bot {scope : Sig} : Ty scope
  | one {scope : Sig} : Ty scope
  | ref {scope : Sig} (reference : StaticRef .type scope) : Ty scope
  | arr {scope : Sig} (domain codomain : Ty scope) : Ty scope
  /-- A negative object consumer binds the parameter interface's local-member
  namespace in its result template.  This is distinct from an ordinary
  runtime arrow whose codomain is interpreted in the ambient namespace. -/
  | objectArrow {scope : Sig} (parameter : ObjectType scope)
      (resultTemplate : Ty scope) : Ty scope
  | capturing {scope : Sig} (captures : Capture scope) (shape : Ty scope) :
      Ty scope
  | forallI {scope : Sig} {sort : StaticSort}
      (interval : Interval sort scope)
      (body : Ty (scope ▹ .static sort)) : Ty scope
  | existsI {scope : Sig} {sort : StaticSort}
      (interval : Interval sort scope)
      (body : Ty (scope ▹ .static sort)) : Ty scope
  | modal {scope : Sig} {separationCount : Nat}
      {modes : List CaptureMode}
      (requirements : ModalRequirements separationCount modes scope)
      (body : Ty scope) : Ty scope
  | object {scope : Sig} (object : ObjectType scope) : Ty scope

/-- A static expression indexed by its sort. -/
inductive StaticExpr : StaticSort → Sig → Type where
  | type {scope : Sig} (type : Ty scope) : StaticExpr .type scope
  | capture {scope : Sig} (capture : Capture scope) :
      StaticExpr .capture scope

/-- One independently optional interval endpoint. -/
inductive Endpoint : StaticSort → Sig → Type where
  | none {scope : Sig} {sort : StaticSort} : Endpoint sort scope
  | some {scope : Sig} {sort : StaticSort}
      (expression : StaticExpr sort scope) : Endpoint sort scope

/-- A true interval with independent lower and upper endpoints. -/
inductive Interval : StaticSort → Sig → Type where
  | bounds {scope : Sig} {sort : StaticSort}
      (lower upper : Endpoint sort scope) : Interval sort scope

/-- Raw intersection interfaces.  Repeated labels are intentional. -/
inductive Interface : Sig → Type where
  | empty {scope : Sig} : Interface scope
  | typeMember {scope : Sig} (label : Label) (lower upper : Ty scope) :
      Interface scope
  | captureMember {scope : Sig} (label : Label)
      (lower upper : Capture scope) : Interface scope
  | inter {scope : Sig} (left right : Interface scope) : Interface scope

/-- One static interface and one runtime representation payload type. -/
inductive ObjectType : Sig → Type where
  | mk {scope : Sig} (interface : Interface scope)
      (representation : Ty scope) (outerCapture : Capture scope) :
      ObjectType scope
  /-- An object whose opened representation contract advertises one capture
  while its existential package uses a separately checked ambient envelope. -/
  | mkContracted {scope : Sig} (interface : Interface scope)
      (representation : Ty scope) (outerCapture packageCapture : Capture scope) :
      ObjectType scope

end

deriving instance DecidableEq for Capture
deriving instance DecidableEq for SeparationContext
deriving instance DecidableEq for ModeContext
deriving instance DecidableEq for ModalRequirements
deriving instance DecidableEq for Ty, StaticExpr, Endpoint, Interval,
  Interface, ObjectType

namespace StaticExpr

/-- Embed a lexical static variable as an expression of its intrinsic sort. -/
def bound {scope : Sig} {sort : StaticSort}
    (name : BVar scope (.static sort)) : StaticExpr sort scope :=
  match sort with
  | .type => .type (.ref (.bound name))
  | .capture => .capture (.ref (.bound name))

end StaticExpr

namespace StaticRef

/-- View any static reference as an expression of the same sort. -/
def asExpression {scope : Sig} {sort : StaticSort}
    (reference : StaticRef sort scope) : StaticExpr sort scope :=
  match reference with
  | .bound name => StaticExpr.bound name
  | reference@(.typeMember _ _) => .type (.ref reference)
  | reference@(.captureMember _ _) => .capture (.ref reference)
  | reference@(.localTypeMember _) => .type (.ref reference)
  | reference@(.localCaptureMember _) => .capture (.ref reference)

end StaticRef

namespace Path

def rename {source target : Sig} (path : Path source)
    (rho : Rename source target) : Path target :=
  match path with
  | .var name => .var (rho.var name)

def weaken {scope : Sig} {kind : BinderKind} (path : Path scope) :
    Path (scope ▹ kind) :=
  path.rename DOTCapture.BinderOnly.Rename.succ

end Path

namespace StaticRef

def rename {sort : StaticSort} {source target : Sig}
    (reference : StaticRef sort source) (rho : Rename source target) :
    StaticRef sort target :=
  match reference with
  | .bound name => .bound (rho.var name)
  | .typeMember receiver label => .typeMember (receiver.rename rho) label
  | .captureMember receiver label => .captureMember (receiver.rename rho) label
  | .localTypeMember label => .localTypeMember label
  | .localCaptureMember label => .localCaptureMember label

def weaken {sort : StaticSort} {scope : Sig} {kind : BinderKind}
    (reference : StaticRef sort scope) : StaticRef sort (scope ▹ kind) :=
  reference.rename DOTCapture.BinderOnly.Rename.succ

end StaticRef

mutual

def Capture.rename {source target : Sig} (capture : Capture source)
    (rho : Rename source target) : Capture target :=
  match capture with
  | .empty => .empty
  | .union left right => .union (left.rename rho) (right.rename rho)
  | .readOnly captures => .readOnly (captures.rename rho)
  | .singleton path => .singleton (path.rename rho)
  | .ref reference => .ref (reference.rename rho)

def SeparationContext.rename {count : Nat} {source target : Sig}
    (context : SeparationContext count source) (rho : Rename source target) :
    SeparationContext count target :=
  match context with
  | .nil => .nil
  | .cons rest capture => .cons (rest.rename rho) (capture.rename rho)

def ModeContext.rename {modes : List CaptureMode} {source target : Sig}
    (context : ModeContext modes source) (rho : Rename source target) :
    ModeContext modes target :=
  match context with
  | .nil => .nil
  | .cons rest capture => .cons (rest.rename rho) (capture.rename rho)

def ModalRequirements.rename {separationCount : Nat}
    {modes : List CaptureMode} {source target : Sig}
    (requirements : ModalRequirements separationCount modes source)
    (rho : Rename source target) :
    ModalRequirements separationCount modes target :=
  match requirements with
  | .mk separation mode => .mk (separation.rename rho) (mode.rename rho)

def Ty.rename {source target : Sig} (type : Ty source)
    (rho : Rename source target) : Ty target :=
  match type with
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .ref reference => .ref (reference.rename rho)
  | .arr domain codomain => .arr (domain.rename rho) (codomain.rename rho)
  | .objectArrow parameter resultTemplate =>
      .objectArrow (parameter.rename rho) (resultTemplate.rename rho)
  | .capturing captures shape =>
      .capturing (captures.rename rho) (shape.rename rho)
  | @Ty.forallI _ sort interval body =>
      .forallI (interval.rename rho)
        (body.rename (rho.lift (kind := .static sort)))
  | @Ty.existsI _ sort interval body =>
      .existsI (interval.rename rho)
        (body.rename (rho.lift (kind := .static sort)))
  | .modal requirements body =>
      .modal (requirements.rename rho) (body.rename rho)
  | .object object => .object (object.rename rho)

def StaticExpr.rename {sort : StaticSort} {source target : Sig}
    (expression : StaticExpr sort source) (rho : Rename source target) :
    StaticExpr sort target :=
  match expression with
  | .type type => .type (type.rename rho)
  | .capture capture => .capture (capture.rename rho)

def Endpoint.rename {sort : StaticSort} {source target : Sig}
    (endpoint : Endpoint sort source) (rho : Rename source target) :
    Endpoint sort target :=
  match endpoint with
  | .none => .none
  | .some expression => .some (expression.rename rho)

def Interval.rename {sort : StaticSort} {source target : Sig}
    (interval : Interval sort source) (rho : Rename source target) :
    Interval sort target :=
  match interval with
  | .bounds lower upper =>
      .bounds (lower.rename rho) (upper.rename rho)

def Interface.rename {source target : Sig} (interface : Interface source)
    (rho : Rename source target) : Interface target :=
  match interface with
  | .empty => .empty
  | .typeMember label lower upper =>
      .typeMember label (lower.rename rho) (upper.rename rho)
  | .captureMember label lower upper =>
      .captureMember label (lower.rename rho) (upper.rename rho)
  | .inter left right => .inter (left.rename rho) (right.rename rho)

def ObjectType.rename {source target : Sig} (object : ObjectType source)
    (rho : Rename source target) : ObjectType target :=
  match object with
  | .mk interface representation outerCapture =>
      .mk (interface.rename rho) (representation.rename rho)
        (outerCapture.rename rho)
  | .mkContracted interface representation outerCapture packageCapture =>
      .mkContracted (interface.rename rho) (representation.rename rho)
        (outerCapture.rename rho) (packageCapture.rename rho)

end

namespace Capture

/-! `seq` records call-by-value immediate-use order while keeping an empty
first prediction definitionally neutral. -/

def seq {scope : Sig} : Capture scope → Capture scope → Capture scope
  | .empty, continuation => continuation
  | immediate, continuation => .union immediate continuation

def weaken {scope : Sig} {kind : BinderKind} (capture : Capture scope) :
    Capture (scope ▹ kind) :=
  capture.rename DOTCapture.BinderOnly.Rename.succ

@[simp]
theorem seq_empty {scope : Sig} (continuation : Capture scope) :
    seq .empty continuation = continuation := rfl

end Capture

namespace SeparationContext

def weaken {scope : Sig} {count : Nat} {kind : BinderKind}
    (context : SeparationContext count scope) :
    SeparationContext count (scope ▹ kind) :=
  context.rename DOTCapture.BinderOnly.Rename.succ

end SeparationContext

namespace ModeContext

def weaken {scope : Sig} {modes : List CaptureMode} {kind : BinderKind}
    (context : ModeContext modes scope) : ModeContext modes (scope ▹ kind) :=
  context.rename DOTCapture.BinderOnly.Rename.succ

end ModeContext

namespace ModalRequirements

def weaken {scope : Sig} {separationCount : Nat}
    {modes : List CaptureMode} {kind : BinderKind}
    (requirements : ModalRequirements separationCount modes scope) :
    ModalRequirements separationCount modes (scope ▹ kind) :=
  requirements.rename DOTCapture.BinderOnly.Rename.succ

end ModalRequirements

namespace Ty

def weaken {scope : Sig} {kind : BinderKind} (type : Ty scope) :
    Ty (scope ▹ kind) :=
  type.rename DOTCapture.BinderOnly.Rename.succ

def outerCapture {scope : Sig} : Ty scope → Capture scope
  | .capturing captures _ => captures
  | _ => .empty

def stripCapture {scope : Sig} : Ty scope → Ty scope
  | .capturing _ shape => shape
  | type => type

def precise {scope : Sig} (type : Ty scope) (path : Path scope) : Ty scope :=
  match type with
  | .capturing _ shape => .capturing (.singleton path) shape
  | bare => bare

end Ty

namespace StaticExpr

def weaken {sort : StaticSort} {scope : Sig} {kind : BinderKind}
    (expression : StaticExpr sort scope) : StaticExpr sort (scope ▹ kind) :=
  expression.rename DOTCapture.BinderOnly.Rename.succ

end StaticExpr

namespace Endpoint

def weaken {sort : StaticSort} {scope : Sig} {kind : BinderKind}
    (endpoint : Endpoint sort scope) : Endpoint sort (scope ▹ kind) :=
  endpoint.rename DOTCapture.BinderOnly.Rename.succ

def toOption {sort : StaticSort} {scope : Sig}
    (endpoint : Endpoint sort scope) : Option (StaticExpr sort scope) :=
  match endpoint with
  | .none => Option.none
  | .some expression => Option.some expression

end Endpoint

namespace Interval

def weaken {sort : StaticSort} {scope : Sig} {kind : BinderKind}
    (interval : Interval sort scope) : Interval sort (scope ▹ kind) :=
  interval.rename DOTCapture.BinderOnly.Rename.succ

def unbounded {sort : StaticSort} {scope : Sig} : Interval sort scope :=
  .bounds .none .none

def exact {sort : StaticSort} {scope : Sig}
    (expression : StaticExpr sort scope) : Interval sort scope :=
  .bounds (.some expression) (.some expression)

end Interval

namespace Interface

/-- Bound expressions indexed by the normalization library's two-sort tag.
The cumulative and intersection source layers use isomorphic sort types. -/
def Expr (scope : Sig) : DOTCapture.Intersections.StaticSort → Type
  | .type => StaticExpr .type scope
  | .capture => StaticExpr .capture scope

/-- Normalize an interface by label before any target name is allocated.
Every occurrence is retained; a repeated label at another sort is the only
collection error. -/
def collect {scope : Sig} : Interface scope →
    Except DOTCapture.Intersections.SortConflict
      (DOTCapture.Intersections.Signature (Expr scope))
  | .empty => .ok .empty
  | .typeMember label lower upper =>
      .ok (.singletonType label (.type lower) (.type upper))
  | .captureMember label lower upper =>
      .ok (.singletonCapture label (.capture lower) (.capture upper))
  | .inter left right => do
      let leftSignature ← left.collect
      let rightSignature ← right.collect
      leftSignature.merge? rightSignature

def weaken {scope : Sig} {kind : BinderKind} (interface : Interface scope) :
    Interface (scope ▹ kind) :=
  interface.rename DOTCapture.BinderOnly.Rename.succ

def exactType {scope : Sig} (label : Label) (witness : Ty scope) :
    Interface scope :=
  .typeMember label witness witness

def exactCapture {scope : Sig} (label : Label) (witness : Capture scope) :
    Interface scope :=
  .captureMember label witness witness

end Interface

namespace ObjectType

def interface {scope : Sig} : ObjectType scope → Interface scope
  | .mk interface _ _ => interface
  | .mkContracted interface _ _ _ => interface

def representation {scope : Sig} : ObjectType scope → Ty scope
  | .mk _ representation _ => representation
  | .mkContracted _ representation _ _ => representation

/-- Capture advertised by the opened object's representation contract. -/
def outerCapture {scope : Sig} : ObjectType scope → Capture scope
  | .mk _ _ outerCapture => outerCapture
  | .mkContracted _ _ outerCapture _ => outerCapture

/-- Ambient envelope carried by the existential package. -/
def packageCapture {scope : Sig} : ObjectType scope → Capture scope
  | .mk _ _ outerCapture => outerCapture
  | .mkContracted _ _ _ packageCapture => packageCapture

def weaken {scope : Sig} {kind : BinderKind} (object : ObjectType scope) :
    ObjectType (scope ▹ kind) :=
  object.rename DOTCapture.BinderOnly.Rename.succ

/-- The positive source type of an object with this static interface. -/
def formedType {scope : Sig} : ObjectType scope → Ty scope
  | object@(.mk _ _ outerCapture) =>
      .capturing outerCapture (.object object)
  | object@(.mkContracted _ _ _ packageCapture) =>
      .capturing packageCapture (.object object)

end ObjectType

end DOTCapture.ModalIntersections
