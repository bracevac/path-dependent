import Coercions.DOT.Captures.Acyclic.Scope

/-!
# Syntax of acyclic DOT with type and capture members

The source has one fixed object signature, with labels `A`, `C`, and `v`.
The bounds of `A` and `C` are independent syntax; formation deliberately
does not demand that either lower endpoint lie below its upper endpoint.
-/

namespace DOTCapture.Acyclic

/-- The two sorts selected by static object members. -/
inductive StaticSort : Type where
  | type
  | capture
deriving DecidableEq, Repr

/-- Paths are variables in the first acyclic layer. -/
inductive Path : Scope → Type where
  | var {scope : Scope} (name : Var scope) : Path scope
deriving DecidableEq

/-- Genuine, sort-indexed member references.

The constructors make `x.A` and `x.C` distinct pieces of syntax.  In
particular, `x.C` is not represented by the singleton capture `{x}`. -/
inductive StaticRef : StaticSort → Scope → Type where
  | typeMember {scope : Scope} (receiver : Path scope) :
      StaticRef .type scope
  | captureMember {scope : Scope} (receiver : Path scope) :
      StaticRef .capture scope
deriving DecidableEq

/-- Capture expressions: empty, union, runtime roots, and selected capture
members. -/
inductive Capture : Scope → Type where
  | empty {scope : Scope} : Capture scope
  | union {scope : Scope} (left right : Capture scope) : Capture scope
  | singleton {scope : Scope} (path : Path scope) : Capture scope
  | ref {scope : Scope} (reference : StaticRef .capture scope) :
      Capture scope
deriving DecidableEq

mutual

/-- Source types.  Object types carry the fixed `A`, `C`, `v` signature;
capturing types retain a capture independently of their shape, and ordinary
arrows provide the computational payload language. -/
inductive Ty : Scope → Type where
  | top {scope : Scope} : Ty scope
  | bot {scope : Scope} : Ty scope
  | one {scope : Scope} : Ty scope
  | ref {scope : Scope} (reference : StaticRef .type scope) : Ty scope
  | arr {scope : Scope} (domain codomain : Ty scope) : Ty scope
  | capturing {scope : Scope} (captures : Capture scope) (shape : Ty scope) :
      Ty scope
  | object {scope : Scope} (signature : ObjectSig scope) : Ty scope

/-- The fixed acyclic object signature
`{ A : L .. U; C : D .. E; v : (x.A)^{x.C} }`.

The value member's type is determined at a receiver path by
`Path.valueMemberType` below, so only its four independent endpoints are
stored here.  There is intentionally no endpoint-consistency field. -/
inductive ObjectSig : Scope → Type where
  | bounds {scope : Scope}
      (typeLower typeUpper : Ty scope)
      (captureLower captureUpper : Capture scope) : ObjectSig scope

end

deriving instance DecidableEq for Ty
deriving instance DecidableEq for ObjectSig

/-- A same-sort expression used by the member-inclusion judgment. -/
inductive StaticExpr : StaticSort → Scope → Type where
  | type {scope : Scope} (type : Ty scope) : StaticExpr .type scope
  | capture {scope : Scope} (capture : Capture scope) :
      StaticExpr .capture scope
deriving DecidableEq

/-- The single value-member label in this fixed source layer. -/
inductive ValueLabel : Type where
  | v
deriving DecidableEq, Repr

mutual

/-- Source values.  Objects remain representation-transparent packages whose
payload is itself a value.  Lambdas contain an ANF computation body and record
ambient, nondependent domain and codomain annotations. -/
inductive Value : Scope → Type where
  | var {scope : Scope} (name : Var scope) : Value scope
  | unit {scope : Scope} : Value scope
  | lam {scope : Scope} (domain codomain : Ty scope)
      (body : Term (scope + 1)) : Value scope
  | object {scope : Scope} (signature : ObjectSig scope)
      (typeWitness : Ty scope) (captureWitness : Capture scope)
      (payload : Value scope) : Value scope

/-- ANF computations.  Applications consume values.  A let records an
ambient result type, making the nonescape boundary for its newest binder
structural in the syntax. -/
inductive Term : Scope → Type where
  | ret {scope : Scope} (value : Value scope) : Term scope
  | select {scope : Scope} (receiver : Path scope) (label : ValueLabel) :
      Term scope
  | app {scope : Scope} (function argument : Value scope) : Term scope
  | let' {scope : Scope} (result : Ty scope) (rhs : Term scope)
      (body : Term (scope + 1)) : Term scope

end

deriving instance DecidableEq for Value
deriving instance DecidableEq for Term

namespace Path

/-- Rename the variable underlying a path. -/
def rename {source target : Scope} (path : Path source)
    (rho : Rename source target) : Path target :=
  match path with
  | .var name => .var (rho.var name)

/-- Weaken a path below one newer object variable. -/
def weaken {scope : Scope} (path : Path scope) : Path (scope + 1) :=
  path.rename Rename.succ

/-- The genuine type-member reference `x.A`. -/
def typeMember {scope : Scope} (receiver : Path scope) :
    StaticRef .type scope :=
  .typeMember receiver

/-- The genuine capture-member reference `x.C`. -/
def captureMember {scope : Scope} (receiver : Path scope) :
    StaticRef .capture scope :=
  .captureMember receiver

/-- The selected type `x.A`. -/
def selectedType {scope : Scope} (receiver : Path scope) : Ty scope :=
  .ref receiver.typeMember

/-- The selected capture `x.C`. -/
def selectedCapture {scope : Scope} (receiver : Path scope) : Capture scope :=
  .ref receiver.captureMember

/-- The declared type of the fixed value member `x.v`: `(x.A)^{x.C}`. -/
def valueMemberType {scope : Scope} (receiver : Path scope) : Ty scope :=
  .capturing receiver.selectedCapture receiver.selectedType

@[simp]
theorem rename_id {scope : Scope} (path : Path scope) :
    path.rename Rename.id = path := by
  cases path
  rfl

@[simp]
theorem rename_comp {first second third : Scope} (path : Path first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (path.rename rho₁).rename rho₂ = path.rename (rho₁.comp rho₂) := by
  cases path
  rfl

end Path

namespace StaticRef

/-- Rename a selected member without changing its sort. -/
def rename {sort : StaticSort} {source target : Scope}
    (reference : StaticRef sort source) (rho : Rename source target) :
    StaticRef sort target :=
  match reference with
  | .typeMember receiver => .typeMember (receiver.rename rho)
  | .captureMember receiver => .captureMember (receiver.rename rho)

/-- Embed a member reference as an expression of the same sort. -/
def expression {sort : StaticSort} {scope : Scope}
    (reference : StaticRef sort scope) : StaticExpr sort scope :=
  match reference with
  | .typeMember receiver => .type (.ref (.typeMember receiver))
  | .captureMember receiver => .capture (.ref (.captureMember receiver))

end StaticRef

mutual

/-- Rename a capture expression. -/
def Capture.rename {source target : Scope} (capture : Capture source)
    (rho : Rename source target) : Capture target :=
  match capture with
  | .empty => .empty
  | .union left right => .union (left.rename rho) (right.rename rho)
  | .singleton path => .singleton (path.rename rho)
  | .ref reference => .ref (reference.rename rho)

/-- Rename a type. -/
def Ty.rename {source target : Scope} (type : Ty source)
    (rho : Rename source target) : Ty target :=
  match type with
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .ref reference => .ref (reference.rename rho)
  | .arr domain codomain => .arr (domain.rename rho) (codomain.rename rho)
  | .capturing captures shape =>
      .capturing (captures.rename rho) (shape.rename rho)
  | .object signature => .object (signature.rename rho)

/-- Rename all four endpoints of an object signature. -/
def ObjectSig.rename {source target : Scope} (signature : ObjectSig source)
    (rho : Rename source target) : ObjectSig target :=
  match signature with
  | .bounds typeLower typeUpper captureLower captureUpper =>
      .bounds (typeLower.rename rho) (typeUpper.rename rho)
        (captureLower.rename rho) (captureUpper.rename rho)

end

namespace Capture

/-- Weaken a capture below one newer object variable. -/
def weaken {scope : Scope} (capture : Capture scope) : Capture (scope + 1) :=
  capture.rename Rename.succ

end Capture

namespace Ty

/-- Weaken a type below one newer object variable. -/
def weaken {scope : Scope} (type : Ty scope) : Ty (scope + 1) :=
  type.rename Rename.succ

/-- Remove one outer capture annotation. -/
def stripCapture {scope : Scope} : Ty scope → Ty scope
  | .capturing _ shape => shape
  | type => type

/-- Project the retained capture of a value type.  Bare shapes are pure. -/
def outerCapture {scope : Scope} : Ty scope → Capture scope
  | .capturing captures _ => captures
  | _ => .empty

/-- Recognize the one object shape whose binding receives the expanded
member layout.  Exactly one outer capture annotation is ignored; nested
capture annotations are not recursively stripped. -/
def objectSignature? {scope : Scope} (type : Ty scope) :
    Option (ObjectSig scope) :=
  match type.stripCapture with
  | .object signature => some signature
  | _ => none

/-- A source type whose term binding occupies one ordinary runtime slot and
does not expose object members. -/
def IsPlain {scope : Scope} (type : Ty scope) : Prop :=
  type.objectSignature? = none

end Ty

namespace ObjectSig

/-- Weaken all signature endpoints below one newer object variable. -/
def weaken {scope : Scope} (signature : ObjectSig scope) :
    ObjectSig (scope + 1) :=
  signature.rename Rename.succ

/-- The lower endpoint `L` of the type member `A`. -/
def typeLower {scope : Scope} : ObjectSig scope → Ty scope
  | .bounds lower _ _ _ => lower

/-- The upper endpoint `U` of the type member `A`. -/
def typeUpper {scope : Scope} : ObjectSig scope → Ty scope
  | .bounds _ upper _ _ => upper

/-- The lower endpoint `D` of the capture member `C`. -/
def captureLower {scope : Scope} : ObjectSig scope → Capture scope
  | .bounds _ _ lower _ => lower

/-- The upper endpoint `E` of the capture member `C`. -/
def captureUpper {scope : Scope} : ObjectSig scope → Capture scope
  | .bounds _ _ _ upper => upper

end ObjectSig

namespace StaticExpr

/-- Rename a sorted member expression. -/
def rename {sort : StaticSort} {source target : Scope}
    (expression : StaticExpr sort source) (rho : Rename source target) :
    StaticExpr sort target :=
  match expression with
  | @StaticExpr.type _ value => .type (value.rename rho)
  | @StaticExpr.capture _ value => .capture (value.rename rho)

end StaticExpr

mutual

/-- Rename a value and every annotation, body, and witness it contains. -/
def Value.rename {source target : Scope} (value : Value source)
    (rho : Rename source target) : Value target :=
  match value with
  | .var name => .var (rho.var name)
  | .unit => .unit
  | .lam domain codomain body =>
      .lam (domain.rename rho) (codomain.rename rho)
        (body.rename rho.lift)
  | .object signature typeWitness captureWitness payload =>
      .object (signature.rename rho) (typeWitness.rename rho)
        (captureWitness.rename rho) (payload.rename rho)

/-- Rename an ANF computation, lifting below each ordinary let binder. -/
def Term.rename {source target : Scope} (term : Term source)
    (rho : Rename source target) : Term target :=
  match term with
  | .ret value => .ret (value.rename rho)
  | .select receiver label => .select (receiver.rename rho) label
  | .app function argument =>
      .app (function.rename rho) (argument.rename rho)
  | .let' result rhs body =>
      .let' (result.rename rho) (rhs.rename rho) (body.rename rho.lift)

end


namespace Value

/-- Weaken a value below one newer ordinary source variable. -/
def weaken {scope : Scope} (value : Value scope) : Value (scope + 1) :=
  value.rename Rename.succ

end Value

namespace Term

/-- Weaken a computation below one newer ordinary source variable. -/
def weaken {scope : Scope} (term : Term scope) : Term (scope + 1) :=
  term.rename Rename.succ

end Term

end DOTCapture.Acyclic
