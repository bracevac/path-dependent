import Coercions.DOT.Captures.BinderOnly.Scope

/-!
# Binder-only DOT-with-captures syntax

The syntax is intentionally the lexical-binder front edge of a future DOT
calculus.  Paths and sorted static references are distinct nodes so that
member selection can be added without changing captures, types, or interval
binders.
-/

namespace DOTCapture.BinderOnly

/-- Paths are variables in the binder-only fragment.  Later object syntax
will extend this datatype with field selection; its exhaustive structural
operations will then be extended in the same change. -/
inductive Path : Sig → Type where
  | var {scope : Sig} (name : BVar scope .term) : Path scope
deriving DecidableEq

/-- A statically sorted reference.  A binder is the only reference form in
this fragment; future type and capture members will add path selections such
as `x.A` and `x.C` here. -/
inductive StaticRef : StaticSort → Sig → Type where
  | bound {scope : Sig} {sort : StaticSort}
      (name : BVar scope (.static sort)) : StaticRef sort scope
deriving DecidableEq

mutual

/-- Capture expressions contain capabilities, abstract capture references,
and finite unions.  In particular, the source has no capture-top expression. -/
inductive Capture : Sig → Type where
  | empty {scope : Sig} : Capture scope
  | union {scope : Sig} (left right : Capture scope) : Capture scope
  | singleton {scope : Sig} (path : Path scope) : Capture scope
  | ref {scope : Sig} (name : StaticRef .capture scope) : Capture scope

/-- Types of the binder-only source.  Static quantifiers bind one true
interval; later DOT members can reuse the same interval representation. -/
inductive Ty : Sig → Type where
  | top {scope : Sig} : Ty scope
  | bot {scope : Sig} : Ty scope
  | one {scope : Sig} : Ty scope
  | ref {scope : Sig} (name : StaticRef .type scope) : Ty scope
  | capturing {scope : Sig} (captures : Capture scope)
      (shape : Ty scope) : Ty scope
  | arr {scope : Sig} (domain codomain : Ty scope) : Ty scope
  | forallI {scope : Sig} {sort : StaticSort}
      (interval : Interval sort scope)
      (body : Ty (scope ▹ .static sort)) : Ty scope
  | existsI {scope : Sig} {sort : StaticSort}
      (interval : Interval sort scope)
      (body : Ty (scope ▹ .static sort)) : Ty scope

/-- A source static expression indexed by its sort. -/
inductive StaticExpr : StaticSort → Sig → Type where
  | type {scope : Sig} (type : Ty scope) : StaticExpr .type scope
  | capture {scope : Sig} (capture : Capture scope) :
      StaticExpr .capture scope

/-- One independently optional endpoint of an interval.

This source-owned option type is part of the mutual syntax so that an
endpoint can contain a recursively formed type. -/
inductive Endpoint : StaticSort → Sig → Type where
  | none {scope : Sig} {sort : StaticSort} : Endpoint sort scope
  | some {scope : Sig} {sort : StaticSort}
      (expression : StaticExpr sort scope) : Endpoint sort scope

/-- Independent optional lower and upper endpoints for a static variable.

Missing endpoints express one-sided or fully open intervals.  There is
deliberately no field requiring the lower endpoint to be below the upper: an
inconsistent interval is valid syntax whose assumptions may have no model. -/
inductive Interval : StaticSort → Sig → Type where
  | bounds {scope : Sig} {sort : StaticSort}
      (lower upper : Endpoint sort scope) : Interval sort scope

end

deriving instance DecidableEq for Capture
deriving instance DecidableEq for Ty
deriving instance DecidableEq for StaticExpr
deriving instance DecidableEq for Endpoint
deriving instance DecidableEq for Interval

namespace StaticExpr

/-- Embed a bound static variable as an expression of its intrinsic sort. -/
def bound {scope : Sig} {sort : StaticSort}
    (name : BVar scope (.static sort)) : StaticExpr sort scope :=
  match sort with
  | .type => .type (.ref (.bound name))
  | .capture => .capture (.ref (.bound name))

end StaticExpr

namespace StaticRef

/-- View a static reference as an expression of the same sort. -/
def asExpression {scope : Sig} {sort : StaticSort}
    (reference : StaticRef sort scope) : StaticExpr sort scope :=
  match reference with
  | .bound name => StaticExpr.bound name

end StaticRef

namespace Path

/-- Rename the variable underlying a path. -/
def rename {source target : Sig} (path : Path source)
    (rho : Rename source target) : Path target :=
  match path with
  | .var name => .var (rho.var name)

/-- Weaken a path below one binder. -/
def weaken {scope : Sig} {kind : BinderKind} (path : Path scope) :
    Path (scope ▹ kind) :=
  path.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} (path : Path scope) :
    path.rename Rename.id = path := by
  cases path
  rfl

@[simp]
theorem rename_comp {first second third : Sig} (path : Path first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (path.rename rho₁).rename rho₂ = path.rename (rho₁.comp rho₂) := by
  cases path
  rfl

end Path

namespace StaticRef

/-- Rename a sorted static reference without changing its sort. -/
def rename {sort : StaticSort} {source target : Sig}
    (reference : StaticRef sort source) (rho : Rename source target) :
    StaticRef sort target :=
  match reference with
  | .bound name => .bound (rho.var name)

/-- Weaken a static reference below one binder. -/
def weaken {sort : StaticSort} {scope : Sig} {kind : BinderKind}
    (reference : StaticRef sort scope) : StaticRef sort (scope ▹ kind) :=
  reference.rename Rename.succ

@[simp]
theorem rename_id {sort : StaticSort} {scope : Sig}
    (reference : StaticRef sort scope) :
    reference.rename Rename.id = reference := by
  cases reference
  rfl

@[simp]
theorem rename_comp {sort : StaticSort} {first second third : Sig}
    (reference : StaticRef sort first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (reference.rename rho₁).rename rho₂ =
      reference.rename (rho₁.comp rho₂) := by
  cases reference
  rfl

end StaticRef

mutual

/-- Rename a capture expression. -/
def Capture.rename {source target : Sig} (capture : Capture source)
    (rho : Rename source target) : Capture target :=
  match capture with
  | .empty => .empty
  | .union left right => .union (left.rename rho) (right.rename rho)
  | .singleton path => .singleton (path.rename rho)
  | .ref name => .ref (name.rename rho)

/-- Rename a type, lifting below static quantifiers. -/
def Ty.rename {source target : Sig} (type : Ty source)
    (rho : Rename source target) : Ty target :=
  match type with
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .ref name => .ref (name.rename rho)
  | .capturing captures shape =>
      .capturing (captures.rename rho) (shape.rename rho)
  | .arr domain codomain => .arr (domain.rename rho) (codomain.rename rho)
  | @Ty.forallI _ sort interval body =>
      .forallI (interval.rename rho)
        (body.rename (rho.lift (kind := .static sort)))
  | @Ty.existsI _ sort interval body =>
      .existsI (interval.rename rho)
        (body.rename (rho.lift (kind := .static sort)))

/-- Rename a sorted static expression. -/
def StaticExpr.rename {sort : StaticSort} {source target : Sig}
    (expression : StaticExpr sort source) (rho : Rename source target) :
    StaticExpr sort target :=
  match expression with
  | .type type => .type (type.rename rho)
  | .capture capture => .capture (capture.rename rho)

/-- Rename an optional interval endpoint. -/
def Endpoint.rename {sort : StaticSort} {source target : Sig}
    (endpoint : Endpoint sort source) (rho : Rename source target) :
    Endpoint sort target :=
  match endpoint with
  | .none => .none
  | .some expression => .some (expression.rename rho)

/-- Rename both optional endpoints of an interval. -/
def Interval.rename {sort : StaticSort} {source target : Sig}
    (interval : Interval sort source) (rho : Rename source target) :
    Interval sort target :=
  match interval with
  | .bounds lower upper =>
      .bounds (lower.rename rho) (upper.rename rho)

end

namespace Capture

/-- Weaken a capture expression below one binder. -/
def weaken {scope : Sig} {kind : BinderKind} (capture : Capture scope) :
    Capture (scope ▹ kind) :=
  capture.rename Rename.succ

end Capture

namespace Ty

/-- Weaken a type below one binder. -/
def weaken {scope : Sig} {kind : BinderKind} (type : Ty scope) :
    Ty (scope ▹ kind) :=
  type.rename Rename.succ

/-- The capabilities retained by the outermost capture annotation.

For a bare type this projection returns the empty capture as the neutral
accounting default; in particular, a bare callable type is treated as
pure/untracked by application prediction.  That default is descriptive, not
evidence that a term variable bound at a bare type contracts to empty:
`captureVariable` requires an explicit `capturing` binding. -/
def outerCapture {scope : Sig} : Ty scope → Capture scope
  | .capturing captures _ => captures
  | _ => .empty

/-- Remove one outer capture annotation and expose the underlying shape.
Bare types are already shapes and are returned unchanged. -/
def stripCapture {scope : Sig} : Ty scope → Ty scope
  | .capturing _ shape => shape
  | type => type

/-- Give a variable its precise singleton capture when its declared type has
an outer capture annotation.  A variable at a bare type, including a callable
shape, remains pure/untracked and, in particular, its binding exports no
logical capture-contraction evidence.

This is the source-level capture-prediction rule: the declaration records an
upper approximation of the value's retained capabilities, while a variable
occurrence names the value itself. -/
def precise {scope : Sig} (type : Ty scope) (path : Path scope) : Ty scope :=
  match type with
  | .capturing _ shape => .capturing (.singleton path) shape
  | bare => bare

@[simp]
theorem outerCapture_rename {source target : Sig} (type : Ty source)
    (rho : Rename source target) :
    (type.rename rho).outerCapture = type.outerCapture.rename rho := by
  cases type <;> rfl

@[simp]
theorem stripCapture_rename {source target : Sig} (type : Ty source)
    (rho : Rename source target) :
    (type.rename rho).stripCapture = type.stripCapture.rename rho := by
  cases type <;> rfl

@[simp]
theorem precise_rename {source target : Sig} (type : Ty source)
    (path : Path source) (rho : Rename source target) :
    (type.precise path).rename rho =
      (type.rename rho).precise (path.rename rho) := by
  cases type <;> rfl

end Ty

namespace StaticExpr

/-- Weaken a static expression below one binder. -/
def weaken {sort : StaticSort} {scope : Sig} {kind : BinderKind}
    (expression : StaticExpr sort scope) :
    StaticExpr sort (scope ▹ kind) :=
  expression.rename Rename.succ

end StaticExpr

namespace Interval

/-- Weaken both interval endpoints below one binder. -/
def weaken {sort : StaticSort} {scope : Sig} {kind : BinderKind}
    (interval : Interval sort scope) : Interval sort (scope ▹ kind) :=
  interval.rename Rename.succ

/-- A completely unconstrained interval. -/
def unbounded {sort : StaticSort} {scope : Sig} : Interval sort scope :=
  .bounds .none .none

/-- An exact interval with equal lower and upper syntax. -/
def exact {sort : StaticSort} {scope : Sig}
    (expression : StaticExpr sort scope) : Interval sort scope :=
  .bounds (.some expression) (.some expression)

end Interval

namespace Endpoint

/-- View a source endpoint through Lean's ordinary `Option` interface. -/
def toOption {sort : StaticSort} {scope : Sig}
    (endpoint : Endpoint sort scope) : Option (StaticExpr sort scope) :=
  match endpoint with
  | .none => Option.none
  | .some expression => Option.some expression

end Endpoint

mutual

@[simp]
def Capture.rename_id {scope : Sig} (capture : Capture scope) :
    capture.rename Rename.id = capture :=
  match capture with
  | .empty => rfl
  | .union left right => by
      simp only [Capture.rename, Capture.rename_id left,
        Capture.rename_id right]
  | .singleton path => by
      simp only [Capture.rename, Path.rename_id path]
  | .ref name => by
      simp only [Capture.rename, StaticRef.rename_id name]

@[simp]
def Ty.rename_id {scope : Sig} (type : Ty scope) :
    type.rename Rename.id = type :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref name => by
      simp only [Ty.rename, StaticRef.rename_id name]
  | .capturing captures shape => by
      simp only [Ty.rename, Capture.rename_id captures, Ty.rename_id shape]
  | .arr domain codomain => by
      simp only [Ty.rename, Ty.rename_id domain, Ty.rename_id codomain]
  | .forallI interval body => by
      simp only [Ty.rename, Interval.rename_id interval, Rename.lift_id,
        Ty.rename_id body]
  | .existsI interval body => by
      simp only [Ty.rename, Interval.rename_id interval, Rename.lift_id,
        Ty.rename_id body]

@[simp]
def StaticExpr.rename_id {sort : StaticSort} {scope : Sig}
    (expression : StaticExpr sort scope) :
    expression.rename Rename.id = expression :=
  match expression with
  | .type type => by
      simp only [StaticExpr.rename, Ty.rename_id type]
  | .capture capture => by
      simp only [StaticExpr.rename, Capture.rename_id capture]

@[simp]
def Endpoint.rename_id {sort : StaticSort} {scope : Sig}
    (endpoint : Endpoint sort scope) :
    endpoint.rename Rename.id = endpoint :=
  match endpoint with
  | .none => rfl
  | .some expression => by
      simp only [Endpoint.rename, StaticExpr.rename_id expression]

@[simp]
def Interval.rename_id {sort : StaticSort} {scope : Sig}
    (interval : Interval sort scope) :
    interval.rename Rename.id = interval :=
  match interval with
  | .bounds lower upper => by
      simp only [Interval.rename, Endpoint.rename_id lower,
        Endpoint.rename_id upper]

end

mutual

@[simp]
def Capture.rename_comp {first second third : Sig}
    (capture : Capture first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (capture.rename rho₁).rename rho₂ =
      capture.rename (rho₁.comp rho₂) :=
  match capture with
  | .empty => rfl
  | .union left right => by
      simp only [Capture.rename, Capture.rename_comp left,
        Capture.rename_comp right]
  | .singleton path => by
      simp only [Capture.rename, Path.rename_comp path]
  | .ref name => by
      simp only [Capture.rename, StaticRef.rename_comp name]

@[simp]
def Ty.rename_comp {first second third : Sig} (type : Ty first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (type.rename rho₁).rename rho₂ = type.rename (rho₁.comp rho₂) :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref name => by
      simp only [Ty.rename, StaticRef.rename_comp name]
  | .capturing captures shape => by
      simp only [Ty.rename, Capture.rename_comp captures,
        Ty.rename_comp shape]
  | .arr domain codomain => by
      simp only [Ty.rename, Ty.rename_comp domain, Ty.rename_comp codomain]
  | .forallI interval body => by
      simp only [Ty.rename, Interval.rename_comp interval,
        Ty.rename_comp body, Rename.lift_comp]
  | .existsI interval body => by
      simp only [Ty.rename, Interval.rename_comp interval,
        Ty.rename_comp body, Rename.lift_comp]

@[simp]
def StaticExpr.rename_comp {sort : StaticSort} {first second third : Sig}
    (expression : StaticExpr sort first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (expression.rename rho₁).rename rho₂ =
      expression.rename (rho₁.comp rho₂) :=
  match expression with
  | .type type => by
      simp only [StaticExpr.rename, Ty.rename_comp type]
  | .capture capture => by
      simp only [StaticExpr.rename, Capture.rename_comp capture]

@[simp]
def Endpoint.rename_comp {sort : StaticSort} {first second third : Sig}
    (endpoint : Endpoint sort first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (endpoint.rename rho₁).rename rho₂ =
      endpoint.rename (rho₁.comp rho₂) :=
  match endpoint with
  | .none => rfl
  | .some expression => by
      simp only [Endpoint.rename, StaticExpr.rename_comp expression]

@[simp]
def Interval.rename_comp {sort : StaticSort} {first second third : Sig}
    (interval : Interval sort first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (interval.rename rho₁).rename rho₂ =
      interval.rename (rho₁.comp rho₂) :=
  match interval with
  | .bounds lower upper => by
      simp only [Interval.rename, Endpoint.rename_comp lower,
        Endpoint.rename_comp upper]

end

end DOTCapture.BinderOnly
