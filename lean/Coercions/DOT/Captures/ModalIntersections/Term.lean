import Coercions.DOT.Captures.ModalIntersections.Structural

/-!
# General captured-DOT terms over heterogeneous scopes

These are the cumulative captured-intersection term forms.  Lexical static
abstraction and packaging remain value-only, so erasing a static wrapper
cannot delay a computation.  Their eliminations accept computations, matching
the general-expression discipline already used by application and object
opening.  A modal lock is likewise a value that suspends an arbitrary
computation; modal unlocking accepts a computed scrutinee.  This is the
access-only separation fragment and carries no consume or freshness claim.
-/

namespace DOTCapture.ModalIntersections

/-- Scope of an existential-open body: the hidden sorted variable followed by
the package payload as the newest term variable. -/
@[reducible]
def PayloadScope (scope : Sig) (sort : StaticSort) : Sig :=
  scope ▹ .static sort ▹ .term

namespace Rename

/-- Lift an ambient renaming through an existential's hidden static variable
and payload variable. -/
def liftPayload {source target : Sig} (rho : Rename source target)
    (sort : StaticSort) :
    Rename (PayloadScope source sort) (PayloadScope target sort) :=
  (rho.lift (kind := .static sort)).lift (kind := .term)

@[simp]
theorem liftPayload_id {scope : Sig} (sort : StaticSort) :
    liftPayload (DOTCapture.BinderOnly.Rename.id (scope := scope)) sort =
      DOTCapture.BinderOnly.Rename.id := by
  unfold liftPayload
  simp

theorem liftPayload_comp {first second third : Sig}
    (rho₁ : Rename first second) (rho₂ : Rename second third)
    (sort : StaticSort) :
    liftPayload (rho₁.comp rho₂) sort =
      (liftPayload rho₁ sort).comp (liftPayload rho₂ sort) := by
  unfold liftPayload
  rw [DOTCapture.BinderOnly.Rename.lift_comp,
    DOTCapture.BinderOnly.Rename.lift_comp]

end Rename

/-- Generalized objects expose one runtime payload. -/
inductive ValueLabel : Type where
  | payload
deriving DecidableEq, Repr

mutual

inductive Value : Sig → Type where
  | var {scope : Sig} (name : BVar scope .term) : Value scope
  | unit {scope : Sig} : Value scope
  | lam {scope : Sig} (domain codomain : Ty scope)
      (body : Term (scope ▹ .term)) : Value scope
  | staticLam {scope : Sig} {sort : StaticSort}
      (interval : Interval sort scope)
      (body : Value (scope ▹ .static sort)) : Value scope
  | pack {scope : Sig} {sort : StaticSort}
      (interval : Interval sort scope)
      (payloadType : Ty (scope ▹ .static sort))
      (witness : StaticExpr sort scope) (payload : Value scope) : Value scope
  /-- Suspend a computation under positional separation and mode assumptions.
  The assumptions affect typing, not the source variable scope. -/
  | lock {scope : Sig} {separationCount : Nat}
      {modes : List CaptureMode}
      (requirements : ModalRequirements separationCount modes scope)
      (result : Ty scope) (closure : Capture scope) (body : Term scope) :
      Value scope
  | object {scope : Sig} (objectType : ObjectType scope)
      (payload : Value scope) : Value scope
  /-- A recursive object literal is syntactically distinct from an ordinary
  canonical object literal.  Both erase to their payload, but recursive
  literals must be opened before they may be consumed negatively. -/
  | recursiveObject {scope : Sig} (objectType : ObjectType scope)
      (payload : Value scope) : Value scope
  | objectConsumer {scope : Sig} (parameter : ObjectType scope)
      (result : Ty scope) (body : Term (scope ▹ .term)) : Value scope

inductive Term : Sig → Type where
  | ret {scope : Sig} (value : Value scope) : Term scope
  | select {scope : Sig} (receiver : Path scope)
      (label : ValueLabel) : Term scope
  | app {scope : Sig} (function argument : Term scope) : Term scope
  | let' {scope : Sig} (result : Ty scope) (rhs : Term scope)
      (body : Term (scope ▹ .term)) : Term scope
  | staticApp {scope : Sig} {sort : StaticSort}
      (interval : Interval sort scope) (function : Term scope)
      (argument : StaticExpr sort scope) : Term scope
  | «open» {scope : Sig} {sort : StaticSort}
      (interval : Interval sort scope)
      (payloadType : Ty (scope ▹ .static sort))
      (result : Ty scope) (package : Term scope)
      (body : Term (PayloadScope scope sort)) : Term scope
  /-- Release a modal value after checking its requirements in the unchanged
  outer context.  The scrutinee may be an arbitrary computation. -/
  | unlock {scope : Sig} {separationCount : Nat}
      {modes : List CaptureMode}
      (requirements : ModalRequirements separationCount modes scope)
      (scrutinee : Term scope) : Term scope
  | objectApp {scope : Sig} (parameter : ObjectType scope)
      (function argument : Term scope) : Term scope
  | objectLet {scope : Sig} (objectType : ObjectType scope)
      (result : Ty scope) (rhs : Term scope)
      (body : Term (scope ▹ .term)) : Term scope

end

deriving instance DecidableEq for Value
deriving instance DecidableEq for Term

mutual

def Value.rename {source target : Sig} (value : Value source)
    (rho : Rename source target) : Value target :=
  match value with
  | .var name => .var (rho.var name)
  | .unit => .unit
  | .lam domain codomain body =>
      .lam (domain.rename rho) (codomain.rename rho)
        (body.rename (rho.lift (kind := .term)))
  | @Value.staticLam _ sort interval body =>
      .staticLam (interval.rename rho)
        (body.rename (rho.lift (kind := .static sort)))
  | @Value.pack _ sort interval payloadType witness payload =>
      .pack (interval.rename rho)
        (payloadType.rename (rho.lift (kind := .static sort)))
        (witness.rename rho) (payload.rename rho)
  | .lock requirements result closure body =>
      .lock (requirements.rename rho) (result.rename rho)
        (closure.rename rho) (body.rename rho)
  | .object objectType payload =>
      .object (objectType.rename rho) (payload.rename rho)
  | .recursiveObject objectType payload =>
      .recursiveObject (objectType.rename rho) (payload.rename rho)
  | .objectConsumer parameter result body =>
      .objectConsumer (parameter.rename rho) (result.rename rho)
        (body.rename (rho.lift (kind := .term)))

def Term.rename {source target : Sig} (term : Term source)
    (rho : Rename source target) : Term target :=
  match term with
  | .ret value => .ret (value.rename rho)
  | .select receiver label => .select (receiver.rename rho) label
  | .app function argument =>
      .app (function.rename rho) (argument.rename rho)
  | .let' result rhs body =>
      .let' (result.rename rho) (rhs.rename rho)
        (body.rename (rho.lift (kind := .term)))
  | @Term.staticApp _ _ interval function argument =>
      .staticApp (interval.rename rho) (function.rename rho)
        (argument.rename rho)
  | @Term.«open» _ sort interval payloadType result package body =>
      .«open» (interval.rename rho)
        (payloadType.rename (rho.lift (kind := .static sort)))
        (result.rename rho) (package.rename rho)
        (body.rename (rho.liftPayload sort))
  | .unlock requirements scrutinee =>
      .unlock (requirements.rename rho) (scrutinee.rename rho)
  | .objectApp parameter function argument =>
      .objectApp (parameter.rename rho) (function.rename rho)
        (argument.rename rho)
  | .objectLet objectType result rhs body =>
      .objectLet (objectType.rename rho) (result.rename rho)
        (rhs.rename rho) (body.rename (rho.lift (kind := .term)))

end

namespace Value

def weaken {scope : Sig} {kind : BinderKind} (value : Value scope) :
    Value (scope ▹ kind) :=
  value.rename DOTCapture.BinderOnly.Rename.succ

end Value

namespace Term

def weaken {scope : Sig} {kind : BinderKind} (term : Term scope) :
    Term (scope ▹ kind) :=
  term.rename DOTCapture.BinderOnly.Rename.succ

end Term

mutual

@[simp]
def Value.rename_id {scope : Sig} (value : Value scope) :
    value.rename DOTCapture.BinderOnly.Rename.id = value :=
  match value with
  | .var _ => rfl
  | .unit => rfl
  | .lam domain codomain body => by
      simp only [Value.rename, Ty.rename_id domain, Ty.rename_id codomain,
        DOTCapture.BinderOnly.Rename.lift_id, Term.rename_id body]
  | .staticLam interval body => by
      simp only [Value.rename, Interval.rename_id interval,
        DOTCapture.BinderOnly.Rename.lift_id, Value.rename_id body]
  | .pack interval payloadType witness payload => by
      simp only [Value.rename, Interval.rename_id interval,
        DOTCapture.BinderOnly.Rename.lift_id, Ty.rename_id payloadType,
        StaticExpr.rename_id witness, Value.rename_id payload]
  | .lock requirements result closure body => by
      simp only [Value.rename, ModalRequirements.rename_id requirements,
        Ty.rename_id result, Capture.rename_id closure, Term.rename_id body]
  | .object objectType payload => by
      simp only [Value.rename, ObjectType.rename_id objectType,
        Value.rename_id payload]
  | .recursiveObject objectType payload => by
      simp only [Value.rename, ObjectType.rename_id objectType,
        Value.rename_id payload]
  | .objectConsumer parameter result body => by
      simp only [Value.rename, ObjectType.rename_id parameter,
        Ty.rename_id result, DOTCapture.BinderOnly.Rename.lift_id,
        Term.rename_id body]

@[simp]
def Term.rename_id {scope : Sig} (term : Term scope) :
    term.rename DOTCapture.BinderOnly.Rename.id = term :=
  match term with
  | .ret value => by
      simp only [Term.rename, Value.rename_id value]
  | .select receiver _ => by
      simp only [Term.rename, Path.rename_id receiver]
  | .app function argument => by
      simp only [Term.rename, Term.rename_id function, Term.rename_id argument]
  | .let' result rhs body => by
      simp only [Term.rename, Ty.rename_id result, Term.rename_id rhs,
        DOTCapture.BinderOnly.Rename.lift_id, Term.rename_id body]
  | .staticApp interval function argument => by
      simp only [Term.rename, Interval.rename_id interval,
        Term.rename_id function, StaticExpr.rename_id argument]
  | .«open» interval payloadType result package body => by
      simp only [Term.rename, Interval.rename_id interval,
        DOTCapture.BinderOnly.Rename.lift_id, Ty.rename_id payloadType,
        Ty.rename_id result, Term.rename_id package, Rename.liftPayload_id,
        Term.rename_id body]
  | .unlock requirements scrutinee => by
      simp only [Term.rename, ModalRequirements.rename_id requirements,
        Term.rename_id scrutinee]
  | .objectApp parameter function argument => by
      simp only [Term.rename, ObjectType.rename_id parameter,
        Term.rename_id function, Term.rename_id argument]
  | .objectLet objectType result rhs body => by
      simp only [Term.rename, ObjectType.rename_id objectType,
        Ty.rename_id result, Term.rename_id rhs,
        DOTCapture.BinderOnly.Rename.lift_id, Term.rename_id body]

end

mutual

@[simp]
def Value.rename_comp {first second third : Sig} (value : Value first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (value.rename rho₁).rename rho₂ = value.rename (rho₁.comp rho₂) :=
  match value with
  | .var _ => rfl
  | .unit => rfl
  | .lam domain codomain body => by
      simp only [Value.rename, Ty.rename_comp domain, Ty.rename_comp codomain,
        Term.rename_comp body, DOTCapture.BinderOnly.Rename.lift_comp]
  | .staticLam interval body => by
      simp only [Value.rename, Interval.rename_comp interval,
        Value.rename_comp body, DOTCapture.BinderOnly.Rename.lift_comp]
  | .pack interval payloadType witness payload => by
      simp only [Value.rename, Interval.rename_comp interval,
        Ty.rename_comp payloadType, StaticExpr.rename_comp witness,
        Value.rename_comp payload, DOTCapture.BinderOnly.Rename.lift_comp]
  | .lock requirements result closure body => by
      simp only [Value.rename, ModalRequirements.rename_comp requirements,
        Ty.rename_comp result, Capture.rename_comp closure,
        Term.rename_comp body]
  | .object objectType payload => by
      simp only [Value.rename, ObjectType.rename_comp objectType,
        Value.rename_comp payload]
  | .recursiveObject objectType payload => by
      simp only [Value.rename, ObjectType.rename_comp objectType,
        Value.rename_comp payload]
  | .objectConsumer parameter result body => by
      simp only [Value.rename, ObjectType.rename_comp parameter,
        Ty.rename_comp result, Term.rename_comp body,
        DOTCapture.BinderOnly.Rename.lift_comp]

@[simp]
def Term.rename_comp {first second third : Sig} (term : Term first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (term.rename rho₁).rename rho₂ = term.rename (rho₁.comp rho₂) :=
  match term with
  | .ret value => by
      simp only [Term.rename, Value.rename_comp value]
  | .select receiver _ => by
      simp only [Term.rename, Path.rename_comp receiver]
  | .app function argument => by
      simp only [Term.rename, Term.rename_comp function,
        Term.rename_comp argument]
  | .let' result rhs body => by
      simp only [Term.rename, Ty.rename_comp result, Term.rename_comp rhs,
        Term.rename_comp body, DOTCapture.BinderOnly.Rename.lift_comp]
  | .staticApp interval function argument => by
      simp only [Term.rename, Interval.rename_comp interval,
        Term.rename_comp function, StaticExpr.rename_comp argument]
  | .«open» interval payloadType result package body => by
      simp only [Term.rename, Interval.rename_comp interval,
        Ty.rename_comp payloadType, Ty.rename_comp result,
        Term.rename_comp package, Term.rename_comp body,
        DOTCapture.BinderOnly.Rename.lift_comp, Rename.liftPayload_comp]
  | .unlock requirements scrutinee => by
      simp only [Term.rename, ModalRequirements.rename_comp requirements,
        Term.rename_comp scrutinee]
  | .objectApp parameter function argument => by
      simp only [Term.rename, ObjectType.rename_comp parameter,
        Term.rename_comp function, Term.rename_comp argument]
  | .objectLet objectType result rhs body => by
      simp only [Term.rename, ObjectType.rename_comp objectType,
        Ty.rename_comp result, Term.rename_comp rhs, Term.rename_comp body,
        DOTCapture.BinderOnly.Rename.lift_comp]

end

namespace Value

@[simp]
theorem weaken_rename {source target : Sig} {kind : BinderKind}
    (value : Value source) (rho : Rename source target) :
    (value.weaken (kind := kind)).rename (rho.lift (kind := kind)) =
      (value.rename rho).weaken := by
  simp only [weaken, rename_comp,
    DOTCapture.BinderOnly.Rename.succ_lift_comm]

end Value

namespace Term

@[simp]
theorem weaken_rename {source target : Sig} {kind : BinderKind}
    (term : Term source) (rho : Rename source target) :
    (term.weaken (kind := kind)).rename (rho.lift (kind := kind)) =
      (term.rename rho).weaken := by
  simp only [weaken, rename_comp,
    DOTCapture.BinderOnly.Rename.succ_lift_comm]

end Term

/-- Direct negative object use admits a canonical literal or stable variable;
other object computations still require an explicit `objectLet`. -/
inductive ObjectArgument.Form : Type where
  | canonicalLiteral
  | recursiveLiteral
  | stableVariable
  | requiresExplicitOpen
deriving DecidableEq, Repr

namespace ObjectArgument

def classify {scope : Sig} : Term scope → Form
  | .ret (.object _ _) => .canonicalLiteral
  | .ret (.recursiveObject _ _) => .recursiveLiteral
  | .ret (.var _) => .stableVariable
  | _ => .requiresExplicitOpen

end ObjectArgument

end DOTCapture.ModalIntersections
