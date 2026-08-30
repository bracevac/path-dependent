import Coercions.DOT.Captures.BinderOnly.Syntax

/-!
# ANF terms for the binder-only DOT-with-captures source

Values and computations are separate syntactic categories.  Applications and
static eliminations consume values, while `let'` sequences computations.
Static boundaries carry source interval annotations but never target evidence
or model certificates; those belong to typing and elaboration.
-/

namespace DOTCapture.BinderOnly

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
    (id (scope := scope)).liftPayload sort = id := by
  unfold liftPayload
  simp

theorem liftPayload_comp {first second third : Sig}
    (rho₁ : Rename first second) (rho₂ : Rename second third)
    (sort : StaticSort) :
    (rho₁.comp rho₂).liftPayload sort =
      (rho₁.liftPayload sort).comp (rho₂.liftPayload sort) := by
  unfold liftPayload
  rw [lift_comp, lift_comp]

end Rename

mutual

/-- Source values.

`staticLam` deliberately has a value body.  Its target static abstraction is
erased at runtime, so it cannot act as a thunk that delays a computation.  A
computation body must first be made a value explicitly, for example by a term
lambda or an ANF binding outside the erased abstraction.

`pack` records the existential interval, its open payload type, and the static
witness.  Checking the witness against the interval and instantiating the
payload type are intentionally left to later judgments rather than stored as
proofs in syntax. -/
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

/-- ANF/MNF-style source computations.

Static application retains the interval annotation used to check its witness.
Existential opening retains the payload type and an ambient result annotation;
the latter makes the nonescape boundary structural.  Static substitution is
not part of this syntax module and will be supplied by later typing and
elaboration layers. -/
inductive Term : Sig → Type where
  | ret {scope : Sig} (value : Value scope) : Term scope
  | app {scope : Sig} (function argument : Value scope) : Term scope
  | let' {scope : Sig} (result : Ty scope) (rhs : Term scope)
      (body : Term (scope ▹ .term)) : Term scope
  | staticApp {scope : Sig} {sort : StaticSort}
      (interval : Interval sort scope) (function : Value scope)
      (argument : StaticExpr sort scope) : Term scope
  | «open» {scope : Sig} {sort : StaticSort}
      (interval : Interval sort scope)
      (payloadType : Ty (scope ▹ .static sort))
      (result : Ty scope) (package : Value scope)
      (body : Term (PayloadScope scope sort)) : Term scope

end

deriving instance DecidableEq for Value
deriving instance DecidableEq for Term

mutual

/-- Rename every free variable and annotation in a value. -/
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

/-- Rename every free variable and annotation in a computation. -/
def Term.rename {source target : Sig} (term : Term source)
    (rho : Rename source target) : Term target :=
  match term with
  | .ret value => .ret (value.rename rho)
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

end

namespace Value

/-- Weaken a value below one source binder. -/
def weaken {scope : Sig} {kind : BinderKind} (value : Value scope) :
    Value (scope ▹ kind) :=
  value.rename Rename.succ

end Value

namespace Term

/-- Weaken a computation below one source binder. -/
def weaken {scope : Sig} {kind : BinderKind} (term : Term scope) :
    Term (scope ▹ kind) :=
  term.rename Rename.succ

end Term

mutual

@[simp]
def Value.rename_id {scope : Sig} (value : Value scope) :
    value.rename Rename.id = value :=
  match value with
  | .var _ => rfl
  | .unit => rfl
  | .lam domain codomain body => by
      simp only [Value.rename, Ty.rename_id domain, Ty.rename_id codomain,
        Rename.lift_id, Term.rename_id body]
  | .staticLam interval body => by
      simp only [Value.rename, Interval.rename_id interval, Rename.lift_id,
        Value.rename_id body]
  | .pack interval payloadType witness payload => by
      simp only [Value.rename, Interval.rename_id interval, Rename.lift_id,
        Ty.rename_id payloadType, StaticExpr.rename_id witness,
        Value.rename_id payload]

@[simp]
def Term.rename_id {scope : Sig} (term : Term scope) :
    term.rename Rename.id = term :=
  match term with
  | .ret value => by
      simp only [Term.rename, Value.rename_id value]
  | .app function argument => by
      simp only [Term.rename, Value.rename_id function,
        Value.rename_id argument]
  | .let' result rhs body => by
      simp only [Term.rename, Ty.rename_id result, Term.rename_id rhs,
        Rename.lift_id, Term.rename_id body]
  | .staticApp interval function argument => by
      simp only [Term.rename, Interval.rename_id interval,
        Value.rename_id function, StaticExpr.rename_id argument]
  | .«open» interval payloadType result package body => by
      simp only [Term.rename, Interval.rename_id interval, Rename.lift_id,
        Ty.rename_id payloadType, Ty.rename_id result,
        Value.rename_id package, Rename.liftPayload_id,
        Term.rename_id body]

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
      simp only [Value.rename, Ty.rename_comp domain,
        Ty.rename_comp codomain, Term.rename_comp body, Rename.lift_comp]
  | .staticLam interval body => by
      simp only [Value.rename, Interval.rename_comp interval,
        Value.rename_comp body, Rename.lift_comp]
  | .pack interval payloadType witness payload => by
      simp only [Value.rename, Interval.rename_comp interval,
        Ty.rename_comp payloadType, StaticExpr.rename_comp witness,
        Value.rename_comp payload, Rename.lift_comp]

@[simp]
def Term.rename_comp {first second third : Sig} (term : Term first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (term.rename rho₁).rename rho₂ = term.rename (rho₁.comp rho₂) :=
  match term with
  | .ret value => by
      simp only [Term.rename, Value.rename_comp value]
  | .app function argument => by
      simp only [Term.rename, Value.rename_comp function,
        Value.rename_comp argument]
  | .let' result rhs body => by
      simp only [Term.rename, Ty.rename_comp result, Term.rename_comp rhs,
        Term.rename_comp body, Rename.lift_comp]
  | .staticApp interval function argument => by
      simp only [Term.rename, Interval.rename_comp interval,
        Value.rename_comp function, StaticExpr.rename_comp argument]
  | .«open» interval payloadType result package body => by
      simp only [Term.rename, Interval.rename_comp interval,
        Ty.rename_comp payloadType, Ty.rename_comp result,
        Value.rename_comp package, Term.rename_comp body,
        Rename.lift_comp, Rename.liftPayload_comp]

end

end DOTCapture.BinderOnly
