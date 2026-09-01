import Coercions.DOT.Captures.ModalIntersections.Structural

/-!
# General captured-DOT terms over heterogeneous scopes

These are the cumulative captured-intersection term forms.  They deliberately
do not yet add guarded modal operations: heterogeneous static binders occur in
types, while every existing captured-intersection runtime binder remains a
term binder.
-/

namespace DOTCapture.ModalIntersections

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
  | object {scope : Sig} (objectType : ObjectType scope)
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
  | .object objectType payload =>
      .object (objectType.rename rho) (payload.rename rho)
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
  | .object objectType payload => by
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
  | .object objectType payload => by
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
  | stableVariable
  | requiresExplicitOpen
deriving DecidableEq, Repr

namespace ObjectArgument

def classify {scope : Sig} : Term scope → Form
  | .ret (.object _ _) => .canonicalLiteral
  | .ret (.var _) => .stableVariable
  | _ => .requiresExplicitOpen

end ObjectArgument

end DOTCapture.ModalIntersections
