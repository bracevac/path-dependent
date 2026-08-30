import Coercions.DOT.Acyclic.Scope

/-!
# Acyclic DOT syntax with signature intersections

`DotFCI` is the conservative intersection-signature extension of the acyclic
source language.  It keeps the heterogeneous scopes and variable-only stable
paths of `DotFC`, but adds intersections and objects containing several exact
type definitions.  The older `DotFC.Source` language remains unchanged as the
acyclic baseline.
-/

namespace DotFCI.Source

open DotFC

/-- Source member labels. -/
abbrev Name : Type := Nat

/-- Types of the acyclic source calculus with intersections. -/
inductive Ty : Sig → Type where
  | top {scope : Sig} : Ty scope
  | bot {scope : Sig} : Ty scope
  | all {scope : Sig} (domain : Ty scope)
      (codomain : Ty (scope ▹ .term)) : Ty scope
  | member {scope : Sig} (label : Name) (lower upper : Ty scope) : Ty scope
  | sel {scope : Sig} (path : BVar scope .term) (label : Name) : Ty scope
  | inter {scope : Sig} (left right : Ty scope) : Ty scope
deriving DecidableEq

/-- One exact type definition stored by a source object. -/
structure TypeDef (scope : Sig) where
  label : Name
  witness : Ty scope
deriving DecidableEq

/-- Administrative-normal-form source terms.  Object definitions are static
and therefore share one unit-like runtime payload after erasure. -/
inductive Tm : Sig → Type where
  | var {scope : Sig} (index : BVar scope .term) : Tm scope
  | lam {scope : Sig} (domain : Ty scope)
      (body : Tm (scope ▹ .term)) : Tm scope
  | obj {scope : Sig} (definitions : List (TypeDef scope)) : Tm scope
  | app {scope : Sig} (function argument : BVar scope .term) : Tm scope
  | let' {scope : Sig} (rhs : Tm scope)
      (body : Tm (scope ▹ .term)) : Tm scope
deriving DecidableEq

namespace Ty

/-- An exact member declaration is an interval with identical bounds. -/
def exact {scope : Sig} (label : Name) (witness : Ty scope) : Ty scope :=
  .member label witness witness

/-- Rename every stable path in a type. -/
def rename {source target : Sig} (type : Ty source)
    (rho : Rename source target) : Ty target :=
  match type with
  | .top => .top
  | .bot => .bot
  | .all domain codomain =>
      .all (rename domain rho) (rename codomain rho.lift)
  | .member label lower upper =>
      .member label (rename lower rho) (rename upper rho)
  | .sel path label => .sel (rho.var path) label
  | .inter left right => .inter (rename left rho) (rename right rho)

/-- Weaken a type below one heterogeneous binder. -/
def weaken {scope : Sig} {kind : BinderKind} (type : Ty scope) :
    Ty (scope ▹ kind) :=
  type.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} (type : Ty scope) :
    type.rename Rename.id = type := by
  induction type with
  | top => rfl
  | bot => rfl
  | all domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction]
  | member label lower upper lowerInduction upperInduction =>
      simp [rename, lowerInduction, upperInduction]
  | sel => rfl
  | inter left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]

@[simp]
theorem rename_comp {first second third : Sig} (type : Ty first)
    (firstRename : Rename first second) (secondRename : Rename second third) :
    (type.rename firstRename).rename secondRename =
      type.rename (firstRename.comp secondRename) := by
  induction type generalizing second third with
  | top => rfl
  | bot => rfl
  | all domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction, Rename.lift_comp]
  | member label lower upper lowerInduction upperInduction =>
      simp [rename, lowerInduction, upperInduction]
  | sel => rfl
  | inter left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]

end Ty

namespace TypeDef

/-- The exact member type contributed by one object definition. -/
def exactTy {scope : Sig} (definition : TypeDef scope) : Ty scope :=
  .exact definition.label definition.witness

/-- Rename the witness stored by a definition. -/
def rename {source target : Sig} (definition : TypeDef source)
    (rho : Rename source target) : TypeDef target where
  label := definition.label
  witness := definition.witness.rename rho

@[simp]
theorem rename_label {source target : Sig} (definition : TypeDef source)
    (rho : Rename source target) :
    (definition.rename rho).label = definition.label := rfl

@[simp]
theorem rename_exactTy {source target : Sig} (definition : TypeDef source)
    (rho : Rename source target) :
    (definition.rename rho).exactTy = definition.exactTy.rename rho := by
  cases definition
  rfl

@[simp]
theorem rename_id {scope : Sig} (definition : TypeDef scope) :
    definition.rename Rename.id = definition := by
  cases definition
  simp [rename]

@[simp]
theorem rename_comp {first second third : Sig}
    (definition : TypeDef first) (firstRename : Rename first second)
    (secondRename : Rename second third) :
    (definition.rename firstRename).rename secondRename =
      definition.rename (firstRename.comp secondRename) := by
  cases definition
  simp [rename, Ty.rename_comp]

end TypeDef

namespace TypeDefs

/-- The raw intersection of the exact declarations in an object.  The empty
case is `top`; object typing may impose a stronger nonempty/unique-label
discipline without making raw syntax partial. -/
def exact {scope : Sig} : List (TypeDef scope) → Ty scope
  | [] => .top
  | [definition] => definition.exactTy
  | definition :: remaining => .inter definition.exactTy (exact remaining)

/-- Rename all object definitions. -/
def rename {source target : Sig} (definitions : List (TypeDef source))
    (rho : Rename source target) : List (TypeDef target) :=
  definitions.map fun definition => definition.rename rho

@[simp]
theorem rename_nil {source target : Sig} (rho : Rename source target) :
    rename ([] : List (TypeDef source)) rho = [] := rfl

@[simp]
theorem rename_cons {source target : Sig} (definition : TypeDef source)
    (remaining : List (TypeDef source)) (rho : Rename source target) :
    rename (definition :: remaining) rho =
      definition.rename rho :: rename remaining rho := rfl

@[simp]
theorem exact_rename {source target : Sig}
    (definitions : List (TypeDef source)) (rho : Rename source target) :
    exact (rename definitions rho) = (exact definitions).rename rho := by
  induction definitions with
  | nil => rfl
  | cons definition remaining induction =>
      cases remaining with
      | nil => simp [exact, rename]
      | cons next rest =>
          simp only [rename_cons, exact, TypeDef.rename_exactTy, Ty.rename]
          simpa only [rename_cons] using
            congrArg (Ty.inter (definition.exactTy.rename rho)) induction

@[simp]
theorem rename_id {scope : Sig} (definitions : List (TypeDef scope)) :
    rename definitions Rename.id = definitions := by
  induction definitions with
  | nil => rfl
  | cons definition remaining induction =>
      simp [rename]

@[simp]
theorem rename_comp {first second third : Sig}
    (definitions : List (TypeDef first))
    (firstRename : Rename first second) (secondRename : Rename second third) :
    rename (rename definitions firstRename) secondRename =
      rename definitions (firstRename.comp secondRename) := by
  induction definitions with
  | nil => rfl
  | cons definition remaining induction =>
      simp [rename]

end TypeDefs

namespace Tm

/-- Rename every variable and type annotation in a source term. -/
def rename {source target : Sig} (term : Tm source)
    (rho : Rename source target) : Tm target :=
  match term with
  | .var index => .var (rho.var index)
  | .lam domain body =>
      .lam (domain.rename rho) (rename body rho.lift)
  | .obj definitions => .obj (TypeDefs.rename definitions rho)
  | .app function argument => .app (rho.var function) (rho.var argument)
  | .let' rhs body => .let' (rename rhs rho) (rename body rho.lift)

/-- Weaken a term below one heterogeneous binder. -/
def weaken {scope : Sig} {kind : BinderKind} (term : Tm scope) :
    Tm (scope ▹ kind) :=
  term.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} (term : Tm scope) :
    term.rename Rename.id = term := by
  induction term with
  | var => rfl
  | lam domain body induction => simp [rename, induction]
  | obj definitions => simp [rename]
  | app => rfl
  | let' rhs body rhsInduction bodyInduction =>
      simp [rename, rhsInduction, bodyInduction]

@[simp]
theorem rename_comp {first second third : Sig} (term : Tm first)
    (firstRename : Rename first second) (secondRename : Rename second third) :
    (term.rename firstRename).rename secondRename =
      term.rename (firstRename.comp secondRename) := by
  induction term generalizing second third with
  | var => rfl
  | lam domain body induction =>
      simp [rename, Ty.rename_comp, induction, Rename.lift_comp]
  | obj definitions => simp [rename, TypeDefs.rename_comp]
  | app => rfl
  | let' rhs body rhsInduction bodyInduction =>
      simp [rename, rhsInduction, bodyInduction, Rename.lift_comp]

end Tm

namespace Rename

/-- Replace the newest term binder by an existing stable path. -/
def openAt {scope : Sig} (path : BVar scope .term) :
    DotFC.Rename (scope ▹ .term) scope where
  var := fun
    | .here => path
    | .there older => older

end Rename

namespace Ty

/-- Open a dependent type at an existing stable path. -/
def «open» {scope : Sig} (type : Ty (scope ▹ .term))
    (path : BVar scope .term) : Ty scope :=
  type.rename (Rename.openAt path)

end Ty

end DotFCI.Source
