import Coercions.DOT.Acyclic.Scope

/-!
# Recursive DOT source syntax

`DotFCR` conservatively extends `DotFCI` with one recursive self binder shared
by an entire type-member object.  Recursive bodies are still ordinary DOT
types: intersections describe several members and selections use stable
variable paths.  Static object definitions carry no runtime payload.
-/

namespace DotFCR.Source

open DotFC

/-- Source member labels. -/
abbrev Name : Type := Nat

/-- DOT types with intersections and an explicitly scoped recursive self
binder.  In `mu body`, `.here` in `body` denotes the object itself. -/
inductive Ty : Sig → Type where
  | top {scope : Sig} : Ty scope
  | bot {scope : Sig} : Ty scope
  | all {scope : Sig} (domain : Ty scope)
      (codomain : Ty (scope ▹ .term)) : Ty scope
  | member {scope : Sig} (label : Name) (lower upper : Ty scope) : Ty scope
  | sel {scope : Sig} (path : BVar scope .term) (label : Name) : Ty scope
  | inter {scope : Sig} (left right : Ty scope) : Ty scope
  | mu {scope : Sig} (body : Ty (scope ▹ .term)) : Ty scope
deriving DecidableEq

/-- One exact type definition.  Recursive objects instantiate this structure
at the scope extended by their shared self binder. -/
structure TypeDef (scope : Sig) where
  label : Name
  witness : Ty scope
deriving DecidableEq

/-- Administrative-normal-form source terms.  `obj` is the nonrecursive
intersection-signature form; `recObj` gives all definitions access to one
shared self path. -/
inductive Tm : Sig → Type where
  | var {scope : Sig} (index : BVar scope .term) : Tm scope
  | lam {scope : Sig} (domain : Ty scope)
      (body : Tm (scope ▹ .term)) : Tm scope
  | obj {scope : Sig} (definitions : List (TypeDef scope)) : Tm scope
  | recObj {scope : Sig}
      (definitions : List (TypeDef (scope ▹ .term))) : Tm scope
  | app {scope : Sig} (function argument : BVar scope .term) : Tm scope
  | let' {scope : Sig} (rhs : Tm scope)
      (body : Tm (scope ▹ .term)) : Tm scope
deriving DecidableEq

namespace Ty

/-- An exact member declaration is an interval with identical bounds. -/
def exact {scope : Sig} (label : Name) (witness : Ty scope) : Ty scope :=
  .member label witness witness

/-- Rename stable paths, lifting under function and recursive-self binders. -/
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
  | .mu body => .mu (rename body rho.lift)

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
  | mu body induction => simp [rename, induction]

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
  | mu body induction =>
      simp [rename, induction, Rename.lift_comp]

end Ty

namespace TypeDef

/-- The exact member type contributed by one definition. -/
def exactTy {scope : Sig} (definition : TypeDef scope) : Ty scope :=
  .exact definition.label definition.witness

/-- Rename a definition's witness. -/
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

/-- Intersection of exact member declarations.  Empty plain objects receive
`top`; recursive-object validity below explicitly rules the empty case out. -/
def exact {scope : Sig} : List (TypeDef scope) → Ty scope
  | [] => .top
  | [definition] => definition.exactTy
  | definition :: remaining => .inter definition.exactTy (exact remaining)

/-- Rename all definitions. -/
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
  | cons definition remaining induction => simp [rename]

@[simp]
theorem rename_comp {first second third : Sig}
    (definitions : List (TypeDef first))
    (firstRename : Rename first second) (secondRename : Rename second third) :
    rename (rename definitions firstRename) secondRename =
      rename definitions (firstRename.comp secondRename) := by
  induction definitions with
  | nil => rfl
  | cons definition remaining induction => simp [rename]

end TypeDefs

/-! ## Explicit recursive-head guardedness -/

/-- A recursive body is head guarded exactly when its outer tree consists of
member declarations and intersections.  Recursive self selections may occur
inside member bounds, but never as an unguarded body head. -/
inductive HeadGuarded : {scope : Sig} → Ty scope → Type where
  | member {scope : Sig} {label : Name} {lower upper : Ty scope} :
      HeadGuarded (.member label lower upper)
  | inter {scope : Sig} {left right : Ty scope}
      (leftGuarded : HeadGuarded left)
      (rightGuarded : HeadGuarded right) :
      HeadGuarded (.inter left right)

namespace HeadGuarded

/-- Head guardedness is stable under ambient path renaming. -/
def rename {source target : Sig} {body : Ty source}
    (guarded : HeadGuarded body) (rho : Rename source target) :
    HeadGuarded (body.rename rho) :=
  match guarded with
  | .member => .member
  | .inter left right => .inter (left.rename rho) (right.rename rho)

end HeadGuarded

/-- Guardedness of one recursive definition witness relative to the newest
self binder.  A naked selection of `.here` is intentionally absent.  Every
proper type constructor is a guard, while an ambient selection is harmless
because it does not refer to the recursive self. -/
inductive WitnessGuarded {scope : Sig} : Ty (scope ▹ .term) → Type where
  | top : WitnessGuarded .top
  | bot : WitnessGuarded .bot
  | all {domain : Ty (scope ▹ .term)}
      {codomain : Ty ((scope ▹ .term) ▹ .term)} :
      WitnessGuarded (.all domain codomain)
  | member {label : Name} {lower upper : Ty (scope ▹ .term)} :
      WitnessGuarded (.member label lower upper)
  | inter {left right : Ty (scope ▹ .term)} :
      WitnessGuarded (.inter left right)
  | mu {body : Ty ((scope ▹ .term) ▹ .term)} :
      WitnessGuarded (.mu body)
  | ambientSel {path : BVar scope .term} {label : Name} :
      WitnessGuarded (.sel (.there path) label)

namespace WitnessGuarded

/-- Witness guardedness is natural under a renaming of the ambient scope. -/
def rename {source target : Sig} {witness : Ty (source ▹ .term)}
    (guarded : WitnessGuarded witness) (rho : Rename source target) :
    WitnessGuarded (witness.rename rho.lift) :=
  match guarded with
  | .top => .top
  | .bot => .bot
  | .all => .all
  | .member => .member
  | .inter => .inter
  | .mu => .mu
  | .ambientSel => .ambientSel

end WitnessGuarded

namespace TypeDefs

/-- Every recursive definition witness has a proper head relative to the
shared self binder. -/
inductive AllGuarded {scope : Sig} :
    List (TypeDef (scope ▹ .term)) → Type where
  | nil : AllGuarded []
  | cons {definition : TypeDef (scope ▹ .term)}
      {remaining : List (TypeDef (scope ▹ .term))}
      (witnessGuarded : WitnessGuarded definition.witness)
      (remainingGuarded : AllGuarded remaining) :
      AllGuarded (definition :: remaining)

namespace AllGuarded

/-- Rename all guarded witnesses while preserving the distinguished newest
self binder. -/
def rename {source target : Sig}
    {definitions : List (TypeDef (source ▹ .term))}
    (guarded : AllGuarded definitions) (rho : Rename source target) :
    AllGuarded (TypeDefs.rename definitions rho.lift) :=
  match guarded with
  | .nil => .nil
  | .cons head tail => .cons (head.rename rho) (tail.rename rho)

end AllGuarded

/-- Every nonempty exact-definition body is head guarded. -/
def exactHeadGuarded {scope : Sig} :
    (definitions : List (TypeDef scope)) → definitions ≠ [] →
      HeadGuarded (exact definitions)
  | [], nonempty => False.elim (nonempty rfl)
  | [_], _ => .member
  | _ :: _ :: _, _ => .inter .member (exactHeadGuarded _ (by simp))

end TypeDefs

/-- The forbidden unguarded recursive head has no certificate. -/
theorem selfSelection_not_witnessGuarded {scope : Sig}
    (label : Name) :
    WitnessGuarded (.sel (.here : BVar (scope ▹ .term) .term) label) →
      False := by
  intro guarded
  cases guarded

namespace Tm

/-- Rename variables and annotations, lifting under both term and self
binders. -/
def rename {source target : Sig} (term : Tm source)
    (rho : Rename source target) : Tm target :=
  match term with
  | .var index => .var (rho.var index)
  | .lam domain body => .lam (domain.rename rho) (rename body rho.lift)
  | .obj definitions => .obj (TypeDefs.rename definitions rho)
  | .recObj definitions => .recObj (TypeDefs.rename definitions rho.lift)
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
  | recObj definitions => simp [rename]
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
  | recObj definitions =>
      simp [rename, TypeDefs.rename_comp, Rename.lift_comp]
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

/-- Open a dependent type (including a recursive body) at a stable path. -/
def «open» {scope : Sig} (type : Ty (scope ▹ .term))
    (path : BVar scope .term) : Ty scope :=
  type.rename (Rename.openAt path)

end Ty

end DotFCR.Source
