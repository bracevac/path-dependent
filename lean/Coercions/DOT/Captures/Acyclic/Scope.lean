/-!
# Scopes for acyclic DOT with capture members

This source language owns a deliberately small scope discipline: an acyclic
context contains term variables only.  Type and capture names are selected
from those variables (`x.A` and `x.C`); they are not lexical static binders.
-/

namespace DOTCapture.Acyclic

/-- The number of term variables in scope. -/
abbrev Scope := Nat

/-- A de Bruijn variable in a term-only source scope. -/
inductive Var : Scope → Type where
  | here {scope : Scope} : Var (scope + 1)
  | there {scope : Scope} : Var scope → Var (scope + 1)
deriving DecidableEq

/-- A map between source scopes. -/
structure Rename (source target : Scope) where
  var : Var source → Var target

namespace Rename

/-- Identity renaming. -/
def id {scope : Scope} : Rename scope scope where
  var := fun index => index

/-- Diagrammatic composition: apply `first`, then `second`. -/
def comp {first second third : Scope} (firstRename : Rename first second)
    (secondRename : Rename second third) : Rename first third where
  var := fun index => secondRename.var (firstRename.var index)

/-- Lift a renaming below one term binder. -/
def lift {source target : Scope} (rho : Rename source target) :
    Rename (source + 1) (target + 1) where
  var := fun
    | .here => .here
    | .there index => .there (rho.var index)

/-- Weaken every existing variable below one new term binder. -/
def succ {scope : Scope} : Rename scope (scope + 1) where
  var := fun index => .there index

@[simp]
theorem id_var {scope : Scope} (index : Var scope) :
    (id (scope := scope)).var index = index := rfl

@[simp]
theorem comp_var {first second third : Scope}
    (firstRename : Rename first second) (secondRename : Rename second third)
    (index : Var first) :
    (firstRename.comp secondRename).var index =
      secondRename.var (firstRename.var index) := rfl

@[simp]
theorem lift_here {source target : Scope} (rho : Rename source target) :
    rho.lift.var (.here : Var (source + 1)) =
      (.here : Var (target + 1)) := rfl

@[simp]
theorem lift_there {source target : Scope} (rho : Rename source target)
    (index : Var source) :
    rho.lift.var (.there index) = .there (rho.var index) := rfl

@[simp]
theorem succ_var {scope : Scope} (index : Var scope) :
    (succ (scope := scope)).var index = .there index := rfl

@[ext]
theorem ext {source target : Scope} {first second : Rename source target}
    (pointwise : ∀ index, first.var index = second.var index) :
    first = second := by
  cases first
  cases second
  congr
  funext index
  exact pointwise index

@[simp]
theorem comp_id {source target : Scope} (rho : Rename source target) :
    rho.comp id = rho := by
  apply ext
  intro index
  rfl

@[simp]
theorem id_comp {source target : Scope} (rho : Rename source target) :
    id.comp rho = rho := by
  apply ext
  intro index
  rfl

@[simp]
theorem lift_id {scope : Scope} :
    (id (scope := scope)).lift = id := by
  apply ext
  intro index
  cases index <;> rfl

@[simp]
theorem lift_comp {first second third : Scope}
    (firstRename : Rename first second) (secondRename : Rename second third) :
    (firstRename.comp secondRename).lift =
      firstRename.lift.comp secondRename.lift := by
  apply ext
  intro index
  cases index <;> rfl

end Rename

end DOTCapture.Acyclic
