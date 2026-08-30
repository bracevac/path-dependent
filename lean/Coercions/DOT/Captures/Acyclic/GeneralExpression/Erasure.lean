import Coercions.DOT.Captures.Acyclic.GeneralExpression.Structural
import Coercions.ManySortedFC.Runtime

/-!
# Direct runtime erasure of general captured-DOT expressions

Erasure is defined independently of normalization and target compilation.
General application maps directly to the shared runtime's left-to-right
call-by-value application.  Objects remain representation-transparent values,
and opening either a plain value or an object is the same runtime `let`.
-/

namespace DOTCapture.Acyclic.GeneralExpression.Erasure

namespace Source

export DOTCapture.Acyclic.GeneralExpression
  (Scope Var Rename Path Value Term)

end Source

namespace Runtime

export ManySortedFC.Runtime (Tm)

end Runtime

/-- Map surface variables into an arbitrary runtime scope. -/
abbrev Renaming (source target : Nat) : Type :=
  Source.Var source → Fin target

namespace Renaming

/-- Preserve the newest source/runtime variable. -/
def lift {source target : Nat} (rho : Renaming source target) :
    Renaming (source + 1) (target + 1) :=
  fun
  | .here => 0
  | .there index => (rho index).succ

/-- Canonical de Bruijn projection from source variables to runtime indices. -/
def identity : {scope : Nat} → Renaming scope scope
  | 0 => fun index => nomatch index
  | _ + 1 => fun
      | .here => 0
      | .there index => (identity index).succ

@[simp]
theorem identity_here {scope : Nat} :
    identity (.here : Source.Var (scope + 1)) = 0 := rfl

@[simp]
theorem identity_there {scope : Nat} (index : Source.Var scope) :
    identity (.there index) = (identity index).succ := rfl

end Renaming

/-- Erase a stable source path to its runtime coordinate. -/
def erasePathWith {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) : Source.Path scope → Fin runtimeScope
  | .var name => rho name

mutual

/-- Erase a surface value.  Object metadata and packaging disappear. -/
def eraseValueWith {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) :
    Source.Value scope → Runtime.Tm runtimeScope
  | .var name => .var (rho name)
  | .unit => .unit
  | .lam _domain _codomain body => .lam (eraseTermWith rho.lift body)
  | .object _signature _typeWitness _captureWitness payload =>
      eraseValueWith rho payload

/-- Erase a general computation homomorphically into the shared runtime. -/
def eraseTermWith {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) :
    Source.Term scope → Runtime.Tm runtimeScope
  | .ret value => eraseValueWith rho value
  | .select receiver .v => .var (erasePathWith rho receiver)
  | .app function argument =>
      .app (eraseTermWith rho function) (eraseTermWith rho argument)
  | .let' _result rhs body =>
      .let' (eraseTermWith rho rhs) (eraseTermWith rho.lift body)

end

/-- Canonical erasure of a surface value at its own term scope. -/
def eraseValue {scope : Nat} (value : Source.Value scope) : Runtime.Tm scope :=
  eraseValueWith Renaming.identity value

/-- Canonical erasure of a general surface computation. -/
def eraseTerm {scope : Nat} (term : Source.Term scope) : Runtime.Tm scope :=
  eraseTermWith Renaming.identity term

@[simp]
theorem eraseValueWith_var {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) (name : Source.Var scope) :
    eraseValueWith rho (.var name) = .var (rho name) := rfl

@[simp]
theorem eraseValueWith_unit {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) :
    eraseValueWith rho (.unit : Source.Value scope) = .unit := rfl

@[simp]
theorem eraseValueWith_lam {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope)
    (domain codomain : DOTCapture.Acyclic.Ty scope)
    (body : Source.Term (scope + 1)) :
    eraseValueWith rho (.lam domain codomain body) =
      .lam (eraseTermWith rho.lift body) := rfl

@[simp]
theorem eraseValueWith_object {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope)
    (signature : DOTCapture.Acyclic.ObjectSig scope)
    (typeWitness : DOTCapture.Acyclic.Ty scope)
    (captureWitness : DOTCapture.Acyclic.Capture scope)
    (payload : Source.Value scope) :
    eraseValueWith rho
        (.object signature typeWitness captureWitness payload) =
      eraseValueWith rho payload := rfl

@[simp]
theorem eraseTermWith_ret {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) (value : Source.Value scope) :
    eraseTermWith rho (.ret value) = eraseValueWith rho value := rfl

@[simp]
theorem eraseTermWith_select {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) (receiver : Source.Path scope) :
    eraseTermWith rho (.select receiver .v) =
      .var (erasePathWith rho receiver) := rfl

@[simp]
theorem eraseTermWith_app {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope)
    (function argument : Source.Term scope) :
    eraseTermWith rho (.app function argument) =
      .app (eraseTermWith rho function) (eraseTermWith rho argument) := rfl

@[simp]
theorem eraseTermWith_let {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope)
    (result : DOTCapture.Acyclic.Ty scope) (rhs : Source.Term scope)
    (body : Source.Term (scope + 1)) :
    eraseTermWith rho (.let' result rhs body) =
      .let' (eraseTermWith rho rhs) (eraseTermWith rho.lift body) := rfl

end DOTCapture.Acyclic.GeneralExpression.Erasure
