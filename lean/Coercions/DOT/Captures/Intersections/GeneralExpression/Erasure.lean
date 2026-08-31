import Coercions.DOT.Captures.Intersections.GeneralExpression.Syntax
import Coercions.ManySortedFC.Runtime

/-!
# Independent runtime erasure for M11 general expressions

This definition mentions neither target compilation nor target evidence.
Generalized object annotations erase, leaving their one payload.  Negative
object abstraction and application erase to ordinary runtime abstraction and
application, and explicit object opening erases to one runtime `let`.
-/

namespace DOTCapture.Intersections.GeneralExpression.Erasure

namespace Source

export DOTCapture.Intersections.GeneralExpression
  (Scope Var Path ValueLabel Value Term)

end Source

namespace Runtime

export ManySortedFC.Runtime (Tm)

end Runtime

/-- Map source variables into an arbitrary runtime scope. -/
abbrev Renaming (source target : Nat) : Type := Source.Var source -> Fin target

namespace Renaming

/-- Preserve the newest source/runtime variable. -/
def lift {source target : Nat} (rho : Renaming source target) :
    Renaming (source + 1) (target + 1) :=
  fun
  | .here => 0
  | .there index => (rho index).succ

/-- Canonical de Bruijn projection from source variables to runtime indices. -/
def identity : {scope : Nat} -> Renaming scope scope
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
    (rho : Renaming scope runtimeScope) : Source.Path scope -> Fin runtimeScope
  | .var name => rho name

mutual

/-- Erase values.  Every positive object is representation-transparent. -/
def eraseValueWith {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) :
    Source.Value scope -> Runtime.Tm runtimeScope
  | .var name => .var (rho name)
  | .unit => .unit
  | .lam _domain _codomain body => .lam (eraseTermWith rho.lift body)
  | .object _objectType payload => eraseValueWith rho payload
  | .objectConsumer _parameter _result body =>
      .lam (eraseTermWith rho.lift body)

/-- Erase computations homomorphically in source evaluation order. -/
def eraseTermWith {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope) :
    Source.Term scope -> Runtime.Tm runtimeScope
  | .ret value => eraseValueWith rho value
  | .select receiver .payload => .var (erasePathWith rho receiver)
  | .app function argument =>
      .app (eraseTermWith rho function) (eraseTermWith rho argument)
  | .let' _result rhs body =>
      .let' (eraseTermWith rho rhs) (eraseTermWith rho.lift body)
  | .objectApp _parameter function argument =>
      .app (eraseTermWith rho function) (eraseTermWith rho argument)
  | .objectLet _objectType _result rhs body =>
      .let' (eraseTermWith rho rhs) (eraseTermWith rho.lift body)

end

/-- Canonical erasure of a value at its own runtime scope. -/
def eraseValue {scope : Nat} (value : Source.Value scope) : Runtime.Tm scope :=
  eraseValueWith Renaming.identity value

/-- Canonical erasure of a computation at its own runtime scope. -/
def eraseTerm {scope : Nat} (term : Source.Term scope) : Runtime.Tm scope :=
  eraseTermWith Renaming.identity term

@[simp]
theorem eraseValueWith_object {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope)
    (objectType : DOTCapture.Intersections.Source.ObjectType scope)
    (payload : Source.Value scope) :
    eraseValueWith rho (.object objectType payload) = eraseValueWith rho payload :=
  rfl

@[simp]
theorem eraseValueWith_objectConsumer {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope)
    (parameter : DOTCapture.Intersections.Source.ObjectType scope)
    (result : DOTCapture.Intersections.Source.Ty scope)
    (body : Source.Term (scope + 1)) :
    eraseValueWith rho (.objectConsumer parameter result body) =
      .lam (eraseTermWith rho.lift body) := rfl

@[simp]
theorem eraseTermWith_objectApp {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope)
    (parameter : DOTCapture.Intersections.Source.ObjectType scope)
    (function argument : Source.Term scope) :
    eraseTermWith rho (.objectApp parameter function argument) =
      .app (eraseTermWith rho function) (eraseTermWith rho argument) := rfl

@[simp]
theorem eraseTermWith_objectLet {scope runtimeScope : Nat}
    (rho : Renaming scope runtimeScope)
    (objectType : DOTCapture.Intersections.Source.ObjectType scope)
    (result : DOTCapture.Intersections.Source.Ty scope)
    (rhs : Source.Term scope) (body : Source.Term (scope + 1)) :
    eraseTermWith rho (.objectLet objectType result rhs body) =
      .let' (eraseTermWith rho rhs) (eraseTermWith rho.lift body) := rfl

end DOTCapture.Intersections.GeneralExpression.Erasure
