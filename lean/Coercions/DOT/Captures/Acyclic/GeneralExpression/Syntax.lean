import Coercions.DOT.Captures.Acyclic.Context

/-!
# General-expression syntax for acyclic captured DOT

This surface layer reuses the static language, paths, and contexts of the
acyclic captured-DOT core while removing its value-MNF restriction on
applications.  Object construction remains a value form, and selection still
requires a stable variable path.  Consequently a computation producing an
object must first be named by a `let'` before its members can be selected.
-/

namespace DOTCapture.Acyclic.GeneralExpression

abbrev Scope := DOTCapture.Acyclic.Scope
abbrev Var := DOTCapture.Acyclic.Var
abbrev Rename := DOTCapture.Acyclic.Rename
abbrev Path := DOTCapture.Acyclic.Path
abbrev StaticSort := DOTCapture.Acyclic.StaticSort
abbrev StaticRef := DOTCapture.Acyclic.StaticRef
abbrev Capture := DOTCapture.Acyclic.Capture
abbrev Ty := DOTCapture.Acyclic.Ty
abbrev ObjectSig := DOTCapture.Acyclic.ObjectSig
abbrev StaticExpr := DOTCapture.Acyclic.StaticExpr
abbrev ValueLabel := DOTCapture.Acyclic.ValueLabel
abbrev Ctx := DOTCapture.Acyclic.Ctx

namespace Capture

/-- Sequence an immediate-use prediction before a continuation prediction.

The empty leading prediction is removed definitionally.  This makes the
general rules specialize to the value-MNF indices when their newly admitted
subcomputation is pure, while retaining an explicit union for a genuine use. -/
def seq {scope : Scope} : Capture scope → Capture scope → Capture scope
  | .empty, continuation => continuation
  | immediate, continuation => .union immediate continuation

end Capture

mutual

/-- Surface values.  Lambdas contain general computations, while an object
still packages a value payload and ambient witnesses only. -/
inductive Value : Scope → Type where
  | var {scope : Scope} (name : Var scope) : Value scope
  | unit {scope : Scope} : Value scope
  | lam {scope : Scope} (domain codomain : Ty scope)
      (body : Term (scope + 1)) : Value scope
  | object {scope : Scope} (signature : ObjectSig scope)
      (typeWitness : Ty scope) (captureWitness : Capture scope)
      (payload : Value scope) : Value scope

/-- General computations.  Both application positions are computations.
`let'` is shared by plain sequencing and object opening; the typing derivation
distinguishes those two binding disciplines. -/
inductive Term : Scope → Type where
  | ret {scope : Scope} (value : Value scope) : Term scope
  | select {scope : Scope} (receiver : Path scope) (label : ValueLabel) :
      Term scope
  | app {scope : Scope} (function argument : Term scope) : Term scope
  | let' {scope : Scope} (result : Ty scope) (rhs : Term scope)
      (body : Term (scope + 1)) : Term scope

end


deriving instance DecidableEq for Value
deriving instance DecidableEq for Term

mutual

/-- Rename every free source variable in a surface value. -/
def Value.rename {source target : Scope} (value : Value source)
    (rho : Rename source target) : Value target :=
  match value with
  | .var name => .var (rho.var name)
  | .unit => .unit
  | .lam domain codomain body =>
      .lam (domain.rename rho) (codomain.rename rho) (body.rename rho.lift)
  | .object signature typeWitness captureWitness payload =>
      .object (signature.rename rho) (typeWitness.rename rho)
        (captureWitness.rename rho) (payload.rename rho)

/-- Rename a general computation, lifting below lambda and let binders. -/
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

/-- Weaken a value below one newer source variable. -/
def weaken {scope : Scope} (value : Value scope) : Value (scope + 1) :=
  value.rename Rename.succ

end Value

namespace Term

/-- Weaken a computation below one newer source variable. -/
def weaken {scope : Scope} (term : Term scope) : Term (scope + 1) :=
  term.rename Rename.succ

end Term

end DOTCapture.Acyclic.GeneralExpression
