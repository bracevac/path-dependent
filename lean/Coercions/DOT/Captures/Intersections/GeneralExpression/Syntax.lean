import Coercions.DOT.Captures.Intersections.SourceSyntax

/-!
# General expressions for captured DOT with intersection signatures

This is a cumulative source layer over the M10 general-expression language.
It retains the ordinary lambda, application, and let forms used by M10, and
adds source forms that state the positive and negative uses of a generalized
`ObjectType` explicitly.

Objects still have one runtime payload.  Their interface, representation type,
and outer capture are static source annotations.  A validity judgment (rather
than this raw syntax) is responsible for supplying and checking a realization
of the interface.  In particular, no target names or target evidence occur in
this syntax.
-/

namespace DOTCapture.Intersections.GeneralExpression

abbrev Scope := DOTCapture.Intersections.Source.Scope
abbrev Var := DOTCapture.Intersections.Source.Var
abbrev Rename := DOTCapture.Intersections.Source.Rename
abbrev Path := DOTCapture.Intersections.Source.Path
abbrev StaticSort := DOTCapture.Intersections.Source.StaticSort
abbrev StaticRef := DOTCapture.Intersections.Source.StaticRef
abbrev Capture := DOTCapture.Intersections.Source.Capture
abbrev Ty := DOTCapture.Intersections.Source.Ty
abbrev Interface := DOTCapture.Intersections.Source.Interface
abbrev ObjectType := DOTCapture.Intersections.Source.ObjectType
abbrev StaticExpr := DOTCapture.Intersections.Source.StaticExpr

/-- Generalized objects continue to expose exactly one runtime component. -/
inductive ValueLabel : Type where
  | payload
deriving DecidableEq, Repr

mutual

/-- Values in the cumulative M11 source language.

`objectConsumer` makes negative object abstraction explicit.  Its body binds
the single runtime representation; static member references rooted at that
parameter use the labels of `parameter.interface` in source types. -/
inductive Value : Scope -> Type where
  | var {scope : Scope} (name : Var scope) : Value scope
  | unit {scope : Scope} : Value scope
  | lam {scope : Scope} (domain codomain : Ty scope)
      (body : Term (scope + 1)) : Value scope
  | object {scope : Scope} (objectType : ObjectType scope)
      (payload : Value scope) : Value scope
  | objectConsumer {scope : Scope} (parameter : ObjectType scope)
      (result : Ty scope) (body : Term (scope + 1)) : Value scope

/-- General computations.

The ordinary forms contain the M10 language verbatim up to translation of its
static annotations.  `objectApp` records the expected generalized interface;
`objectLet` is the explicit opening point at which an arbitrary
object-producing computation acquires a stable variable root. -/
inductive Term : Scope -> Type where
  | ret {scope : Scope} (value : Value scope) : Term scope
  | select {scope : Scope} (receiver : Path scope)
      (label : ValueLabel) : Term scope
  | app {scope : Scope} (function argument : Term scope) : Term scope
  | let' {scope : Scope} (result : Ty scope) (rhs : Term scope)
      (body : Term (scope + 1)) : Term scope
  | objectApp {scope : Scope} (parameter : ObjectType scope)
      (function argument : Term scope) : Term scope
  | objectLet {scope : Scope} (objectType : ObjectType scope)
      (result : Ty scope) (rhs : Term scope) (body : Term (scope + 1)) :
      Term scope

end

deriving instance DecidableEq for Value
deriving instance DecidableEq for Term

mutual

/-- Rename every free term variable in a value and its static annotations. -/
def Value.rename {source target : Scope} (value : Value source)
    (rho : Rename source target) : Value target :=
  match value with
  | .var name => .var (rho.var name)
  | .unit => .unit
  | .lam domain codomain body =>
      .lam (domain.rename rho) (codomain.rename rho) (body.rename rho.lift)
  | .object objectType payload =>
      .object (objectType.rename rho) (payload.rename rho)
  | .objectConsumer parameter result body =>
      .objectConsumer (parameter.rename rho) (result.rename rho)
        (body.rename rho.lift)

/-- Rename a computation, lifting below each runtime binder. -/
def Term.rename {source target : Scope} (term : Term source)
    (rho : Rename source target) : Term target :=
  match term with
  | .ret value => .ret (value.rename rho)
  | .select receiver label => .select (receiver.rename rho) label
  | .app function argument =>
      .app (function.rename rho) (argument.rename rho)
  | .let' result rhs body =>
      .let' (result.rename rho) (rhs.rename rho) (body.rename rho.lift)
  | .objectApp parameter function argument =>
      .objectApp (parameter.rename rho) (function.rename rho)
        (argument.rename rho)
  | .objectLet objectType result rhs body =>
      .objectLet (objectType.rename rho) (result.rename rho)
        (rhs.rename rho) (body.rename rho.lift)

end

namespace Value

/-- Weaken a value below one newer source variable. -/
def weaken {scope : Scope} (value : Value scope) : Value (scope + 1) :=
  value.rename DOTCapture.Acyclic.Rename.succ

end Value

namespace Term

/-- Weaken a computation below one newer source variable. -/
def weaken {scope : Scope} (term : Term scope) : Term (scope + 1) :=
  term.rename DOTCapture.Acyclic.Rename.succ

end Term

namespace ObjectType

/-- The positive type of an object carrying this static interface. -/
def formedType {scope : Scope} : ObjectType scope -> Ty scope
  | object@(.mk _interface _representation outerCapture) =>
      .capturing outerCapture (.object object)

end ObjectType

/-- Direct negative use admits only a canonical literal or an already stable
variable.  Other object-producing computations must be named by `objectLet`. -/
inductive ObjectArgument.Form : Type where
  | canonicalLiteral
  | stableVariable
  | requiresExplicitOpen
deriving DecidableEq, Repr

namespace ObjectArgument

def classify {scope : Scope} : Term scope -> Form
  | .ret (.object _ _) => .canonicalLiteral
  | .ret (.var _) => .stableVariable
  | _ => .requiresExplicitOpen

end ObjectArgument

end DOTCapture.Intersections.GeneralExpression
