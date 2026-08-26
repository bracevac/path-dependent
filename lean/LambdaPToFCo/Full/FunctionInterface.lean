import LambdaPToFCo.Full.FunctionModel
import LambdaPToFCo.Full.ValueInterface

/-!
# Opened dependent-function interfaces

A function value remains hidden behind its stable identity.  An opened
interface supplies the retained `I ⇒ code` observation, which this module
turns into executable dependent code without identifying `I` with the code
type.  Application consumes the complete mixed argument interface and
therefore instantiates the dependent codomain by the exact heterogeneous
substitution represented by those arguments.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace FunctionInterface

/-- The single function observation after opening a concrete value
interface. -/
structure Observation {sig : Sig} (base : Ctx sig)
    (identity code : Ty sig) : Type where
  coercion : Co sig
  typing : Co.HasType base coercion identity code

noncomputable def observationArguments
    {sig : Sig} {base : Ctx sig}
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope)
    (interface : ValueInterface base)
    (plan_eq : interface.plan = Function.plan domain codomain) :
    Telescope.Args base
      (.cvar interface.identity (Function.codeTy domain codomain) .nil) := by
  have arguments := interface.observations
  rw [plan_eq] at arguments
  simpa only [Function.plan, Telescope.subst,
    Single.identityAtPayload_open,
    Function.codeAtPayload_open] using arguments

noncomputable def observation
    {sig : Sig} {base : Ctx sig}
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope)
    (interface : ValueInterface base)
    (plan_eq : interface.plan = Function.plan domain codomain) :
    Observation base interface.identity (Function.codeTy domain codomain) := by
  have arguments := observationArguments domain codomain interface plan_eq
  cases arguments with
  | cvar coercion typing rest => exact ⟨coercion, typing⟩

/-- A concrete opened value known to implement the indicated dependent
function plan. -/
structure View {sig : Sig} (base : Ctx sig)
    (domain : ValuePlan sig) (codomain : ValuePlan domain.scope) : Type where
  interface : ValueInterface base
  plan_eq : interface.plan = Function.plan domain codomain

namespace View

noncomputable def toCode
    {sig : Sig} {base : Ctx sig}
    {domain : ValuePlan sig} {codomain : ValuePlan domain.scope}
    (view : View base domain codomain) : Co sig :=
  (observation domain codomain view.interface view.plan_eq).coercion

noncomputable def toCode_hasType
    {sig : Sig} {base : Ctx sig}
    {domain : ValuePlan sig} {codomain : ValuePlan domain.scope}
    (view : View base domain codomain) :
    Co.HasType base view.toCode view.interface.identity
      (Function.codeTy domain codomain) :=
  (observation domain codomain view.interface view.plan_eq).typing

/-- Cast the retained function payload to its executable mixed-telescope
code. -/
noncomputable def asCode
    {sig : Sig} {base : Ctx sig}
    {domain : ValuePlan sig} {codomain : ValuePlan domain.scope}
    (view : View base domain codomain) : Exp sig :=
  .cast view.interface.payload view.toCode

noncomputable def asCode_hasType
    {sig : Sig} {base : Ctx sig}
    {domain : ValuePlan sig} {codomain : ValuePlan domain.scope}
    (view : View base domain codomain) :
    Exp.HasType base view.asCode (Function.codeTy domain codomain) :=
  .cast view.interface.payloadTyping view.toCode_hasType

/-- Apply the retained code to every field of a concrete domain interface. -/
noncomputable def apply
    {sig : Sig} {base : Ctx sig}
    {domain : ValuePlan sig} {codomain : ValuePlan domain.scope}
    (view : View base domain codomain)
    (arguments : Telescope.Args base domain.telescope) : Exp sig :=
  arguments.apply view.asCode

noncomputable def apply_hasType
    {sig : Sig} {base : Ctx sig}
    {domain : ValuePlan sig} {codomain : ValuePlan domain.scope}
    (view : View base domain codomain)
    (arguments : Telescope.Args base domain.telescope) :
    Exp.HasType base (view.apply arguments)
      (codomain.inputTy.subst arguments.substitution) := by
  have typing := arguments.apply_hasType view.asCode_hasType
  rw [arguments.instantiate_eq_subst] at typing
  exact typing

/-- Apply directly to an opened domain interface. -/
noncomputable def applyInterface
    {sig : Sig} {base : Ctx sig}
    {domain : ValuePlan sig} {codomain : ValuePlan domain.scope}
    (view : View base domain codomain)
    (argument : ValueInterface base)
    (plan_eq : argument.plan = domain) : Exp sig := by
  subst plan_eq
  exact view.apply argument.arguments

noncomputable def applyInterface_hasType
    {sig : Sig} {base : Ctx sig}
    {domain : ValuePlan sig} {codomain : ValuePlan domain.scope}
    (view : View base domain codomain)
    (argument : ValueInterface base)
    (plan_eq : argument.plan = domain) :
    Exp.HasType base (view.applyInterface argument plan_eq)
      (codomain.inputTy.subst (by
        subst plan_eq
        exact argument.arguments.substitution)) := by
  subst plan_eq
  exact view.apply_hasType argument.arguments

end View

/-! The result type is definitionally the codomain opened by the exact
mixed argument substitution; this is the key dependent-application index. -/

noncomputable example {sig : Sig} {base : Ctx sig}
    {domain : ValuePlan sig} {codomain : ValuePlan domain.scope}
    (view : View base domain codomain)
    (argument : ValueInterface base)
    (plan_eq : argument.plan = domain) :
    Exp.HasType base (view.applyInterface argument plan_eq)
      (codomain.inputTy.subst (by
        subst plan_eq
        exact argument.arguments.substitution)) :=
  view.applyInterface_hasType argument plan_eq

end FunctionInterface

end LambdaPToFCo.Full
