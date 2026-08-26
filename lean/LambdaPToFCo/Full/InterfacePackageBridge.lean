import LambdaPToFCo.Full.FunctionModel
import LambdaPToFCo.Full.ValueInterface

/-!
# Package bridges for one concrete opened interface

The forward bridge repacks an arbitrary value of the retained hidden identity
using the interface's already-available observation fields. The reverse bridge
is intentionally value-specific: it returns the retained payload constant.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace InterfacePackageBridge

/-- Target types observe only type-variable components of a substitution. -/
private theorem Ty.subst_eq_of_tvar
    (type : Ty source) (first second : Subst source target)
    (equal : forall index, first.tvar index = second.tvar index) :
    type.subst first = type.subst second := by
  induction type generalizing target with
  | top => rfl
  | tvar index => exact equal index
  | arrow parameter result parameterIH resultIH =>
      simp only [Ty.subst]
      congr 1
      · exact parameterIH first second equal
      · exact resultIH first second equal
  | poly body bodyIH =>
      simp only [Ty.subst]
      congr 1
      apply bodyIH
      intro index
      cases index with
      | here => rfl
      | there index =>
          exact congrArg (fun type => type.weaken .tvar) (equal index)
  | qual source target body sourceIH targetIH bodyIH =>
      simp only [Ty.subst]
      congr 1
      · exact sourceIH first second equal
      · exact targetIH first second equal
      · apply bodyIH
        intro index
        cases index with
        | there index =>
            exact congrArg (fun type => type.weaken .cvar) (equal index)

/-- Mixed telescope indices likewise observe only type-variable components. -/
private theorem Telescope.subst_eq_of_tvar
    (tele : Telescope source) (first second : Subst source target)
    (equal : forall index, first.tvar index = second.tvar index) :
    tele.subst first = tele.subst second := by
  induction tele generalizing target with
  | nil => rfl
  | var type tail ih =>
      simp only [Telescope.subst]
      congr 1
      · exact Ty.subst_eq_of_tvar type first second equal
      · apply ih
        intro index
        cases index with
        | there index =>
            exact congrArg (fun type => type.weaken .var) (equal index)
  | tvar tail ih =>
      simp only [Telescope.subst]
      congr 1
      apply ih
      intro index
      cases index with
      | here => rfl
      | there index =>
          exact congrArg (fun type => type.weaken .tvar) (equal index)
  | cvar source result tail ih =>
      simp only [Telescope.subst]
      congr 1
      · exact Ty.subst_eq_of_tvar source first second equal
      · exact Ty.subst_eq_of_tvar result first second equal
      · apply ih
        intro index
        cases index with
        | there index =>
            exact congrArg (fun type => type.weaken .cvar) (equal index)

/-- Opening the payload binder of an observation telescope is independent of
the payload term. This is the precise target-language fact used by repacking. -/
theorem observation_payload_irrel
    (observations : Telescope ((sig ,, .tvar) ,, .var))
    (identity : Ty sig) (first second : Exp sig) :
    (observations.subst ((Subst.openTVar identity).lift .var)).subst
        (Subst.openVar first) =
      (observations.subst ((Subst.openTVar identity).lift .var)).subst
        (Subst.openVar second) := by
  apply Telescope.subst_eq_of_tvar
  intro index
  cases index with
  | there index => rfl

/-- Replace only the payload of an opened interface. Its observation Args
remain well indexed because target types cannot inspect term variables. -/
noncomputable def repayload {sig : Sig} {base : Ctx sig}
    (interface : ValueInterface base) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload interface.identity) :
    ValueInterface base where
  plan := interface.plan
  identity := interface.identity
  payload := payload
  payloadTyping := payloadTyping
  observations := by
    rw [← observation_payload_irrel interface.plan.observations
      interface.identity interface.payload payload]
    exact interface.observations

@[simp] theorem repayload_plan {sig : Sig} {base : Ctx sig}
    (interface : ValueInterface base) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload interface.identity) :
    (repayload interface payload payloadTyping).plan = interface.plan := by
  rfl

@[simp] theorem repayload_identity {sig : Sig} {base : Ctx sig}
    (interface : ValueInterface base) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload interface.identity) :
    (repayload interface payload payloadTyping).identity =
      interface.identity := by
  rfl

@[simp] theorem repayload_payload {sig : Sig} {base : Ctx sig}
    (interface : ValueInterface base) (payload : Exp sig)
    (payloadTyping : Exp.HasType base payload interface.identity) :
    (repayload interface payload payloadTyping).payload = payload := by
  rfl

/-- The interface renamed under `x : I`, with `x` replacing the retained
payload while every observation field is reused. -/
noncomputable def atArgument {sig : Sig} {base : Ctx sig}
    (interface : ValueInterface base) :
    ValueInterface (base.bindVar interface.identity) := by
  let renamed := interface.rename (Rename.weaken .var)
    (Rename.Typed.weaken base (.var interface.identity))
  have argumentTyping :
      Exp.HasType (base.bindVar interface.identity) (.var .here)
        renamed.identity := by
    rw [ValueInterface.rename_identity]
    exact .var Ctx.Lookup.here
  exact repayload renamed (.var .here) argumentTyping

@[simp] theorem atArgument_plan {sig : Sig} {base : Ctx sig}
    (interface : ValueInterface base) :
    (atArgument interface).plan =
      interface.plan.rename (Rename.weaken .var) := by
  rfl

@[simp] theorem atArgument_identity {sig : Sig} {base : Ctx sig}
    (interface : ValueInterface base) :
    (atArgument interface).identity =
      interface.identity.weaken .var := by
  rfl

@[simp] theorem atArgument_payload {sig : Sig} {base : Ctx sig}
    (interface : ValueInterface base) :
    (atArgument interface).payload = (.var .here : Exp (sig ,, .var)) := by
  rfl

/-- Forward adapter body: package arbitrary `x : I` with the concrete
interface's retained observation values. -/
noncomputable def toPackageBody {sig : Sig} {base : Ctx sig}
    (interface : ValueInterface base) : Exp (sig ,, .var) :=
  (atArgument interface).package

noncomputable def toPackageBody_hasType
    {sig : Sig} {base : Ctx sig} (interface : ValueInterface base) :
    Exp.HasType (base.bindVar interface.identity)
      (toPackageBody interface) (interface.plan.inputTy.weaken .var) := by
  have typed := (atArgument interface).package_hasType
  rw [atArgument_plan] at typed
  simpa only [Ty.weaken, ValuePlan.inputTy_rename] using typed

/-- Repack arbitrary hidden-identity values at this interface's public plan
type. -/
noncomputable def toPackage {sig : Sig} {base : Ctx sig}
    (interface : ValueInterface base) : Co sig :=
  .adapter interface.identity (toPackageBody interface)

noncomputable def toPackage_hasType
    {sig : Sig} {base : Ctx sig} (interface : ValueInterface base) :
    Co.HasType base (toPackage interface) interface.identity
      interface.plan.inputTy :=
  .adapter (toPackageBody_hasType interface)

/-- Reverse adapter body. It deliberately ignores its package argument and
returns the concrete interface's retained payload. -/
def fromPackageBody {sig : Sig} {base : Ctx sig}
    (interface : ValueInterface base) : Exp (sig ,, .var) :=
  interface.payload.weaken .var

noncomputable def fromPackageBody_hasType
    {sig : Sig} {base : Ctx sig} (interface : ValueInterface base) :
    Exp.HasType (base.bindVar interface.plan.inputTy)
      (fromPackageBody interface) (interface.identity.weaken .var) :=
  interface.payloadTyping.weaken (.var interface.plan.inputTy)

/-- Map any package at the interface's plan back to the retained payload.
This is a value-specific constant bridge, not an existential identity
eliminator and not an inverse law for arbitrary packages. -/
def fromPackage {sig : Sig} {base : Ctx sig}
    (interface : ValueInterface base) : Co sig :=
  .adapter interface.plan.inputTy (fromPackageBody interface)

noncomputable def fromPackage_hasType
    {sig : Sig} {base : Ctx sig} (interface : ValueInterface base) :
    Co.HasType base (fromPackage interface) interface.plan.inputTy
      interface.identity :=
  .adapter (fromPackageBody_hasType interface)

theorem fromPackageBody_rename
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target}
    (interface : ValueInterface sourceContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    (fromPackageBody interface).rename (mapping.lift .var) =
      fromPackageBody (interface.rename mapping typed) := by
  unfold fromPackageBody
  rw [Exp.weaken_rename_comm, ValueInterface.rename_payload]

theorem fromPackage_rename
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target}
    (interface : ValueInterface sourceContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    (fromPackage interface).rename mapping =
      fromPackage (interface.rename mapping typed) := by
  unfold fromPackage
  simp only [Co.rename]
  have planEq : (interface.rename mapping typed).plan =
      interface.plan.rename mapping := by
    rfl
  rw [ValuePlan.inputTy_rename interface.plan mapping,
    fromPackageBody_rename interface mapping typed, planEq]

/-- Renaming the forward bridge preserves its endpoint typing. This avoids a
false definitional equality claim through dependent `Args` proof transports. -/
noncomputable def toPackage_rename_hasType
    {source target : Sig} {sourceContext : Ctx source}
    {targetContext : Ctx target}
    (interface : ValueInterface sourceContext)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Co.HasType targetContext ((toPackage interface).rename mapping)
      (interface.rename mapping typed).identity
      (interface.rename mapping typed).plan.inputTy := by
  have renamed := (toPackage_hasType interface).rename typed
  simpa only [ValueInterface.rename_identity,
    ValuePlan.inputTy_rename] using renamed

end InterfacePackageBridge

namespace InterfacePackageBridgeRegression

def domain : ValuePlan ([] : Sig) := FunctionRegression.domain

def codomain : ValuePlan domain.scope := FunctionRegression.codomain

noncomputable def implementation : Exp ([] : Sig) :=
  Function.abstraction domain FunctionRegression.body

noncomputable def implementation_hasType :
    Exp.HasType Ctx.empty implementation (Function.codeTy domain codomain) := by
  exact Function.abstraction_hasType domain codomain
    FunctionRegression.body FunctionRegression.body_hasType

noncomputable def functionInterface : ValueInterface Ctx.empty :=
  ValueInterface.ofArguments (Function.plan domain codomain)
    (Function.exactArguments domain codomain implementation
      implementation_hasType)

@[simp] theorem functionInterface_plan :
    functionInterface.plan = Function.plan domain codomain := by
  unfold functionInterface Function.exactArguments Function.arguments
  rfl

@[simp] theorem functionInterface_identity :
    functionInterface.identity = Function.codeTy domain codomain := by
  unfold functionInterface Function.exactArguments Function.arguments
  rfl

noncomputable def forwardTyping :
    Co.HasType Ctx.empty
      (InterfacePackageBridge.toPackage functionInterface)
      functionInterface.identity functionInterface.plan.inputTy :=
  InterfacePackageBridge.toPackage_hasType functionInterface

noncomputable def reverseTyping :
    Co.HasType Ctx.empty
      (InterfacePackageBridge.fromPackage functionInterface)
      functionInterface.plan.inputTy functionInterface.identity :=
  InterfacePackageBridge.fromPackage_hasType functionInterface

noncomputable def concreteForwardTyping :
    Co.HasType Ctx.empty
      (InterfacePackageBridge.toPackage functionInterface)
      (Function.codeTy domain codomain)
      (Function.plan domain codomain).inputTy := by
  simpa only [functionInterface_identity, functionInterface_plan] using
    forwardTyping

noncomputable def concreteReverseTyping :
    Co.HasType Ctx.empty
      (InterfacePackageBridge.fromPackage functionInterface)
      (Function.plan domain codomain).inputTy
      (Function.codeTy domain codomain) := by
  simpa only [functionInterface_identity, functionInterface_plan] using
    reverseTyping

end InterfacePackageBridgeRegression

end LambdaPToFCo.Full
