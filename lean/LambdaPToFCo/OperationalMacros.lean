import LambdaPToFCo.Interface
import SystemFCo.Operational

/-!
# Operational macro laws for compiled binders

These lemmas concern only target syntax and target reduction.  In particular,
opening an exact binding below is ordinary Church-package reduction; it does
not appeal to a source store, a realization relation, or runtime subtyping.
-/

namespace LambdaPToFCo
namespace OperationalMacros

open SystemFCo

namespace CompiledBinder

/-! ## Small target-substitution cancellations -/

@[simp] theorem exp_weaken_openVar (expression : Exp sig)
    (argument : Exp sig) :
    (expression.weaken .var).subst (Subst.openVar argument) = expression :=
  expression.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openVar argument)

@[simp] theorem ty_weaken_openVar (ty : Ty sig) (argument : Exp sig) :
    (ty.weaken .var).subst (Subst.openVar argument) = ty :=
  ty.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openVar argument)

@[simp] theorem co_weaken_openVar (coercion : Co sig)
    (argument : Exp sig) :
    (coercion.weaken .var).subst (Subst.openVar argument) = coercion :=
  coercion.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openVar argument)

@[simp] theorem exp_weaken_openTVar (expression : Exp sig)
    (argument : Ty sig) :
    (expression.weaken .tvar).subst (Subst.openTVar argument) = expression :=
  expression.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openTVar argument)

@[simp] theorem ty_weaken_openTVar (ty : Ty sig) (argument : Ty sig) :
    (ty.weaken .tvar).subst (Subst.openTVar argument) = ty :=
  ty.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openTVar argument)

@[simp] theorem co_weaken_openTVar (coercion : Co sig)
    (argument : Ty sig) :
    (coercion.weaken .tvar).subst (Subst.openTVar argument) = coercion :=
  coercion.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openTVar argument)

@[simp] theorem exp_weaken_openCVar (expression : Exp sig)
    (argument : Co sig) :
    (expression.weaken .cvar).subst (Subst.openCVar argument) = expression :=
  expression.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openCVar argument)

@[simp] theorem ty_weaken_openCVar (ty : Ty sig) (argument : Co sig) :
    (ty.weaken .cvar).subst (Subst.openCVar argument) = ty :=
  ty.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openCVar argument)

@[simp] theorem co_weaken_openCVar (coercion : Co sig)
    (argument : Co sig) :
    (coercion.weaken .cvar).subst (Subst.openCVar argument) = coercion :=
  coercion.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openCVar argument)

@[simp] theorem exp_weaken_subst_lift (expression : Exp source)
    (substitution : Subst source target) :
    (expression.weaken kind).subst (substitution.lift kind) =
      (expression.subst substitution).weaken kind :=
  (expression.weaken_subst_comm_base substitution).symm

@[simp] theorem ty_weaken_subst_lift (ty : Ty source)
    (substitution : Subst source target) :
    (ty.weaken kind).subst (substitution.lift kind) =
      (ty.subst substitution).weaken kind :=
  (ty.weaken_subst_comm_base substitution).symm

@[simp] theorem co_weaken_subst_lift (coercion : Co source)
    (substitution : Subst source target) :
    (coercion.weaken kind).subst (substitution.lift kind) =
      (coercion.subst substitution).weaken kind :=
  (coercion.weaken_subst_comm_base substitution).symm

/-! ## Instantiating compiled interfaces -/

/-- Simultaneously instantiate all five target slots of an exact binder.

The composition follows the heterogeneous telescope from oldest to newest:
raw package, hidden witness type, lower evidence, upper evidence, and payload.
Consequently it maps those five fresh slots to `package`, `witness`,
`lowerEvidence`, `upperEvidence`, and `payload`, while leaving the old scope
unchanged. -/
def exactSubst
    (package : Exp sig) (witness : Ty sig)
    (lowerEvidence upperEvidence : Co sig) (payload : Exp sig) :
    Subst (((((sig ,, .var) ,, .tvar) ,, .cvar) ,, .cvar) ,, .var) sig :=
  let raw :=
    ((((Subst.openVar package).lift .tvar).lift .cvar).lift .cvar).lift .var
  let hidden :=
    (((Subst.openTVar witness).lift .cvar).lift .cvar).lift .var
  let lower := ((Subst.openCVar lowerEvidence).lift .cvar).lift .var
  let upper := (Subst.openCVar upperEvidence).lift .var
  let value := Subst.openVar payload
  (((raw.comp hidden).comp lower).comp upper).comp value

/-- Instantiation of the complete body scope for an exact binder. -/
def instantiateExact
    (body : Exp (((((sig ,, .var) ,, .tvar) ,, .cvar) ,, .cvar) ,, .var))
    (package : Exp sig) (witness : Ty sig)
    (lowerEvidence upperEvidence : Co sig) (payload : Exp sig) : Exp sig :=
  body.subst (exactSubst package witness lowerEvidence upperEvidence payload)

/-! ## Binder macro laws -/

/-- An ordinary compiled binder is just one call-by-value beta step. -/
theorem close_ordinary_step
    (argumentValue : Exp.IsValue argument) :
    Exp.Step
      ((Interface.BinderPlan.ordinary valueType).close argument result body)
      (body.subst (Subst.openVar argument)) := by
  exact .beta argumentValue

/-- Opening an exact compiled binder is a seven-step target-language macro:
one beta step binds the raw package, then the Church encoding performs one
type beta, one handler beta, one hidden-type beta, two coercion betas, and one
payload beta. -/
theorem close_exact_pack_steps
    (payloadValue : Exp.IsValue payload) :
    Exp.Steps
      ((Interface.BinderPlan.exact lower upper payloadType).close
        (Exp.packMember lower upper witness payloadType
          lowerEvidence upperEvidence payload)
        result body)
      (instantiateExact body
        (Exp.packMember lower upper witness payloadType
          lowerEvidence upperEvidence payload)
        witness lowerEvidence upperEvidence payload) := by
  apply Exp.Steps.tail (.beta .tabs)
  apply Exp.Steps.tail (.appFunction .typeBeta)
  apply Exp.Steps.tail (.beta .tabs)
  apply Exp.Steps.tail
    (.appFunction (.cappFunction (.cappFunction .typeBeta)))
  apply Exp.Steps.tail
    (.appFunction (.cappFunction .coercionBeta))
  apply Exp.Steps.tail (.appFunction .coercionBeta)
  simp only [exp_weaken_subst_lift, ty_weaken_subst_lift,
    co_weaken_subst_lift, exp_weaken_openVar, ty_weaken_openVar,
    co_weaken_openVar, exp_weaken_openTVar, ty_weaken_openTVar,
    co_weaken_openTVar]
  apply Exp.Steps.tail (.beta payloadValue)
  simp only [Exp.subst_comp]
  change Exp.Steps
    (body.subst (exactSubst
      (Exp.packMember lower upper witness payloadType
        lowerEvidence upperEvidence payload)
      witness lowerEvidence upperEvidence payload))
    (instantiateExact body
      (Exp.packMember lower upper witness payloadType
        lowerEvidence upperEvidence payload)
      witness lowerEvidence upperEvidence payload)
  exact .refl

end CompiledBinder

end OperationalMacros
end LambdaPToFCo
