import LambdaPToFCo.OperationalEnvironment

/-!
# Substitution naturality for compiled binder interfaces

This module makes compiled binder plans and their concrete instantiations
functorial under arbitrary heterogeneous `SystemFCo.Subst`s.  An ordinary
plan lifts a substitution through one term binder.  An exact plan lifts it
through the complete raw-package/type/evidence/evidence/payload telescope.

These are target-syntax equations only.  They do not interpret source types
or appeal to a source realization relation.
-/

namespace SystemFCo

namespace Ty

/-- Substitution commutes with inserting a binder immediately below a
newest type binder. -/
theorem insertBelowTVar_subst (payload : Ty (source ,, .tvar))
    (inserted : Kind) (substitution : Subst source target) :
    (payload.rename ((Rename.weaken inserted).lift .tvar)).subst
        ((substitution.lift inserted).lift .tvar) =
      (payload.subst (substitution.lift .tvar)).rename
        ((Rename.weaken inserted).lift .tvar) := by
  have comm : Subst.RenameComm (substitution.lift .tvar)
      ((Rename.weaken inserted).lift .tvar)
      ((Rename.weaken inserted).lift .tvar)
      ((substitution.lift inserted).lift .tvar) := by
    constructor
    · intro index
      cases index with
      | there index =>
          simp only [Rename.lift_there, Subst.lift_var_there]
          exact Exp.weaken_rename_comm (substitution.var index)
            (Rename.weaken inserted)
    · intro index
      cases index with
      | here => rfl
      | there index =>
          simp only [Rename.lift_there, Subst.lift_tvar_there]
          exact Ty.weaken_rename_comm (substitution.tvar index)
            (Rename.weaken inserted)
    · intro index
      cases index with
      | there index =>
          simp only [Rename.lift_there, Subst.lift_cvar_there]
          exact Co.weaken_rename_comm (substitution.cvar index)
            (Rename.weaken inserted)
  exact (payload.rename_subst_comm comm).symm

/-- Specialization used by the Church package encoding. -/
theorem insertUnderTVar_subst (payload : Ty (source ,, .tvar))
    (substitution : Subst source target) :
    (payload.rename ChurchPackage.insertUnderTVar).subst
        ((substitution.lift .tvar).lift .tvar) =
      (payload.subst (substitution.lift .tvar)).rename
        ChurchPackage.insertUnderTVar := by
  simpa only [ChurchPackage.insertUnderTVar] using
    insertBelowTVar_subst payload .tvar substitution

/-- Substitution through a Church-encoded abstract-member type. -/
theorem member_subst (lower upper : Ty source)
    (payload : Ty (source ,, .tvar))
    (substitution : Subst source target) :
    (Ty.member lower upper payload).subst substitution =
      Ty.member (lower.subst substitution) (upper.subst substitution)
        (payload.subst (substitution.lift .tvar)) := by
  unfold Ty.member Ty.memberBody
  simp only [Ty.subst, Ty.memberHandler_subst,
    ← Ty.weaken_subst_comm_base, Subst.lift_tvar_here]
  rw [insertUnderTVar_subst]

end Ty

namespace Exp

theorem memberHandler_subst
    (lower upper : Ty source) (payloadTy : Ty (source ,, .tvar))
    (body : Exp ((((source ,, .tvar) ,, .cvar) ,, .cvar) ,, .var))
    (substitution : Subst source target) :
    (Exp.memberHandler lower upper payloadTy body).subst substitution =
      Exp.memberHandler (lower.subst substitution)
        (upper.subst substitution)
        (payloadTy.subst (substitution.lift .tvar))
        (body.subst
          ((((substitution.lift .tvar).lift .cvar).lift .cvar).lift .var)) := by
  unfold Exp.memberHandler
  simp only [Exp.subst, Ty.subst, ← Ty.weaken_subst_comm_base,
    Subst.lift_tvar_here]

theorem unpackMember_subst
    (package : Exp source) (result : Ty source) (handler : Exp source)
    (substitution : Subst source target) :
    (Exp.unpackMember package result handler).subst substitution =
      Exp.unpackMember (package.subst substitution)
        (result.subst substitution) (handler.subst substitution) := by
  rfl

theorem unpackMemberBody_subst
    (package : Exp source) (lower upper result : Ty source)
    (payloadTy : Ty (source ,, .tvar))
    (body : Exp ((((source ,, .tvar) ,, .cvar) ,, .cvar) ,, .var))
    (substitution : Subst source target) :
    (Exp.unpackMemberBody package lower upper result payloadTy body).subst
        substitution =
      Exp.unpackMemberBody (package.subst substitution)
        (lower.subst substitution) (upper.subst substitution)
        (result.subst substitution)
        (payloadTy.subst (substitution.lift .tvar))
        (body.subst
          ((((substitution.lift .tvar).lift .cvar).lift .cvar).lift .var)) := by
  unfold Exp.unpackMemberBody
  rw [unpackMember_subst, memberHandler_subst]

/-- Substitution distributes through exact-package introduction. -/
theorem packMember_subst
    (lower upper witness : Ty source)
    (payloadTy : Ty (source ,, .tvar))
    (lowerEvidence upperEvidence : Co source) (payload : Exp source)
    (substitution : Subst source target) :
    (Exp.packMember lower upper witness payloadTy lowerEvidence
      upperEvidence payload).subst substitution =
      Exp.packMember (lower.subst substitution) (upper.subst substitution)
        (witness.subst substitution)
        (payloadTy.subst (substitution.lift .tvar))
        (lowerEvidence.subst substitution) (upperEvidence.subst substitution)
        (payload.subst substitution) := by
  unfold Exp.packMember
  simp only [Exp.subst, Ty.memberHandler_subst,
    ← Ty.weaken_subst_comm_base, ← Co.weaken_subst_comm_base,
    ← Exp.weaken_subst_comm_base, Subst.lift_var_here]
  rw [Ty.insertUnderTVar_subst]
  rfl

end Exp

namespace Subst

/-- Opening a term binder commutes with lifting through any newer
heterogeneous telescope. -/
theorem openVar_liftMany_comp (argument : Exp source)
    (substitution : Subst source target) (binders : Sig) :
    ((Subst.openVar argument).liftMany binders).comp
        (substitution.liftMany binders) =
      ((substitution.lift .var).liftMany binders).comp
        ((Subst.openVar (argument.subst substitution)).liftMany binders) := by
  rw [← Subst.comp_liftMany, Subst.openVar_comp, Subst.comp_liftMany]

/-- Type-binder counterpart of `openVar_liftMany_comp`. -/
theorem openTVar_liftMany_comp (argument : Ty source)
    (substitution : Subst source target) (binders : Sig) :
    ((Subst.openTVar argument).liftMany binders).comp
        (substitution.liftMany binders) =
      ((substitution.lift .tvar).liftMany binders).comp
        ((Subst.openTVar (argument.subst substitution)).liftMany binders) := by
  rw [← Subst.comp_liftMany, Subst.openTVar_comp, Subst.comp_liftMany]

/-- Coercion-binder counterpart of `openVar_liftMany_comp`. -/
theorem openCVar_liftMany_comp (argument : Co source)
    (substitution : Subst source target) (binders : Sig) :
    ((Subst.openCVar argument).liftMany binders).comp
        (substitution.liftMany binders) =
      ((substitution.lift .cvar).liftMany binders).comp
        ((Subst.openCVar (argument.subst substitution)).liftMany binders) := by
  rw [← Subst.comp_liftMany, Subst.openCVar_comp, Subst.comp_liftMany]

end Subst
end SystemFCo

namespace LambdaPToFCo

open SystemFCo

namespace Interface
namespace BinderPlan

/-- Substitute every type occurring in a compiled binder plan. -/
def subst : BinderPlan source -> Subst source target -> BinderPlan target
| .ordinary valueType, substitution =>
    .ordinary (valueType.subst substitution)
| .exact lower upper payloadType, substitution =>
    .exact (lower.subst substitution) (upper.subst substitution)
      (payloadType.subst (substitution.lift .tvar))

/-- Lift a base substitution through every slot introduced by a plan. -/
def scopeSubst (plan : BinderPlan source)
    (substitution : Subst source target) :
    Subst plan.scope (plan.subst substitution).scope :=
  match plan with
  | .ordinary _ => substitution.lift .var
  | .exact _ _ _ =>
      ((((substitution.lift .var).lift .tvar).lift .cvar).lift .cvar).lift .var

@[simp] theorem subst_ordinary (valueType : Ty source)
    (substitution : Subst source target) :
    (BinderPlan.ordinary valueType).subst substitution =
      .ordinary (valueType.subst substitution) := rfl

@[simp] theorem subst_exact (lower upper : Ty source)
    (payloadType : Ty (source ,, .tvar))
    (substitution : Subst source target) :
    (BinderPlan.exact lower upper payloadType).subst substitution =
      .exact (lower.subst substitution) (upper.subst substitution)
        (payloadType.subst (substitution.lift .tvar)) := rfl

@[simp] theorem inputType_subst (plan : BinderPlan source)
    (substitution : Subst source target) :
    plan.inputType.subst substitution =
      (plan.subst substitution).inputType := by
  cases plan with
  | ordinary => rfl
  | exact lower upper payloadType =>
      exact Ty.member_subst lower upper payloadType substitution

@[simp] theorem rawLower_subst (lower : Ty source)
    (substitution : Subst source target) :
    (rawLower lower).subst (substitution.lift .var) =
      rawLower (lower.subst substitution) := by
  exact (Ty.weaken_subst_comm_base lower substitution).symm

@[simp] theorem rawUpper_subst (upper : Ty source)
    (substitution : Subst source target) :
    (rawUpper upper).subst (substitution.lift .var) =
      rawUpper (upper.subst substitution) := by
  exact (Ty.weaken_subst_comm_base upper substitution).symm

@[simp] theorem rawPayload_subst (payloadType : Ty (source ,, .tvar))
    (substitution : Subst source target) :
    (rawPayload payloadType).subst
        ((substitution.lift .var).lift .tvar) =
      rawPayload (payloadType.subst (substitution.lift .tvar)) := by
  simpa only [rawPayload] using
    Ty.insertBelowTVar_subst payloadType .var substitution

/-- Substitution commutes with both forms of compiled binder elimination. -/
theorem close_subst (plan : BinderPlan source)
    (argument : Exp source) (result : Ty source) (body : Exp plan.scope)
    (substitution : Subst source target) :
    (plan.close argument result body).subst substitution =
      (plan.subst substitution).close (argument.subst substitution)
        (result.subst substitution)
        (body.subst (plan.scopeSubst substitution)) := by
  cases plan with
  | ordinary valueType => rfl
  | exact lower upper payloadType =>
      unfold close subst scopeSubst
      simp only [Exp.subst, Ty.member_subst]
      rw [Exp.unpackMemberBody_subst]
      simp only [rawLower_subst, rawUpper_subst, rawPayload_subst,
        Exp.subst, Subst.lift_var_here]
      rw [← Ty.weaken_subst_comm_base result substitution]
      rfl

end BinderPlan
end Interface

namespace OperationalMacros
namespace CompiledBinder

/-! The exact substitution equation is factored through the five opening
substitutions rather than proved by enumerating mixed de Bruijn indices. -/

theorem exactSubst_comp
    (lower upper witness : Ty source)
    (payloadType : Ty (source ,, .tvar))
    (lowerEvidence upperEvidence : Co source) (payload : Exp source)
    (substitution : Subst source target) :
    (exactSubst
        (Exp.packMember lower upper witness payloadType
          lowerEvidence upperEvidence payload)
        witness lowerEvidence upperEvidence payload).comp substitution =
      (((((substitution.lift .var).lift .tvar).lift .cvar).lift .cvar).lift
          .var).comp
        (exactSubst
          (Exp.packMember (lower.subst substitution)
            (upper.subst substitution) (witness.subst substitution)
            (payloadType.subst (substitution.lift .tvar))
            (lowerEvidence.subst substitution)
            (upperEvidence.subst substitution) (payload.subst substitution))
          (witness.subst substitution)
          (lowerEvidence.subst substitution)
          (upperEvidence.subst substitution) (payload.subst substitution)) := by
  let packageS := Exp.packMember lower upper witness payloadType
    lowerEvidence upperEvidence payload
  let packageT := Exp.packMember (lower.subst substitution)
    (upper.subst substitution) (witness.subst substitution)
    (payloadType.subst (substitution.lift .tvar))
    (lowerEvidence.subst substitution) (upperEvidence.subst substitution)
    (payload.subst substitution)
  let rawS := ((((Subst.openVar packageS).lift .tvar).lift .cvar).lift
    .cvar).lift .var
  let rawT := ((((Subst.openVar packageT).lift .tvar).lift .cvar).lift
    .cvar).lift .var
  let hiddenS := (((Subst.openTVar witness).lift .cvar).lift .cvar).lift .var
  let hiddenT := (((Subst.openTVar (witness.subst substitution)).lift
    .cvar).lift .cvar).lift .var
  let lowerS := ((Subst.openCVar lowerEvidence).lift .cvar).lift .var
  let lowerT := ((Subst.openCVar (lowerEvidence.subst substitution)).lift
    .cvar).lift .var
  let upperS := (Subst.openCVar upperEvidence).lift .var
  let upperT := (Subst.openCVar (upperEvidence.subst substitution)).lift .var
  let valueS := Subst.openVar payload
  let valueT := Subst.openVar (payload.subst substitution)
  let first := substitution.lift .var
  let second := (substitution.lift .cvar).lift .var
  let third := ((substitution.lift .cvar).lift .cvar).lift .var
  let fourth := (((substitution.lift .tvar).lift .cvar).lift .cvar).lift .var
  let fifth := ((((substitution.lift .var).lift .tvar).lift .cvar).lift
    .cvar).lift .var
  have valueNat : valueS.comp substitution = first.comp valueT := by
    exact Subst.openVar_comp payload substitution
  have upperNat : upperS.comp first = second.comp upperT := by
    simpa only [upperS, upperT, first, second, Subst.liftMany] using
      Subst.openCVar_liftMany_comp upperEvidence substitution [.var]
  have lowerNat : lowerS.comp second = third.comp lowerT := by
    simpa only [lowerS, lowerT, second, third, Subst.liftMany] using
      Subst.openCVar_liftMany_comp lowerEvidence substitution [.var, .cvar]
  have hiddenNat : hiddenS.comp third = fourth.comp hiddenT := by
    simpa only [hiddenS, hiddenT, third, fourth, Subst.liftMany] using
      Subst.openTVar_liftMany_comp witness substitution
        [.var, .cvar, .cvar]
  have packageNat : packageS.subst substitution = packageT := by
    exact Exp.packMember_subst _ _ _ _ _ _ _ _
  have rawNat : rawS.comp fourth = fifth.comp rawT := by
    simpa only [rawS, rawT, packageNat, fifth, fourth, Subst.liftMany] using
      Subst.openVar_liftMany_comp packageS substitution
        [.var, .cvar, .cvar, .tvar]
  change (((((rawS.comp hiddenS).comp lowerS).comp upperS).comp valueS).comp
      substitution) =
    fifth.comp ((((rawT.comp hiddenT).comp lowerT).comp upperT).comp valueT)
  calc
    (((((rawS.comp hiddenS).comp lowerS).comp upperS).comp valueS).comp
        substitution) =
        rawS.comp (hiddenS.comp (lowerS.comp
          (upperS.comp (valueS.comp substitution)))) := by
      repeat rw [Subst.comp_assoc]
    _ = rawS.comp (hiddenS.comp (lowerS.comp
          (upperS.comp (first.comp valueT)))) := by
      exact congrArg
        (fun tail => rawS.comp (hiddenS.comp (lowerS.comp
          (upperS.comp tail)))) valueNat
    _ = rawS.comp (hiddenS.comp (lowerS.comp
          (second.comp (upperT.comp valueT)))) := by
      have moved : upperS.comp (first.comp valueT) =
          second.comp (upperT.comp valueT) := by
        rw [← Subst.comp_assoc, upperNat, Subst.comp_assoc]
      exact congrArg
        (fun tail => rawS.comp (hiddenS.comp (lowerS.comp tail))) moved
    _ = rawS.comp (hiddenS.comp
          (third.comp (lowerT.comp (upperT.comp valueT)))) := by
      have moved : lowerS.comp (second.comp (upperT.comp valueT)) =
          third.comp (lowerT.comp (upperT.comp valueT)) := by
        rw [← Subst.comp_assoc, lowerNat, Subst.comp_assoc]
      exact congrArg (fun tail => rawS.comp (hiddenS.comp tail)) moved
    _ = rawS.comp
          (fourth.comp (hiddenT.comp (lowerT.comp (upperT.comp valueT)))) := by
      have moved : hiddenS.comp
            (third.comp (lowerT.comp (upperT.comp valueT))) =
          fourth.comp (hiddenT.comp (lowerT.comp (upperT.comp valueT))) := by
        rw [← Subst.comp_assoc, hiddenNat, Subst.comp_assoc]
      exact congrArg (fun tail => rawS.comp tail) moved
    _ = fifth.comp
          (rawT.comp (hiddenT.comp (lowerT.comp (upperT.comp valueT)))) := by
      rw [← Subst.comp_assoc, rawNat, Subst.comp_assoc]
    _ = fifth.comp
          ((((rawT.comp hiddenT).comp lowerT).comp upperT).comp valueT) := by
      congr 1
      repeat rw [Subst.comp_assoc]

end CompiledBinder
end OperationalMacros

namespace OperationalEnvironment
namespace Instantiation

/-- Substitute all concrete syntax stored in an instantiation. -/
def subst : {plan : Interface.BinderPlan source} ->
    Instantiation plan -> (substitution : Subst source target) ->
      Instantiation (plan.subst substitution)
| _, .ordinary value, substitution => .ordinary (value.subst substitution)
| _, .exact witness lowerEvidence upperEvidence payload, substitution =>
    .exact (witness.subst substitution)
      (lowerEvidence.subst substitution) (upperEvidence.subst substitution)
      (payload.subst substitution)

@[simp] theorem argument_subst
    {plan : Interface.BinderPlan source} (actual : Instantiation plan)
    (substitution : Subst source target) :
    actual.argument.subst substitution =
      (actual.subst substitution).argument := by
  cases actual with
  | ordinary => rfl
  | exact => exact Exp.packMember_subst _ _ _ _ _ _ _ _

/-- The substitution that opens a concrete interface is natural in its base
signature.  The right side first transports the whole interface telescope,
then opens the transported concrete data. -/
theorem substitution_comp
    {plan : Interface.BinderPlan source} (actual : Instantiation plan)
    (substitution : Subst source target) :
    actual.substitution.comp substitution =
      (plan.scopeSubst substitution).comp
        (actual.subst substitution).substitution := by
  cases actual with
  | ordinary value =>
      exact Subst.openVar_comp value substitution
  | exact witness lowerEvidence upperEvidence payload =>
      unfold OperationalEnvironment.Instantiation.substitution
        OperationalEnvironment.Instantiation.subst
        Interface.BinderPlan.scopeSubst
      exact OperationalMacros.CompiledBinder.exactSubst_comp
        _ _ witness _ lowerEvidence upperEvidence payload substitution

/-- Instantiating a compiled body commutes with substitution. -/
@[simp] theorem instantiate_subst
    {plan : Interface.BinderPlan source} (actual : Instantiation plan)
    (body : Exp plan.scope) (substitution : Subst source target) :
    (actual.instantiate body).subst substitution =
      (actual.subst substitution).instantiate
        (body.subst (plan.scopeSubst substitution)) := by
  unfold instantiate
  rw [Exp.subst_comp, Exp.subst_comp, substitution_comp]

/-- Substitution preserves the operational readiness of an instantiation. -/
theorem Ready.subst
    {plan : Interface.BinderPlan source} {actual : Instantiation plan}
    (ready : actual.Ready) (substitution : Subst source target) :
    (actual.subst substitution).Ready := by
  cases actual with
  | ordinary value =>
      exact SystemFCo.Exp.IsValue.subst ready substitution
  | exact witness lowerEvidence upperEvidence payload =>
      exact SystemFCo.Exp.IsValue.subst ready substitution

end Instantiation

namespace ClosingEnv

/-- Close the types in a binder plan with an environment. -/
def closePlan (environment : ClosingEnv source target)
    (plan : Interface.BinderPlan source) : Interface.BinderPlan target :=
  plan.subst environment.substitution

/-- Close all concrete syntax carried by a binder instantiation. -/
def closeInstantiation (environment : ClosingEnv source target)
    {plan : Interface.BinderPlan source} (actual : Instantiation plan) :
    Instantiation (environment.closePlan plan) :=
  actual.subst environment.substitution

/-- Close a body under the whole interface telescope. -/
def closeBody (environment : ClosingEnv source target)
    (plan : Interface.BinderPlan source) (body : Exp plan.scope) :
    Exp (environment.closePlan plan).scope :=
  body.subst (plan.scopeSubst environment.substitution)

@[simp] theorem closeExp_plan_close
    (environment : ClosingEnv source target)
    (plan : Interface.BinderPlan source) (actual : Instantiation plan)
    (result : Ty source) (body : Exp plan.scope) :
    environment.closeExp (plan.close actual.argument result body) =
      (environment.closePlan plan).close
        (environment.closeInstantiation actual).argument
        (environment.closeTy result) (environment.closeBody plan body) := by
  unfold closeExp closePlan closeInstantiation closeTy closeBody
  rw [plan.close_subst, Instantiation.argument_subst]
  rfl

@[simp] theorem closeExp_instantiate
    (environment : ClosingEnv source target)
    {plan : Interface.BinderPlan source} (actual : Instantiation plan)
    (body : Exp plan.scope) :
    environment.closeExp (actual.instantiate body) =
      (environment.closeInstantiation actual).instantiate
        (environment.closeBody plan body) := by
  exact Instantiation.instantiate_subst actual body environment.substitution

/-- After closing the base signature, binder elimination is the ordinary
`Instantiation.close_steps` theorem for the substituted plan and actual. -/
theorem closePlan_steps
    (environment : ClosingEnv source target)
    {plan : Interface.BinderPlan source} (actual : Instantiation plan)
    (ready : actual.Ready) (result : Ty source) (body : Exp plan.scope) :
    Exp.Steps
      ((environment.closePlan plan).close
        (environment.closeInstantiation actual).argument
        (environment.closeTy result) (environment.closeBody plan body))
      ((environment.closeInstantiation actual).instantiate
        (environment.closeBody plan body)) :=
  (environment.closeInstantiation actual).close_steps
    (ready.subst environment.substitution)
    (environment.closeTy result) (environment.closeBody plan body)

end ClosingEnv
end OperationalEnvironment

end LambdaPToFCo
