import LambdaPToFCo.OperationalBindingView
import SystemFCo.ChurchPackageCovariance

/-!
# Behavioral elimination of a covariantly converted member package

A literal exact-package instantiation is not closed under interval
covariance.  Its converted argument is a value of the form

`cast (packMember ...) (Co.member lowerAdapter upperAdapter (refl payload))`.

The cast does not reduce by itself.  It becomes active only when the exact
binder eliminates the package.  This file gives that target-only reduction
trace and packages it as an `EliminationView`.  The exposed lower and upper
slots are the expected transitive compositions.  The two reflexive result
casts left by `Co.member` are recorded by `Resume.doubleRefl`; they cannot be
discarded before the instantiated body has evaluated to a value.

This is an operational macro theorem about target syntax.  It is not a
source simulation or a semantic realization argument.
-/

namespace SystemFCo
namespace Co

/-- Coercion substitution commutes with the binder insertion used by the
payload component of `Co.member`. -/
theorem insertUnderTVar_subst
    (payload : Co (source ,, .tvar))
    (substitution : Subst source target) :
    (payload.rename ChurchPackage.insertUnderTVar).subst
        ((substitution.lift .tvar).lift .tvar) =
      (payload.subst (substitution.lift .tvar)).rename
        ChurchPackage.insertUnderTVar := by
  have comm : Subst.RenameComm (substitution.lift .tvar)
      ChurchPackage.insertUnderTVar ChurchPackage.insertUnderTVar
      ((substitution.lift .tvar).lift .tvar) := by
    constructor
    · intro index
      cases index with
      | there index =>
          simp only [ChurchPackage.insertUnderTVar, Rename.lift_there,
            Subst.lift_var_there]
          exact Exp.weaken_rename_comm (substitution.var index)
            (Rename.weaken .tvar)
    · intro index
      cases index with
      | here => rfl
      | there index =>
          simp only [ChurchPackage.insertUnderTVar, Rename.lift_there,
            Subst.lift_tvar_there]
          exact Ty.weaken_rename_comm (substitution.tvar index)
            (Rename.weaken .tvar)
    · intro index
      cases index with
      | there index =>
          simp only [ChurchPackage.insertUnderTVar, Rename.lift_there,
            Subst.lift_cvar_there]
          exact Co.weaken_rename_comm (substitution.cvar index)
            (Rename.weaken .tvar)
  exact (payload.rename_subst_comm comm).symm

/-- `Co.member` is natural under arbitrary heterogeneous target
substitution. -/
theorem member_subst
    (lower upper : Co source) (payload : Co (source ,, .tvar))
    (substitution : Subst source target) :
    (Co.member lower upper payload).subst substitution =
      Co.member (lower.subst substitution) (upper.subst substitution)
        (payload.subst (substitution.lift .tvar)) := by
  unfold Co.member
  simp only [Co.subst]
  simp only [
    LambdaPToFCo.OperationalMacros.CompiledBinder.co_weaken_subst_lift,
    LambdaPToFCo.OperationalMacros.CompiledBinder.ty_weaken_subst_lift,
    insertUnderTVar_subst, Ty.subst, Subst.lift_cvar_here,
    Subst.lift_tvar_here]

end Co
end SystemFCo

namespace LambdaPToFCo
namespace OperationalMemberView

open SystemFCo
open OperationalBindingView

/-- A literal member package converted to a wider interval while preserving
its payload family. -/
def convertedArgument
    (lower upper witness : Ty sig)
    (payloadType : Ty (sig ,, .tvar))
    (lowerEvidence upperEvidence lowerAdapter upperAdapter : Co sig)
    (payload : Exp sig) : Exp sig :=
  .cast
    (Exp.packMember lower upper witness payloadType
      lowerEvidence upperEvidence payload)
    (Co.member lowerAdapter upperAdapter (.refl payloadType))

/-- The five exact-binder slots exposed by eliminating a converted package.
The raw slot deliberately retains the converted package itself. -/
def convertedSubstitution
    (targetLower targetUpper : Ty sig)
    (lower upper witness : Ty sig)
    (payloadType : Ty (sig ,, .tvar))
    (lowerEvidence upperEvidence lowerAdapter upperAdapter : Co sig)
    (payload : Exp sig) :
    Subst (Interface.BinderPlan.exact
      targetLower targetUpper payloadType).scope sig :=
  OperationalMacros.CompiledBinder.exactSubst
    (convertedArgument lower upper witness payloadType lowerEvidence
      upperEvidence lowerAdapter upperAdapter payload)
    witness (.trans lowerAdapter lowerEvidence)
    (.trans upperEvidence upperAdapter) payload

private theorem lower_slot
    (result witness : Ty sig)
    (lowerEvidence lowerAdapter : Co sig) :
    (Co.trans (((lowerAdapter.weaken .tvar).weaken .tvar).weaken .cvar)
          (.cvar .here)
        |>.subst (((Subst.openTVar result).lift .tvar).lift .cvar)
        |>.subst ((Subst.openTVar witness).lift .cvar)
        |>.subst (Subst.openCVar lowerEvidence)) =
      .trans lowerAdapter lowerEvidence := by
  simp only [Co.subst]
  simp only [
    OperationalMacros.CompiledBinder.co_weaken_subst_lift,
    OperationalMacros.CompiledBinder.co_weaken_openTVar,
    OperationalMacros.CompiledBinder.co_weaken_openCVar,
    Subst.lift_cvar_here]
  rfl

private theorem upper_slot
    (result witness : Ty sig)
    (lowerEvidence upperEvidence upperAdapter : Co sig) :
    (Co.trans (.cvar .here)
          ((((upperAdapter.weaken .tvar).weaken .tvar).weaken .cvar).weaken
            .cvar)
        |>.subst ((((Subst.openTVar result).lift .tvar).lift .cvar).lift .cvar)
        |>.subst (((Subst.openTVar witness).lift .cvar).lift .cvar)
        |>.subst ((Subst.openCVar lowerEvidence).lift .cvar)
        |>.subst (Subst.openCVar upperEvidence)) =
      Co.trans upperEvidence upperAdapter := by
  simp only [Co.subst]
  simp only [
    OperationalMacros.CompiledBinder.co_weaken_subst_lift,
    OperationalMacros.CompiledBinder.co_weaken_openTVar,
    OperationalMacros.CompiledBinder.co_weaken_openCVar,
    Subst.lift_cvar_here]
  rfl

private theorem inner_result
    (result witness : Ty sig)
    (lowerEvidence upperEvidence : Co sig) :
    (Co.refl ((((.tvar .here : Ty (sig ,, .tvar)).weaken .tvar).weaken
          .cvar).weaken .cvar)
        |>.subst ((((Subst.openTVar result).lift .tvar).lift .cvar).lift .cvar)
        |>.subst (((Subst.openTVar witness).lift .cvar).lift .cvar)
        |>.subst ((Subst.openCVar lowerEvidence).lift .cvar)
        |>.subst (Subst.openCVar upperEvidence)) = Co.refl result := by
  simp only [Co.subst]
  simp only [
    OperationalMacros.CompiledBinder.ty_weaken_subst_lift,
    OperationalMacros.CompiledBinder.ty_weaken_openTVar,
    OperationalMacros.CompiledBinder.ty_weaken_openCVar]
  rfl

/-- Eliminating a member package converted with `Co.member` exposes the
adapted interval evidence and payload.  The endpoint retains the two
administrative reflexive result casts introduced by the package conversion.
-/
theorem close_converted_steps
    (targetLower targetUpper : Ty sig)
    (lower upper witness : Ty sig)
    (payloadType : Ty (sig ,, .tvar))
    (lowerEvidence upperEvidence lowerAdapter upperAdapter : Co sig)
    (payload : Exp sig) (payloadReady : Exp.IsValue payload)
    (result : Ty sig)
    (body : Exp
      (Interface.BinderPlan.exact
        targetLower targetUpper payloadType).scope) :
    Exp.Steps
      ((Interface.BinderPlan.exact targetLower targetUpper payloadType).close
        (convertedArgument lower upper witness payloadType lowerEvidence
          upperEvidence lowerAdapter upperAdapter payload)
        result body)
      ((Resume.doubleRefl result).plug
        (body.subst
          (convertedSubstitution targetLower targetUpper lower upper witness
            payloadType lowerEvidence upperEvidence lowerAdapter upperAdapter
            payload))) := by
  apply Exp.Steps.tail (.beta (.castPoly .tabs))
  apply Exp.Steps.tail (.appFunction (.castPolyTapp .tabs))
  apply Exp.Steps.tail (.appFunction (.castExpression .typeBeta))
  apply Exp.Steps.tail (.castArrowApp .abs .tabs)
  apply Exp.Steps.tail (.castExpression (.beta (.castPoly .tabs)))
  apply Exp.Steps.tail
    (.castExpression
      (.appFunction (.cappFunction (.cappFunction (.castPolyTapp .tabs)))))
  apply Exp.Steps.tail
    (.castExpression
      (.appFunction
        (.cappFunction (.cappFunction (.castExpression .typeBeta)))))
  apply Exp.Steps.tail
    (.castExpression
      (.appFunction (.cappFunction (.castQualCapp .cabs))))
  apply Exp.Steps.tail
    (.castExpression
      (.appFunction (.cappFunction (.castExpression .coercionBeta))))
  apply Exp.Steps.tail
    (.castExpression (.appFunction (.castQualCapp .cabs)))
  apply Exp.Steps.tail
    (.castExpression (.appFunction (.castExpression .coercionBeta)))
  simp only [
    OperationalMacros.CompiledBinder.exp_weaken_subst_lift,
    OperationalMacros.CompiledBinder.ty_weaken_subst_lift,
    OperationalMacros.CompiledBinder.co_weaken_subst_lift,
    OperationalMacros.CompiledBinder.exp_weaken_openVar,
    OperationalMacros.CompiledBinder.ty_weaken_openVar,
    OperationalMacros.CompiledBinder.co_weaken_openVar,
    OperationalMacros.CompiledBinder.exp_weaken_openTVar,
    OperationalMacros.CompiledBinder.ty_weaken_openTVar,
    OperationalMacros.CompiledBinder.co_weaken_openTVar]
  apply Exp.Steps.tail
    (.castExpression (.castArrowApp .abs payloadReady))
  apply Exp.Steps.tail
    (.castExpression
      (.castExpression (.appArgument .abs (.castRefl payloadReady))))
  apply Exp.Steps.tail
    (.castExpression (.castExpression (.beta payloadReady)))
  simp only [Exp.subst_comp]
  rw [lower_slot, upper_slot, inner_result]
  change Exp.Steps
    ((Resume.doubleRefl result).plug
      (body.subst
        (convertedSubstitution targetLower targetUpper lower upper witness
          payloadType lowerEvidence upperEvidence lowerAdapter upperAdapter
          payload)))
    ((Resume.doubleRefl result).plug
      (body.subst
        (convertedSubstitution targetLower targetUpper lower upper witness
          payloadType lowerEvidence upperEvidence lowerAdapter upperAdapter
          payload)))
  exact .refl

/-- The covariantly converted literal package as a behavioral exact-binding
view. -/
def eliminationView
    (targetLower targetUpper : Ty sig)
    (lower upper witness : Ty sig)
    (payloadType : Ty (sig ,, .tvar))
    (lowerEvidence upperEvidence lowerAdapter upperAdapter : Co sig)
    (payload : Exp sig) (payloadReady : Exp.IsValue payload) :
    EliminationView
      (Interface.BinderPlan.exact targetLower targetUpper payloadType) where
  argument := convertedArgument lower upper witness payloadType lowerEvidence
    upperEvidence lowerAdapter upperAdapter payload
  substitution := convertedSubstitution targetLower targetUpper lower upper
    witness payloadType lowerEvidence upperEvidence lowerAdapter upperAdapter
    payload
  ready := .castPoly .tabs
  resume := Resume.doubleRefl
  eliminate := close_converted_steps targetLower targetUpper lower upper witness
    payloadType lowerEvidence upperEvidence lowerAdapter upperAdapter payload
    payloadReady

end OperationalMemberView
end LambdaPToFCo
