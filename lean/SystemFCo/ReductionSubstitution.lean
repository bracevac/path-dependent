import SystemFCo.Reduction

/-!
# Substitution stability of target reduction

System FCo reduction is stable under every heterogeneous simultaneous
substitution.  No value-valued or typed-substitution hypothesis is needed:
substitution preserves the outer constructor of every target value, and each
reduction rule retains its redex constructor.  The beta and cast-push cases
use the standard equations commuting a surrounding substitution with
single-binder opening.
-/

namespace SystemFCo

/-! ## Opening under a surrounding substitution -/

theorem Exp.openVar_subst (body : Exp (source ,, .var))
    (argument : Exp source) (substitution : Subst source target) :
    (body.subst (Subst.openVar argument)).subst substitution =
      (body.subst (substitution.lift .var)).subst
        (Subst.openVar (argument.subst substitution)) := by
  rw [Exp.subst_comp, Exp.subst_comp, Subst.openVar_comp]

theorem Exp.openTVar_subst (body : Exp (source ,, .tvar))
    (argument : Ty source) (substitution : Subst source target) :
    (body.subst (Subst.openTVar argument)).subst substitution =
      (body.subst (substitution.lift .tvar)).subst
        (Subst.openTVar (argument.subst substitution)) := by
  rw [Exp.subst_comp, Exp.subst_comp, Subst.openTVar_comp]

theorem Exp.openCVar_subst (body : Exp (source ,, .cvar))
    (argument : Co source) (substitution : Subst source target) :
    (body.subst (Subst.openCVar argument)).subst substitution =
      (body.subst (substitution.lift .cvar)).subst
        (Subst.openCVar (argument.subst substitution)) := by
  rw [Exp.subst_comp, Exp.subst_comp, Subst.openCVar_comp]

theorem Co.openTVar_subst (body : Co (source ,, .tvar))
    (argument : Ty source) (substitution : Subst source target) :
    (body.subst (Subst.openTVar argument)).subst substitution =
      (body.subst (substitution.lift .tvar)).subst
        (Subst.openTVar (argument.subst substitution)) := by
  rw [Co.subst_comp, Co.subst_comp, Subst.openTVar_comp]

theorem Co.openCVar_subst (body : Co (source ,, .cvar))
    (argument : Co source) (substitution : Subst source target) :
    (body.subst (Subst.openCVar argument)).subst substitution =
      (body.subst (substitution.lift .cvar)).subst
        (Subst.openCVar (argument.subst substitution)) := by
  rw [Co.subst_comp, Co.subst_comp, Subst.openCVar_comp]

namespace Exp

/-! ## Values and reduction -/

/-- Arbitrary simultaneous substitution preserves target values. -/
theorem IsValue.subst
    {expression : Exp source} (value : IsValue expression)
    (substitution : Subst source target) :
    IsValue (expression.subst substitution) := by
  induction value with
  | abs => exact .abs
  | tabs => exact .tabs
  | cabs => exact .cabs
  | castTop _ ih => exact .castTop ih
  | castArrow _ ih => exact .castArrow ih
  | castPoly _ ih => exact .castPoly ih
  | castQual _ ih => exact .castQual ih

/-- Every target step remains one target step after an arbitrary
heterogeneous simultaneous substitution. -/
theorem Step.subst
    {first last : Exp source} (step : Step first last)
    (substitution : Subst source target) :
    Step (first.subst substitution) (last.subst substitution) := by
  induction step with
  | appFunction _ ih =>
      exact .appFunction ih
  | appArgument value _ ih =>
      exact .appArgument (value.subst substitution) ih
  | beta value =>
      simpa only [Exp.subst, Exp.openVar_subst] using
        (Step.beta (value.subst substitution))
  | tappFunction _ ih =>
      exact .tappFunction ih
  | typeBeta =>
      simpa only [Exp.subst, Exp.openTVar_subst] using
        (Step.typeBeta : Step _ _)
  | cappFunction _ ih =>
      exact .cappFunction ih
  | coercionBeta =>
      simpa only [Exp.subst, Exp.openCVar_subst] using
        (Step.coercionBeta : Step _ _)
  | castExpression _ ih =>
      exact .castExpression ih
  | castRefl value =>
      exact .castRefl (value.subst substitution)
  | castTrans value =>
      exact .castTrans (value.subst substitution)
  | castArrowApp functionValue argumentValue =>
      exact .castArrowApp (functionValue.subst substitution)
        (argumentValue.subst substitution)
  | castPolyTapp functionValue =>
      simpa only [Exp.subst, Co.subst, Co.openTVar_subst] using
        (Step.castPolyTapp (functionValue.subst substitution))
  | castQualCapp functionValue =>
      simpa only [Exp.subst, Co.subst, Co.openCVar_subst] using
        (Step.castQualCapp (functionValue.subst substitution))

/-- Finite target reduction is stable under arbitrary simultaneous
substitution. -/
theorem Steps.subst
    {first last : Exp source} (steps : Steps first last)
    (substitution : Subst source target) :
    Steps (first.subst substitution) (last.subst substitution) := by
  induction steps with
  | refl => exact .refl
  | tail step rest ih =>
      exact .tail (step.subst substitution) ih

end Exp
end SystemFCo
