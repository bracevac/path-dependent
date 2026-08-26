import SystemFCo.Reduction

/-!
# Basic operational facts for the explicit-coercion target

These facts isolate the deterministic target dynamics used by later erasure
and administrative-step arguments.
-/

namespace SystemFCo.Exp

theorem IsValue.not_step {value next : Exp sig}
    (valueTyping : IsValue value) : Not (Step value next) := by
  induction valueTyping generalizing next with
  | abs => intro reduction; cases reduction
  | tabs => intro reduction; cases reduction
  | cabs => intro reduction; cases reduction
  | castTop _ ih =>
      intro reduction
      cases reduction with
      | castExpression inner => exact ih inner
  | castArrow _ ih =>
      intro reduction
      cases reduction with
      | castExpression inner => exact ih inner
  | castPoly _ ih =>
      intro reduction
      cases reduction with
      | castExpression inner => exact ih inner
  | castQual _ ih =>
      intro reduction
      cases reduction with
      | castExpression inner => exact ih inner

theorem Step.not_value {expression next : Exp sig}
    (reduction : Step expression next) : Not (IsValue expression) := by
  intro value
  exact value.not_step reduction

theorem Steps.single (reduction : Step expression expression') :
    Steps expression expression' :=
  .tail reduction .refl

theorem Steps.trans
    (first : Steps expression middle) (second : Steps middle result) :
    Steps expression result := by
  induction first with
  | refl => exact second
  | tail reduction reductions ih => exact .tail reduction (ih second)

theorem IsValue.steps_eq (value : IsValue expression)
    (reductions : Steps expression result) : expression = result := by
  cases reductions with
  | refl => rfl
  | tail reduction _ => exact False.elim (value.not_step reduction)

theorem Step.deterministic
    (first : Step expression firstResult)
    (second : Step expression secondResult) :
    firstResult = secondResult := by
  induction first generalizing secondResult with
  | appFunction reduction ih =>
      cases second with
      | appFunction reduction' =>
          exact congrArg (fun function => Exp.app function _) (ih reduction')
      | appArgument value _ => exact False.elim (value.not_step reduction)
      | beta _ => exact False.elim (IsValue.abs.not_step reduction)
      | castArrowApp value _ =>
          exact False.elim ((IsValue.castArrow value).not_step reduction)
  | appArgument functionValue reduction ih =>
      cases second with
      | appFunction reduction' =>
          exact False.elim (functionValue.not_step reduction')
      | appArgument _ reduction' =>
          exact congrArg (fun argument => Exp.app _ argument) (ih reduction')
      | beta argumentValue =>
          exact False.elim (argumentValue.not_step reduction)
      | castArrowApp _ argumentValue =>
          exact False.elim (argumentValue.not_step reduction)
  | beta argumentValue =>
      cases second with
      | appFunction reduction =>
          exact False.elim (IsValue.abs.not_step reduction)
      | appArgument _ reduction =>
          exact False.elim (argumentValue.not_step reduction)
      | beta _ => rfl
  | tappFunction reduction ih =>
      cases second with
      | tappFunction reduction' =>
          exact congrArg (fun function => Exp.tapp function _) (ih reduction')
      | typeBeta => exact False.elim (IsValue.tabs.not_step reduction)
      | castPolyTapp value =>
          exact False.elim ((IsValue.castPoly value).not_step reduction)
  | typeBeta =>
      cases second with
      | tappFunction reduction =>
          exact False.elim (IsValue.tabs.not_step reduction)
      | typeBeta => rfl
  | cappFunction reduction ih =>
      cases second with
      | cappFunction reduction' =>
          exact congrArg (fun function => Exp.capp function _) (ih reduction')
      | coercionBeta => exact False.elim (IsValue.cabs.not_step reduction)
      | castQualCapp value =>
          exact False.elim ((IsValue.castQual value).not_step reduction)
  | coercionBeta =>
      cases second with
      | cappFunction reduction =>
          exact False.elim (IsValue.cabs.not_step reduction)
      | coercionBeta => rfl
  | castExpression reduction ih =>
      cases second with
      | castExpression reduction' =>
          exact congrArg (fun expression => Exp.cast expression _) (ih reduction')
      | castRefl value => exact False.elim (value.not_step reduction)
      | castTrans value => exact False.elim (value.not_step reduction)
  | castRefl value =>
      cases second with
      | castExpression reduction =>
          exact False.elim (value.not_step reduction)
      | castRefl _ => rfl
  | castTrans value =>
      cases second with
      | castExpression reduction =>
          exact False.elim (value.not_step reduction)
      | castTrans _ => rfl
  | castArrowApp functionValue argumentValue =>
      cases second with
      | appFunction reduction =>
          exact False.elim ((IsValue.castArrow functionValue).not_step reduction)
      | appArgument _ reduction =>
          exact False.elim (argumentValue.not_step reduction)
      | castArrowApp _ _ => rfl
  | castPolyTapp functionValue =>
      cases second with
      | tappFunction reduction =>
          exact False.elim ((IsValue.castPoly functionValue).not_step reduction)
      | castPolyTapp _ => rfl
  | castQualCapp functionValue =>
      cases second with
      | cappFunction reduction =>
          exact False.elim ((IsValue.castQual functionValue).not_step reduction)
      | castQualCapp _ => rfl

end SystemFCo.Exp
