import SystemFCoExt.Reduction

/-! One-step type preservation for the explicit-coercion target. -/

namespace SystemFCoExt.Exp

theorem preservation
    (typing : context |-e expression : ty)
    (reduction : Step expression expression') :
    Nonempty (context |-e expression' : ty) := by
  induction reduction generalizing ty with
  | appFunction _ ih =>
      cases typing with
      | app functionTyping argumentTyping =>
          rcases ih functionTyping with ⟨functionTyping'⟩
          exact ⟨.app functionTyping' argumentTyping⟩
  | appArgument _ _ ih =>
      cases typing with
      | app functionTyping argumentTyping =>
          rcases ih argumentTyping with ⟨argumentTyping'⟩
          exact ⟨.app functionTyping argumentTyping'⟩
  | beta _ =>
      cases typing with
      | app functionTyping argumentTyping =>
          cases functionTyping with
          | abs bodyTyping =>
              exact ⟨by
                simpa only [Ty.weaken_subst_cancel _ _
                  (Subst.weakenAsSubst_comp_openVar _)] using
                  bodyTyping.openVar argumentTyping⟩
  | tappFunction _ ih =>
      cases typing with
      | tapp functionTyping =>
          rcases ih functionTyping with ⟨functionTyping'⟩
          exact ⟨.tapp functionTyping'⟩
  | typeBeta =>
      cases typing with
      | tapp functionTyping =>
          cases functionTyping with
          | tabs bodyTyping =>
              exact ⟨bodyTyping.openTVar _⟩
  | cappFunction _ ih =>
      cases typing with
      | capp functionTyping argumentTyping =>
          rcases ih functionTyping with ⟨functionTyping'⟩
          exact ⟨.capp functionTyping' argumentTyping⟩
  | coercionBeta =>
      cases typing with
      | capp functionTyping argumentTyping =>
          cases functionTyping with
          | cabs bodyTyping =>
              exact ⟨bodyTyping.openCVar argumentTyping⟩
  | castExpression _ ih =>
      cases typing with
      | cast expressionTyping coercionTyping =>
          rcases ih expressionTyping with ⟨expressionTyping'⟩
          exact ⟨.cast expressionTyping' coercionTyping⟩
  | castRefl _ =>
      cases typing with
      | cast expressionTyping coercionTyping =>
          cases coercionTyping
          exact ⟨expressionTyping⟩
  | castTrans _ =>
      cases typing with
      | cast expressionTyping coercionTyping =>
          cases coercionTyping with
          | trans firstTyping secondTyping =>
              exact ⟨.cast (.cast expressionTyping firstTyping) secondTyping⟩
  | castBottom _ =>
      cases typing with
      | cast expressionTyping coercionTyping =>
          cases coercionTyping with
          | bottom => exact ⟨Exp.HasType.tapp expressionTyping⟩
  | castAdapter _ =>
      cases typing with
      | cast expressionTyping coercionTyping =>
          cases coercionTyping with
          | adapter bodyTyping =>
              exact ⟨by
                simpa only [Ty.weaken_subst_cancel _ _
                  (Subst.weakenAsSubst_comp_openVar _)] using
                  bodyTyping.openVar expressionTyping⟩
  | castArrowApp _ _ =>
      cases typing with
      | app functionTyping argumentTyping =>
          cases functionTyping with
          | cast innerTyping coercionTyping =>
              cases coercionTyping with
              | arrow parameterTyping resultTyping =>
                  exact ⟨.cast
                    (.app innerTyping (.cast argumentTyping parameterTyping))
                    resultTyping⟩
  | castPolyTapp _ =>
      cases typing with
      | tapp functionTyping =>
          cases functionTyping with
          | cast innerTyping coercionTyping =>
              cases coercionTyping with
              | poly bodyTyping =>
                  exact ⟨.cast (.tapp innerTyping) (bodyTyping.openTVar _)⟩
  | castQualCapp _ =>
      cases typing with
      | capp functionTyping argumentTyping =>
          cases functionTyping with
          | cast innerTyping coercionTyping =>
              cases coercionTyping with
              | qual evidenceTyping resultTyping =>
                  have openedEvidence := evidenceTyping.openCVar argumentTyping
                  rw [Ty.weaken_subst_cancel _ _
                    (Subst.weakenAsSubst_comp_openCVar _),
                    Ty.weaken_subst_cancel _ _
                      (Subst.weakenAsSubst_comp_openCVar _)] at openedEvidence
                  have openedResult := resultTyping.openCVar argumentTyping
                  rw [Ty.rebindCVar_openCVar] at openedResult
                  exact ⟨.cast (.capp innerTyping openedEvidence) openedResult⟩

end SystemFCoExt.Exp
