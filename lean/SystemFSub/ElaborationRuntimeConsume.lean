import SystemFSub.ElaborationRuntimeLift

/-! Structural consumption of target value wrappers by runtime eliminators. -/

namespace SystemFSub.Elaboration

theorem consumeArrowValue
    {function argument : SystemFCo.Exp []}
    {parameter result : SystemFCo.Ty []}
    (functionTyping : SystemFCo.Exp.HasType .empty function
      (.arrow parameter result))
    (functionValue : SystemFCo.Exp.IsValue function)
    (argumentValue : SystemFCo.Exp.IsValue argument)
    {body : Runtime.Term [()]}
    (shape : eraseTarget function = Runtime.Term.abs body) :
    Exists fun targetResult =>
      SystemFCo.Exp.Steps (.app function argument) targetResult /\
      eraseTarget targetResult = body.instantiate (eraseTarget argument) := by
  cases functionValue with
  | abs =>
      cases functionTyping with
      | abs bodyTyping =>
          refine ⟨_, SystemFCo.Exp.Steps.single (.beta argumentValue), ?_⟩
          rw [eraseTarget_openVar]
          simp only [eraseTarget] at shape
          cases shape
          rfl
  | tabs => cases functionTyping
  | cabs => cases functionTyping
  | castTop value =>
      cases functionTyping with | cast _ coercionTyping => cases coercionTyping
  | @castArrow inner parameterCo resultCo innerValue =>
      cases functionTyping with
      | cast innerTyping coercionTyping =>
          cases coercionTyping with
          | arrow parameterTyping resultTyping =>
              rcases normalizeValueCast argumentValue parameterTyping with
                ⟨argument', argumentSteps, argumentValue', argumentErase⟩
              rcases consumeArrowValue (function := inner) (argument := argument')
                  innerTyping innerValue argumentValue' shape with
                ⟨innerResult, innerSteps, innerErase⟩
              refine ⟨.cast innerResult resultCo, ?_, ?_⟩
              · exact (SystemFCo.Exp.Steps.single
                    (.castArrowApp innerValue argumentValue)).trans
                  (((argumentSteps.appArgument innerValue).castExpression).trans
                    innerSteps.castExpression)
              · simp only [eraseTarget]
                rw [innerErase, argumentErase]
  | castPoly value =>
      cases functionTyping with | cast _ coercionTyping => cases coercionTyping
  | castQual value =>
      cases functionTyping with | cast _ coercionTyping => cases coercionTyping
termination_by sizeOf function
decreasing_by
  all_goals
    simp_all
    omega

theorem consumePolyValue
    {function : SystemFCo.Exp []} {argument : SystemFCo.Ty []}
    {result : SystemFCo.Ty ([.tvar])}
    (functionTyping : SystemFCo.Exp.HasType .empty function (.poly result))
    (functionValue : SystemFCo.Exp.IsValue function)
    {body : Runtime.Term []}
    (shape : eraseTarget function = Runtime.Term.tabs body) :
    Exists fun targetResult =>
      SystemFCo.Exp.Steps (.tapp function argument) targetResult /\
      eraseTarget targetResult = body := by
  cases functionValue with
  | abs => cases functionTyping
  | tabs =>
      cases functionTyping with
      | tabs bodyTyping =>
          refine ⟨_, SystemFCo.Exp.Steps.single .typeBeta, ?_⟩
          rw [eraseTarget_openTVar]
          simp only [eraseTarget] at shape
          cases shape
          rfl
  | cabs => cases functionTyping
  | castTop value =>
      cases functionTyping with | cast _ coercionTyping => cases coercionTyping
  | castArrow value =>
      cases functionTyping with | cast _ coercionTyping => cases coercionTyping
  | @castPoly inner bodyCo innerValue =>
      cases functionTyping with
      | cast innerTyping coercionTyping =>
          cases coercionTyping with
          | poly bodyTyping =>
              rcases consumePolyValue (function := inner) (argument := argument)
                  innerTyping innerValue shape with
                ⟨innerResult, innerSteps, innerErase⟩
              refine ⟨.cast innerResult
                (bodyCo.subst (SystemFCo.Subst.openTVar argument)), ?_, ?_⟩
              · exact (SystemFCo.Exp.Steps.single
                    (.castPolyTapp innerValue)).trans
                  innerSteps.castExpression
              · simpa only [eraseTarget] using innerErase
  | castQual value =>
      cases functionTyping with | cast _ coercionTyping => cases coercionTyping
termination_by sizeOf function
decreasing_by
  all_goals
    simp_all
    omega

theorem consumeQualValue
    {function : SystemFCo.Exp []} {argument : SystemFCo.Co []}
    {source target : SystemFCo.Ty []} {result : SystemFCo.Ty ([.cvar])}
    (functionTyping : SystemFCo.Exp.HasType .empty function
      (.qual source target result))
    (functionValue : SystemFCo.Exp.IsValue function)
    {body : Runtime.Term []}
    (shape : eraseTarget function = Runtime.Term.tabs body) :
    Exists fun targetResult =>
      SystemFCo.Exp.Steps (.capp function argument) targetResult /\
      eraseTarget targetResult = body := by
  cases functionValue with
  | abs => cases functionTyping
  | tabs => cases functionTyping
  | cabs =>
      cases functionTyping with
      | cabs bodyTyping =>
          refine ⟨_, SystemFCo.Exp.Steps.single .coercionBeta, ?_⟩
          rw [eraseTarget_openCVar]
          simp only [eraseTarget] at shape
          cases shape
          rfl
  | castTop value =>
      cases functionTyping with | cast _ coercionTyping => cases coercionTyping
  | castArrow value =>
      cases functionTyping with | cast _ coercionTyping => cases coercionTyping
  | castPoly value =>
      cases functionTyping with | cast _ coercionTyping => cases coercionTyping
  | @castQual inner evidenceCo resultCo innerValue =>
      cases functionTyping with
      | cast innerTyping coercionTyping =>
          cases coercionTyping with
          | qual argumentTyping resultTyping =>
              rcases consumeQualValue (function := inner)
                  (argument := evidenceCo.subst
                    (SystemFCo.Subst.openCVar argument)) innerTyping innerValue shape with
                ⟨innerResult, innerSteps, innerErase⟩
              refine ⟨.cast innerResult
                (resultCo.subst (SystemFCo.Subst.openCVar argument)), ?_, ?_⟩
              · exact (SystemFCo.Exp.Steps.single
                    (.castQualCapp innerValue)).trans
                  innerSteps.castExpression
              · simpa only [eraseTarget] using innerErase
termination_by sizeOf function
decreasing_by
  all_goals
    simp_all
    omega

end SystemFSub.Elaboration
