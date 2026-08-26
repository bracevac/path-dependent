import SystemFSub.ElaborationRuntimeConsume

/-! Reverse lifting of one common-runtime step into finite target reduction. -/

namespace SystemFSub.Elaboration

theorem liftRuntimeStep
    {expression : SystemFCo.Exp []} {ty : SystemFCo.Ty []}
    (typing : SystemFCo.Exp.HasType .empty expression ty)
    {runtimeResult : Runtime.Term []}
    (runtimeStep : Runtime.Step (eraseTarget expression) runtimeResult) :
    Exists fun targetResult =>
      SystemFCo.Exp.Steps expression targetResult /\
      eraseTarget targetResult = runtimeResult := by
  cases typing with
  | var lookup => exact nomatch lookup
  | abs =>
      simp only [eraseTarget] at runtimeStep
      exact nomatch runtimeStep
  | @app _ _ function parameter result argument functionTyping argumentTyping =>
      simp only [eraseTarget] at runtimeStep
      generalize functionEq : eraseTarget function = runtimeFunction at runtimeStep
      generalize argumentEq : eraseTarget argument = runtimeArgument at runtimeStep
      cases runtimeStep with
      | appFunction functionStep =>
          have sourceStep := functionStep
          rw [← functionEq] at sourceStep
          rcases liftRuntimeStep functionTyping sourceStep with
            ⟨function', functionSteps, functionErase⟩
          refine ⟨.app function' argument, functionSteps.appFunction, ?_⟩
          simp only [eraseTarget]
          rw [functionErase, argumentEq]
      | appArgument functionValue argumentStep =>
          have sourceValue := functionValue
          rw [← functionEq] at sourceValue
          have sourceStep := argumentStep
          rw [← argumentEq] at sourceStep
          rcases normalizeRuntimeValue functionTyping sourceValue with
            ⟨functionValue', functionSteps, targetFunctionValue, functionErase⟩
          rcases liftRuntimeStep argumentTyping sourceStep with
            ⟨argument', argumentSteps, argumentErase⟩
          refine ⟨.app functionValue' argument', ?_, ?_⟩
          · exact functionSteps.appFunction |>.trans
              (argumentSteps.appArgument targetFunctionValue)
          · simp only [eraseTarget]
            rw [functionErase, functionEq, argumentErase]
      | beta argumentValue =>
          have sourceFunctionValue : Runtime.IsValue (eraseTarget function) := by
            rw [functionEq]
            exact .abs
          have sourceArgumentValue := argumentValue
          rw [← argumentEq] at sourceArgumentValue
          rcases normalizeRuntimeValue functionTyping sourceFunctionValue with
            ⟨functionValue', functionSteps, targetFunctionValue, functionErase⟩
          rcases normalizeRuntimeValue argumentTyping sourceArgumentValue with
            ⟨argumentValue', argumentSteps, targetArgumentValue, argumentErase⟩
          rcases SystemFCo.Exp.preservation_steps functionTyping functionSteps with
            ⟨functionTyping'⟩
          rcases consumeArrowValue functionTyping' targetFunctionValue
              targetArgumentValue (functionErase.trans functionEq) with
            ⟨result, betaSteps, resultErase⟩
          refine ⟨result, ?_, ?_⟩
          · exact functionSteps.appFunction |>.trans
              ((argumentSteps.appArgument targetFunctionValue).trans betaSteps)
          · exact resultErase.trans
              (congrArg (Runtime.Term.instantiate _)
                (argumentErase.trans argumentEq))
  | tabs =>
      simp only [eraseTarget] at runtimeStep
      exact nomatch runtimeStep
  | @tapp _ _ function result argument functionTyping =>
      simp only [eraseTarget] at runtimeStep
      generalize functionEq : eraseTarget function = runtimeFunction at runtimeStep
      cases runtimeStep with
      | tappFunction functionStep =>
          have sourceStep := functionStep
          rw [← functionEq] at sourceStep
          rcases liftRuntimeStep functionTyping sourceStep with
            ⟨function', functionSteps, functionErase⟩
          refine ⟨.tapp function' argument, functionSteps.tappFunction, ?_⟩
          simp only [eraseTarget, functionErase]
      | typeBeta =>
          have sourceValue : Runtime.IsValue (eraseTarget function) := by
            rw [functionEq]
            exact .tabs
          rcases normalizeRuntimeValue functionTyping sourceValue with
            ⟨functionValue', functionSteps, targetFunctionValue, functionErase⟩
          rcases SystemFCo.Exp.preservation_steps functionTyping functionSteps with
            ⟨functionTyping'⟩
          rcases consumePolyValue functionTyping' targetFunctionValue
              (functionErase.trans functionEq) with
            ⟨result, betaSteps, resultErase⟩
          exact ⟨result, functionSteps.tappFunction |>.trans betaSteps, resultErase⟩
  | cabs =>
      simp only [eraseTarget] at runtimeStep
      exact nomatch runtimeStep
  | @capp _ _ function source target result argument functionTyping argumentTyping =>
      simp only [eraseTarget] at runtimeStep
      generalize functionEq : eraseTarget function = runtimeFunction at runtimeStep
      cases runtimeStep with
      | tappFunction functionStep =>
          have sourceStep := functionStep
          rw [← functionEq] at sourceStep
          rcases liftRuntimeStep functionTyping sourceStep with
            ⟨function', functionSteps, functionErase⟩
          refine ⟨.capp function' argument, functionSteps.cappFunction, ?_⟩
          simp only [eraseTarget, functionErase]
      | typeBeta =>
          have sourceValue : Runtime.IsValue (eraseTarget function) := by
            rw [functionEq]
            exact .tabs
          rcases normalizeRuntimeValue functionTyping sourceValue with
            ⟨functionValue', functionSteps, targetFunctionValue, functionErase⟩
          rcases SystemFCo.Exp.preservation_steps functionTyping functionSteps with
            ⟨functionTyping'⟩
          rcases consumeQualValue functionTyping' targetFunctionValue
              (functionErase.trans functionEq) with
            ⟨result, betaSteps, resultErase⟩
          exact ⟨result, functionSteps.cappFunction |>.trans betaSteps, resultErase⟩
  | @cast _ _ inner source coercion target expressionTyping coercionTyping =>
      rcases liftRuntimeStep expressionTyping runtimeStep with
        ⟨expression', expressionSteps, expressionErase⟩
      exact ⟨.cast expression' coercion, expressionSteps.castExpression,
        expressionErase⟩
termination_by sizeOf expression
decreasing_by
  all_goals
    simp_all
    omega

end SystemFSub.Elaboration
