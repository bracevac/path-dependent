import SystemFSub.ElaborationOperational
import SystemFCo.Safety

/-! Structural administration and coarse common-runtime progress. -/

namespace SystemFCo.Exp.Steps

theorem appFunction (steps : SystemFCo.Exp.Steps function function') :
    SystemFCo.Exp.Steps (.app function argument) (.app function' argument) := by
  induction steps with
  | refl => exact .refl
  | tail step rest ih => exact .tail (.appFunction step) ih

theorem appArgument (value : SystemFCo.Exp.IsValue function)
    (steps : SystemFCo.Exp.Steps argument argument') :
    SystemFCo.Exp.Steps (.app function argument) (.app function argument') := by
  induction steps with
  | refl => exact .refl
  | tail step rest ih => exact .tail (.appArgument value step) ih

theorem tappFunction (steps : SystemFCo.Exp.Steps function function') :
    SystemFCo.Exp.Steps (.tapp function argument) (.tapp function' argument) := by
  induction steps with
  | refl => exact .refl
  | tail step rest ih => exact .tail (.tappFunction step) ih

theorem cappFunction (steps : SystemFCo.Exp.Steps function function') :
    SystemFCo.Exp.Steps (.capp function argument) (.capp function' argument) := by
  induction steps with
  | refl => exact .refl
  | tail step rest ih => exact .tail (.cappFunction step) ih

theorem castExpression (steps : SystemFCo.Exp.Steps expression expression') :
    SystemFCo.Exp.Steps (.cast expression coercion)
      (.cast expression' coercion) := by
  induction steps with
  | refl => exact .refl
  | tail step rest ih => exact .tail (.castExpression step) ih

end SystemFCo.Exp.Steps

namespace SystemFSub.Elaboration

/-- Normalize a cast whose underlying expression is already a value.
The recursion measure is the coercion-typing derivation. -/
theorem normalizeValueCast
    {value : SystemFCo.Exp []} (valueIsValue : SystemFCo.Exp.IsValue value)
    {coercion : SystemFCo.Co []} {source target : SystemFCo.Ty []}
    (coercionTyping : SystemFCo.Co.HasType .empty coercion source target) :
    Exists fun result =>
      SystemFCo.Exp.Steps (.cast value coercion) result /\
      SystemFCo.Exp.IsValue result /\
      eraseTarget result = eraseTarget value := by
  cases coercionTyping with
  | cvar lookup => exact nomatch lookup
  | refl =>
      exact ⟨value, SystemFCo.Exp.Steps.single (.castRefl valueIsValue),
        valueIsValue, rfl⟩
  | trans firstTyping secondTyping =>
      rcases normalizeValueCast valueIsValue firstTyping with
        ⟨firstResult, firstSteps, firstValue, firstErase⟩
      rcases normalizeValueCast firstValue secondTyping with
        ⟨result, secondSteps, resultValue, resultErase⟩
      refine ⟨result, ?_, resultValue, resultErase.trans firstErase⟩
      exact (SystemFCo.Exp.Steps.single (.castTrans valueIsValue)).trans
        ((firstSteps.castExpression).trans secondSteps)
  | top => exact ⟨_, .refl, .castTop valueIsValue, rfl⟩
  | arrow => exact ⟨_, .refl, .castArrow valueIsValue, rfl⟩
  | poly => exact ⟨_, .refl, .castPoly valueIsValue, rfl⟩
  | qual => exact ⟨_, .refl, .castQual valueIsValue, rfl⟩
termination_by sizeOf coercion
decreasing_by
  all_goals
    simp_all
    omega

/-- Reach a target value whenever the common-runtime erasure is a value. -/
theorem normalizeRuntimeValue
    {expression : SystemFCo.Exp []} {ty : SystemFCo.Ty []}
    (typing : SystemFCo.Exp.HasType .empty expression ty)
    (runtimeValue : Runtime.IsValue (eraseTarget expression)) :
    Exists fun result =>
      SystemFCo.Exp.Steps expression result /\
      SystemFCo.Exp.IsValue result /\
      eraseTarget result = eraseTarget expression := by
  cases typing with
  | var lookup => exact nomatch lookup
  | abs => exact ⟨_, .refl, .abs, rfl⟩
  | app => exact nomatch runtimeValue
  | tabs => exact ⟨_, .refl, .tabs, rfl⟩
  | tapp => exact nomatch runtimeValue
  | cabs => exact ⟨_, .refl, .cabs, rfl⟩
  | capp => exact nomatch runtimeValue
  | cast expressionTyping coercionTyping =>
      rcases normalizeRuntimeValue expressionTyping runtimeValue with
        ⟨value, expressionSteps, valueIsValue, valueErase⟩
      rcases normalizeValueCast valueIsValue coercionTyping with
        ⟨result, castSteps, resultValue, resultErase⟩
      refine ⟨result, expressionSteps.castExpression |>.trans castSteps,
        resultValue, resultErase.trans valueErase⟩
termination_by sizeOf expression
decreasing_by
  all_goals
    simp_all
    omega

theorem arrowValue_erases_abs
    {value : SystemFCo.Exp []}
    {parameter result : SystemFCo.Ty []}
    (typing : SystemFCo.Exp.HasType .empty value (.arrow parameter result))
    (valueIsValue : SystemFCo.Exp.IsValue value) :
    Exists fun body => eraseTarget value = Runtime.Term.abs body := by
  induction valueIsValue generalizing parameter result with
  | abs => exact ⟨_, rfl⟩
  | tabs => cases typing
  | cabs => cases typing
  | castTop _ _ => cases typing with | cast _ coercionTyping => cases coercionTyping
  | castArrow innerValue ih =>
      cases typing with
      | cast innerTyping coercionTyping =>
          cases coercionTyping with
          | arrow => exact ih innerTyping
  | castPoly _ _ => cases typing with | cast _ coercionTyping => cases coercionTyping
  | castQual _ _ => cases typing with | cast _ coercionTyping => cases coercionTyping

theorem polyValue_erases_tabs
    {value : SystemFCo.Exp []} {result : SystemFCo.Ty ([.tvar])}
    (typing : SystemFCo.Exp.HasType .empty value (.poly result))
    (valueIsValue : SystemFCo.Exp.IsValue value) :
    Exists fun body => eraseTarget value = Runtime.Term.tabs body := by
  induction valueIsValue generalizing result with
  | abs => cases typing
  | tabs => exact ⟨_, rfl⟩
  | cabs => cases typing
  | castTop _ _ => cases typing with | cast _ coercionTyping => cases coercionTyping
  | castArrow _ _ => cases typing with | cast _ coercionTyping => cases coercionTyping
  | castPoly innerValue ih =>
      cases typing with
      | cast innerTyping coercionTyping =>
          cases coercionTyping with
          | poly => exact ih innerTyping
  | castQual _ _ => cases typing with | cast _ coercionTyping => cases coercionTyping

theorem qualValue_erases_tabs
    {value : SystemFCo.Exp []} {source target : SystemFCo.Ty []}
    {result : SystemFCo.Ty ([.cvar])}
    (typing : SystemFCo.Exp.HasType .empty value (.qual source target result))
    (valueIsValue : SystemFCo.Exp.IsValue value) :
    Exists fun body => eraseTarget value = Runtime.Term.tabs body := by
  induction valueIsValue generalizing source target result with
  | abs => cases typing
  | tabs => cases typing
  | cabs => exact ⟨_, rfl⟩
  | castTop _ _ => cases typing with | cast _ coercionTyping => cases coercionTyping
  | castArrow _ _ => cases typing with | cast _ coercionTyping => cases coercionTyping
  | castPoly _ _ => cases typing with | cast _ coercionTyping => cases coercionTyping
  | castQual innerValue ih =>
      cases typing with
      | cast innerTyping coercionTyping =>
          cases coercionTyping with
          | qual => exact ih innerTyping

theorem runtimeArrowShape
    {expression : SystemFCo.Exp []}
    {parameter result : SystemFCo.Ty []}
    (typing : SystemFCo.Exp.HasType .empty expression (.arrow parameter result))
    (value : Runtime.IsValue (eraseTarget expression)) :
    Exists fun body => eraseTarget expression = Runtime.Term.abs body := by
  rcases normalizeRuntimeValue typing value with
    ⟨targetValue, steps, targetIsValue, eraseEq⟩
  rcases SystemFCo.Exp.preservation_steps typing steps with ⟨valueTyping⟩
  rcases arrowValue_erases_abs valueTyping targetIsValue with ⟨body, shape⟩
  exact ⟨body, eraseEq.symm.trans shape⟩

theorem runtimePolyShape
    {expression : SystemFCo.Exp []} {result : SystemFCo.Ty ([.tvar])}
    (typing : SystemFCo.Exp.HasType .empty expression (.poly result))
    (value : Runtime.IsValue (eraseTarget expression)) :
    Exists fun body => eraseTarget expression = Runtime.Term.tabs body := by
  rcases normalizeRuntimeValue typing value with
    ⟨targetValue, steps, targetIsValue, eraseEq⟩
  rcases SystemFCo.Exp.preservation_steps typing steps with ⟨valueTyping⟩
  rcases polyValue_erases_tabs valueTyping targetIsValue with ⟨body, shape⟩
  exact ⟨body, eraseEq.symm.trans shape⟩

theorem runtimeQualShape
    {expression : SystemFCo.Exp []} {source target : SystemFCo.Ty []}
    {result : SystemFCo.Ty ([.cvar])}
    (typing : SystemFCo.Exp.HasType .empty expression
      (.qual source target result))
    (value : Runtime.IsValue (eraseTarget expression)) :
    Exists fun body => eraseTarget expression = Runtime.Term.tabs body := by
  rcases normalizeRuntimeValue typing value with
    ⟨targetValue, steps, targetIsValue, eraseEq⟩
  rcases SystemFCo.Exp.preservation_steps typing steps with ⟨valueTyping⟩
  rcases qualValue_erases_tabs valueTyping targetIsValue with ⟨body, shape⟩
  exact ⟨body, eraseEq.symm.trans shape⟩

/-- Closed target typing implies progress of its common-runtime erasure. -/
theorem typedRuntimeProgress
    {expression : SystemFCo.Exp []} {ty : SystemFCo.Ty []}
    (typing : SystemFCo.Exp.HasType .empty expression ty) :
    Runtime.IsValue (eraseTarget expression) \/
      Exists fun next => Runtime.Step (eraseTarget expression) next := by
  cases typing with
  | var lookup => exact nomatch lookup
  | abs => exact Or.inl .abs
  | app functionTyping argumentTyping =>
      rcases typedRuntimeProgress functionTyping with
        functionValue | ⟨function', functionStep⟩
      · rcases typedRuntimeProgress argumentTyping with
          argumentValue | ⟨argument', argumentStep⟩
        · rcases runtimeArrowShape functionTyping functionValue with ⟨body, shape⟩
          simp only [eraseTarget]
          rw [shape]
          exact Or.inr ⟨_, .beta argumentValue⟩
        · exact Or.inr ⟨_, .appArgument functionValue argumentStep⟩
      · exact Or.inr ⟨_, .appFunction functionStep⟩
  | tabs => exact Or.inl .tabs
  | tapp functionTyping =>
      rcases typedRuntimeProgress functionTyping with
        functionValue | ⟨function', functionStep⟩
      · rcases runtimePolyShape functionTyping functionValue with ⟨body, shape⟩
        simp only [eraseTarget]
        rw [shape]
        exact Or.inr ⟨_, .typeBeta⟩
      · exact Or.inr ⟨_, .tappFunction functionStep⟩
  | cabs => exact Or.inl .tabs
  | capp functionTyping _ =>
      rcases typedRuntimeProgress functionTyping with
        functionValue | ⟨function', functionStep⟩
      · rcases runtimeQualShape functionTyping functionValue with ⟨body, shape⟩
        simp only [eraseTarget]
        rw [shape]
        exact Or.inr ⟨_, .typeBeta⟩
      · exact Or.inr ⟨_, .tappFunction functionStep⟩
  | cast expressionTyping _ =>
      have progress := typedRuntimeProgress expressionTyping
      exact progress
termination_by sizeOf expression
decreasing_by
  all_goals
    simp_all
    omega

end SystemFSub.Elaboration
