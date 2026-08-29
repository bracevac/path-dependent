import FCsub.Runtime

/-!
# Basic metatheory of the erased runtime
-/

namespace FCsub.Runtime

/-- Runtime values cannot reduce. -/
theorem IsValue.noStep {scope : Sig} {term next : Tm scope}
    (value : IsValue term) : ¬ Step term next := by
  intro step
  cases value <;> cases step

/-- The erased call-by-value semantics is deterministic. -/
theorem Step.deterministic {scope : Sig} {term leftTarget rightTarget : Tm scope}
    (left : Step term leftTarget) (right : Step term rightTarget) :
    leftTarget = rightTarget := by
  induction left generalizing rightTarget with
  | appFunction leftStep induction =>
      cases right with
      | appFunction rightStep =>
          congr
          exact induction rightStep
      | appArgument value _ => exact False.elim (value.noStep leftStep)
      | beta _ => exact False.elim (IsValue.lam.noStep leftStep)
  | appArgument functionValue leftStep induction =>
      cases right with
      | appFunction rightStep =>
          exact False.elim (functionValue.noStep rightStep)
      | appArgument _ rightStep =>
          congr
          exact induction rightStep
      | beta argumentValue =>
          exact False.elim (argumentValue.noStep leftStep)
  | beta argumentValue =>
      cases right with
      | appFunction rightStep =>
          exact False.elim (IsValue.lam.noStep rightStep)
      | appArgument _ rightStep =>
          exact False.elim (argumentValue.noStep rightStep)
      | beta _ => rfl
  | letRhs leftStep induction =>
      cases right with
      | letRhs rightStep =>
          congr
          exact induction rightStep
      | zeta value => exact False.elim (value.noStep leftStep)
  | zeta value =>
      cases right with
      | letRhs rightStep => exact False.elim (value.noStep rightStep)
      | zeta _ => rfl

namespace Steps

def single {scope : Sig} {first second : Tm scope}
    (step : Step first second) : Steps first second :=
  .tail .refl step

/-- Concatenation of finite reduction traces. -/
def trans {scope : Sig} {first second third : Tm scope}
    (left : Steps first second) (right : Steps second third) :
    Steps first third :=
  match right with
  | .refl => left
  | .tail initial final => .tail (trans left initial) final

@[simp]
theorem refl_trans {scope : Sig} {first second : Tm scope}
    (steps : Steps first second) :
    trans (.refl : Steps first first) steps = steps := by
  induction steps with
  | refl => rfl
  | tail initial final induction => simp

end Steps

end FCsub.Runtime
