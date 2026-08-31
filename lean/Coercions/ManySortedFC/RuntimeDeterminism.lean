import Coercions.ManySortedFC.Runtime

/-!
# Determinism of the erased runtime

The runtime evaluates applications and lets from left to right.  A modal
suspension is inert until `force`; `force` evaluates its operand once before
releasing the suspended body.
-/

namespace ManySortedFC.Runtime

namespace IsValue

/-- Runtime values have no outgoing reduction step. -/
theorem noStep {scope : Nat} {value next : Tm scope}
    (valueForm : IsValue value) : ¬ Step value next := by
  intro step
  cases valueForm <;> cases step

end IsValue

namespace Step

/-- Left-to-right call-by-value reduction is deterministic. -/
theorem deterministic {scope : Nat} {first second third : Tm scope}
    (firstStep : Step first second) (secondStep : Step first third) :
    second = third := by
  induction firstStep generalizing third with
  | appFunction step induction =>
      cases secondStep with
      | appFunction other =>
          exact congrArg (fun function => Tm.app function _) (induction other)
      | appArgument functionValue _ =>
          exact False.elim (functionValue.noStep step)
      | beta _ => cases step
  | appArgument functionValue step induction =>
      cases secondStep with
      | appFunction other =>
          exact False.elim (functionValue.noStep other)
      | appArgument _ other =>
          exact congrArg (Tm.app _) (induction other)
      | beta argumentValue =>
          exact False.elim (argumentValue.noStep step)
  | beta argumentValue =>
      cases secondStep with
      | appFunction step => cases step
      | appArgument _ step =>
          exact False.elim (argumentValue.noStep step)
      | beta _ => rfl
  | letRhs step induction =>
      cases secondStep with
      | letRhs other =>
          exact congrArg (fun rhs => Tm.let' rhs _) (induction other)
      | zeta rhsValue =>
          exact False.elim (rhsValue.noStep step)
  | zeta rhsValue =>
      cases secondStep with
      | letRhs step =>
          exact False.elim (rhsValue.noStep step)
      | zeta _ => rfl
  | forceSuspension step induction =>
      cases secondStep with
      | forceSuspension other =>
          exact congrArg Tm.force (induction other)
      | forceBeta => cases step
  | forceBeta =>
      cases secondStep with
      | forceSuspension step => cases step
      | forceBeta => rfl

end Step

end ManySortedFC.Runtime
