import LambdaPToFCo.Full.FunctionInterface
import LambdaPToFCo.Full.PathPackageZipper

/-!
# Open-interface application kernel

The full path/term compiler opens Church packages in continuations.  Once a
function interface and its argument interface are genuinely available in the
same target context, application is local: apply the retained dependent code
to every mixed argument field and return a package at the codomain plan
instantiated by that exact argument substitution.

This module deliberately does not move the result out of the open context.
That closing step requires the synchronized source/target path-instantiation
proof retained by the higher compiler.
-/

namespace LambdaPToFCo.Full.ApplicationCompilerCore

open SystemFCoExt

/-- Apply an opened dependent function to an opened argument with the exact
domain plan, retaining the instantiated codomain as a compiled package. -/
noncomputable def applyOpened
    {sig : Sig} {base : Ctx sig}
    {domain : ValuePlan sig} {codomain : ValuePlan domain.scope}
    (function : FunctionInterface.View base domain codomain)
    (argument : ValueInterface base)
    (plan_eq : argument.plan = domain) :
    PathPackageZipper.CompiledPackage base
      (codomain.subst (by
        subst plan_eq
        exact argument.arguments.substitution)) := by
  subst plan_eq
  let substitution := argument.arguments.substitution
  have applied := function.apply_hasType argument.arguments
  have appliedTyping :
      Exp.HasType base (function.apply argument.arguments)
        (codomain.subst substitution).inputTy := by
    rw [← ValuePlan.inputTy_subst]
    exact applied
  exact
    { expression := function.apply argument.arguments
      typing := appliedTyping }

end LambdaPToFCo.Full.ApplicationCompilerCore
