import LambdaPToFCo.Full.GeneralPairCanonicalIntervalSubtypingRegression
import LambdaPToFCo.Full.GeneralPairLetPlanningRegression

/-!
# Closed full-calculus GeneralPair compilation regression

This module joins the independently certified pieces for
`LambdaPFC.GeneralPairRegression.term`:

* the bound dependent identity abstraction, adapted to its advertised `Top`;
* the exact type-member pair introduction;
* both dependent interval-pair subsumptions; and
* Church-package closure at the root result plan.

The final target expression is closed and well typed in `SystemFCoExt`. Every
package and adapter is computed by the sealed compiler interfaces used by the
preceding leaves; this module supplies no resolver, raw coercion, package, or
plan equality.  It is a concrete constructor-complete acceptance regression,
not yet the generic full-term translation theorem.
-/

namespace LambdaPToFCo.Full.GeneralPairClosedStaticRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

noncomputable section

/-- Existing full-calculus source typing accepted by this regression. -/
def sourceTyping : Tm.Ty LambdaPFC.Ctx.nil
    LambdaPFC.GeneralPairRegression.term
    LambdaPFC.GeneralPairRegression.intervalTarget :=
  LambdaPFC.GeneralPairRegression.term_typing

/-- The fully adapted body plan is definitionally the exact demand chosen by
the enclosing let. No root-factorization theorem is used. -/
theorem body_plan_eq :
    GeneralPairCanonicalIntervalSubtypingRegression.pushed.plan =
      GeneralPairLetPlanningRegression.plannedBodyDemand.plan := by
  rfl

noncomputable def bodyPackage : CompiledPackage
    (GeneralPairLetPlanningRegression.bound.plan.context
      SystemFCoExt.Ctx.empty)
    GeneralPairLetPlanningRegression.plannedBodyDemand.plan := by
  rw [← body_plan_eq]
  exact GeneralPairCanonicalIntervalSubtypingRegression.pushed.package

/-- Closed target compilation of the existing unrestricted source term. -/
noncomputable def compiled : CompiledPackage SystemFCoExt.Ctx.empty
    GeneralPairLetPlanningRegression.rootResult.plan :=
  LetPlanning.closeBody GeneralPairLetPlanningRegression.rootScope
    GeneralPairLetPlanningRegression.bound
    GeneralPairLetPlanningRegression.rootResult bodyPackage

/-- Concrete closed target typing for the complete regression. -/
noncomputable def targetTerm_hasType :
    Exp.HasType SystemFCoExt.Ctx.empty compiled.expression
      GeneralPairLetPlanningRegression.rootResult.plan.inputTy :=
  compiled.typing

end

end LambdaPToFCo.Full.GeneralPairClosedStaticRegression
