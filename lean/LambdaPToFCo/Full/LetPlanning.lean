import LambdaPToFCo.Full.LetCompilerCore
import LambdaPToFCo.Full.ContextWellFormed
import LambdaPToFCo.Full.WfPlan

/-!
# Demand-local planning for full lets

A full source `let` stores well-formedness only for its root result.  The body
is checked under the bound source type and must be compiled against that root
result weakened through the exact target package used for the bound value.

This leaf derives that negative body interface from one concrete bound
producer and one demand-local `WfPlan.Proper`.  Its plan is definitionally the
root result plan renamed through the bound telescope, so the target package can
be closed by `LetCompilerCore` without a root-factorization assumption.
-/

namespace LambdaPToFCo.Full.LetPlanning

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

/-- The exact source/target scope in which a let body is compiled. -/
noncomputable def bodyScope
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {boundType : LambdaPFC.Ty n}
    (bound : OrdinaryProducer sourceContext targetContext scope boundType) :
    ScopeModel (sourceContext.snoc boundType)
      (bound.plan.context targetContext) :=
  scope.bind bound.modeled

/-- The closable body demand induced by the root result plan.  No global path
resolver is needed once that one result plan has been certified. -/
noncomputable def bodyDemand
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {boundType resultType : LambdaPFC.Ty n}
    (bound : OrdinaryProducer sourceContext targetContext scope boundType)
    (result : WfPlan.Proper sourceContext targetContext scope resultType) :
    ProperDemand (sourceContext.snoc boundType)
      (bound.plan.context targetContext) (bodyScope scope bound)
      resultType.weaken where
  trace := DemandTrace.ofWf (TypeWellFormed.weaken result.wf boundType)
  model :=
    ⟨result.plan.rename bound.plan.telescope.weaken,
      DemandPlanModel.underBinding bound.modeled result.model.demand⟩

@[simp] theorem bodyDemand_plan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {boundType resultType : LambdaPFC.Ty n}
    (bound : OrdinaryProducer sourceContext targetContext scope boundType)
    (result : WfPlan.Proper sourceContext targetContext scope resultType) :
    (bodyDemand scope bound result).plan =
      result.plan.rename bound.plan.telescope.weaken := by
  rfl

/-- Close a body compiled against `bodyDemand` back to the root result plan.
The only target computation here is the ordinary Church elimination already
typed by `LetCompilerCore.closeBody`. -/
noncomputable def closeBody
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {boundType resultType : LambdaPFC.Ty n}
    (bound : OrdinaryProducer sourceContext targetContext scope boundType)
    (result : WfPlan.Proper sourceContext targetContext scope resultType)
    (body : CompiledPackage (bound.plan.context targetContext)
      (bodyDemand scope bound result).plan) :
    CompiledPackage targetContext result.plan :=
  LetCompilerCore.closeBody bound.package result.plan body
    (bodyDemand_plan scope bound result)

end LambdaPToFCo.Full.LetPlanning
