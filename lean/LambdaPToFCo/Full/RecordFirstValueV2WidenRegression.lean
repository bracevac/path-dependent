import LambdaPToFCo.Full.IntervalPairFirstWidenV2
import LambdaPToFCo.Full.RecordFirstValueStaticRegression

/-!
# Record first-value V2 widening regression

The existing Record source derivation instantiates the sealed V2 direct
type-pair and exact first-component-widening rules without any plan equality,
adapter, package, or descriptor input.
-/

namespace LambdaPToFCo.Full.RecordFirstValueV2WidenRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open RecordFirstValueStaticRegression

noncomputable section

noncomputable def exact :=
  IntervalPairIntroductionV2.ExactTypePairResult.compile BodyScope (0 : Fin 1)
    LambdaPFC.RecordRegression.typeLabel
    LambdaPFC.RecordRegression.implementationTypeWf witnessPlan

noncomputable def targetEndpoint : BidirectionalPlanModel
    (SourceContext.snoc TargetFirst)
    (exact.capability.firstPlan.context TargetContext)
    (ScopeView.bindPlan BodyScope.view exact.capability.firstPlan)
    Endpoint witnessPlan.plan :=
  targetEndpointResult.model

noncomputable def widened :=
  IntervalPairFirstWidenV2.Result.compile BodyScope (0 : Fin 1)
    LambdaPFC.RecordRegression.typeLabel
    LambdaPFC.RecordRegression.implementationTypeWf witnessPlan exact
    firstPrecise targetEndpoint

theorem source_type_eq : widened.sourceType = SourcePair := by
  rfl

theorem target_type_eq : widened.targetType = TargetPair := by
  rfl

theorem subtyping_eq : widened.subtyping = pairSubtyping := by
  rfl

theorem first_arguments_retained : widened.exactSource.firstArguments =
    (BodyScope.view (0 : Fin 1)).arguments := by
  rfl

theorem plan_eq : widened.plan =
    Pair.IntervalV2.plan targetFirstResult.plan
      targetEndpointResult.plan.inputTy targetEndpointResult.plan.inputTy := by
  rfl

theorem descriptor_retained : widened.capability.descriptor =
    exact.capability.descriptor := by
  rfl

noncomputable def producer := widened.producer

noncomputable def bound := widened.bind

theorem newest_plan : bound.newestInterface.plan =
    widened.plan.rename widened.plan.telescope.weaken := by
  rfl

theorem older_plan : (bound.olderSlot (0 : Fin 1)).interface.plan =
    firstPath.plan.rename widened.plan.telescope.weaken := by
  rfl

noncomputable def packageTyping : Exp.HasType TargetContext
    producer.package.expression widened.plan.inputTy :=
  producer.package.typing

end

end LambdaPToFCo.Full.RecordFirstValueV2WidenRegression
