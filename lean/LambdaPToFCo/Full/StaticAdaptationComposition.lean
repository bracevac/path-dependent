import LambdaPToFCo.Full.StaticAdaptation

/-!
# Sealed static-adaptation composition

Transitivity is compiled without materializing an arbitrary middle package.
The first sealed adaptation fixes one literal middle demand plan; exact
positive evidence at that same plan re-exposes its computed package as the
only middle producer accepted by the second sealed adaptation.  The outer
adapter is then definitionally the composition of the two sealed adapters and
its source derivation is the exact `Tau.Sub.trans` proof.

No adapter, package, plan choice, or callback is supplied independently of
the two `StaticAdaptation` inputs and the exact positive middle model.
-/

namespace LambdaPToFCo.Full.StaticAdaptationComposition

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

/-- The only middle producer accepted by composition: the literal result of
the first sealed adaptation at its exact demanded plan. -/
noncomputable def middleProducer
    {sourceScope middleScope : ScopeModel sourceContext targetContext}
    {firstAlignment : ScopeAlignment sourceScope.view middleScope.view}
    {sourceType middleType : LambdaPFC.Ty n}
    {firstSubtyping : Tau.Sub sourceContext
      (.ty sourceType) (.ty middleType)}
    {source : ProperProducer sourceContext targetContext sourceScope sourceType}
    {middleDemand : ProperDemand sourceContext targetContext middleScope
      middleType}
    (first : StaticAdaptation firstAlignment firstSubtyping source
      middleDemand)
    (middleModel : ProducerPlanModel sourceContext targetContext
      middleScope.view middleType middleDemand.plan) :
    OrdinaryProducer sourceContext targetContext middleScope middleType :=
  first.toOrdinary middleModel

/-- Compose two sealed adaptations through the literal computed middle
producer. -/
noncomputable def compose
    {sourceScope middleScope demandScope :
      ScopeModel sourceContext targetContext}
    {firstAlignment : ScopeAlignment sourceScope.view middleScope.view}
    {secondAlignment : ScopeAlignment middleScope.view demandScope.view}
    {sourceType middleType targetType : LambdaPFC.Ty n}
    {firstSubtyping : Tau.Sub sourceContext
      (.ty sourceType) (.ty middleType)}
    {secondSubtyping : Tau.Sub sourceContext
      (.ty middleType) (.ty targetType)}
    {source : ProperProducer sourceContext targetContext sourceScope sourceType}
    {middleDemand : ProperDemand sourceContext targetContext middleScope
      middleType}
    (first : StaticAdaptation firstAlignment firstSubtyping source
      middleDemand)
    (middleModel : ProducerPlanModel sourceContext targetContext
      middleScope.view middleType middleDemand.plan)
    {demand : ProperDemand sourceContext targetContext demandScope targetType}
    (second : StaticAdaptation secondAlignment secondSubtyping
      (.ordinary (middleProducer first middleModel)) demand) :
    StaticAdaptation (firstAlignment.compose secondAlignment)
      (.trans firstSubtyping secondSubtyping) source demand where
  adapter := first.adapter.compose second.adapter
  evidence := .trans first.evidence middleModel second.evidence

/-! ## Closed core regression -/

namespace Regression

open DemandDirectedSubtyping

noncomputable def firstDemand
    (scope : ScopeModel sourceContext targetContext) :
    ProperDemand sourceContext targetContext scope .Top :=
  SubtypingCompilerCore.opaqueDemand scope (.root (.opaque .Top))

noncomputable def first
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (source : ProperProducer sourceContext targetContext scope sourceType) :
    StaticAdaptation (ScopeAlignment.identity scope.view)
      (.top : Tau.Sub sourceContext (.ty sourceType) (.ty .Top)) source
      (firstDemand scope) :=
  StaticAdaptation.ofCore
    (FusedAdaptation.toOpaque (ScopeAlignment.identity scope.view) .top source
      (.root (.opaque .Top)))

noncomputable def middle
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (source : ProperProducer sourceContext targetContext scope sourceType) :
    OrdinaryProducer sourceContext targetContext scope .Top :=
  middleProducer (first scope source) ProducerPlanModel.top

noncomputable def second
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (source : ProperProducer sourceContext targetContext scope sourceType) :
    StaticAdaptation (ScopeAlignment.identity scope.view)
      (.refl : Tau.Sub sourceContext (.ty .Top) (.ty .Top))
      (.ordinary (middle scope source)) (firstDemand scope) :=
  StaticAdaptation.ofCore
    (FusedAdaptation.toOpaque (ScopeAlignment.identity scope.view) .refl
      (.ordinary (middle scope source)) (.root (.opaque .Top)))

/-- The result retains the literal outer transitivity derivation. -/
noncomputable def composed
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (source : ProperProducer sourceContext targetContext scope sourceType) :
    StaticAdaptation
      ((ScopeAlignment.identity scope.view).compose
        (ScopeAlignment.identity scope.view))
      (.trans
        (.top : Tau.Sub sourceContext (.ty sourceType) (.ty .Top))
        (.refl : Tau.Sub sourceContext (.ty .Top) (.ty .Top)))
      source (firstDemand scope) :=
  compose (first scope source) ProducerPlanModel.top (second scope source)

noncomputable def finalProducer
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (source : ProperProducer sourceContext targetContext scope sourceType) :
    OrdinaryProducer sourceContext targetContext scope .Top :=
  (composed scope source).toOrdinary ProducerPlanModel.top

theorem final_origin_eq
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (source : ProperProducer sourceContext targetContext scope sourceType) :
    (finalProducer scope source).origin =
      .push (.trans
        (.top : Tau.Sub sourceContext (.ty sourceType) (.ty .Top))
        (.refl : Tau.Sub sourceContext (.ty .Top) (.ty .Top)))
        source.origin := by
  rfl

end Regression

end LambdaPToFCo.Full.StaticAdaptationComposition
