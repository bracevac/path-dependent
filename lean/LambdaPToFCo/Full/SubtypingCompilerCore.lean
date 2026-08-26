import LambdaPToFCo.Full.TranslationInterfaces

/-!
# Full proper-subtyping compiler core

This first derivation-directed layer covers the representation-independent
proper rules and the compositional core.  Heterogeneous reflexivity takes an
explicit structural rebase witness: aligned source slots preserve identity
and payload, but their observation plans need not coincide.

Every covariant result is built through the sealed `ProperPushResult` smart
constructors.  Consequently this module never fabricates a target package or
producer origin.  Static Bottom synthesis remains separate from ordinary
execution evidence.
-/

namespace LambdaPToFCo.Full.SubtypingCompilerCore

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

/-! ## Heterogeneous reflexivity -/

/-- Covariantly transport one certified positive plan across aligned scopes. -/
structure PositiveRebase
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType : LambdaPFC.Ty n}
    (source : PositivePlan sourceContext targetContext sourceScope.view
      sourceType) : Type where
  target : PositivePlan sourceContext targetContext targetScope.view sourceType
  adapter : StableIdentity.Adapter targetContext source.plan target.plan

/-- Contravariantly transport one certified negative plan across aligned
scopes. -/
structure NegativeRebase
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType : LambdaPFC.Ty n}
    (target : NegativePlan sourceContext targetContext targetScope.view
      sourceType) : Type where
  source : NegativePlan sourceContext targetContext sourceScope.view sourceType
  adapter : StableIdentity.Adapter targetContext source.plan target.plan

namespace PositiveRebase

noncomputable def identity
    (scope : ScopeModel sourceContext targetContext)
    (endpoint : PositivePlan sourceContext targetContext scope.view sourceType) :
    PositiveRebase (ScopeAlignment.identity scope.view) endpoint where
  target := endpoint
  adapter := StableIdentity.Adapter.identity targetContext endpoint.plan

end PositiveRebase

namespace NegativeRebase

noncomputable def identity
    (scope : ScopeModel sourceContext targetContext)
    (endpoint : NegativePlan sourceContext targetContext scope.view sourceType) :
    NegativeRebase (ScopeAlignment.identity scope.view) endpoint where
  source := endpoint
  adapter := StableIdentity.Adapter.identity targetContext endpoint.plan

end NegativeRebase

/-- Heterogeneous positive reflexivity.  The rebase chooses only certified
target structural evidence and an adapter; the sealed constructor creates the
actual target origin and package. -/
noncomputable def pushRefl
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType : LambdaPFC.Ty n}
    (source : ProperProducer sourceContext targetContext sourceScope sourceType)
    (ordinaryRebase : (ordinary : OrdinaryProducer sourceContext targetContext
      sourceScope sourceType) -> PositiveRebase alignment
        ordinary.positivePlan) :
    ProperPushResult alignment (Tau.Sub.refl (τ := .ty sourceType)) source := by
  cases source with
  | ordinary ordinary =>
      let rebased := ordinaryRebase ordinary
      exact ProperPushResult.ordinary alignment .refl ordinary
        rebased.target.model rebased.adapter
  | absurd bottom advertised =>
      exact ProperPushResult.fromAbsurd alignment .refl bottom

/-- Heterogeneous negative reflexivity. -/
def pullRefl
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType : LambdaPFC.Ty n}
    (target : ProperDemand sourceContext targetContext targetScope sourceType)
    (rebase : NegativeRebase alignment target.negativePlan) :
    ProperPullResult alignment (Tau.Sub.refl (τ := .ty sourceType)) target :=
  { model := rebase.source.model
    adapter := rebase.adapter }

noncomputable def pushReflSameScope
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (source : ProperProducer sourceContext targetContext scope sourceType) :
    ProperPushResult (ScopeAlignment.identity scope.view)
      (Tau.Sub.refl (τ := .ty sourceType)) source :=
  pushRefl (ScopeAlignment.identity scope.view) source fun ordinary =>
    PositiveRebase.identity scope ordinary.positivePlan

noncomputable def pullReflSameScope
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (target : ProperDemand sourceContext targetContext scope sourceType) :
    ProperPullResult (ScopeAlignment.identity scope.view)
      (Tau.Sub.refl (τ := .ty sourceType)) target :=
  pullRefl (ScopeAlignment.identity scope.view) target
    (NegativeRebase.identity scope target.negativePlan)

/-! ## Bottom and Top -/

/-- Bottom covariance preserves the exact package as distinct absurd
provenance. -/
noncomputable def pushBottom
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {targetType : LambdaPFC.Ty n}
    (source : ProperProducer sourceContext targetContext sourceScope .Bot) :
    ProperPushResult alignment (Tau.Sub.bot (T := targetType)) source := by
  cases source with
  | ordinary ordinary =>
      exact ProperPushResult.fromBottom alignment .bot ordinary
  | absurd bottom advertised =>
      exact ProperPushResult.fromAbsurd alignment .bot bottom

/-- Top covariance forgets every observation. -/
noncomputable def pushTop
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType : LambdaPFC.Ty n}
    (source : ProperProducer sourceContext targetContext sourceScope sourceType) :
    ProperPushResult alignment (Tau.Sub.top (T := sourceType)) source := by
  cases source with
  | ordinary ordinary =>
      exact ProperPushResult.ordinary alignment .top ordinary
        ⟨Top.plan sig, .top⟩
        (StableIdentity.Adapter.toTop targetContext ordinary.plan)
  | absurd bottom advertised =>
      exact ProperPushResult.fromAbsurd alignment .top bottom

/-- A Top target pulls back to the observation-free demand at any raw source
type. -/
noncomputable def pullTop
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType : LambdaPFC.Ty n}
    (target : ProperDemand sourceContext targetContext targetScope .Top) :
    ProperPullResult alignment (Tau.Sub.top (T := sourceType)) target := by
  rcases target with ⟨trace, ⟨plan, model⟩⟩
  cases model with
  | «opaque» =>
      exact
        { model := ⟨Top.plan sig, .opaque sourceType⟩
          adapter := StableIdentity.Adapter.identity targetContext
            (Top.plan sig) }

/-- Bottom contravariance statically supplies every target observation. -/
noncomputable def pullBottom
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {targetType : LambdaPFC.Ty n}
    (target : ProperDemand sourceContext targetContext targetScope targetType) :
    ProperPullResult alignment (Tau.Sub.bot (T := targetType)) target :=
  { model := ⟨Bot.plan sig, .bottom⟩
    adapter := StableIdentity.Adapter.fromBottom targetContext target.plan }

/-! ## Transitivity -/

/-- Compose two ordinary covariance legs, rebuilding the sealed final result
from the original package and the exact composed source derivation. -/
noncomputable def composeOrdinaryPush
    {firstScope middleScope finalScope : ScopeModel sourceContext targetContext}
    {firstAlignment : ScopeAlignment firstScope.view middleScope.view}
    {secondAlignment : ScopeAlignment middleScope.view finalScope.view}
    {sourceType middleType targetType : LambdaPFC.Ty n}
    {firstSubtyping : Tau.Sub sourceContext (.ty sourceType) (.ty middleType)}
    {secondSubtyping : Tau.Sub sourceContext (.ty middleType) (.ty targetType)}
    (source : OrdinaryProducer sourceContext targetContext firstScope sourceType)
    (middleModel : Sigma fun plan =>
      ProducerPlanModel sourceContext targetContext middleScope.view middleType
        plan)
    (firstAdapter : StableIdentity.Adapter targetContext source.plan
      middleModel.1)
    (targetModel : Sigma fun plan =>
      ProducerPlanModel sourceContext targetContext finalScope.view targetType
        plan)
    (secondAdapter : StableIdentity.Adapter targetContext middleModel.1
      targetModel.1) :
    ProperPushResult (firstAlignment.compose secondAlignment)
      (.trans firstSubtyping secondSubtyping) (.ordinary source) :=
  ProperPushResult.ordinary (firstAlignment.compose secondAlignment)
    (.trans firstSubtyping secondSubtyping) source targetModel
    (firstAdapter.compose secondAdapter)

/-- If the exact intermediate is Bottom, seal the first adapter-produced
Bottom package as absurd provenance for the second leg. -/
noncomputable def composeThroughBottom
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType targetType : LambdaPFC.Ty n}
    (first : Tau.Sub sourceContext (.ty sourceType) (.ty .Bot))
    (second : Tau.Sub sourceContext (.ty .Bot) (.ty targetType))
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      sourceType)
    (bottomModel : Sigma fun plan =>
      ProducerPlanModel sourceContext targetContext targetScope.view .Bot plan)
    (adapter : StableIdentity.Adapter targetContext source.plan bottomModel.1) :
    ProperPushResult alignment (.trans first second) (.ordinary source) :=
  ProperPushResult.throughBottom alignment first second source bottomModel
    adapter

/-- Pull composition is total and direct. -/
noncomputable def composePull
    {firstScope middleScope finalScope : ScopeModel sourceContext targetContext}
    {firstAlignment : ScopeAlignment firstScope.view middleScope.view}
    {secondAlignment : ScopeAlignment middleScope.view finalScope.view}
    {sourceType middleType targetType : LambdaPFC.Ty n}
    {firstSubtyping : Tau.Sub sourceContext (.ty sourceType) (.ty middleType)}
    {secondSubtyping : Tau.Sub sourceContext (.ty middleType) (.ty targetType)}
    (target : ProperDemand sourceContext targetContext finalScope targetType)
    (second : ProperPullResult secondAlignment secondSubtyping target)
    (first : ProperPullResult firstAlignment firstSubtyping second.source) :
    ProperPullResult (firstAlignment.compose secondAlignment)
      (.trans firstSubtyping secondSubtyping) target where
  model := first.model
  adapter := first.adapter.compose second.adapter

/-! ## Static satisfaction -/

def opaqueDemand
    (scope : ScopeModel sourceContext targetContext)
    (trace : DemandTrace sourceContext sourceType) :
    ProperDemand sourceContext targetContext scope sourceType where
  trace := trace
  model := ⟨Top.plan sig, .opaque sourceType⟩

/-- Every package statically satisfies an observation-free demand.  This
makes no ordinary readiness claim for an absurd producer. -/
noncomputable def satisfyOpaque
    {producerScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment producerScope.view demandScope.view)
    (producer : ProperProducer sourceContext targetContext producerScope
      sourceType)
    (trace : DemandTrace sourceContext sourceType) :
    ProperSatisfaction alignment producer (opaqueDemand demandScope trace) where
  adapter := StableIdentity.Adapter.toTop targetContext producer.plan

/-- Equal plans are sufficient for static satisfaction. -/
noncomputable def satisfyEqualPlan
    {producerScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment producerScope.view demandScope.view)
    {sourceType : LambdaPFC.Ty n}
    (producer : ProperProducer sourceContext targetContext producerScope
      sourceType)
    (demand : ProperDemand sourceContext targetContext demandScope sourceType)
    (plans : producer.plan = demand.plan) :
    ProperSatisfaction alignment producer demand := by
  constructor
  simpa only [plans] using
    (StableIdentity.Adapter.identity targetContext producer.plan)

end LambdaPToFCo.Full.SubtypingCompilerCore
