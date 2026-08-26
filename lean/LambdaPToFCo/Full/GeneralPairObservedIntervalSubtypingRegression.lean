import LambdaPToFCo.Full.GeneralPairIntroductionStaticRegression
import LambdaPToFCo.Full.StaticAdaptation
import LambdaPToFCo.Full.TargetModelRenaming

/-!
# Observed interval-pair subsumption for the GeneralPair body

This leaf continues `GeneralPairIntroductionStaticRegression` through the
first, genuinely dependent subsumption in `LambdaPFC.GeneralPairRegression`.
The exact source type stores the outer `Top` variable as both interval
endpoints; the target exposes the adapted `Top` first component through the
two singleton endpoints `{y}..{y}`.

The bridge context is constructed from its literal source representation and
target-first telescope openings. All four endpoint plans are reconstructed
from the certified body scope in that context. The lower `.widen` and upper
`.symm` adaptations then erase into the exact canonical `Top.plan` carried by
those singleton paths. No `WfPlan.Resolver`, target package callback, raw
stable adapter, or caller-supplied endpoint equality appears in the public
construction.

The result is one static `StableIdentity.Adapter` and the corresponding typed
target package. It does not claim ordinary execution readiness or close the
outer source `let`.
-/

namespace LambdaPToFCo.Full.GeneralPairObservedIntervalSubtypingRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open DemandDirectedSubtyping
open IntervalPairSubtypingRuleConstruction
open SubtypingCompilerCore
open DemandDirectedPairSubtyping

noncomputable section

abbrev SourceContext : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc .Top

abbrev SourceFirst : LambdaPFC.Ty 1 := .Single (.var 0)
abbrev TargetFirst : LambdaPFC.Ty 1 := .Top

abbrev SourceLower : LambdaPFC.Ty 2 := .Single (.var 1)
abbrev SourceUpper : LambdaPFC.Ty 2 := .Single (.var 1)
abbrev TargetLower : LambdaPFC.Ty 2 := .Single (.var 0)
abbrev TargetUpper : LambdaPFC.Ty 2 := .Single (.var 0)

abbrev SourcePair : LambdaPFC.Ty 1 :=
  .Pair SourceFirst LambdaPFC.GeneralPairRegression.label
    (.intv SourceLower SourceUpper)

abbrev TargetPair : LambdaPFC.Ty 1 :=
  .Pair TargetFirst LambdaPFC.GeneralPairRegression.label
    (.intv TargetLower TargetUpper)

/-- The explicit target below is definitionally the first exposed interval
pair in the existing source regression. -/
theorem targetPair_eq :
    TargetPair = LambdaPFC.GeneralPairRegression.intervalSource.weaken := by
  rfl

def firstSubtyping :
    Tau.Sub SourceContext (.ty SourceFirst) (.ty TargetFirst) :=
  .top

def lowerSubtyping :
    Tau.Sub (SourceContext.snoc SourceFirst)
      (.ty TargetLower) (.ty SourceLower) :=
  .widen .var

def upperSubtyping :
    Tau.Sub (SourceContext.snoc SourceFirst)
      (.ty SourceUpper) (.ty TargetUpper) :=
  .symm .var

def nonempty :
    Tau.Sub (SourceContext.snoc SourceFirst)
      (.ty SourceLower) (.ty SourceUpper) :=
  .refl

def memberSubtyping :
    Tau.Sub (SourceContext.snoc SourceFirst)
      (.intv SourceLower SourceUpper) (.intv TargetLower TargetUpper) :=
  .bounds lowerSubtyping upperSubtyping nonempty

abbrev BaseTargetContext :=
  GeneralPairIntroductionStaticRegression.topResult.plan.context
    SystemFCoExt.Ctx.empty

noncomputable def source : OrdinaryProducer SourceContext BaseTargetContext
    GeneralPairIntroductionStaticRegression.bodyScope SourcePair :=
  GeneralPairIntroductionStaticRegression.compiled

noncomputable def targetFirstResult :
    WfPlan.Proper SourceContext BaseTargetContext
      GeneralPairIntroductionStaticRegression.bodyScope TargetFirst :=
  WfPlan.Proper.top GeneralPairIntroductionStaticRegression.bodyScope

noncomputable def targetBoundScope :
    ScopeModel (SourceContext.snoc TargetFirst)
      (targetFirstResult.plan.context BaseTargetContext) :=
  GeneralPairIntroductionStaticRegression.bodyScope.bindBidirectional
    targetFirstResult.model

def targetPrecise :
    Path.Ty (SourceContext.snoc TargetFirst) (.var 0)
      (.ty (.Top : LambdaPFC.Ty 2)) :=
  .var

noncomputable def targetPath := targetBoundScope.variablePath (0 : Fin 2)

noncomputable def targetEndpointResult :
    WfPlan.Proper (SourceContext.snoc TargetFirst)
      (targetFirstResult.plan.context BaseTargetContext)
      targetBoundScope TargetLower :=
  WfPlan.Proper.singletonFromPathPackage targetBoundScope targetPrecise
    targetPath

noncomputable def targetMemberResult :
    WfPlan.Interval (SourceContext.snoc TargetFirst)
      (targetFirstResult.plan.context BaseTargetContext)
      targetBoundScope TargetLower TargetUpper :=
  WfPlan.Interval.bounds targetBoundScope targetEndpointResult
    targetEndpointResult .refl

noncomputable def targetResult :
    WfPlan.Proper SourceContext BaseTargetContext
      GeneralPairIntroductionStaticRegression.bodyScope
      TargetPair :=
  WfPlan.Proper.intervalPair GeneralPairIntroductionStaticRegression.bodyScope
    targetFirstResult targetMemberResult

noncomputable def demand := targetResult.demand

noncomputable def endpoints : EndpointModels source demand where
  sourceFirstPlan :=
    (PairIntroductionCompiler.variableSingleton
      GeneralPairIntroductionStaticRegression.bodyScope (0 : Fin 1)).plan
  sourceLowerPlan :=
    GeneralPairIntroductionStaticRegression.witnessPlan.plan
  sourceUpperPlan :=
    GeneralPairIntroductionStaticRegression.witnessPlan.plan
  sourceFirstModel :=
    (PairIntroductionCompiler.variableSingleton
      GeneralPairIntroductionStaticRegression.bodyScope (0 : Fin 1)).modeled
  sourceMemberModel := .bounds
    GeneralPairIntroductionStaticRegression.witnessPlan.model.demand
    GeneralPairIntroductionStaticRegression.witnessPlan.model.producer
  sourceModel_eq := rfl
  targetFirstPlan := targetFirstResult.plan
  targetLowerPlan := targetEndpointResult.plan
  targetUpperPlan := targetEndpointResult.plan
  targetFirstModel := targetFirstResult.model
  targetMemberModel := targetMemberResult.model
  demandModel_eq := rfl

noncomputable def first : FirstAdaptation endpoints firstSubtyping where
  producerScope := GeneralPairIntroductionStaticRegression.bodyScope
  consumerScope := GeneralPairIntroductionStaticRegression.bodyScope
  alignment := ScopeAlignment.identity
    GeneralPairIntroductionStaticRegression.bodyScope.view
  producer := .ordinary
    (PairIntroductionCompiler.variableSingleton
      GeneralPairIntroductionStaticRegression.bodyScope (0 : Fin 1))
  consumer := targetFirstResult.demand
  adaptation := FusedAdaptation.toOpaque
    (ScopeAlignment.identity
      GeneralPairIntroductionStaticRegression.bodyScope.view)
    firstSubtyping
    (.ordinary (PairIntroductionCompiler.variableSingleton
      GeneralPairIntroductionStaticRegression.bodyScope (0 : Fin 1)))
    (DemandTrace.ofWf targetFirstResult.wf)
  producerPlan_eq := rfl
  consumerPlan_eq := rfl

noncomputable abbrev SourceFirstPlan := endpoints.sourceFirstPlan
noncomputable abbrev SourceLowerPlan := endpoints.sourceLowerPlan
noncomputable abbrev SourceUpperPlan := endpoints.sourceUpperPlan
noncomputable abbrev TargetFirstPlan := endpoints.targetFirstPlan

noncomputable abbrev SourceRepresentation :=
  Pair.Interval.representation SourceFirstPlan SourceLowerPlan.inputTy
    SourceUpperPlan.inputTy

noncomputable abbrev SourceMemberAtBinder :=
  IntervalPairRepresentationBridgeConstruction.sourceMemberAtBinder
    SourceFirstPlan SourceLowerPlan SourceUpperPlan

noncomputable abbrev TargetFirstAtSource :=
  IntervalPairRepresentationBridgeConstruction.targetFirstAtSource
    SourceFirstPlan SourceLowerPlan SourceUpperPlan TargetFirstPlan

noncomputable def commonMapping :=
  ((Rename.weaken .var).comp
    (IntervalPairRepresentationBridgeConstruction.sourceOpening
      SourceFirstPlan SourceLowerPlan SourceUpperPlan)).comp
    TargetFirstAtSource.telescope.weaken

noncomputable def commonMappingTyped : Rename.Typed BaseTargetContext
    (CommonEndpointContext endpoints) commonMapping := by
  apply Rename.Typed.comp
  · apply Rename.Typed.comp
    · exact Rename.Typed.weaken BaseTargetContext
        (.var SourceRepresentation.existsTy)
    · apply Rename.Typed.comp
      · exact
          (IntervalPairRepresentationBridgeConstruction.sourceFirstAtBinder
            SourceFirstPlan).telescope.weaken_typed
            (BaseTargetContext.bindVar SourceRepresentation.existsTy)
      · exact
          (IntervalPairRepresentationBridgeConstruction.sourceMemberAtBinder
            SourceFirstPlan SourceLowerPlan SourceUpperPlan).weaken_typed
            ((IntervalPairRepresentationBridgeConstruction.sourceFirstAtBinder
              SourceFirstPlan).context
              (BaseTargetContext.bindVar SourceRepresentation.existsTy))
  · exact TargetFirstAtSource.telescope.weaken_typed
      (IntervalPairRepresentationBridgeConstruction.sourceOpenedContext
        BaseTargetContext SourceFirstPlan SourceLowerPlan SourceUpperPlan)

noncomputable def commonBaseScope :
    ScopeModel SourceContext (CommonEndpointContext endpoints) :=
  GeneralPairIntroductionStaticRegression.bodyScope.targetRename commonMapping
    commonMappingTyped

/- The source representation opens the exact first package retained by the
direct type-pair introduction. The following target-first opening keeps that
interface in the bridge's final common context. -/
noncomputable def commonSourceFirstInterface :
    ValueInterface (CommonEndpointContext endpoints) :=
  (IntervalPairRepresentationBridgeConstruction.sourceFirstInterface
    BaseTargetContext SourceFirstPlan SourceLowerPlan SourceUpperPlan).rename
      TargetFirstAtSource.telescope.weaken
      (TargetFirstAtSource.telescope.weaken_typed
        (IntervalPairRepresentationBridgeConstruction.sourceOpenedContext
          BaseTargetContext SourceFirstPlan SourceLowerPlan SourceUpperPlan))

theorem commonSourceFirstInterface_plan_eq :
    commonSourceFirstInterface.plan = Top.plan _ := by
  rfl

theorem commonBaseSlot_plan_eq :
    (commonBaseScope.view (0 : Fin 1)).plan = Top.plan _ := by
  unfold commonBaseScope
  rfl

theorem commonBase_plan_eq (index : Fin 1) :
    (commonBaseScope.view index).plan = Top.plan _ := by
  refine Fin.cases commonBaseSlot_plan_eq (fun impossible => ?_) index
  exact Fin.elim0 impossible

noncomputable abbrev CommonView :
    ScopeView 2 (CommonEndpointContext endpoints) :=
  commonBaseScope.view.snocExisting commonSourceFirstInterface

/- Both heterogeneous binder scopes use this same target view. On the left,
the newest source type is the singleton of the older Top slot; on the right,
it is Top itself. The first adaptation preserves the exact hidden identity and
payload, and both source/target first plans are definitionally `Top.plan`, so
the opened source-first interface is the exact shared newest target slot. -/

noncomputable def leftScope :
    ScopeModel (SourceContext.snoc SourceFirst)
      (CommonEndpointContext endpoints) where
  view := CommonView
  slot index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · simp only [LambdaPFC.Ctx.lookup, ScopeView.snocExisting_here]
      rw [commonSourceFirstInterface_plan_eq]
      exact ProducerPlanModel.singleton
        (Path.Ty.var (x := (1 : Fin 2))) ProducerPlanModel.top
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) older
      simp only [LambdaPFC.Ctx.lookup, ScopeView.snocExisting_there]
      rw [commonBaseSlot_plan_eq]
      exact ProducerPlanModel.top

noncomputable def rightScope :
    ScopeModel (SourceContext.snoc TargetFirst)
      (CommonEndpointContext endpoints) where
  view := CommonView
  slot index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · simp only [LambdaPFC.Ctx.lookup, ScopeView.snocExisting_here]
      rw [commonSourceFirstInterface_plan_eq]
      exact ProducerPlanModel.top
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) older
      simp only [LambdaPFC.Ctx.lookup, ScopeView.snocExisting_there]
      rw [commonBaseSlot_plan_eq]
      exact ProducerPlanModel.top

noncomputable def commonAlignment : ScopeAlignment rightScope.view leftScope.view :=
  ScopeAlignment.identity CommonView

noncomputable def lowerProducer : PositivePlan
    (SourceContext.snoc TargetFirst) (CommonEndpointContext endpoints)
    rightScope.view TargetLower where
  model := ⟨(rightScope.view (0 : Fin 2)).plan,
    .singleton targetPrecise (rightScope.slot 0)⟩

noncomputable def lowerDemand : NegativePlan
    (SourceContext.snoc SourceFirst) (CommonEndpointContext endpoints)
    leftScope.view SourceLower where
  model := ⟨(leftScope.view (1 : Fin 2)).plan,
    .singleton (Path.Ty.var (x := (1 : Fin 2))) (leftScope.slot 1)⟩

noncomputable def upperProducer : PositivePlan
    (SourceContext.snoc SourceFirst) (CommonEndpointContext endpoints)
    leftScope.view SourceUpper where
  model := ⟨(leftScope.view (1 : Fin 2)).plan,
    .singleton (Path.Ty.var (x := (1 : Fin 2))) (leftScope.slot 1)⟩

noncomputable def upperDemand : NegativePlan
    (SourceContext.snoc TargetFirst) (CommonEndpointContext endpoints)
    rightScope.view TargetUpper where
  model := ⟨(rightScope.view (0 : Fin 2)).plan,
    .singleton targetPrecise (rightScope.slot 0)⟩

theorem lowerProducerPlan_eq : lowerProducer.plan =
    IntervalPairRepresentationBridgeConstruction.targetLowerAtSource
      endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan
      endpoints.targetLowerPlan := by
  rfl

theorem lowerDemandPlan_eq : lowerDemand.plan =
    IntervalPairRepresentationBridgeConstruction.sourceLowerAtTargetFirst
      endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan := by
  rfl

theorem upperProducerPlan_eq : upperProducer.plan =
    IntervalPairRepresentationBridgeConstruction.sourceUpperAtTargetFirst
      endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan := by
  rfl

theorem upperDemandPlan_eq : upperDemand.plan =
    IntervalPairRepresentationBridgeConstruction.targetUpperAtSource
      endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan
      endpoints.targetUpperPlan := by
  rfl

theorem lowerDemand_plan_top : lowerDemand.plan = Top.plan _ := by
  rfl

theorem upperDemand_plan_top : upperDemand.plan = Top.plan _ := by
  rfl

noncomputable def lowerAdaptation :
    ContravariantHeterogeneousPlanAdaptation
      (CommonEndpointContext endpoints)
      (ContextSubtyping.underBinder firstSubtyping) commonAlignment
      lowerSubtyping lowerProducer lowerDemand :=
  ContravariantHeterogeneousPlanAdaptation.observationFree
    (ContextSubtyping.underBinder firstSubtyping) commonAlignment
    lowerSubtyping lowerProducer lowerDemand lowerDemand_plan_top

noncomputable def upperAlignment :
    ScopeAlignment leftScope.view rightScope.view :=
  ScopeAlignment.identity CommonView

noncomputable def upperAdaptation :
    HeterogeneousPlanAdaptation (CommonEndpointContext endpoints)
      (ContextSubtyping.underBinder firstSubtyping) upperAlignment
      upperSubtyping upperProducer upperDemand :=
  HeterogeneousPlanAdaptation.observationFree
    (ContextSubtyping.underBinder firstSubtyping) upperAlignment
    upperSubtyping upperProducer upperDemand upperDemand_plan_top

noncomputable def endpointInput : HeterogeneousEndpointInput endpoints
    firstSubtyping lowerSubtyping upperSubtyping nonempty where
  lowerProducerScope := rightScope
  lowerDemandScope := leftScope
  lowerAlignment := commonAlignment
  lowerProducer := lowerProducer
  lowerDemand := lowerDemand
  lowerAdaptation := lowerAdaptation
  lowerProducerPlan_eq := lowerProducerPlan_eq
  lowerDemandPlan_eq := lowerDemandPlan_eq
  upperProducerScope := leftScope
  upperDemandScope := rightScope
  upperAlignment := upperAlignment
  upperProducer := upperProducer
  upperDemand := upperDemand
  upperAdaptation := upperAdaptation
  upperProducerPlan_eq := upperProducerPlan_eq
  upperDemandPlan_eq := upperDemandPlan_eq

noncomputable def member : ContextualEndpointAdaptation endpoints
    firstSubtyping (ContextSubtyping.underBinder firstSubtyping)
    memberSubtyping :=
  ContextualEndpointAdaptation.ofHeterogeneous firstSubtyping
    lowerSubtyping upperSubtyping nonempty endpointInput

def pairSubtyping : Tau.Sub SourceContext
    (.ty SourcePair) (.ty TargetPair) :=
  .pair firstSubtyping memberSubtyping

/- The generic post-rule wrapper seals the already constructed exact
rank-2 pair evidence before any package or positive result is exposed. -/
noncomputable def adaptation : PairFusedAdaptation
    (ScopeAlignment.identity
      GeneralPairIntroductionStaticRegression.bodyScope.view)
    pairSubtyping source demand :=
  PairFusedAdaptation.ofInterval
    (ScopeAlignment.identity
      GeneralPairIntroductionStaticRegression.bodyScope.view)
    firstSubtyping memberSubtyping source demand endpoints first member

/- The dispatcher-facing sum embeds the sealed pair branch without changing
its derivation, source, demand, alignment, or computed adapter. -/
noncomputable def staticAdaptation : StaticAdaptation
    (ScopeAlignment.identity
      GeneralPairIntroductionStaticRegression.bodyScope.view)
    pairSubtyping (.ordinary source) demand :=
  StaticAdaptation.ofPair source adaptation

noncomputable def outerAdapter : StableIdentity.Adapter BaseTargetContext
    source.plan demand.plan :=
  staticAdaptation.adapter

noncomputable def adaptedPackage : CompiledPackage BaseTargetContext
    demand.plan :=
  staticAdaptation.package

/-- The concrete result of the first source subsumption. Its origin is the
exact pair derivation, its positive target model is the locally constructed
`intervalSource` model, and its package is obtained only by applying the
sealed rank-2 bridge adapter. -/
noncomputable def pushed : OrdinaryProducer SourceContext BaseTargetContext
    GeneralPairIntroductionStaticRegression.bodyScope TargetPair :=
  staticAdaptation.toOrdinary targetResult.model.producer

noncomputable def targetTerm_hasType :
    Exp.HasType BaseTargetContext pushed.package.expression
      pushed.plan.inputTy :=
  pushed.package.typing

end
end LambdaPToFCo.Full.GeneralPairObservedIntervalSubtypingRegression
