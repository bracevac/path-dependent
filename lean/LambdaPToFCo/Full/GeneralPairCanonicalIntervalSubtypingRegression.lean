import LambdaPToFCo.Full.GeneralPairObservedIntervalSubtypingRegression

/-!
# Canonical endpoint hiding for the GeneralPair body

This leaf performs the second source subsumption in
`LambdaPFC.GeneralPairRegression`. It consumes the exact ordinary
`intervalSource.weaken` producer from the observed-endpoint regression and
adapts it to `intervalTarget.weaken` along
`.pair .refl (.bounds .bot .top .refl)`.

The target pair demand is built structurally from local Bottom and Top plans.
Its rank-2 endpoint bridge uses the sealed canonical branch: Bottom supplies
only a static `fromBottom` adapter and Top supplies observation erasure. No
Bottom readiness, global path resolver, raw adapter, or package callback is
introduced. The output is the exact pushed ordinary producer and its concrete
target typing; closing the surrounding source `let` remains a separate step.
-/

namespace LambdaPToFCo.Full.GeneralPairCanonicalIntervalSubtypingRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open DemandDirectedSubtyping
open SubtypingCompilerCore
open IntervalPairSubtypingRuleConstruction
open DemandDirectedPairSubtyping

noncomputable section

abbrev SourceContext :=
  GeneralPairObservedIntervalSubtypingRegression.SourceContext

abbrev BaseTargetContext :=
  GeneralPairObservedIntervalSubtypingRegression.BaseTargetContext

abbrev First : LambdaPFC.Ty 1 := .Top
abbrev SourceLower : LambdaPFC.Ty 2 := .Single (.var 0)
abbrev SourceUpper : LambdaPFC.Ty 2 := .Single (.var 0)
abbrev TargetLower : LambdaPFC.Ty 2 := .Bot
abbrev TargetUpper : LambdaPFC.Ty 2 := .Top

abbrev SourcePair : LambdaPFC.Ty 1 :=
  .Pair First LambdaPFC.GeneralPairRegression.label
    (.intv SourceLower SourceUpper)

abbrev TargetPair : LambdaPFC.Ty 1 :=
  .Pair First LambdaPFC.GeneralPairRegression.label
    (.intv TargetLower TargetUpper)

theorem sourcePair_eq : SourcePair =
    LambdaPFC.GeneralPairRegression.intervalSource.weaken := by
  rfl

theorem targetPair_eq : TargetPair =
    LambdaPFC.GeneralPairRegression.intervalTarget.weaken := by
  rfl

noncomputable def source : OrdinaryProducer SourceContext BaseTargetContext
    GeneralPairIntroductionStaticRegression.bodyScope SourcePair :=
  GeneralPairObservedIntervalSubtypingRegression.pushed

def firstSubtyping : Tau.Sub SourceContext (.ty First) (.ty First) :=
  .refl

def lowerSubtyping : Tau.Sub (SourceContext.snoc First)
    (.ty TargetLower) (.ty SourceLower) :=
  .bot

def upperSubtyping : Tau.Sub (SourceContext.snoc First)
    (.ty SourceUpper) (.ty TargetUpper) :=
  .top

def nonempty : Tau.Sub (SourceContext.snoc First)
    (.ty SourceLower) (.ty SourceUpper) :=
  .refl

def memberSubtyping : Tau.Sub (SourceContext.snoc First)
    (.intv SourceLower SourceUpper) (.intv TargetLower TargetUpper) :=
  .bounds lowerSubtyping upperSubtyping nonempty

def pairSubtyping : Tau.Sub SourceContext (.ty SourcePair) (.ty TargetPair) :=
  .pair firstSubtyping memberSubtyping

noncomputable def targetFirstResult : WfPlan.Proper SourceContext
    BaseTargetContext GeneralPairIntroductionStaticRegression.bodyScope First :=
  WfPlan.Proper.top GeneralPairIntroductionStaticRegression.bodyScope

noncomputable def targetBoundScope : ScopeModel (SourceContext.snoc First)
    (targetFirstResult.plan.context BaseTargetContext) :=
  GeneralPairIntroductionStaticRegression.bodyScope.bindBidirectional
    targetFirstResult.model

noncomputable def targetLowerResult : WfPlan.Proper
    (SourceContext.snoc First)
    (targetFirstResult.plan.context BaseTargetContext)
    targetBoundScope TargetLower :=
  WfPlan.Proper.bottom targetBoundScope

noncomputable def targetUpperResult : WfPlan.Proper
    (SourceContext.snoc First)
    (targetFirstResult.plan.context BaseTargetContext)
    targetBoundScope TargetUpper :=
  WfPlan.Proper.top targetBoundScope

noncomputable def targetMemberResult : WfPlan.Interval
    (SourceContext.snoc First)
    (targetFirstResult.plan.context BaseTargetContext)
    targetBoundScope TargetLower TargetUpper :=
  WfPlan.Interval.bounds targetBoundScope targetLowerResult targetUpperResult
    .bot

noncomputable def targetResult : WfPlan.Proper SourceContext
    BaseTargetContext GeneralPairIntroductionStaticRegression.bodyScope
    TargetPair :=
  WfPlan.Proper.intervalPair GeneralPairIntroductionStaticRegression.bodyScope
    targetFirstResult targetMemberResult

noncomputable def demand := targetResult.demand

noncomputable def endpoints : EndpointModels source demand where
  sourceFirstPlan :=
    GeneralPairObservedIntervalSubtypingRegression.targetFirstResult.plan
  sourceLowerPlan :=
    GeneralPairObservedIntervalSubtypingRegression.targetEndpointResult.plan
  sourceUpperPlan :=
    GeneralPairObservedIntervalSubtypingRegression.targetEndpointResult.plan
  sourceFirstModel :=
    GeneralPairObservedIntervalSubtypingRegression.targetFirstResult.model.producer
  sourceMemberModel :=
    GeneralPairObservedIntervalSubtypingRegression.targetMemberResult.model.producer
  sourceModel_eq := rfl
  targetFirstPlan := targetFirstResult.plan
  targetLowerPlan := targetLowerResult.plan
  targetUpperPlan := targetUpperResult.plan
  targetFirstModel := targetFirstResult.model
  targetMemberModel := targetMemberResult.model
  demandModel_eq := rfl

def sourceFirstPrecise : Path.Ty SourceContext (.var 0) (.ty First) :=
  .var

noncomputable def sourceFirstProducer : OrdinaryProducer SourceContext
    BaseTargetContext GeneralPairIntroductionStaticRegression.bodyScope First :=
  (GeneralPairIntroductionStaticRegression.bodyScope.variablePath
    (0 : Fin 1)).preciseProducer

noncomputable def first : FirstAdaptation endpoints firstSubtyping where
  producerScope := GeneralPairIntroductionStaticRegression.bodyScope
  consumerScope := GeneralPairIntroductionStaticRegression.bodyScope
  alignment := ScopeAlignment.identity
    GeneralPairIntroductionStaticRegression.bodyScope.view
  producer := .ordinary sourceFirstProducer
  consumer := targetFirstResult.demand
  adaptation := FusedAdaptation.toOpaque
    (ScopeAlignment.identity
      GeneralPairIntroductionStaticRegression.bodyScope.view)
    firstSubtyping (.ordinary sourceFirstProducer)
    (DemandTrace.ofWf targetFirstResult.wf)
  producerPlan_eq := rfl
  consumerPlan_eq := rfl

noncomputable def member : ContextualEndpointAdaptation endpoints
    firstSubtyping (ContextSubtyping.underBinder firstSubtyping)
    memberSubtyping :=
  ContextualEndpointAdaptation.canonical firstSubtyping memberSubtyping rfl rfl

/- Generic pair-rule sealing begins only after the exact canonical contextual
endpoint evidence above has been constructed. -/
noncomputable def adaptation : PairFusedAdaptation
    (ScopeAlignment.identity
      GeneralPairIntroductionStaticRegression.bodyScope.view)
    pairSubtyping source demand :=
  PairFusedAdaptation.ofInterval
    (ScopeAlignment.identity
      GeneralPairIntroductionStaticRegression.bodyScope.view)
    firstSubtyping memberSubtyping source demand endpoints first member

noncomputable def outerAdapter : StableIdentity.Adapter BaseTargetContext
    source.plan demand.plan :=
  adaptation.adapter

noncomputable def adaptedPackage : CompiledPackage BaseTargetContext
    demand.plan :=
  adaptation.package

noncomputable def pushed : OrdinaryProducer SourceContext BaseTargetContext
    GeneralPairIntroductionStaticRegression.bodyScope TargetPair :=
  adaptation.toOrdinary targetResult.model.producer

noncomputable def targetTerm_hasType :
    Exp.HasType BaseTargetContext pushed.package.expression
      pushed.plan.inputTy :=
  pushed.package.typing

end
end LambdaPToFCo.Full.GeneralPairCanonicalIntervalSubtypingRegression
