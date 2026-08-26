import LambdaPToFCo.Full.DemandDirectedPairSubtyping

/-!
# Unified sealed static adaptations

The core demand-directed compiler and the structural pair-rule compiler live
on opposite sides of an intentional import boundary.  This leaf provides the
closed sum a future generic subtyping dispatcher can return without moving
either implementation or introducing a dependency cycle.

Each branch retains the exact scope alignment, subtyping derivation, source,
and target demand.  The cached adapter can only come from an already sealed
`FusedAdaptation` or `PairFusedAdaptation`; there is no raw-adapter constructor
or callback.  Package construction and positive re-exposure are static only
and make no operational-readiness claim.
-/

namespace LambdaPToFCo.Full

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open DemandDirectedSubtyping
open DemandDirectedPairSubtyping

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

/-- Closed provenance for one unified static adaptation.  The pair branch is
necessarily indexed by an ordinary source because structural pair evidence
retains the exact source pair model and package. -/
inductive StaticAdaptationEvidence
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view demandScope.view) :
    {sourceType targetType : LambdaPFC.Ty n} ->
    (subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)) ->
    (source : ProperProducer sourceContext targetContext sourceScope
      sourceType) ->
    (demand : ProperDemand sourceContext targetContext demandScope
      targetType) ->
    StableIdentity.Adapter targetContext source.plan demand.plan -> Type where
  | core
      {sourceType targetType : LambdaPFC.Ty n}
      {subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)}
      {source : ProperProducer sourceContext targetContext sourceScope
        sourceType}
      {demand : ProperDemand sourceContext targetContext demandScope
        targetType}
      (adaptation : FusedAdaptation alignment subtyping source demand) :
      StaticAdaptationEvidence alignment subtyping source demand
        adaptation.adapter
  | pair
      {sourceType targetType : LambdaPFC.Ty n}
      {subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)}
      (source : OrdinaryProducer sourceContext targetContext sourceScope
        sourceType)
      {demand : ProperDemand sourceContext targetContext demandScope
        targetType}
      (adaptation : PairFusedAdaptation alignment subtyping source demand) :
      StaticAdaptationEvidence alignment subtyping (.ordinary source) demand
        adaptation.adapter

/-- The common dispatcher-facing result for every presently sealed static
subtyping branch. -/
structure StaticAdaptation
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view demandScope.view)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType))
    (source : ProperProducer sourceContext targetContext sourceScope sourceType)
    (demand : ProperDemand sourceContext targetContext demandScope targetType) :
    Type where
  adapter : StableIdentity.Adapter targetContext source.plan demand.plan
  evidence : StaticAdaptationEvidence alignment subtyping source demand adapter

namespace StaticAdaptation

/-- Embed an existing core fused result without changing any index. -/
noncomputable def ofCore
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view demandScope.view}
    {sourceType targetType : LambdaPFC.Ty n}
    {subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)}
    {source : ProperProducer sourceContext targetContext sourceScope sourceType}
    {demand : ProperDemand sourceContext targetContext demandScope targetType}
    (adaptation : FusedAdaptation alignment subtyping source demand) :
    StaticAdaptation alignment subtyping source demand where
  adapter := adaptation.adapter
  evidence := .core adaptation

/-- Embed an already sealed structural pair rule. -/
noncomputable def ofPair
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view demandScope.view}
    {sourceType targetType : LambdaPFC.Ty n}
    {subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)}
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      sourceType)
    {demand : ProperDemand sourceContext targetContext demandScope targetType}
    (adaptation : PairFusedAdaptation alignment subtyping source demand) :
    StaticAdaptation alignment subtyping (.ordinary source) demand where
  adapter := adaptation.adapter
  evidence := .pair source adaptation

/-- Apply the adapter selected by either sealed branch. -/
noncomputable def package
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view demandScope.view}
    {sourceType targetType : LambdaPFC.Ty n}
    {subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)}
    {source : ProperProducer sourceContext targetContext sourceScope sourceType}
    {demand : ProperDemand sourceContext targetContext demandScope targetType}
    (adaptation : StaticAdaptation alignment subtyping source demand) :
    CompiledPackage targetContext demand.plan :=
  source.package.adapt adaptation.adapter

/-- Re-expose either sealed branch positively at the exact demanded plan.
This is static package evidence only, including when the core source is
absurd. -/
noncomputable def toOrdinary
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view demandScope.view}
    {sourceType targetType : LambdaPFC.Ty n}
    {subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)}
    {source : ProperProducer sourceContext targetContext sourceScope sourceType}
    {demand : ProperDemand sourceContext targetContext demandScope targetType}
    (adaptation : StaticAdaptation alignment subtyping source demand)
    (targetModel : ProducerPlanModel sourceContext targetContext
      demandScope.view targetType demand.plan) :
    OrdinaryProducer sourceContext targetContext demandScope targetType where
  origin := .push subtyping source.origin
  model := ⟨demand.plan, targetModel⟩
  package := adaptation.package

/-! ## Core-branch regression -/

namespace Regression

/-- A core Top/opaque adaptation embeds without changing its proof-relevant
indices. -/
noncomputable def coreTop
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (source : ProperProducer sourceContext targetContext scope sourceType) :
    StaticAdaptation (ScopeAlignment.identity scope.view)
      (.top : Tau.Sub sourceContext (.ty sourceType) (.ty .Top)) source
      (SubtypingCompilerCore.opaqueDemand scope (.root (.opaque .Top))) :=
  StaticAdaptation.ofCore
    (FusedAdaptation.toOpaque (ScopeAlignment.identity scope.view) .top source
      (.root (.opaque .Top)))

/-- The unified result exposes the same package eliminator for a core branch. -/
noncomputable def coreTopPackage
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (source : ProperProducer sourceContext targetContext scope sourceType) :
    CompiledPackage targetContext
      (SubtypingCompilerCore.opaqueDemand scope
        (.root (.opaque .Top))).plan :=
  (coreTop scope source).package

/-- Positive re-exposure is also uniform when the opaque Top plan is
certified structurally. -/
noncomputable def coreTopOrdinary
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (source : ProperProducer sourceContext targetContext scope sourceType) :
    OrdinaryProducer sourceContext targetContext scope .Top :=
  (coreTop scope source).toOrdinary ProducerPlanModel.top

end Regression

end StaticAdaptation

end LambdaPToFCo.Full
