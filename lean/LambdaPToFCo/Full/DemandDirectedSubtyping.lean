import LambdaPToFCo.Full.FunctionStableAdapter
import LambdaPToFCo.Full.SubtypingCompilerCore

/-!
# Demand-directed full subtyping

Covariant compilation cannot honestly choose a structural target plan for an
arbitrary raw subtyping endpoint.  In particular, independent function push
would have to invent positive and negative evidence for the target domain.

This module therefore retains the exact source derivation and producer until
a sealed target demand fixes the observation plan.  Adaptation then either
composes an exact pull with exact source satisfaction or erases observations
for an opaque demand.  The precise typed dependent-function code bridge still
needed by a structural function demand is exposed separately below.  No
target producer or transitivity-middle carrier is materialized.

All results here are static.  `ProperExecutionEvidence` remains the separate
operational boundary, so an absurd Bottom source is never presented as an
ordinary ready execution.
-/

namespace LambdaPToFCo.Full.DemandDirectedSubtyping

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open SubtypingCompilerCore

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

/-! ## Deferred covariance -/

/-- A covariantly pushed producer with no independently chosen target plan,
model, package, or representation. -/
structure PushedProducer
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    (targetType : LambdaPFC.Ty n) : Type where
  sourceType : LambdaPFC.Ty n
  subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)
  source : ProperProducer sourceContext targetContext sourceScope sourceType

namespace PushedProducer

/-- Covariance only seals the exact pair `(subtyping, source)`. -/
def push
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType))
    (source : ProperProducer sourceContext targetContext sourceScope
      sourceType) :
    PushedProducer alignment targetType where
  sourceType := sourceType
  subtyping := subtyping
  source := source

/-- The source origin and exact derivation already fix target provenance even
though target observations remain demand-directed. -/
def origin
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view targetScope.view}
    {targetType : LambdaPFC.Ty n}
    (pushed : PushedProducer alignment targetType) :
    ProducerOrigin sourceContext targetType :=
  .push pushed.subtyping pushed.source.origin

/-- Function covariance itself requires no target-domain model. -/
def function
    (scope : ScopeModel sourceContext targetContext)
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    (domain : Tau.Sub sourceContext (.ty targetDomain) (.ty sourceDomain))
    (codomain : Tau.Sub (sourceContext.snoc targetDomain)
      (.ty sourceCodomain) (.ty targetCodomain))
    (source : ProperProducer sourceContext targetContext scope
      (.Fun sourceDomain sourceCodomain)) :
    PushedProducer (ScopeAlignment.identity scope.view)
      (.Fun targetDomain targetCodomain) :=
  .push (ScopeAlignment.identity scope.view) (.fun domain codomain) source

end PushedProducer

/-! ## Exact dependent-function bridge -/

/-- The next proof-relevant function-compilation input.  The source equality
exposes an actual positive function model, whose domain remains
bidirectional.  The demand equality exposes a negative function model, whose
target domain is only positive.  The final field is the exact typed wrapper
between their complete dependent code types.

This record does not claim that a non-reflexive wrapper has already been
derived from domain and codomain subtyping. -/
structure FunctionCodeBridge
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain))
    (demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain)) : Type where
  sourceDomainPlan : ValuePlan sig
  sourceCodomainPlan : ValuePlan sourceDomainPlan.scope
  sourceDomainModel : BidirectionalPlanModel sourceContext targetContext
    sourceScope.view sourceDomain sourceDomainPlan
  sourceCodomainModel : ProducerPlanModel
    (sourceContext.snoc sourceDomain)
    (sourceDomainPlan.context targetContext)
    (ScopeView.bindPlan sourceScope.view sourceDomainPlan)
    sourceCodomain sourceCodomainPlan
  sourceModel_eq : source.model =
    ⟨Function.plan sourceDomainPlan sourceCodomainPlan,
      .function sourceDomainModel sourceCodomainModel⟩
  targetDomainPlan : ValuePlan sig
  targetCodomainPlan : ValuePlan targetDomainPlan.scope
  targetDomainModel : ProducerPlanModel sourceContext targetContext
    demandScope.view targetDomain targetDomainPlan
  targetCodomainModel : DemandPlanModel
    (sourceContext.snoc targetDomain)
    (targetDomainPlan.context targetContext)
    (ScopeView.bindPlan demandScope.view targetDomainPlan)
    targetCodomain targetCodomainPlan
  demandModel_eq : demand.model =
    ⟨Function.plan targetDomainPlan targetCodomainPlan,
      .function targetDomainModel targetCodomainModel⟩
  coercion : Co sig
  typing : Co.HasType targetContext coercion
    (Function.codeTy sourceDomainPlan sourceCodomainPlan)
    (Function.codeTy targetDomainPlan targetCodomainPlan)

namespace FunctionCodeBridge

/-- Lift the exact code wrapper to the stable outer function packages. -/
noncomputable def adapter
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain)}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain)}
    (bridge : FunctionCodeBridge source demand) :
    StableIdentity.Adapter targetContext source.plan demand.plan := by
  change StableIdentity.Adapter targetContext source.model.1 demand.model.1
  rw [bridge.sourceModel_eq, bridge.demandModel_eq]
  exact FunctionStableAdapter.adapter targetContext
    bridge.sourceDomainPlan bridge.sourceCodomainPlan
    bridge.targetDomainPlan bridge.targetCodomainPlan
    bridge.coercion bridge.typing

end FunctionCodeBridge

/-! The wrapper is kept in a small exact input record before entering the
general fused-evidence family.  This keeps the public constructor explicit
and seals its cached stable adapter by equality to the typed code bridge. -/

structure FunctionAdaptationInput
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    (domain : Tau.Sub sourceContext (.ty targetDomain) (.ty sourceDomain))
    (codomain : Tau.Sub (sourceContext.snoc targetDomain)
      (.ty sourceCodomain) (.ty targetCodomain))
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain))
    (demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain)) : Type where
  bridge : FunctionCodeBridge source demand
  adapter : StableIdentity.Adapter targetContext source.plan demand.plan
  adapter_eq : adapter = bridge.adapter

/-! ## Sealed fused adaptation -/

/-- Closed construction evidence for a fused static adapter. -/
inductive FusedAdaptationEvidence
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view demandScope.view) :
    {sourceType targetType : LambdaPFC.Ty n} ->
    (subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)) ->
    (source : ProperProducer sourceContext targetContext sourceScope
      sourceType) ->
    (demand : ProperDemand sourceContext targetContext demandScope
      targetType) ->
    StableIdentity.Adapter targetContext source.plan demand.plan -> Type where
  | viaPull
      (pulled : ProperPullResult alignment subtyping demand)
      (satisfaction : ProperSatisfaction
        (ScopeAlignment.identity sourceScope.view) source pulled.source) :
      FusedAdaptationEvidence alignment subtyping source demand
        (satisfaction.adapter.compose pulled.adapter)
  | toOpaque
      (subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType))
      (source : ProperProducer sourceContext targetContext sourceScope
        sourceType)
      (trace : DemandTrace sourceContext targetType) :
      FusedAdaptationEvidence alignment subtyping source
        (opaqueDemand demandScope trace)
        (StableIdentity.Adapter.toTop targetContext source.plan)
  | widenResolved
      {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
      (precise : Path.Ty sourceContext path (.ty referent))
      (translated : ProperPathPackage sourceContext targetContext sourceScope
        precise)
      (trace : DemandTrace sourceContext referent)
      (demandModel : DemandPlanModel sourceContext targetContext
        demandScope.view referent translated.plan) :
      FusedAdaptationEvidence alignment (.widen precise)
        (.ordinary translated.singletonProducer)
        { trace := trace
          model := ⟨translated.plan, demandModel⟩ }
        (StableIdentity.Adapter.identity targetContext translated.plan)
  | reflExact
      (source : OrdinaryProducer sourceContext targetContext sourceScope
        sourceType)
      (trace : DemandTrace sourceContext sourceType)
      (demandModel : DemandPlanModel sourceContext targetContext
        demandScope.view sourceType source.plan) :
      FusedAdaptationEvidence alignment
        (Tau.Sub.refl (τ := .ty sourceType)) (.ordinary source)
        { trace := trace
          model := ⟨source.plan, demandModel⟩ }
        (StableIdentity.Adapter.identity targetContext source.plan)
  | function
      (domain : Tau.Sub sourceContext (.ty targetDomain) (.ty sourceDomain))
      (codomain : Tau.Sub (sourceContext.snoc targetDomain)
        (.ty sourceCodomain) (.ty targetCodomain))
      (source : OrdinaryProducer sourceContext targetContext sourceScope
        (.Fun sourceDomain sourceCodomain))
      (demand : ProperDemand sourceContext targetContext demandScope
        (.Fun targetDomain targetCodomain))
      (input : FunctionAdaptationInput domain codomain source demand) :
      FusedAdaptationEvidence alignment (.fun domain codomain)
        (.ordinary source) demand input.adapter

/-- A producer-to-demand adapter indexed by the exact source derivation.  The
evidence field prevents callers from installing an unrelated adapter. -/
structure FusedAdaptation
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view demandScope.view)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType))
    (source : ProperProducer sourceContext targetContext sourceScope sourceType)
    (demand : ProperDemand sourceContext targetContext demandScope targetType) :
    Type where
  adapter : StableIdentity.Adapter targetContext source.plan demand.plan
  evidence : FusedAdaptationEvidence alignment subtyping source demand adapter

namespace FusedAdaptation

/-- Realize by exact pull, source satisfaction, and adapter composition. -/
noncomputable def ofPull
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view demandScope.view}
    {sourceType targetType : LambdaPFC.Ty n}
    {subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)}
    {source : ProperProducer sourceContext targetContext sourceScope sourceType}
    {demand : ProperDemand sourceContext targetContext demandScope targetType}
    (pulled : ProperPullResult alignment subtyping demand)
    (satisfaction : ProperSatisfaction
      (ScopeAlignment.identity sourceScope.view) source pulled.source) :
    FusedAdaptation alignment subtyping source demand where
  adapter := satisfaction.adapter.compose pulled.adapter
  evidence := .viaPull pulled satisfaction

/-- Erase all observations without inspecting the derivation or constructing
any transitivity middle. -/
noncomputable def toOpaque
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view demandScope.view)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType))
    (source : ProperProducer sourceContext targetContext sourceScope sourceType)
    (trace : DemandTrace sourceContext targetType) :
    FusedAdaptation alignment subtyping source
      (opaqueDemand demandScope trace) where
  adapter := StableIdentity.Adapter.toTop targetContext source.plan
  evidence := .toOpaque subtyping source trace

/-- Fuse the exact singleton package synthesized for a translated path with
a demand for that path's precise referent at the very same resolved plan.

The source is not merely plan-equal to the translated singleton: it is
definitionally `translated.singletonProducer`.  Likewise, the demand model is
indexed directly by `translated.plan`.  This makes the only possible adapter
stable identity and, for a translated selection, preserves the selected
representation already sealed inside `translated` rather than admitting a
new witness choice. -/
noncomputable def widenResolved
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view demandScope.view)
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    (precise : Path.Ty sourceContext path (.ty referent))
    (translated : ProperPathPackage sourceContext targetContext sourceScope
      precise)
    (trace : DemandTrace sourceContext referent)
    (demandModel : DemandPlanModel sourceContext targetContext
      demandScope.view referent translated.plan) :
    FusedAdaptation alignment (.widen precise)
      (.ordinary translated.singletonProducer)
      { trace := trace
        model := ⟨translated.plan, demandModel⟩ } where
  adapter := StableIdentity.Adapter.identity targetContext translated.plan
  evidence := .widenResolved precise translated trace demandModel

/-- Reflexivity at one exact retained ordinary package and one demand indexed
definitionally by that package's plan.  The target adapter is necessarily
stable identity and is computed inside the sealed evidence; callers supply
neither a plan equality nor an adapter. -/
noncomputable def reflExact
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view demandScope.view)
    {sourceType : LambdaPFC.Ty n}
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      sourceType)
    (trace : DemandTrace sourceContext sourceType)
    (demandModel : DemandPlanModel sourceContext targetContext
      demandScope.view sourceType source.plan) :
    FusedAdaptation alignment (Tau.Sub.refl (τ := .ty sourceType))
      (.ordinary source)
      { trace := trace
        model := ⟨source.plan, demandModel⟩ } where
  adapter := StableIdentity.Adapter.identity targetContext source.plan
  evidence := .reflExact source trace demandModel

/-- Consume the exact typed bridge for one structural function rule.  This
does not derive the bridge from the two recursive subtyping premises. -/
noncomputable def ofFunction
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view demandScope.view)
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    (domain : Tau.Sub sourceContext (.ty targetDomain) (.ty sourceDomain))
    (codomain : Tau.Sub (sourceContext.snoc targetDomain)
      (.ty sourceCodomain) (.ty targetCodomain))
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain))
    (demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain))
    (bridge : FunctionCodeBridge source demand) :
    FusedAdaptation alignment (.fun domain codomain) (.ordinary source)
      demand := by
  let input : FunctionAdaptationInput domain codomain source demand :=
    { bridge := bridge
      adapter := bridge.adapter
      adapter_eq := rfl }
  exact
    { adapter := input.adapter
      evidence := .function domain codomain source demand input }

/-- Static package construction is delayed until the target demand has fixed
its exact plan.  This is not operational readiness evidence. -/
noncomputable def package
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view demandScope.view}
    {sourceType targetType : LambdaPFC.Ty n}
    {subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)}
    {source : ProperProducer sourceContext targetContext sourceScope sourceType}
    {demand : ProperDemand sourceContext targetContext demandScope targetType}
    (adaptation : FusedAdaptation alignment subtyping source demand) :
    CompiledPackage targetContext demand.plan :=
  source.package.adapt adaptation.adapter

/-- Re-expose a fused result as an ordinary positive endpoint when the exact
demand plan is also certified positively.  This is the static chaining seam
used after a well-formed subsumption target: the package is still computed by
the sealed adaptation, and the source origin retains the exact subtyping
derivation.  It makes no operational readiness claim (in particular for a
Bottom-derived package). -/
noncomputable def toOrdinary
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view demandScope.view}
    {sourceType targetType : LambdaPFC.Ty n}
    {subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)}
    {source : ProperProducer sourceContext targetContext sourceScope sourceType}
    {demand : ProperDemand sourceContext targetContext demandScope targetType}
    (adaptation : FusedAdaptation alignment subtyping source demand)
    (targetModel : ProducerPlanModel sourceContext targetContext
      demandScope.view targetType demand.plan) :
    OrdinaryProducer sourceContext targetContext demandScope targetType where
  origin := .push subtyping source.origin
  model := ⟨demand.plan, targetModel⟩
  package := adaptation.package

end FusedAdaptation

/-! ## Continuation demand -/

/-- A negative continuation fixes one sealed target demand and accepts any
concrete lower producer with its exact derivation.  Its result remains sealed
by `FusedAdaptationEvidence`, so it cannot choose an unrelated target plan. -/
structure ContinuationDemand
    (demandScope : ScopeModel sourceContext targetContext)
    (targetType : LambdaPFC.Ty n) : Type where
  demand : ProperDemand sourceContext targetContext demandScope targetType
  consume : {sourceScope : ScopeModel sourceContext targetContext} ->
    (alignment : ScopeAlignment sourceScope.view demandScope.view) ->
    {sourceType : LambdaPFC.Ty n} ->
    (subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)) ->
    (source : ProperProducer sourceContext targetContext sourceScope
      sourceType) ->
    FusedAdaptation alignment subtyping source demand

namespace ContinuationDemand

/-- Observation erasure supplies a total continuation for every raw source
endpoint and every full subtyping derivation. -/
noncomputable def observationFree
    (scope : ScopeModel sourceContext targetContext)
    {targetType : LambdaPFC.Ty n}
    (trace : DemandTrace sourceContext targetType) :
    ContinuationDemand scope targetType where
  demand := opaqueDemand scope trace
  consume := fun {_sourceScope} alignment {_sourceType} subtyping source =>
    FusedAdaptation.toOpaque alignment subtyping source trace

end ContinuationDemand

namespace PushedProducer

/-- Realize a deferred producer only when a continuation supplies the exact
sealed demand. -/
noncomputable def realize
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view demandScope.view}
    {targetType : LambdaPFC.Ty n}
    (pushed : PushedProducer alignment targetType)
    (continuation : ContinuationDemand demandScope targetType) :
    FusedAdaptation alignment pushed.subtyping pushed.source
      continuation.demand :=
  continuation.consume alignment pushed.subtyping pushed.source

end PushedProducer

/-! ## Focused regression -/

namespace Regression

/-- The exact counterexample for independent covariance.  The function middle
may be raw and has no producer, demand, Wf proof, or target-domain
bidirectional model.  The composed derivation is consumed directly by the
observation-free continuation. -/
noncomputable def functionThroughTop
    (scope : ScopeModel sourceContext targetContext)
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    (domain : Tau.Sub sourceContext (.ty targetDomain) (.ty sourceDomain))
    (codomain : Tau.Sub (sourceContext.snoc targetDomain)
      (.ty sourceCodomain) (.ty targetCodomain))
    (source : ProperProducer sourceContext targetContext scope
      (.Fun sourceDomain sourceCodomain)) :
    let subtyping : Tau.Sub sourceContext
        (.ty (.Fun sourceDomain sourceCodomain)) (.ty .Top) :=
      .trans (.fun domain codomain) .top
    let pushed : PushedProducer (ScopeAlignment.identity scope.view) .Top :=
      .push (ScopeAlignment.identity scope.view) subtyping source
    let continuation : ContinuationDemand scope .Top :=
      .observationFree scope (.root (.opaque .Top))
    FusedAdaptation (ScopeAlignment.identity scope.view) pushed.subtyping
      pushed.source continuation.demand := by
  dsimp only
  exact PushedProducer.realize
    (.push (ScopeAlignment.identity scope.view)
      (.trans (.fun domain codomain) .top) source)
    (.observationFree scope (.root (.opaque .Top)))

end Regression

end LambdaPToFCo.Full.DemandDirectedSubtyping
