import LambdaPToFCo.Full.HeterogeneousAdaptation
import LambdaPToFCo.Full.FunctionCodeBridgeConstruction

/-!
# Closed observation-free function subtyping

This leaf assembles one exact `Tau.Sub.fun` adaptation without transporting a
codomain model between its two binder contexts. The contravariant domain is
an ordinary sealed `FusedAdaptation`. The codomain seam is dual: its subtyping
derivation and target demand live under `Gamma.snoc targetDomain`, while the
retained source codomain producer model lives under
`Gamma.snoc sourceDomain`.

The contextual result family is indexed by the exact
`ContextSubtyping.underBinder domainSubtyping` proof. Its only constructor
forces the target codomain plan to canonical `Top.plan` and constructs the
common-context result adapter internally with `StableIdentity.Adapter.toTop`.
No result adapter, code coercion, or model transport is accepted as input.
-/

namespace LambdaPToFCo.Full.FunctionSubtypingRuleConstruction

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open DemandDirectedSubtyping

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

/-- Public exact endpoint shape used by the function rule leaf. -/
abbrev EndpointModels
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain))
    (demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain)) :=
  FunctionCodeBridgeConstruction.EndpointModels source demand

/-- The contravariant domain seam is a recursive fused adaptation indexed by
the exact first premise. Plan equalities tie its adapter to the enclosing
function endpoint models. -/
structure DomainAdaptation
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain)}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain)}
    (endpoints : EndpointModels source demand)
    (subtyping : Tau.Sub sourceContext (.ty targetDomain)
      (.ty sourceDomain)) : Type where
  producerScope : ScopeModel sourceContext targetContext
  consumerScope : ScopeModel sourceContext targetContext
  alignment : ScopeAlignment producerScope.view consumerScope.view
  producer : ProperProducer sourceContext targetContext producerScope
    targetDomain
  consumer : ProperDemand sourceContext targetContext consumerScope
    sourceDomain
  adaptation : FusedAdaptation alignment subtyping producer consumer
  producerPlan_eq : producer.plan = endpoints.targetDomainPlan
  consumerPlan_eq : consumer.plan = endpoints.sourceDomainPlan

namespace DomainAdaptation

/-- Project the exact target-domain-to-source-domain stable adapter fixed by
the enclosing function plans. -/
noncomputable def adapter
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain)}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain)}
    {endpoints : EndpointModels source demand}
    {subtyping : Tau.Sub sourceContext (.ty targetDomain)
      (.ty sourceDomain)}
    (domain : DomainAdaptation endpoints subtyping) :
    StableIdentity.Adapter targetContext endpoints.targetDomainPlan
      endpoints.sourceDomainPlan := by
  rw [← domain.producerPlan_eq, ← domain.consumerPlan_eq]
  exact domain.adaptation.adapter

end DomainAdaptation

/-- Context relation for the codomain premise. The source codomain model is
under the right context; the target demand and the derivation are under the
left context. -/
abbrev CodomainContexts
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    (domainSubtyping : Tau.Sub sourceContext (.ty targetDomain)
      (.ty sourceDomain)) :
    ContextSubtyping (sourceContext.snoc targetDomain)
      (sourceContext.snoc sourceDomain) :=
  ContextSubtyping.underBinder domainSubtyping

/-- Reindexing canonical `Top.plan` into the common result context remains
canonical `Top.plan`. -/
theorem targetResultPlan_top
    (sourceDomain targetDomain : ValuePlan sig) :
    FunctionCodeBridgeConstruction.targetResultPlan sourceDomain targetDomain
        (Top.plan targetDomain.scope) =
      Top.plan
        (FunctionCodeBridgeConstruction.sourceDomainCommon sourceDomain
          targetDomain).scope := by
  rfl

private noncomputable def observationFreeResultAdapter
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain)}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain)}
    (endpoints : EndpointModels source demand)
    (targetPlan_eq : endpoints.targetCodomainPlan =
      Top.plan endpoints.targetDomainPlan.scope) :
    FunctionCodeBridgeConstruction.ResultAdapter targetContext
      endpoints.sourceDomainPlan endpoints.sourceCodomainPlan
      endpoints.targetDomainPlan endpoints.targetCodomainPlan where
  adapter := by
    rw [targetPlan_eq, targetResultPlan_top]
    exact StableIdentity.Adapter.toTop
      ((FunctionCodeBridgeConstruction.sourceDomainCommon
        endpoints.sourceDomainPlan endpoints.targetDomainPlan).context
        (FunctionCodeBridgeConstruction.commonContext targetContext
          endpoints.sourceDomainPlan endpoints.sourceCodomainPlan
          endpoints.targetDomainPlan))
      (FunctionCodeBridgeConstruction.sourceResultPlan targetContext
        endpoints.sourceDomainPlan endpoints.sourceCodomainPlan
        endpoints.targetDomainPlan)

/-- Closed evidence for the contextual codomain result adapter. The context
index can be constructed only from the exact contravariant domain premise. -/
inductive ContextualResultAdaptationEvidence
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain)}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain)}
    (endpoints : EndpointModels source demand)
    (domainSubtyping : Tau.Sub sourceContext (.ty targetDomain)
      (.ty sourceDomain))
    (codomainSubtyping : Tau.Sub (sourceContext.snoc targetDomain)
      (.ty sourceCodomain) (.ty targetCodomain)) :
    ContextSubtyping (sourceContext.snoc targetDomain)
        (sourceContext.snoc sourceDomain) ->
    FunctionCodeBridgeConstruction.ResultAdapter targetContext
      endpoints.sourceDomainPlan endpoints.sourceCodomainPlan
      endpoints.targetDomainPlan endpoints.targetCodomainPlan -> Type where
  | observationFree
      (targetPlan_eq : endpoints.targetCodomainPlan =
        Top.plan endpoints.targetDomainPlan.scope) :
      ContextualResultAdaptationEvidence endpoints domainSubtyping codomainSubtyping
        (ContextSubtyping.underBinder domainSubtyping)
        (observationFreeResultAdapter endpoints targetPlan_eq)

/-- The sealed result-adapter output. Its adapter is accepted only when the
evidence family fixes it to the observation-free construction above. -/
structure ContextualResultAdaptation
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain)}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain)}
    (endpoints : EndpointModels source demand)
    (domainSubtyping : Tau.Sub sourceContext (.ty targetDomain)
      (.ty sourceDomain))
    (contexts : ContextSubtyping (sourceContext.snoc targetDomain)
      (sourceContext.snoc sourceDomain))
    (codomainSubtyping : Tau.Sub (sourceContext.snoc targetDomain)
      (.ty sourceCodomain) (.ty targetCodomain)) : Type where
  resultAdapter : FunctionCodeBridgeConstruction.ResultAdapter targetContext
    endpoints.sourceDomainPlan endpoints.sourceCodomainPlan
    endpoints.targetDomainPlan endpoints.targetCodomainPlan
  evidence : ContextualResultAdaptationEvidence endpoints domainSubtyping
    codomainSubtyping contexts resultAdapter

namespace ContextualResultAdaptation

/-- Construct the sole initial contextual result: exact observation erasure
at the target codomain plan. -/
noncomputable def observationFree
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain)}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain)}
    {endpoints : EndpointModels source demand}
    (domainSubtyping : Tau.Sub sourceContext (.ty targetDomain)
      (.ty sourceDomain))
    (codomainSubtyping : Tau.Sub (sourceContext.snoc targetDomain)
      (.ty sourceCodomain) (.ty targetCodomain))
    (targetPlan_eq : endpoints.targetCodomainPlan =
      Top.plan endpoints.targetDomainPlan.scope) :
    ContextualResultAdaptation endpoints domainSubtyping
      (ContextSubtyping.underBinder domainSubtyping) codomainSubtyping where
  resultAdapter := observationFreeResultAdapter endpoints targetPlan_eq
  evidence := .observationFree targetPlan_eq

end ContextualResultAdaptation

/-- Assemble the exact typed code bridge from the sealed domain and codomain
adaptations. -/
noncomputable def bridge
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain)}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain)}
    {domainSubtyping : Tau.Sub sourceContext (.ty targetDomain)
      (.ty sourceDomain)}
    {codomainSubtyping : Tau.Sub (sourceContext.snoc targetDomain)
      (.ty sourceCodomain) (.ty targetCodomain)}
    (endpoints : EndpointModels source demand)
    (domain : DomainAdaptation endpoints domainSubtyping)
    (result : ContextualResultAdaptation endpoints domainSubtyping
      (ContextSubtyping.underBinder domainSubtyping) codomainSubtyping) :
    FunctionCodeBridge source demand :=
  FunctionCodeBridgeConstruction.bridge endpoints domain.adapter
    result.resultAdapter

/-- The exact input cached by the sealed `.function` evidence constructor.
Its adapter is definitionally the adapter derived from the typed code bridge. -/
noncomputable def input
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain)}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain)}
    {domainSubtyping : Tau.Sub sourceContext (.ty targetDomain)
      (.ty sourceDomain)}
    {codomainSubtyping : Tau.Sub (sourceContext.snoc targetDomain)
      (.ty sourceCodomain) (.ty targetCodomain)}
    (endpoints : EndpointModels source demand)
    (domain : DomainAdaptation endpoints domainSubtyping)
    (result : ContextualResultAdaptation endpoints domainSubtyping
      (ContextSubtyping.underBinder domainSubtyping) codomainSubtyping) :
    FunctionAdaptationInput domainSubtyping codomainSubtyping source demand :=
  let exactBridge := bridge endpoints domain result
  { bridge := exactBridge
    adapter := exactBridge.adapter
    adapter_eq := rfl }

/-- Compile the exact source `Tau.Sub.fun` rule into sealed fused adaptation
evidence. No code coercion or stable adapter is accepted by this constructor. -/
noncomputable def adaptation
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view demandScope.view)
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    (domainSubtyping : Tau.Sub sourceContext (.ty targetDomain)
      (.ty sourceDomain))
    (codomainSubtyping : Tau.Sub (sourceContext.snoc targetDomain)
      (.ty sourceCodomain) (.ty targetCodomain))
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain))
    (demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain))
    (endpoints : EndpointModels source demand)
    (domain : DomainAdaptation endpoints domainSubtyping)
    (result : ContextualResultAdaptation endpoints domainSubtyping
      (ContextSubtyping.underBinder domainSubtyping) codomainSubtyping) :
    FusedAdaptation alignment (.fun domainSubtyping codomainSubtyping)
      (.ordinary source) demand := by
  let exactInput := input endpoints domain result
  exact
    { adapter := exactInput.adapter
      evidence := .function domainSubtyping codomainSubtyping source demand
        exactInput }

end LambdaPToFCo.Full.FunctionSubtypingRuleConstruction
