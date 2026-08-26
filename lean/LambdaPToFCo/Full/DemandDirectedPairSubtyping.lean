import LambdaPToFCo.Full.PairSubtypingRuleConstruction
import LambdaPToFCo.Full.IntervalPairSubtypingRuleConstruction

/-!
# Demand-directed pair-rule adaptations

The proper-pair and interval-pair representation bridges are defined above
the core demand-directed layer: their first and dependent-member inputs
recursively contain `FusedAdaptation` and `HeterogeneousAdaptation`. Importing
those rule modules back into `DemandDirectedSubtyping` would therefore create
a module cycle.

This post-rule layer provides the corresponding sealed fused result. Each
branch consumes the exact existing endpoint, first, and contextual-member
evidence. Its cached stable adapter is propositionally fixed to the adapter
computed by the relevant representation bridge, exactly as the function
branch's `FunctionAdaptationInput` fixes its cache to `FunctionCodeBridge`.
No constructor accepts a raw adapter, adapter callback, target package, or
operational-readiness claim.

Constructing the contextual evidence remains deliberately separate. This
module only packages an already sealed structural `.pair` rule and exposes
uniform package and positive-result eliminators.
-/

namespace LambdaPToFCo.Full.DemandDirectedPairSubtyping

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

/-! ## Exact rule inputs -/

/-- Exact proper-pair rule input, including the only adapter it may cache. -/
structure ProperAdaptationInput
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceMember targetMember : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    (firstSubtyping : Tau.Sub sourceContext
      (.ty sourceFirst) (.ty targetFirst))
    (memberSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
      (.ty sourceMember) (.ty targetMember))
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.ty sourceMember)))
    (demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.ty targetMember))) : Type where
  endpoints : PairSubtypingRuleConstruction.EndpointModels source demand
  first : PairSubtypingRuleConstruction.FirstAdaptation endpoints
    firstSubtyping
  member : PairSubtypingRuleConstruction.ContextualMemberAdaptation endpoints
    firstSubtyping memberSubtyping
  adapter : StableIdentity.Adapter targetContext source.plan demand.plan
  adapter_eq : adapter = PairSubtypingRuleConstruction.adapter
    firstSubtyping memberSubtyping endpoints first member

/-- Exact interval-pair rule input, retaining its rank-2 contextual endpoint
evidence without exposing the hidden witness. -/
structure IntervalAdaptationInput
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceLower sourceUpper targetLower targetUpper :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    (firstSubtyping : Tau.Sub sourceContext
      (.ty sourceFirst) (.ty targetFirst))
    (memberSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
      (.intv sourceLower sourceUpper) (.intv targetLower targetUpper))
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.intv sourceLower sourceUpper)))
    (demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.intv targetLower targetUpper))) : Type where
  endpoints : IntervalPairSubtypingRuleConstruction.EndpointModels source
    demand
  first : IntervalPairSubtypingRuleConstruction.FirstAdaptation endpoints
    firstSubtyping
  member : IntervalPairSubtypingRuleConstruction.ContextualEndpointAdaptation
    endpoints firstSubtyping
      (ContextSubtyping.underBinder firstSubtyping) memberSubtyping
  adapter : StableIdentity.Adapter targetContext source.plan demand.plan
  adapter_eq : adapter = IntervalPairSubtypingRuleConstruction.adapter
    firstSubtyping memberSubtyping endpoints first member

/-! ## Sealed pair-fused result -/

/-- Closed evidence for a demand-directed structural pair adapter. The outer
scope alignment remains proof-relevant even though the target-only
representation bridges compute independently of it. -/
inductive PairFusedAdaptationEvidence
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view demandScope.view) :
    {sourceType targetType : LambdaPFC.Ty n} ->
    (subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)) ->
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      sourceType) ->
    (demand : ProperDemand sourceContext targetContext demandScope
      targetType) ->
    StableIdentity.Adapter targetContext source.plan demand.plan -> Type where
  | proper
      (firstSubtyping : Tau.Sub sourceContext
        (.ty sourceFirst) (.ty targetFirst))
      (memberSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
        (.ty sourceMember) (.ty targetMember))
      (source : OrdinaryProducer sourceContext targetContext sourceScope
        (.Pair sourceFirst label (.ty sourceMember)))
      (demand : ProperDemand sourceContext targetContext demandScope
        (.Pair targetFirst label (.ty targetMember)))
      (input : ProperAdaptationInput firstSubtyping memberSubtyping source
        demand) :
      PairFusedAdaptationEvidence alignment
        (.pair firstSubtyping memberSubtyping) source demand input.adapter
  | interval
      (firstSubtyping : Tau.Sub sourceContext
        (.ty sourceFirst) (.ty targetFirst))
      (memberSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
        (.intv sourceLower sourceUpper) (.intv targetLower targetUpper))
      (source : OrdinaryProducer sourceContext targetContext sourceScope
        (.Pair sourceFirst label (.intv sourceLower sourceUpper)))
      (demand : ProperDemand sourceContext targetContext demandScope
        (.Pair targetFirst label (.intv targetLower targetUpper)))
      (input : IntervalAdaptationInput firstSubtyping memberSubtyping source
        demand) :
      PairFusedAdaptationEvidence alignment
        (.pair firstSubtyping memberSubtyping) source demand input.adapter

/-- Reusable demand-directed result for either structural source pair rule.
It intentionally starts after contextual first/member evidence has been
constructed. -/
structure PairFusedAdaptation
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view demandScope.view)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType))
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      sourceType)
    (demand : ProperDemand sourceContext targetContext demandScope
      targetType) : Type where
  adapter : StableIdentity.Adapter targetContext source.plan demand.plan
  evidence : PairFusedAdaptationEvidence alignment subtyping source demand
    adapter

namespace PairFusedAdaptation

/-- Seal one exact proper-pair rule. -/
noncomputable def ofProper
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view demandScope.view)
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceMember targetMember : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    (firstSubtyping : Tau.Sub sourceContext
      (.ty sourceFirst) (.ty targetFirst))
    (memberSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
      (.ty sourceMember) (.ty targetMember))
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.ty sourceMember)))
    (demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.ty targetMember)))
    (endpoints : PairSubtypingRuleConstruction.EndpointModels source demand)
    (first : PairSubtypingRuleConstruction.FirstAdaptation endpoints
      firstSubtyping)
    (member : PairSubtypingRuleConstruction.ContextualMemberAdaptation
      endpoints firstSubtyping memberSubtyping) :
    PairFusedAdaptation alignment (.pair firstSubtyping memberSubtyping)
      source demand := by
  let input : ProperAdaptationInput firstSubtyping memberSubtyping source
      demand :=
    { endpoints := endpoints
      first := first
      member := member
      adapter := PairSubtypingRuleConstruction.adapter firstSubtyping
        memberSubtyping endpoints first member
      adapter_eq := rfl }
  exact
    { adapter := input.adapter
      evidence := .proper firstSubtyping memberSubtyping source demand input }

/-- Seal one exact interval-pair rule. The contextual endpoint evidence keeps
the bridge's hidden witness rank-2. -/
noncomputable def ofInterval
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view demandScope.view)
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceLower sourceUpper targetLower targetUpper :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    (firstSubtyping : Tau.Sub sourceContext
      (.ty sourceFirst) (.ty targetFirst))
    (memberSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
      (.intv sourceLower sourceUpper) (.intv targetLower targetUpper))
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.intv sourceLower sourceUpper)))
    (demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.intv targetLower targetUpper)))
    (endpoints : IntervalPairSubtypingRuleConstruction.EndpointModels source
      demand)
    (first : IntervalPairSubtypingRuleConstruction.FirstAdaptation endpoints
      firstSubtyping)
    (member : IntervalPairSubtypingRuleConstruction.ContextualEndpointAdaptation
      endpoints firstSubtyping (ContextSubtyping.underBinder firstSubtyping)
        memberSubtyping) :
    PairFusedAdaptation alignment (.pair firstSubtyping memberSubtyping)
      source demand := by
  let input : IntervalAdaptationInput firstSubtyping memberSubtyping source
      demand :=
    { endpoints := endpoints
      first := first
      member := member
      adapter := IntervalPairSubtypingRuleConstruction.adapter firstSubtyping
        memberSubtyping endpoints first member
      adapter_eq := rfl }
  exact
    { adapter := input.adapter
      evidence := .interval firstSubtyping memberSubtyping source demand input }

/-- Apply the adapter fixed by the sealed structural rule input. -/
noncomputable def package
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view demandScope.view}
    {sourceType targetType : LambdaPFC.Ty n}
    {subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      sourceType}
    {demand : ProperDemand sourceContext targetContext demandScope targetType}
    (adaptation : PairFusedAdaptation alignment subtyping source demand) :
    CompiledPackage targetContext demand.plan :=
  source.package.adapt adaptation.adapter

/-- Re-expose a sealed pair-rule result positively when the exact target
demand plan is also certified by a positive structural model. -/
noncomputable def toOrdinary
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view demandScope.view}
    {sourceType targetType : LambdaPFC.Ty n}
    {subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      sourceType}
    {demand : ProperDemand sourceContext targetContext demandScope targetType}
    (adaptation : PairFusedAdaptation alignment subtyping source demand)
    (targetModel : ProducerPlanModel sourceContext targetContext
      demandScope.view targetType demand.plan) :
    OrdinaryProducer sourceContext targetContext demandScope targetType where
  origin := .push subtyping source.origin
  model := ⟨demand.plan, targetModel⟩
  package := adaptation.package

end PairFusedAdaptation

end LambdaPToFCo.Full.DemandDirectedPairSubtyping
