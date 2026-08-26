import LambdaPToFCo.Full.HeterogeneousAdaptation
import LambdaPToFCo.Full.HeterogeneousPlanAdaptation
import LambdaPToFCo.Full.IntervalPairRepresentationBridgeConstruction

/-!
# Sealed interval-pair subtyping endpoints

The target representation bridge requests its endpoint adapters only inside
the context where the source interval representation and adapted first
package have been opened.  This source leaf retains that scoped boundary and
constructs the canonical observation-free endpoint adapters without naming
or exporting the hidden witness representation.

The canonical lower adapter uses `StableIdentity.Adapter.fromBottom` only as
static representation evidence. This leaf constructs a
`StableIdentity.Adapter`; it makes no ordinary readiness or operational
execution claim for Bottom. General observed endpoints consume the sealed
plan-only heterogeneous families from `HeterogeneousPlanAdaptation`: interval
endpoints carry positive/negative plan models, not term packages or producer
origins. The lower half adapts a positive target-lower plan under
`Γ,targetFirst` to a negative source-lower plan under `Γ,sourceFirst`; the
upper half adapts a positive source-upper plan under `Γ,sourceFirst` to a
negative target-upper plan under `Γ,targetFirst`, with both derivations
checked under the left source-first context.
-/

namespace LambdaPToFCo.Full.IntervalPairSubtypingRuleConstruction

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open DemandDirectedSubtyping

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

/-- Exact structural views of the two enclosing interval-pair endpoints. -/
structure EndpointModels
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceLower sourceUpper targetLower targetUpper :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.intv sourceLower sourceUpper)))
    (demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.intv targetLower targetUpper))) : Type where
  sourceFirstPlan : ValuePlan sig
  sourceLowerPlan : ValuePlan sourceFirstPlan.scope
  sourceUpperPlan : ValuePlan sourceFirstPlan.scope
  sourceFirstModel : ProducerPlanModel sourceContext targetContext
    sourceScope.view sourceFirst sourceFirstPlan
  sourceMemberModel : IntervalProducerPlanModel
    (sourceContext.snoc sourceFirst) (sourceFirstPlan.context targetContext)
    (ScopeView.bindPlan sourceScope.view sourceFirstPlan)
    sourceLower sourceUpper sourceLowerPlan sourceUpperPlan
  sourceModel_eq : source.model =
    ⟨Pair.Interval.plan sourceFirstPlan sourceLowerPlan.inputTy
        sourceUpperPlan.inputTy,
      .intervalPair (label := label) sourceFirstModel sourceMemberModel⟩
  targetFirstPlan : ValuePlan sig
  targetLowerPlan : ValuePlan targetFirstPlan.scope
  targetUpperPlan : ValuePlan targetFirstPlan.scope
  targetFirstModel : BidirectionalPlanModel sourceContext targetContext
    demandScope.view targetFirst targetFirstPlan
  targetMemberModel : IntervalBidirectionalPlanModel
    (sourceContext.snoc targetFirst) (targetFirstPlan.context targetContext)
    (ScopeView.bindPlan demandScope.view targetFirstPlan)
    targetLower targetUpper targetLowerPlan targetUpperPlan
  demandModel_eq : demand.model =
    ⟨Pair.Interval.plan targetFirstPlan targetLowerPlan.inputTy
        targetUpperPlan.inputTy,
      .intervalPair (label := label) targetFirstModel targetMemberModel⟩

/-- Exact recursive first-component adaptation. -/
structure FirstAdaptation
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceLower sourceUpper targetLower targetUpper :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.intv sourceLower sourceUpper))}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.intv targetLower targetUpper))}
    (endpoints : EndpointModels source demand)
    (subtyping : Tau.Sub sourceContext (.ty sourceFirst) (.ty targetFirst)) :
    Type where
  producerScope : ScopeModel sourceContext targetContext
  consumerScope : ScopeModel sourceContext targetContext
  alignment : ScopeAlignment producerScope.view consumerScope.view
  producer : ProperProducer sourceContext targetContext producerScope
    sourceFirst
  consumer : ProperDemand sourceContext targetContext consumerScope targetFirst
  adaptation : FusedAdaptation alignment subtyping producer consumer
  producerPlan_eq : producer.plan = endpoints.sourceFirstPlan
  consumerPlan_eq : consumer.plan = endpoints.targetFirstPlan

namespace FirstAdaptation

noncomputable def adapter
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceLower sourceUpper targetLower targetUpper :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.intv sourceLower sourceUpper))}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.intv targetLower targetUpper))}
    {endpoints : EndpointModels source demand}
    {subtyping : Tau.Sub sourceContext (.ty sourceFirst) (.ty targetFirst)}
    (first : FirstAdaptation endpoints subtyping) :
    StableIdentity.Adapter targetContext endpoints.sourceFirstPlan
      endpoints.targetFirstPlan := by
  rw [← first.producerPlan_eq, ← first.consumerPlan_eq]
  exact first.adaptation.adapter

end FirstAdaptation

/-- The rank-2 common context. Its bound source witness remains abstract. -/
abbrev CommonEndpointContext
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceLower sourceUpper targetLower targetUpper :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.intv sourceLower sourceUpper))}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.intv targetLower targetUpper))}
    (endpoints : EndpointModels source demand) :=
  IntervalPairRepresentationBridgeConstruction.targetFirstOpenedContext
    targetContext endpoints.sourceFirstPlan endpoints.sourceLowerPlan
    endpoints.sourceUpperPlan endpoints.targetFirstPlan

theorem targetLowerAtSource_bot
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    IntervalPairRepresentationBridgeConstruction.targetLowerAtSource
        sourceFirst sourceLower sourceUpper targetFirst
        (Bot.plan targetFirst.scope) =
      Bot.plan
        (IntervalPairRepresentationBridgeConstruction.targetFirstAtSource
          sourceFirst sourceLower sourceUpper targetFirst).scope := by
  rfl

theorem targetUpperAtSource_top
    (sourceFirst : ValuePlan sig)
    (sourceLower sourceUpper : ValuePlan sourceFirst.scope)
    (targetFirst : ValuePlan sig) :
    IntervalPairRepresentationBridgeConstruction.targetUpperAtSource
        sourceFirst sourceLower sourceUpper targetFirst
        (Top.plan targetFirst.scope) =
      Top.plan
        (IntervalPairRepresentationBridgeConstruction.targetFirstAtSource
          sourceFirst sourceLower sourceUpper targetFirst).scope := by
  rfl

/-- Canonical endpoint erasure in the abstract-witness context. -/
noncomputable def canonicalEndpointAdapters
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceLower sourceUpper targetLower targetUpper :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.intv sourceLower sourceUpper))}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.intv targetLower targetUpper))}
    (endpoints : EndpointModels source demand)
    (targetLowerPlan_eq : endpoints.targetLowerPlan =
      Bot.plan endpoints.targetFirstPlan.scope)
    (targetUpperPlan_eq : endpoints.targetUpperPlan =
      Top.plan endpoints.targetFirstPlan.scope) :
    IntervalPairRepresentationBridgeConstruction.ScopedEndpointAdapters
      targetContext endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan
      endpoints.targetLowerPlan endpoints.targetUpperPlan where
  lower := by
    rw [targetLowerPlan_eq, targetLowerAtSource_bot]
    exact StableIdentity.Adapter.fromBottom (CommonEndpointContext endpoints)
      (IntervalPairRepresentationBridgeConstruction.sourceLowerAtTargetFirst
        endpoints.sourceFirstPlan endpoints.sourceLowerPlan
        endpoints.sourceUpperPlan endpoints.targetFirstPlan)
  upper := by
    rw [targetUpperPlan_eq, targetUpperAtSource_top]
    exact StableIdentity.Adapter.toTop (CommonEndpointContext endpoints)
      (IntervalPairRepresentationBridgeConstruction.sourceUpperAtTargetFirst
        endpoints.sourceFirstPlan endpoints.sourceLowerPlan
        endpoints.sourceUpperPlan endpoints.targetFirstPlan)

/-! ## Observed heterogeneous endpoints -/

/-- Exact plan-only endpoint evidence for one interval-bounds member rule.
The lower positive endpoint remains under the right/target-first source
context and adapts contravariantly to the lower negative endpoint under the
left/source-first context. The upper endpoints use the covariant orientation.
All four plans already inhabit the bridge's concrete common target context;
the equalities tie them to the rank-2 representation plans without exposing
the hidden witness. -/
structure HeterogeneousEndpointInput
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceLower sourceUpper targetLower targetUpper :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.intv sourceLower sourceUpper))}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.intv targetLower targetUpper))}
    (endpoints : EndpointModels source demand)
    (firstSubtyping : Tau.Sub sourceContext
      (.ty sourceFirst) (.ty targetFirst))
    (lowerSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
      (.ty targetLower) (.ty sourceLower))
    (upperSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
      (.ty sourceUpper) (.ty targetUpper))
    (_nonempty : Tau.Sub (sourceContext.snoc sourceFirst)
      (.ty sourceLower) (.ty sourceUpper)) : Type where
  lowerProducerScope : ScopeModel (sourceContext.snoc targetFirst)
    (CommonEndpointContext endpoints)
  lowerDemandScope : ScopeModel (sourceContext.snoc sourceFirst)
    (CommonEndpointContext endpoints)
  lowerAlignment : ScopeAlignment lowerProducerScope.view
    lowerDemandScope.view
  lowerProducer : PositivePlan (sourceContext.snoc targetFirst)
    (CommonEndpointContext endpoints) lowerProducerScope.view targetLower
  lowerDemand : NegativePlan (sourceContext.snoc sourceFirst)
    (CommonEndpointContext endpoints) lowerDemandScope.view sourceLower
  lowerAdaptation : ContravariantHeterogeneousPlanAdaptation
    (CommonEndpointContext endpoints)
    (ContextSubtyping.underBinder firstSubtyping) lowerAlignment
    lowerSubtyping lowerProducer lowerDemand
  lowerProducerPlan_eq : lowerProducer.plan =
    IntervalPairRepresentationBridgeConstruction.targetLowerAtSource
      endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan
      endpoints.targetLowerPlan
  lowerDemandPlan_eq : lowerDemand.plan =
    IntervalPairRepresentationBridgeConstruction.sourceLowerAtTargetFirst
      endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan
  upperProducerScope : ScopeModel (sourceContext.snoc sourceFirst)
    (CommonEndpointContext endpoints)
  upperDemandScope : ScopeModel (sourceContext.snoc targetFirst)
    (CommonEndpointContext endpoints)
  upperAlignment : ScopeAlignment upperProducerScope.view upperDemandScope.view
  upperProducer : PositivePlan (sourceContext.snoc sourceFirst)
    (CommonEndpointContext endpoints) upperProducerScope.view sourceUpper
  upperDemand : NegativePlan (sourceContext.snoc targetFirst)
    (CommonEndpointContext endpoints) upperDemandScope.view targetUpper
  upperAdaptation : HeterogeneousPlanAdaptation
    (CommonEndpointContext endpoints)
    (ContextSubtyping.underBinder firstSubtyping) upperAlignment
    upperSubtyping upperProducer upperDemand
  upperProducerPlan_eq : upperProducer.plan =
    IntervalPairRepresentationBridgeConstruction.sourceUpperAtTargetFirst
      endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan
  upperDemandPlan_eq : upperDemand.plan =
    IntervalPairRepresentationBridgeConstruction.targetUpperAtSource
      endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan
      endpoints.targetUpperPlan

namespace HeterogeneousEndpointInput

/-- Eliminate the two sealed plan adaptations into the exact rank-2 endpoint
pair consumed by the representation bridge. -/
noncomputable def endpointAdapters
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceLower sourceUpper targetLower targetUpper :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.intv sourceLower sourceUpper))}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.intv targetLower targetUpper))}
    {endpoints : EndpointModels source demand}
    {firstSubtyping : Tau.Sub sourceContext
      (.ty sourceFirst) (.ty targetFirst)}
    {lowerSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
      (.ty targetLower) (.ty sourceLower)}
    {upperSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
      (.ty sourceUpper) (.ty targetUpper)}
    {nonempty : Tau.Sub (sourceContext.snoc sourceFirst)
      (.ty sourceLower) (.ty sourceUpper)}
    (input : HeterogeneousEndpointInput endpoints firstSubtyping
      lowerSubtyping upperSubtyping nonempty) :
    IntervalPairRepresentationBridgeConstruction.ScopedEndpointAdapters
      targetContext endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan
      endpoints.targetLowerPlan endpoints.targetUpperPlan where
  lower := by
    rw [← input.lowerProducerPlan_eq, ← input.lowerDemandPlan_eq]
    exact input.lowerAdaptation.adapter
  upper := by
    rw [← input.upperProducerPlan_eq, ← input.upperDemandPlan_eq]
    exact input.upperAdaptation.adapter

end HeterogeneousEndpointInput

/-- The exact endpoint input for preserving one equal-bound interval member
by source `.refl` while its enclosing first binder changes only by
`.widen precise`.  The three decomposed endpoint checks are all reflexive and
their adapters remain sealed by `HeterogeneousEndpointInput`; this record
does not accept an adapter or an arbitrary member derivation. -/
structure ReflexiveUnderWidenEndpointInput
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    {endpoint : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair (.Single path) label (.intv endpoint endpoint))}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Pair referent label (.intv endpoint endpoint))}
    (endpoints : EndpointModels source demand)
    (precise : Path.Ty sourceContext path (.ty referent)) : Type where
  input : HeterogeneousEndpointInput endpoints (.widen precise)
    (.refl (τ := .ty endpoint)) (.refl (τ := .ty endpoint))
    (.refl (τ := .ty endpoint))

namespace ReflexiveUnderWidenEndpointInput

noncomputable def endpointAdapters
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    {endpoint : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair (.Single path) label (.intv endpoint endpoint))}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Pair referent label (.intv endpoint endpoint))}
    {endpoints : EndpointModels source demand}
    {precise : Path.Ty sourceContext path (.ty referent)}
    (member : ReflexiveUnderWidenEndpointInput endpoints precise) :
    IntervalPairRepresentationBridgeConstruction.ScopedEndpointAdapters
      targetContext endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan
      endpoints.targetLowerPlan endpoints.targetUpperPlan :=
  member.input.endpointAdapters

end ReflexiveUnderWidenEndpointInput

/-- Sealed contextual evidence indexed by both exact pair premises and the
heterogeneous binder relation generated by the first premise. -/
inductive ContextualEndpointAdaptationEvidence
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceLower sourceUpper targetLower targetUpper :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.intv sourceLower sourceUpper))}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.intv targetLower targetUpper))}
    (endpoints : EndpointModels source demand)
    (firstSubtyping : Tau.Sub sourceContext
      (.ty sourceFirst) (.ty targetFirst)) :
    (memberSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
      (.intv sourceLower sourceUpper) (.intv targetLower targetUpper)) →
    ContextSubtyping (sourceContext.snoc sourceFirst)
        (sourceContext.snoc targetFirst) →
    IntervalPairRepresentationBridgeConstruction.ScopedEndpointAdapters
      targetContext endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan
      endpoints.targetLowerPlan endpoints.targetUpperPlan → Type where
  | canonical
      (memberSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
        (.intv sourceLower sourceUpper) (.intv targetLower targetUpper))
      (targetLowerPlan_eq : endpoints.targetLowerPlan =
        Bot.plan endpoints.targetFirstPlan.scope)
      (targetUpperPlan_eq : endpoints.targetUpperPlan =
        Top.plan endpoints.targetFirstPlan.scope) :
      ContextualEndpointAdaptationEvidence endpoints firstSubtyping
        memberSubtyping (ContextSubtyping.underBinder firstSubtyping)
        (canonicalEndpointAdapters endpoints targetLowerPlan_eq
          targetUpperPlan_eq)
  | heterogeneous
      {lowerSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
        (.ty targetLower) (.ty sourceLower)}
      {upperSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
        (.ty sourceUpper) (.ty targetUpper)}
      {nonempty : Tau.Sub (sourceContext.snoc sourceFirst)
        (.ty sourceLower) (.ty sourceUpper)}
      (input : HeterogeneousEndpointInput endpoints firstSubtyping
        lowerSubtyping upperSubtyping nonempty) :
      ContextualEndpointAdaptationEvidence endpoints firstSubtyping
        (.bounds lowerSubtyping upperSubtyping nonempty)
        (ContextSubtyping.underBinder firstSubtyping) input.endpointAdapters

/-- Exact endpoint output consumed by the target-only rank-2 bridge. -/
structure ContextualEndpointAdaptation
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceLower sourceUpper targetLower targetUpper :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.intv sourceLower sourceUpper))}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.intv targetLower targetUpper))}
    (endpoints : EndpointModels source demand)
    (firstSubtyping : Tau.Sub sourceContext
      (.ty sourceFirst) (.ty targetFirst))
    (contexts : ContextSubtyping (sourceContext.snoc sourceFirst)
      (sourceContext.snoc targetFirst))
    (memberSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
      (.intv sourceLower sourceUpper)
      (.intv targetLower targetUpper)) : Type where
  endpointAdapters :
    IntervalPairRepresentationBridgeConstruction.ScopedEndpointAdapters
      targetContext endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan
      endpoints.targetLowerPlan endpoints.targetUpperPlan
  evidence : ContextualEndpointAdaptationEvidence endpoints firstSubtyping
    memberSubtyping contexts endpointAdapters

namespace ContextualEndpointAdaptation

noncomputable def canonical
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceLower sourceUpper targetLower targetUpper :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.intv sourceLower sourceUpper))}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.intv targetLower targetUpper))}
    {endpoints : EndpointModels source demand}
    (firstSubtyping : Tau.Sub sourceContext
      (.ty sourceFirst) (.ty targetFirst))
    (memberSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
      (.intv sourceLower sourceUpper) (.intv targetLower targetUpper))
    (targetLowerPlan_eq : endpoints.targetLowerPlan =
      Bot.plan endpoints.targetFirstPlan.scope)
    (targetUpperPlan_eq : endpoints.targetUpperPlan =
      Top.plan endpoints.targetFirstPlan.scope) :
    ContextualEndpointAdaptation endpoints firstSubtyping
      (ContextSubtyping.underBinder firstSubtyping) memberSubtyping where
  endpointAdapters := canonicalEndpointAdapters endpoints targetLowerPlan_eq
    targetUpperPlan_eq
  evidence := .canonical memberSubtyping targetLowerPlan_eq
    targetUpperPlan_eq

/-- Consume the exact two heterogeneous plan adaptations for a structural
interval-bounds member rule. The resulting endpoint adapters are computed by
eliminating sealed evidence; no raw adapter or callback crosses this API. -/
noncomputable def ofHeterogeneous
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceLower sourceUpper targetLower targetUpper :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.intv sourceLower sourceUpper))}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.intv targetLower targetUpper))}
    {endpoints : EndpointModels source demand}
    (firstSubtyping : Tau.Sub sourceContext
      (.ty sourceFirst) (.ty targetFirst))
    (lowerSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
      (.ty targetLower) (.ty sourceLower))
    (upperSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
      (.ty sourceUpper) (.ty targetUpper))
    (nonempty : Tau.Sub (sourceContext.snoc sourceFirst)
      (.ty sourceLower) (.ty sourceUpper))
    (input : HeterogeneousEndpointInput endpoints firstSubtyping
      lowerSubtyping upperSubtyping nonempty) :
    ContextualEndpointAdaptation endpoints firstSubtyping
      (ContextSubtyping.underBinder firstSubtyping)
      (.bounds lowerSubtyping upperSubtyping nonempty) where
  endpointAdapters := input.endpointAdapters
  evidence := .heterogeneous input

end ContextualEndpointAdaptation

/-- Assemble the exact outer static stable adapter. The hidden witness is
introduced and eliminated entirely by
`IntervalPairRepresentationBridgeConstruction`. This result is not
operational execution evidence. -/
noncomputable def adapter
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceFirst targetFirst : LambdaPFC.Ty n}
    {sourceLower sourceUpper targetLower targetUpper :
      LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair sourceFirst label (.intv sourceLower sourceUpper))}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Pair targetFirst label (.intv targetLower targetUpper))}
    (firstSubtyping : Tau.Sub sourceContext
      (.ty sourceFirst) (.ty targetFirst))
    (memberSubtyping : Tau.Sub (sourceContext.snoc sourceFirst)
      (.intv sourceLower sourceUpper) (.intv targetLower targetUpper))
    (endpoints : EndpointModels source demand)
    (first : FirstAdaptation endpoints firstSubtyping)
    (member : ContextualEndpointAdaptation endpoints firstSubtyping
      (ContextSubtyping.underBinder firstSubtyping) memberSubtyping) :
    StableIdentity.Adapter targetContext source.plan demand.plan := by
  change StableIdentity.Adapter targetContext source.model.1 demand.model.1
  rw [endpoints.sourceModel_eq, endpoints.demandModel_eq]
  exact IntervalPairRepresentationBridgeConstruction.adapter first.adapter
    member.endpointAdapters

/-- Assemble the rank-2 representation bridge for the literal source member
proof `.refl` under an enclosing singleton `.widen precise`.  Internally the
same reflexive endpoint fact is decomposed only to satisfy the representation
bridge; the caller-facing pair proof remains exact in the sealed
demand-directed wrapper. -/
noncomputable def reflexiveUnderWidenAdapter
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    {endpoint : LambdaPFC.Ty (n + 1)}
    {label : LambdaPFC.Name}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Pair (.Single path) label (.intv endpoint endpoint))}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Pair referent label (.intv endpoint endpoint))}
    (precise : Path.Ty sourceContext path (.ty referent))
    (endpoints : EndpointModels source demand)
    (first : FirstAdaptation endpoints (.widen precise))
    (member : ReflexiveUnderWidenEndpointInput endpoints precise) :
    StableIdentity.Adapter targetContext source.plan demand.plan :=
  adapter (.widen precise)
    (.bounds (.refl (τ := .ty endpoint)) (.refl (τ := .ty endpoint))
      (.refl (τ := .ty endpoint))) endpoints first
    (ContextualEndpointAdaptation.ofHeterogeneous (.widen precise)
      (.refl (τ := .ty endpoint)) (.refl (τ := .ty endpoint))
      (.refl (τ := .ty endpoint)) member.input)

end LambdaPToFCo.Full.IntervalPairSubtypingRuleConstruction
