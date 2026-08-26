import LambdaPToFCo.Full.ContextSubtyping
import LambdaPToFCo.Full.TranslationInterfaces

/-!
# Sealed heterogeneous plan adaptation

Interval endpoints carry only positive and negative plans.  They have no term
package, producer origin, or operational readiness evidence.  This module
therefore gives the two context orientations needed by dependent interval
members directly at the plan level.

For equal source contexts, the initial ordinary constructor is exact
reflexivity between endpoints whose plans are propositionally equal; it
computes the stable identity adapter internally. Across genuinely
heterogeneous contexts, observation erasure is available whenever the exact
negative endpoint is canonical `Top.plan`, in either context orientation;
the contravariant orientation also retains the canonical static map from
`Bot.plan`. No constructor accepts a pull result, plan satisfaction, stable
adapter, or adapter-producing callback, and the Bottom case makes no
readiness claim.
-/

namespace LambdaPToFCo.Full

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

/-! ## Homogeneous plan adaptation -/

/-- A closed ordinary plan adaptation. Its initial constructor is exact
source reflexivity and requires the two endpoint plans to coincide; the
stable identity adapter is computed only by the eliminator below. -/
inductive PlanAdaptation
    {n : Nat} {sourceContext : Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {producerScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment producerScope.view demandScope.view) :
    {sourceType targetType : Ty n} ->
    (subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)) ->
    (producer : PositivePlan sourceContext targetContext producerScope.view
      sourceType) ->
    (demand : NegativePlan sourceContext targetContext demandScope.view
      targetType) -> Type where
  | reflexive
      {sourceType : Ty n}
      {producer : PositivePlan sourceContext targetContext producerScope.view
        sourceType}
      {demand : NegativePlan sourceContext targetContext demandScope.view
        sourceType}
      (plan_eq : producer.plan = demand.plan) :
      PlanAdaptation alignment (Tau.Sub.refl (τ := .ty sourceType)) producer
        demand

namespace PlanAdaptation

/-- Compute the only adapter admitted by the closed homogeneous evidence. -/
noncomputable def adapter
    (adaptation : PlanAdaptation alignment subtyping producer demand) :
    StableIdentity.Adapter targetContext producer.plan demand.plan := by
  cases adaptation with
  | reflexive plan_eq =>
      rw [plan_eq]
      exact StableIdentity.Adapter.identity targetContext _

end PlanAdaptation

/-! ## Producer-left orientation -/

/-- A sealed plan-only adaptation whose positive endpoint and subtyping
derivation inhabit the left context while its negative endpoint inhabits the
right context. -/
inductive HeterogeneousPlanAdaptation
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig) :
    {n : Nat} ->
    {leftContext rightContext : Ctx n} ->
    (contexts : ContextSubtyping leftContext rightContext) ->
    {producerScope : ScopeModel leftContext targetContext} ->
    {demandScope : ScopeModel rightContext targetContext} ->
    (alignment : ScopeAlignment producerScope.view demandScope.view) ->
    {sourceType targetType : Ty n} ->
    (subtyping : Tau.Sub leftContext (.ty sourceType) (.ty targetType)) ->
    (producer : PositivePlan leftContext targetContext producerScope.view
      sourceType) ->
    (demand : NegativePlan rightContext targetContext demandScope.view
      targetType) -> Type where
  | ofHomogeneous
      {n : Nat} {context : Ctx n}
      (contexts : ContextSubtyping context context)
      {producerScope demandScope : ScopeModel context targetContext}
      {alignment : ScopeAlignment producerScope.view demandScope.view}
      {sourceType targetType : Ty n}
      {subtyping : Tau.Sub context (.ty sourceType) (.ty targetType)}
      {producer : PositivePlan context targetContext producerScope.view
        sourceType}
      {demand : NegativePlan context targetContext demandScope.view targetType}
      (adaptation : PlanAdaptation alignment subtyping producer demand) :
      @HeterogeneousPlanAdaptation sig targetContext n context context
        contexts producerScope demandScope alignment sourceType
        targetType subtyping producer demand
  | toTop
      {n : Nat} {leftContext rightContext : Ctx n}
      (contexts : ContextSubtyping leftContext rightContext)
      {producerScope : ScopeModel leftContext targetContext}
      {demandScope : ScopeModel rightContext targetContext}
      (alignment : ScopeAlignment producerScope.view demandScope.view)
      {sourceType targetType : Ty n}
      (subtyping : Tau.Sub leftContext (.ty sourceType) (.ty targetType))
      (producer : PositivePlan leftContext targetContext producerScope.view
        sourceType)
      (demand : NegativePlan rightContext targetContext demandScope.view
        targetType)
      (demandPlan_eq : demand.plan = Top.plan sig) :
      HeterogeneousPlanAdaptation targetContext contexts alignment subtyping
        producer demand

namespace HeterogeneousPlanAdaptation

/-- The stable adapter determined by the sealed plan evidence. -/
noncomputable def adapter
    (adaptation : HeterogeneousPlanAdaptation targetContext contexts alignment
      subtyping producer demand) :
    StableIdentity.Adapter targetContext producer.plan demand.plan := by
  cases adaptation with
  | ofHomogeneous _ homogeneous =>
      exact homogeneous.adapter
  | toTop _ _ _ producer _ demandPlan_eq =>
      rw [demandPlan_eq]
      exact StableIdentity.Adapter.toTop targetContext producer.plan

/-- Embed a sealed homogeneous adaptation while preserving the exact
proof-relevant relation between the equal source contexts. -/
noncomputable def fromHomogeneous
    {n : Nat} {sourceContext : Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {producerScope demandScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment producerScope.view demandScope.view}
    {sourceType targetType : Ty n}
    {subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)}
    {producer : PositivePlan sourceContext targetContext producerScope.view
      sourceType}
    {demand : NegativePlan sourceContext targetContext demandScope.view
      targetType}
    (contexts : ContextSubtyping sourceContext sourceContext)
    (adaptation : PlanAdaptation alignment subtyping producer demand) :
    HeterogeneousPlanAdaptation targetContext contexts
      alignment subtyping producer demand :=
  .ofHomogeneous contexts adaptation

/-- Canonical observation erasure is valid across any retained context
relation.  This is static plan evidence only. -/
noncomputable def observationFree
    {n : Nat} {leftContext rightContext : Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {producerScope : ScopeModel leftContext targetContext}
    {demandScope : ScopeModel rightContext targetContext}
    {sourceType targetType : Ty n}
    (contexts : ContextSubtyping leftContext rightContext)
    (alignment : ScopeAlignment producerScope.view demandScope.view)
    (subtyping : Tau.Sub leftContext (.ty sourceType) (.ty targetType))
    (producer : PositivePlan leftContext targetContext producerScope.view
      sourceType)
    (demand : NegativePlan rightContext targetContext demandScope.view
      targetType)
    (demandPlan_eq : demand.plan = Top.plan sig) :
    HeterogeneousPlanAdaptation targetContext contexts alignment subtyping
      producer demand :=
  .toTop contexts alignment subtyping producer demand demandPlan_eq

end HeterogeneousPlanAdaptation

/-! ## Producer-right orientation -/

/-- A sealed plan-only adaptation whose positive endpoint inhabits the right
context while its derivation and negative endpoint inhabit the left context.
This is the orientation of a lower interval bound. -/
inductive ContravariantHeterogeneousPlanAdaptation
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig) :
    {n : Nat} ->
    {leftContext rightContext : Ctx n} ->
    (contexts : ContextSubtyping leftContext rightContext) ->
    {producerScope : ScopeModel rightContext targetContext} ->
    {demandScope : ScopeModel leftContext targetContext} ->
    (alignment : ScopeAlignment producerScope.view demandScope.view) ->
    {sourceType targetType : Ty n} ->
    (subtyping : Tau.Sub leftContext (.ty sourceType) (.ty targetType)) ->
    (producer : PositivePlan rightContext targetContext producerScope.view
      sourceType) ->
    (demand : NegativePlan leftContext targetContext demandScope.view
      targetType) -> Type where
  | ofHomogeneous
      {n : Nat} {context : Ctx n}
      (contexts : ContextSubtyping context context)
      {producerScope demandScope : ScopeModel context targetContext}
      {alignment : ScopeAlignment producerScope.view demandScope.view}
      {sourceType targetType : Ty n}
      {subtyping : Tau.Sub context (.ty sourceType) (.ty targetType)}
      {producer : PositivePlan context targetContext producerScope.view
        sourceType}
      {demand : NegativePlan context targetContext demandScope.view targetType}
      (adaptation : PlanAdaptation alignment subtyping producer demand) :
      @ContravariantHeterogeneousPlanAdaptation sig targetContext n context
        context contexts producerScope demandScope alignment
        sourceType targetType subtyping producer demand
  | fromBottom
      {n : Nat} {leftContext rightContext : Ctx n}
      (contexts : ContextSubtyping leftContext rightContext)
      {producerScope : ScopeModel rightContext targetContext}
      {demandScope : ScopeModel leftContext targetContext}
      (alignment : ScopeAlignment producerScope.view demandScope.view)
      {sourceType targetType : Ty n}
      (subtyping : Tau.Sub leftContext (.ty sourceType) (.ty targetType))
      (producer : PositivePlan rightContext targetContext producerScope.view
        sourceType)
      (demand : NegativePlan leftContext targetContext demandScope.view
        targetType)
      (producerPlan_eq : producer.plan = Bot.plan sig) :
      ContravariantHeterogeneousPlanAdaptation targetContext contexts alignment
        subtyping producer demand
  | toTop
      {n : Nat} {leftContext rightContext : Ctx n}
      (contexts : ContextSubtyping leftContext rightContext)
      {producerScope : ScopeModel rightContext targetContext}
      {demandScope : ScopeModel leftContext targetContext}
      (alignment : ScopeAlignment producerScope.view demandScope.view)
      {sourceType targetType : Ty n}
      (subtyping : Tau.Sub leftContext (.ty sourceType) (.ty targetType))
      (producer : PositivePlan rightContext targetContext producerScope.view
        sourceType)
      (demand : NegativePlan leftContext targetContext demandScope.view
        targetType)
      (demandPlan_eq : demand.plan = Top.plan sig) :
      ContravariantHeterogeneousPlanAdaptation targetContext contexts alignment
        subtyping producer demand

namespace ContravariantHeterogeneousPlanAdaptation

/-- The exact stable adapter determined by the sealed contravariant evidence.
The Bottom branch is a static adapter, not readiness evidence. -/
noncomputable def adapter
    (adaptation : ContravariantHeterogeneousPlanAdaptation targetContext
      contexts alignment subtyping producer demand) :
    StableIdentity.Adapter targetContext producer.plan demand.plan := by
  cases adaptation with
  | ofHomogeneous _ homogeneous =>
      exact homogeneous.adapter
  | fromBottom _ _ _ _ demand producerPlan_eq =>
      rw [producerPlan_eq]
      exact StableIdentity.Adapter.fromBottom targetContext demand.plan
  | toTop _ _ _ producer _ demandPlan_eq =>
      rw [demandPlan_eq]
      exact StableIdentity.Adapter.toTop targetContext producer.plan

/-- Embed a sealed homogeneous adaptation while preserving the exact
proof-relevant relation between the equal source contexts. No reverse context
relation is introduced. -/
noncomputable def fromHomogeneous
    {n : Nat} {sourceContext : Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {producerScope demandScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment producerScope.view demandScope.view}
    {sourceType targetType : Ty n}
    {subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType)}
    {producer : PositivePlan sourceContext targetContext producerScope.view
      sourceType}
    {demand : NegativePlan sourceContext targetContext demandScope.view
      targetType}
    (contexts : ContextSubtyping sourceContext sourceContext)
    (adaptation : PlanAdaptation alignment subtyping producer demand) :
    ContravariantHeterogeneousPlanAdaptation targetContext
      contexts alignment subtyping producer demand :=
  .ofHomogeneous contexts adaptation

/-- Canonical Bottom elimination is valid across any retained context
relation.  It supplies only a static stable adapter. -/
noncomputable def canonicalBottom
    {n : Nat} {leftContext rightContext : Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {producerScope : ScopeModel rightContext targetContext}
    {demandScope : ScopeModel leftContext targetContext}
    {sourceType targetType : Ty n}
    (contexts : ContextSubtyping leftContext rightContext)
    (alignment : ScopeAlignment producerScope.view demandScope.view)
    (subtyping : Tau.Sub leftContext (.ty sourceType) (.ty targetType))
    (producer : PositivePlan rightContext targetContext producerScope.view
      sourceType)
    (demand : NegativePlan leftContext targetContext demandScope.view
      targetType)
    (producerPlan_eq : producer.plan = Bot.plan sig) :
    ContravariantHeterogeneousPlanAdaptation targetContext contexts alignment
      subtyping producer demand :=
  .fromBottom contexts alignment subtyping producer demand producerPlan_eq

/-- Observation erasure is independent of which side of a heterogeneous
context relation contains the positive endpoint. The exact negative endpoint
is forced to canonical `Top.plan`, and the stable adapter is computed
internally. -/
noncomputable def observationFree
    {n : Nat} {leftContext rightContext : Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {producerScope : ScopeModel rightContext targetContext}
    {demandScope : ScopeModel leftContext targetContext}
    {sourceType targetType : Ty n}
    (contexts : ContextSubtyping leftContext rightContext)
    (alignment : ScopeAlignment producerScope.view demandScope.view)
    (subtyping : Tau.Sub leftContext (.ty sourceType) (.ty targetType))
    (producer : PositivePlan rightContext targetContext producerScope.view
      sourceType)
    (demand : NegativePlan leftContext targetContext demandScope.view
      targetType)
    (demandPlan_eq : demand.plan = Top.plan sig) :
    ContravariantHeterogeneousPlanAdaptation targetContext contexts alignment
      subtyping producer demand :=
  .toTop contexts alignment subtyping producer demand demandPlan_eq

end ContravariantHeterogeneousPlanAdaptation

end LambdaPToFCo.Full
