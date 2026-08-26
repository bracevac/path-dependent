import LambdaPToFCo.Full.PairModel
import LambdaPToFCo.Full.ScopeView
import LambdaPToFCo.Full.StableIdentity
import LambdaPToFCo.Full.TranslationOrigins

/-!
# Internal proper-plan and interval translation carriers

This is an internal package-map carrier, not the public compiler ABI. Its raw
proper endpoint records intentionally do not certify that a target plan
models the advertised source type. `TranslationInterfaces` supplies that
closed evidence and is the only layer derivation-directed compiler code
should consume. Raw constructors here are used only after refinement.

An interval producer owns a positive existential descriptor

  lower package -> Selection(X) package -> upper package

where `X` is hidden by `IntervalDescriptor`. Bounds-push retains that exact
`X`. An interval demand does not choose an `X`; it is the dual recipe made
from a lower producer and an upper demand. Satisfaction consumes any
positive producer descriptor and hides the producer's same `X` again.

Every arrow below is a package-level `StableIdentity.Adapter`. This module
states no open-context readiness or reduction property.
-/

namespace LambdaPToFCo.Full.TranslationModelCore

open LambdaPFC
open SystemFCoExt

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

/-! ## Source-indexed plan endpoints -/

/-- Internal positive plan endpoint. It intentionally has no source term
origin or package: interval upper bounds need plans without inhabitants. -/
structure PositivePlan (sourceContext : LambdaPFC.Ctx n)
    (targetContext : SystemFCoExt.Ctx sig)
    (view : ScopeView n targetContext)
    (sourceType : LambdaPFC.Ty n) : Type where
  plan : ValuePlan sig

/-- Internal negative plan endpoint. It intentionally has no demand trace:
interval lower/upper descriptors need polarity, not term evidence. -/
structure NegativePlan (sourceContext : LambdaPFC.Ctx n)
    (targetContext : SystemFCoExt.Ctx sig)
    (view : ScopeView n targetContext)
    (sourceType : LambdaPFC.Ty n) : Type where
  plan : ValuePlan sig

/-- The only proper endpoint forms retained by interval carriers. -/
inductive PlanEndpoint (sourceContext : LambdaPFC.Ctx n)
    (targetContext : SystemFCoExt.Ctx sig)
    (view : ScopeView n targetContext)
    (sourceType : LambdaPFC.Ty n) : Type where
  | positive
      (value : PositivePlan sourceContext targetContext view sourceType)
  | negative
      (value : NegativePlan sourceContext targetContext view sourceType)

namespace PlanEndpoint

def plan
    (interface : PlanEndpoint sourceContext targetContext view sourceType) :
    ValuePlan sig :=
  match interface with
  | .positive value => value.plan
  | .negative value => value.plan

end PlanEndpoint

/-- Internal result of derivation-indexed proper covariance. The refined high
layer certifies the returned target plan against source structure. -/
structure ProperPushResult
    {sourceView targetView : ScopeView n targetContext}
    (alignment : ScopeAlignment sourceView targetView)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : LambdaPFC.Tau.Sub sourceContext (.ty sourceType)
      (.ty targetType))
    (source : PositivePlan sourceContext targetContext sourceView sourceType) :
    Type where
  plan : ValuePlan sig
  adapter : StableIdentity.Adapter targetContext source.plan plan

namespace ProperPushResult

def positive
    {sourceView targetView : ScopeView n targetContext}
    (alignment : ScopeAlignment sourceView targetView)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : LambdaPFC.Tau.Sub sourceContext (.ty sourceType)
      (.ty targetType))
    (source : PositivePlan sourceContext targetContext sourceView sourceType)
    (result : ProperPushResult alignment subtyping source) :
    PositivePlan sourceContext targetContext targetView targetType where
  plan := result.plan

end ProperPushResult

/-- Internal result of derivation-indexed proper contravariance. The refined
high layer retains the exact pulled demand trace. -/
structure ProperPullResult
    {sourceView targetView : ScopeView n targetContext}
    (alignment : ScopeAlignment sourceView targetView)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : LambdaPFC.Tau.Sub sourceContext (.ty sourceType)
      (.ty targetType))
    (target : NegativePlan sourceContext targetContext targetView targetType) :
    Type where
  plan : ValuePlan sig
  adapter : StableIdentity.Adapter targetContext plan target.plan

namespace ProperPullResult

def negative
    {sourceView targetView : ScopeView n targetContext}
    (alignment : ScopeAlignment sourceView targetView)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : LambdaPFC.Tau.Sub sourceContext (.ty sourceType)
      (.ty targetType))
    (target : NegativePlan sourceContext targetContext targetView targetType)
    (result : ProperPullResult alignment subtyping target) :
    NegativePlan sourceContext targetContext sourceView sourceType where
  plan := result.plan

end ProperPullResult

/-- Static producer-to-demand endpoint satisfaction. The alignment records
the source-slot identity agreement; the adapter is the exact package map. -/
structure ProperSatisfaction
    {producerView demandView : ScopeView n targetContext}
    (alignment : ScopeAlignment producerView demandView)
    {sourceType : LambdaPFC.Ty n}
    (producer : PositivePlan sourceContext targetContext producerView
      sourceType)
    (demand : NegativePlan sourceContext targetContext demandView sourceType) :
    Type where
  adapter : StableIdentity.Adapter targetContext producer.plan demand.plan

/-! ## Positive existential interval descriptors -/

/-- A positive interval carrier. The selected representation is existential:
it is not an external index and a map can only preserve it by eliminating this
descriptor. Both bridges operate on complete value packages. -/
inductive IntervalDescriptor (sourceContext : LambdaPFC.Ctx n)
    (targetContext : SystemFCoExt.Ctx sig)
    {lowerView upperView : ScopeView n targetContext}
    {lowerType upperType : LambdaPFC.Ty n}
    (lower : PlanEndpoint sourceContext targetContext lowerView lowerType)
    (upper : PlanEndpoint sourceContext targetContext upperView upperType) :
    Type where
  | selected (representation : SystemFCoExt.Ty sig)
      (lowerToSelected : StableIdentity.Adapter targetContext lower.plan
        (Selection.plan representation))
      (selectedToUpper : StableIdentity.Adapter targetContext
        (Selection.plan representation) upper.plan) :
      IntervalDescriptor sourceContext targetContext lower upper

namespace IntervalDescriptor

/-- A static positive interval map. Lower endpoints run contravariantly and
upper endpoints covariantly. There is deliberately no witness field here. -/
structure Map
    {sourceLowerView sourceUpperView targetLowerView targetUpperView :
      ScopeView n targetContext}
    (lowerAlignment : ScopeAlignment targetLowerView sourceLowerView)
    (upperAlignment : ScopeAlignment sourceUpperView targetUpperView)
    {sourceLowerType sourceUpperType targetLowerType targetUpperType :
      LambdaPFC.Ty n}
    (sourceLower : PlanEndpoint sourceContext targetContext sourceLowerView
      sourceLowerType)
    (sourceUpper : PlanEndpoint sourceContext targetContext sourceUpperView
      sourceUpperType)
    (targetLower : PlanEndpoint sourceContext targetContext targetLowerView
      targetLowerType)
    (targetUpper : PlanEndpoint sourceContext targetContext targetUpperView
      targetUpperType) : Type where
  lower : StableIdentity.Adapter targetContext targetLower.plan sourceLower.plan
  upper : StableIdentity.Adapter targetContext sourceUpper.plan targetUpper.plan

/-- Apply a positive map. Pattern matching opens the source existential and
immediately repackages the exact same `representation`. -/
noncomputable def map
    (descriptor : IntervalDescriptor sourceContext targetContext sourceLower
      sourceUpper)
    (mapping : Map lowerAlignment upperAlignment sourceLower sourceUpper
      targetLower targetUpper) :
    IntervalDescriptor sourceContext targetContext targetLower targetUpper :=
  match descriptor with
  | .selected representation lowerToSelected selectedToUpper =>
      .selected representation
        (mapping.lower.compose lowerToSelected)
        (selectedToUpper.compose mapping.upper)

/-- Identity positive map. -/
noncomputable def Map.identity
    (lower : PlanEndpoint sourceContext targetContext view lowerType)
    (upper : PlanEndpoint sourceContext targetContext view upperType) :
    Map (ScopeAlignment.identity view) (ScopeAlignment.identity view)
      lower upper lower upper where
  lower := StableIdentity.Adapter.identity targetContext lower.plan
  upper := StableIdentity.Adapter.identity targetContext upper.plan

/-- Composition has the characteristic reversed order at the lower bound. -/
noncomputable def Map.compose
    (first : Map firstLowerAlignment firstUpperAlignment
      sourceLower sourceUpper middleLower middleUpper)
    (second : Map secondLowerAlignment secondUpperAlignment
      middleLower middleUpper targetLower targetUpper) :
    Map (secondLowerAlignment.compose firstLowerAlignment)
      (firstUpperAlignment.compose secondUpperAlignment)
      sourceLower sourceUpper targetLower targetUpper where
  lower := second.lower.compose first.lower
  upper := first.upper.compose second.upper

/-- Feed the positive descriptor directly to PairModel's existential member
telescope. This is the key package-level boundary: no endpoint is reduced to
a raw coercion between representation types. -/
noncomputable def memberArguments
    {view : ScopeView n targetContext}
    {lowerType upperType : LambdaPFC.Ty n}
    {lower : PlanEndpoint sourceContext targetContext view lowerType}
    {upper : PlanEndpoint sourceContext targetContext view upperType}
    (descriptor : IntervalDescriptor sourceContext targetContext lower upper) :
    Telescope.Args targetContext
      (Pair.Interval.memberTelescope lower.plan.inputTy upper.plan.inputTy) :=
  match descriptor with
  | .selected representation lowerToSelected selectedToUpper =>
      Pair.Interval.memberArgumentsWithAdapters targetContext
        lower.plan.inputTy upper.plan.inputTy representation
        lowerToSelected.coercion lowerToSelected.coercion_hasType
        selectedToUpper.coercion selectedToUpper.coercion_hasType

end IntervalDescriptor

/-! ## Producer and dual demand -/

/-- An interval producer owns the positive descriptor. Its lower endpoint
is negative and its upper endpoint positive, matching bounds variance. -/
structure IntervalProducer (sourceContext : LambdaPFC.Ctx n)
    (targetContext : SystemFCoExt.Ctx sig)
    (view : ScopeView n targetContext)
    (lowerType upperType : LambdaPFC.Ty n) : Type where
  origin : IntervalProducerOrigin sourceContext lowerType upperType
  lower : NegativePlan sourceContext targetContext view lowerType
  upper : PositivePlan sourceContext targetContext view upperType
  descriptor : IntervalDescriptor sourceContext targetContext (.negative lower)
    (.positive upper)

/-- An interval demand fixes no selected representation. It is the dual
recipe: a positive lower endpoint and a negative upper endpoint. -/
structure IntervalDemand (sourceContext : LambdaPFC.Ctx n)
    (targetContext : SystemFCoExt.Ctx sig)
    (view : ScopeView n targetContext)
    (lowerType upperType : LambdaPFC.Ty n) : Type where
  trace : IntervalDemandTrace sourceContext lowerType upperType
  lower : PositivePlan sourceContext targetContext view lowerType
  upper : NegativePlan sourceContext targetContext view upperType

namespace IntervalProducer

/-- Bounds covariance. The recursive lower pull and upper push supply the
two endpoint maps; the positive descriptor retains its exact hidden `X`. -/
noncomputable def pushBounds
    {sourceView targetView : ScopeView n targetContext}
    {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
    (source : IntervalProducer sourceContext targetContext sourceView
      sourceLower sourceUpper)
    (alignment : ScopeAlignment sourceView targetView)
    (lowerSubtyping : LambdaPFC.Tau.Sub sourceContext (.ty targetLower)
      (.ty sourceLower))
    (upperSubtyping : LambdaPFC.Tau.Sub sourceContext (.ty sourceUpper)
      (.ty targetUpper))
    (nonempty : LambdaPFC.Tau.Sub sourceContext (.ty sourceLower)
      (.ty sourceUpper))
    (lowerResult : ProperPullResult alignment.symm lowerSubtyping source.lower)
    (upperResult : ProperPushResult alignment upperSubtyping source.upper) :
    IntervalProducer sourceContext targetContext targetView targetLower
      targetUpper := by
  let targetLowerDemand := ProperPullResult.negative alignment.symm
    lowerSubtyping source.lower lowerResult
  let targetUpperProducer := ProperPushResult.positive alignment
    upperSubtyping source.upper upperResult
  let mapping : IntervalDescriptor.Map alignment.symm alignment
      (.negative source.lower) (.positive source.upper)
      (.negative targetLowerDemand) (.positive targetUpperProducer) :=
    { lower := lowerResult.adapter
      upper := upperResult.adapter }
  exact
    { origin := .push (.bounds lowerSubtyping upperSubtyping nonempty)
        source.origin
      lower := targetLowerDemand
      upper := targetUpperProducer
      descriptor := source.descriptor.map mapping }

end IntervalProducer

namespace IntervalDemand

/-- Bounds contravariance precomposes the dual recipe. Since a demand has no
`X`, this operation cannot accidentally replace a producer-selected witness. -/
def pullBounds
    {sourceView targetView : ScopeView n targetContext}
    {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
    (target : IntervalDemand sourceContext targetContext targetView targetLower
      targetUpper)
    (alignment : ScopeAlignment sourceView targetView)
    (lowerSubtyping : LambdaPFC.Tau.Sub sourceContext (.ty targetLower)
      (.ty sourceLower))
    (upperSubtyping : LambdaPFC.Tau.Sub sourceContext (.ty sourceUpper)
      (.ty targetUpper))
    (nonempty : LambdaPFC.Tau.Sub sourceContext (.ty sourceLower)
      (.ty sourceUpper))
    (lowerResult : ProperPushResult alignment.symm lowerSubtyping target.lower)
    (upperResult : ProperPullResult alignment upperSubtyping target.upper) :
    IntervalDemand sourceContext targetContext sourceView sourceLower
      sourceUpper where
  trace := .pull (.bounds lowerSubtyping upperSubtyping nonempty) target.trace
  lower := ProperPushResult.positive alignment.symm lowerSubtyping
    target.lower lowerResult
  upper := ProperPullResult.negative alignment upperSubtyping target.upper
    upperResult

/-- Satisfy a dual interval demand with any positive producer descriptor.
The result is another positive descriptor at the demand's enclosing endpoint
plans. The producer's existential `X` is retained by `IntervalDescriptor.map`.
-/
noncomputable def satisfy
    {producerView demandView : ScopeView n targetContext}
    {lowerType upperType : LambdaPFC.Ty n}
    (producer : IntervalProducer sourceContext targetContext producerView
      lowerType upperType)
    (demand : IntervalDemand sourceContext targetContext demandView lowerType
      upperType)
    (alignment : ScopeAlignment producerView demandView)
    (lower : ProperSatisfaction alignment.symm demand.lower producer.lower)
    (upper : ProperSatisfaction alignment producer.upper demand.upper) :
    IntervalDescriptor sourceContext targetContext (.positive demand.lower)
      (.negative demand.upper) := by
  let mapping : IntervalDescriptor.Map alignment.symm alignment
      (.negative producer.lower) (.positive producer.upper)
      (.positive demand.lower) (.negative demand.upper) :=
    { lower := lower.adapter
      upper := upper.adapter }
  exact producer.descriptor.map mapping

/-- Rank-2 consumer signature: the demand works for every producer view and
therefore for every producer-selected existential representation. -/
def Consumer
    (demand : IntervalDemand sourceContext targetContext demandView lowerType
      upperType) : Type :=
  {producerView : ScopeView n targetContext} ->
  (producer : IntervalProducer sourceContext targetContext producerView
    lowerType upperType) ->
  (alignment : ScopeAlignment producerView demandView) ->
  ProperSatisfaction alignment.symm demand.lower producer.lower ->
  ProperSatisfaction alignment producer.upper demand.upper ->
  IntervalDescriptor sourceContext targetContext (.positive demand.lower)
    (.negative demand.upper)

noncomputable def consumer
    (demand : IntervalDemand sourceContext targetContext demandView lowerType
      upperType) :
    Consumer demand :=
  fun producer alignment lower upper =>
    satisfy producer demand alignment lower upper

end IntervalDemand

/-! ## Focused static checks -/

noncomputable example
    (lower : PlanEndpoint sourceContext targetContext view lowerType)
    (upper : PlanEndpoint sourceContext targetContext view upperType)
    (descriptor : IntervalDescriptor sourceContext targetContext lower upper) :
    IntervalDescriptor sourceContext targetContext lower upper :=
  descriptor.map (IntervalDescriptor.Map.identity lower upper)

noncomputable example
    (descriptor : IntervalDescriptor sourceContext targetContext sourceLower
      sourceUpper)
    (first : IntervalDescriptor.Map firstLowerAlignment firstUpperAlignment
      sourceLower sourceUpper middleLower middleUpper)
    (second : IntervalDescriptor.Map secondLowerAlignment secondUpperAlignment
      middleLower middleUpper targetLower targetUpper) :
    IntervalDescriptor sourceContext targetContext targetLower targetUpper :=
  descriptor.map (first.compose second)

noncomputable example
    (producer : IntervalProducer sourceContext targetContext producerView
      lowerType upperType)
    (demand : IntervalDemand sourceContext targetContext demandView lowerType
      upperType)
    (alignment : ScopeAlignment producerView demandView)
    (lower : ProperSatisfaction alignment.symm demand.lower producer.lower)
    (upper : ProperSatisfaction alignment producer.upper demand.upper) :
    Telescope.Args targetContext
      (Pair.Interval.memberTelescope demand.lower.plan.inputTy
        demand.upper.plan.inputTy) :=
  (demand.satisfy producer alignment lower upper).memberArguments

end LambdaPToFCo.Full.TranslationModelCore
