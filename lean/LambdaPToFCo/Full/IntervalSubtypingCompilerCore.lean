import LambdaPToFCo.Full.SubtypingCompilerCore

/-!
# Full interval-subtyping compiler core

Intervals contain plan-only positive and negative endpoints rather than term
inhabitants.  This module supplies the kind-`iota` half of reflexivity,
transitivity, and satisfaction.  Lower adapters compose contravariantly;
upper adapters compose covariantly; and every positive push retains the exact
producer-selected descriptor through `IntervalPushResult.target`.
-/

namespace LambdaPToFCo.Full.IntervalSubtypingCompilerCore

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open SubtypingCompilerCore

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

/-! ## Plan-only recursive results -/

structure PositivePushResult
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType))
    (source : PositivePlan sourceContext targetContext sourceScope.view
      sourceType) : Type where
  target : PositivePlan sourceContext targetContext targetScope.view targetType
  adapter : StableIdentity.Adapter targetContext source.plan target.plan

structure NegativePullResult
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : Tau.Sub sourceContext (.ty sourceType) (.ty targetType))
    (target : NegativePlan sourceContext targetContext targetScope.view
      targetType) : Type where
  source : NegativePlan sourceContext targetContext sourceScope.view sourceType
  adapter : StableIdentity.Adapter targetContext source.plan target.plan

noncomputable def pushPositiveRefl
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view targetScope.view}
    {sourceType : LambdaPFC.Ty n}
    {source : PositivePlan sourceContext targetContext sourceScope.view
      sourceType}
    (rebase : PositiveRebase alignment source) :
    PositivePushResult alignment (Tau.Sub.refl (τ := .ty sourceType)) source :=
  { target := rebase.target
    adapter := rebase.adapter }

noncomputable def pullNegativeRefl
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view targetScope.view}
    {sourceType : LambdaPFC.Ty n}
    {target : NegativePlan sourceContext targetContext targetScope.view
      sourceType}
    (rebase : NegativeRebase alignment target) :
    NegativePullResult alignment (Tau.Sub.refl (τ := .ty sourceType)) target :=
  { source := rebase.source
    adapter := rebase.adapter }

noncomputable def composePositivePush
    {firstScope middleScope finalScope : ScopeModel sourceContext targetContext}
    {firstAlignment : ScopeAlignment firstScope.view middleScope.view}
    {secondAlignment : ScopeAlignment middleScope.view finalScope.view}
    {sourceType middleType targetType : LambdaPFC.Ty n}
    {firstSubtyping : Tau.Sub sourceContext (.ty sourceType) (.ty middleType)}
    {secondSubtyping : Tau.Sub sourceContext (.ty middleType) (.ty targetType)}
    {source : PositivePlan sourceContext targetContext firstScope.view sourceType}
    (first : PositivePushResult firstAlignment firstSubtyping source)
    (second : PositivePushResult secondAlignment secondSubtyping first.target) :
    PositivePushResult (firstAlignment.compose secondAlignment)
      (.trans firstSubtyping secondSubtyping) source where
  target := second.target
  adapter := first.adapter.compose second.adapter

noncomputable def composeNegativePull
    {firstScope middleScope finalScope : ScopeModel sourceContext targetContext}
    {firstAlignment : ScopeAlignment firstScope.view middleScope.view}
    {secondAlignment : ScopeAlignment middleScope.view finalScope.view}
    {sourceType middleType targetType : LambdaPFC.Ty n}
    {firstSubtyping : Tau.Sub sourceContext (.ty sourceType) (.ty middleType)}
    {secondSubtyping : Tau.Sub sourceContext (.ty middleType) (.ty targetType)}
    {target : NegativePlan sourceContext targetContext finalScope.view targetType}
    (second : NegativePullResult secondAlignment secondSubtyping target)
    (first : NegativePullResult firstAlignment firstSubtyping second.source) :
    NegativePullResult (firstAlignment.compose secondAlignment)
      (.trans firstSubtyping secondSubtyping) target where
  source := first.source
  adapter := first.adapter.compose second.adapter

/-! ## Kind-`iota` reflexivity -/

noncomputable def pushRefl
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {lower upper : LambdaPFC.Ty n}
    (source : IntervalProducer sourceContext targetContext sourceScope lower
      upper)
    (lowerRebase : NegativeRebase alignment.symm source.lower)
    (upperRebase : PositiveRebase alignment source.upper) :
    IntervalPushResult alignment (Tau.Sub.refl (τ := .intv lower upper))
      source where
  lower := lowerRebase.source
  upper := upperRebase.target
  lowerAdapter := lowerRebase.adapter
  upperAdapter := upperRebase.adapter

noncomputable def pullRefl
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {lower upper : LambdaPFC.Ty n}
    (target : IntervalDemand sourceContext targetContext targetScope lower upper)
    (lowerRebase : PositiveRebase alignment.symm target.lower)
    (upperRebase : NegativeRebase alignment target.upper) :
    IntervalPullResult alignment (Tau.Sub.refl (τ := .intv lower upper))
      target where
  lower := lowerRebase.target
  upper := upperRebase.source
  lowerAdapter := lowerRebase.adapter
  upperAdapter := upperRebase.adapter

/-! ## Kind-`iota` transitivity -/

noncomputable def composePush
    {firstScope middleScope finalScope : ScopeModel sourceContext targetContext}
    {firstAlignment : ScopeAlignment firstScope.view middleScope.view}
    {secondAlignment : ScopeAlignment middleScope.view finalScope.view}
    {sourceLower sourceUpper middleLower middleUpper targetLower targetUpper :
      LambdaPFC.Ty n}
    {firstSubtyping : Tau.Sub sourceContext (.intv sourceLower sourceUpper)
      (.intv middleLower middleUpper)}
    {secondSubtyping : Tau.Sub sourceContext (.intv middleLower middleUpper)
      (.intv targetLower targetUpper)}
    {source : IntervalProducer sourceContext targetContext firstScope sourceLower
      sourceUpper}
    (first : IntervalPushResult firstAlignment firstSubtyping source)
    (second : IntervalPushResult secondAlignment secondSubtyping first.target) :
    IntervalPushResult (firstAlignment.compose secondAlignment)
      (.trans firstSubtyping secondSubtyping) source where
  lower := second.lower
  upper := second.upper
  lowerAdapter := second.lowerAdapter.compose first.lowerAdapter
  upperAdapter := first.upperAdapter.compose second.upperAdapter

noncomputable def composePull
    {firstScope middleScope finalScope : ScopeModel sourceContext targetContext}
    {firstAlignment : ScopeAlignment firstScope.view middleScope.view}
    {secondAlignment : ScopeAlignment middleScope.view finalScope.view}
    {sourceLower sourceUpper middleLower middleUpper targetLower targetUpper :
      LambdaPFC.Ty n}
    {firstSubtyping : Tau.Sub sourceContext (.intv sourceLower sourceUpper)
      (.intv middleLower middleUpper)}
    {secondSubtyping : Tau.Sub sourceContext (.intv middleLower middleUpper)
      (.intv targetLower targetUpper)}
    {target : IntervalDemand sourceContext targetContext finalScope targetLower
      targetUpper}
    (second : IntervalPullResult secondAlignment secondSubtyping target)
    (first : IntervalPullResult firstAlignment firstSubtyping second.source) :
    IntervalPullResult (firstAlignment.compose secondAlignment)
      (.trans firstSubtyping secondSubtyping) target where
  lower := first.lower
  upper := first.upper
  lowerAdapter := second.lowerAdapter.compose first.lowerAdapter
  upperAdapter := first.upperAdapter.compose second.upperAdapter

/-! ## Kind-`iota` satisfaction -/

noncomputable def satisfy
    {producerScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment producerScope.view demandScope.view)
    {lower upper : LambdaPFC.Ty n}
    (producer : IntervalProducer sourceContext targetContext producerScope lower
      upper)
    (demand : IntervalDemand sourceContext targetContext demandScope lower upper)
    (lowerSatisfaction : PlanSatisfaction alignment.symm demand.lower
      producer.lower)
    (upperSatisfaction : PlanSatisfaction alignment producer.upper
      demand.upper) :
    IntervalSatisfaction alignment producer demand where
  lower := lowerSatisfaction
  upper := upperSatisfaction

/-! ## Kind-complete result eliminators -/

noncomputable def TauPushResult.target
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view targetScope.view}
    {kind : LambdaPFC.Kind} {sourceType targetType : Tau n kind}
    {subtyping : Tau.Sub sourceContext sourceType targetType}
    {source : TauProducer sourceContext targetContext sourceScope sourceType}
    (result : TauPushResult alignment subtyping source) :
    TauProducer sourceContext targetContext targetScope targetType :=
  match result with
  | .proper result => .proper result.target
  | .interval result => .interval result.target

def TauPullResult.source
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view targetScope.view}
    {kind : LambdaPFC.Kind} {sourceType targetType : Tau n kind}
    {subtyping : Tau.Sub sourceContext sourceType targetType}
    {target : TauDemand sourceContext targetContext targetScope targetType}
    (result : TauPullResult alignment subtyping target) :
    TauDemand sourceContext targetContext sourceScope sourceType :=
  match result with
  | .proper result => .proper result.source
  | .interval result => .interval result.source

end LambdaPToFCo.Full.IntervalSubtypingCompilerCore
