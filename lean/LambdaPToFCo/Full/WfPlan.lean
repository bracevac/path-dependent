import LambdaPToFCo.Full.TranslationInterfaces

/-!
# Canonical certified plans from full source well-formedness

Structural `Tau.Wf` constructors determine one bidirectional target plan once
precisely typed paths have been translated. Path and selection cases are
therefore supplied by a proof-relevant `Resolver`: its proper method returns
the exact `ProperPathPackage`, and its interval method returns the exact
hidden descriptor and both endpoint models for that `Path.Ty` derivation.

The theorem is deliberately conditional on this resolver until the total
path translation layer lands. No Wf evidence is requested for arbitrary
subtyping middles.
-/

namespace LambdaPToFCo.Full.WfPlan

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

/-- Exact target descriptor synthesized for one precisely typed interval
path. Endpoint models are bidirectional at the same plans used by the hidden
positive descriptor; the selected representation remains existential. -/
inductive IntervalPathTranslation
    {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (scope : ScopeModel sourceContext targetContext)
    {path : LambdaPFC.Path n} {lower upper : LambdaPFC.Ty n}
    (precise : LambdaPFC.Path.Ty sourceContext path (.intv lower upper)) :
    Type where
  | resolved
      (lowerPlan upperPlan : ValuePlan sig)
      (lowerModel : BidirectionalPlanModel sourceContext targetContext
        scope.view lower lowerPlan)
      (upperModel : BidirectionalPlanModel sourceContext targetContext
        scope.view upper upperPlan)
      (descriptor : TranslationModelCore.IntervalDescriptor sourceContext
        targetContext
        (.negative
          ({ plan := lowerPlan } : TranslationModelCore.NegativePlan
            sourceContext targetContext scope.view lower))
        (.positive
          ({ plan := upperPlan } : TranslationModelCore.PositivePlan
            sourceContext targetContext scope.view upper))) :
      IntervalPathTranslation sourceContext targetContext scope precise

/-- The sole non-structural input to Wf plan construction. A future total
path compiler implements this record; arbitrary target plans do not satisfy
either method. -/
structure Resolver : Type where
  proper :
    {n : Nat} -> {sourceContext : LambdaPFC.Ctx n} ->
    {sig : Sig} -> {targetContext : SystemFCoExt.Ctx sig} ->
    (scope : ScopeModel sourceContext targetContext) ->
    {path : LambdaPFC.Path n} -> {referent : LambdaPFC.Ty n} ->
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty referent)) ->
    ProperPathPackage sourceContext targetContext scope precise
  interval :
    {n : Nat} -> {sourceContext : LambdaPFC.Ctx n} ->
    {sig : Sig} -> {targetContext : SystemFCoExt.Ctx sig} ->
    (scope : ScopeModel sourceContext targetContext) ->
    {path : LambdaPFC.Path n} -> {lower upper : LambdaPFC.Ty n} ->
    (precise : LambdaPFC.Path.Ty sourceContext path (.intv lower upper)) ->
    IntervalPathTranslation sourceContext targetContext scope precise

/-- Canonical bidirectional model for a well-formed proper type. -/
structure Proper
    {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (scope : ScopeModel sourceContext targetContext)
    (sourceType : LambdaPFC.Ty n) : Type where
  wf : LambdaPFC.Tau.Wf sourceContext (.ty sourceType)
  plan : ValuePlan sig
  model : BidirectionalPlanModel sourceContext targetContext scope.view
    sourceType plan

namespace Proper

def positive
    (result : Proper sourceContext targetContext scope sourceType) :
    PositivePlan sourceContext targetContext scope.view sourceType where
  model := ⟨result.plan, result.model.producer⟩

def negative
    (result : Proper sourceContext targetContext scope sourceType) :
    NegativePlan sourceContext targetContext scope.view sourceType where
  model := ⟨result.plan, result.model.demand⟩

/-- Canonical demand root justified by the stored source Wf derivation. -/
def demand
    (result : Proper sourceContext targetContext scope sourceType) :
    ProperDemand sourceContext targetContext scope sourceType where
  trace := DemandTrace.ofWf result.wf
  model := ⟨result.plan, result.model.demand⟩

end Proper

/-- Canonical bidirectional external endpoint plans for a well-formed
interval. No selected representation is chosen here. -/
structure Interval
    {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (scope : ScopeModel sourceContext targetContext)
    (lower upper : LambdaPFC.Ty n) : Type where
  wf : LambdaPFC.Tau.Wf sourceContext (.intv lower upper)
  lowerPlan : ValuePlan sig
  upperPlan : ValuePlan sig
  model : IntervalBidirectionalPlanModel sourceContext targetContext scope.view
    lower upper lowerPlan upperPlan

namespace Interval

def positive
    (result : Interval sourceContext targetContext scope lower upper) :
    IntervalProducerPlanModel sourceContext targetContext scope.view lower upper
      result.lowerPlan result.upperPlan :=
  result.model.producer

def negative
    (result : Interval sourceContext targetContext scope lower upper) :
    IntervalDemandPlanModel sourceContext targetContext scope.view lower upper
      result.lowerPlan result.upperPlan :=
  result.model.demand

/-- Canonical witness-free interval demand rooted in Wf. -/
def demand
    (result : Interval sourceContext targetContext scope lower upper) :
    IntervalDemand sourceContext targetContext scope lower upper :=
  match result.model with
  | .both _ (.bounds lowerModel upperModel) =>
      { trace := IntervalDemandTrace.ofWf result.wf
        lower := { model := ⟨result.lowerPlan, lowerModel⟩ }
        upper := { model := ⟨result.upperPlan, upperModel⟩ } }

end Interval

/-! ## Canonical constructor roots -/

def Proper.bottom
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) :
    Proper sourceContext targetContext scope .Bot where
  wf := .bot
  plan := Bot.plan sig
  model := .both .bottom .bottom

def Proper.top
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) :
    Proper sourceContext targetContext scope .Top where
  wf := .top
  plan := Top.plan sig
  model := .both .top (.opaque .Top)

/-- Demand-local singleton Wf reuses one exact already-translated path
package. This is sufficient for callers that resolve only the path required by
their current constructor and does not demand a global `Resolver`. -/
def Proper.singletonFromPathPackage
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty referent))
    (translated : ProperPathPackage sourceContext targetContext scope
      precise) :
    Proper sourceContext targetContext scope (.Single path) :=
  { wf := .path precise
    plan := translated.plan
    model := .both
      (.singleton precise translated.modeled)
      (.singleton precise translated.modeled) }

/-- Convenience wrapper that obtains the exact path package from a total
resolver. -/
def Proper.singleton
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (resolver : Resolver) (scope : ScopeModel sourceContext targetContext)
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty referent)) :
    Proper sourceContext targetContext scope (.Single path) :=
  Proper.singletonFromPathPackage scope precise (resolver.proper scope precise)

/-- Selection Wf opens only the exact descriptor translated for the selected
path. Its hidden representation becomes the selected plan and never escapes
as a resolver-supplied free identity. -/
noncomputable def Proper.selection
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (resolver : Resolver) (scope : ScopeModel sourceContext targetContext)
    {path : LambdaPFC.Path n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty n}
    (precise : LambdaPFC.Path.Ty sourceContext (.sel path label)
      (.intv lower upper))
    (nonempty : LambdaPFC.Tau.Sub sourceContext (.ty lower) (.ty upper)) :
    Proper sourceContext targetContext scope (.TSel path label) :=
  match resolver.interval scope precise with
  | .resolved lowerPlan upperPlan lowerModel upperModel
      (.selected representation lowerToSelected selectedToUpper) =>
      let origin : SelectionOrigin sourceContext path label :=
        { lower := lower
          upper := upper
          precise := precise
          nonempty := nonempty }
      let bounds : IntervalDemandPlanModel sourceContext targetContext
          scope.view lower upper lowerPlan upperPlan :=
        .bounds lowerModel.producer upperModel.demand
      let selected : SelectionPlanModel sourceContext targetContext scope.view
          origin (Selection.plan representation) :=
        .between bounds lowerToSelected selectedToUpper
      { wf := .sel precise nonempty
        plan := Selection.plan representation
        model := .both (.selection selected) (.selection selected) }

/-- Function Wf fixes one bidirectional domain plan and recurses under its
positive opened scope for both codomain polarities. -/
noncomputable def Proper.function
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {domain : LambdaPFC.Ty n} {codomain : LambdaPFC.Ty (n + 1)}
    (domainResult : Proper sourceContext targetContext scope domain)
    (codomainResult : Proper (sourceContext.snoc domain)
      (domainResult.plan.context targetContext)
      (scope.bindBidirectional domainResult.model) codomain) :
    Proper sourceContext targetContext scope (.Fun domain codomain) where
  wf := .fun domainResult.wf codomainResult.wf
  plan := Function.plan domainResult.plan codomainResult.plan
  model := .both
    (.function domainResult.model codomainResult.model.producer)
    (.function domainResult.model.producer codomainResult.model.demand)

/-- Proper-pair Wf shares the first bidirectional plan across the dependent
member scope. -/
noncomputable def Proper.properPair
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {first : LambdaPFC.Ty n} {label : LambdaPFC.Name}
    {member : LambdaPFC.Ty (n + 1)}
    (firstResult : Proper sourceContext targetContext scope first)
    (memberResult : Proper (sourceContext.snoc first)
      (firstResult.plan.context targetContext)
      (scope.bindBidirectional firstResult.model) member) :
    Proper sourceContext targetContext scope
      (.Pair first label (.ty member)) where
  wf := .pair firstResult.wf memberResult.wf
  plan := Pair.Proper.plan firstResult.plan memberResult.plan
  model := .both
    (.properPair firstResult.model.producer memberResult.model.producer)
    (.properPair firstResult.model memberResult.model)

/-- Interval-pair Wf retains a bidirectional interval member descriptor at
the exact endpoint plans chosen under the first component. -/
noncomputable def Proper.intervalPair
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {first : LambdaPFC.Ty n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty (n + 1)}
    (firstResult : Proper sourceContext targetContext scope first)
    (memberResult : Interval (sourceContext.snoc first)
      (firstResult.plan.context targetContext)
      (scope.bindBidirectional firstResult.model) lower upper) :
    Proper sourceContext targetContext scope
      (.Pair first label (.intv lower upper)) where
  wf := .pair firstResult.wf memberResult.wf
  plan := Pair.Interval.plan firstResult.plan memberResult.lowerPlan.inputTy
    memberResult.upperPlan.inputTy
  model := .both
    (.intervalPair firstResult.model.producer memberResult.model.producer)
    (.intervalPair firstResult.model memberResult.model)

/-- Interval Wf chooses only endpoint plans. The nonempty source proof is
retained in Wf; compiling its package adapters belongs to subtyping. -/
def Interval.bounds
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {lower upper : LambdaPFC.Ty n}
    (lowerResult : Proper sourceContext targetContext scope lower)
    (upperResult : Proper sourceContext targetContext scope upper)
    (nonempty : LambdaPFC.Tau.Sub sourceContext (.ty lower) (.ty upper)) :
    Interval sourceContext targetContext scope lower upper where
  wf := .bounds_wf lowerResult.wf upperResult.wf nonempty
  lowerPlan := lowerResult.plan
  upperPlan := upperResult.plan
  model := .both
    (.bounds lowerResult.model.demand upperResult.model.producer)
    (.bounds lowerResult.model.producer upperResult.model.demand)

/-- Kind-complete result of Wf plan construction. -/
inductive Result
    {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (scope : ScopeModel sourceContext targetContext) :
    {kind : LambdaPFC.Kind} -> LambdaPFC.Tau n kind -> Type where
  | proper
      (result : Proper sourceContext targetContext scope sourceType) :
      Result sourceContext targetContext scope (.ty sourceType)
  | interval
      (result : Interval sourceContext targetContext scope lower upper) :
      Result sourceContext targetContext scope (.intv lower upper)

private def depth (wf : LambdaPFC.Tau.Wf sourceContext source) : Nat :=
  match wf with
  | .bot => 1
  | .top => 1
  | .path _ => 1
  | .sel _ _ => 1
  | .fun domain codomain => depth domain + depth codomain + 1
  | .pair first member => depth first + depth member + 1
  | .bounds_wf lower upper _ => depth lower + depth upper + 1

/-- Constructor-complete Wf plan translation, conditional only on exact path
translation. Recursive calls follow the Wf derivation and never inspect a
subtyping middle. -/
noncomputable def withResolver
    (resolver : Resolver)
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) :
    {kind : LambdaPFC.Kind} -> {source : LambdaPFC.Tau n kind} ->
    (wf : LambdaPFC.Tau.Wf sourceContext source) ->
    Result sourceContext targetContext scope source
  | _, _, .bot => .proper (.bottom scope)
  | _, _, .top => .proper (.top scope)
  | _, _, .path precise => .proper (.singleton resolver scope precise)
  | _, _, .sel precise nonempty =>
      .proper (.selection resolver scope precise nonempty)
  | _, _, .fun domainWf codomainWf =>
      match withResolver resolver scope domainWf with
      | .proper domainResult =>
          match withResolver resolver
              (scope.bindBidirectional domainResult.model) codomainWf with
          | .proper codomainResult =>
              .proper (.function scope domainResult codomainResult)
  | _, _, .pair firstWf memberWf =>
      match withResolver resolver scope firstWf with
      | .proper firstResult =>
          match withResolver resolver
              (scope.bindBidirectional firstResult.model) memberWf with
          | .proper memberResult =>
              .proper (.properPair scope firstResult memberResult)
          | .interval memberResult =>
              .proper (.intervalPair scope firstResult memberResult)
  | _, _, .bounds_wf lowerWf upperWf nonempty =>
      match withResolver resolver scope lowerWf,
          withResolver resolver scope upperWf with
      | .proper lowerResult, .proper upperResult =>
          .interval (.bounds scope lowerResult upperResult nonempty)
termination_by kind source wf => depth wf
decreasing_by all_goals simp [depth] <;> omega

/-- Proper-specialized projection of `withResolver`. -/
noncomputable def properWithResolver
    (resolver : Resolver)
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n}
    (wf : LambdaPFC.Tau.Wf sourceContext (.ty sourceType)) :
    Proper sourceContext targetContext scope sourceType := by
  cases withResolver resolver scope wf with
  | proper result => exact result

/-- Interval-specialized projection of `withResolver`. -/
noncomputable def intervalWithResolver
    (resolver : Resolver)
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {lower upper : LambdaPFC.Ty n}
    (wf : LambdaPFC.Tau.Wf sourceContext (.intv lower upper)) :
    Interval sourceContext targetContext scope lower upper := by
  cases withResolver resolver scope wf with
  | interval result => exact result

end LambdaPToFCo.Full.WfPlan
