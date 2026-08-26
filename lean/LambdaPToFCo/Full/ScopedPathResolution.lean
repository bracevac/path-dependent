import LambdaPToFCo.Full.TranslationInterfaces
import LambdaPToFCo.Full.PathPackageClosure

/-!
# Zipper-scoped path resolution

A total path translation returns its exact package or interval descriptor at
the target context where all required Church fields have actually been
opened. Returning a proper package to the root is a separate operation: the
caller must provide a certified stable adapter from the focus-local plan to
a renamed root plan. No equality between those plans is inferred from source
typing or model-instantiation coherence.
-/

namespace LambdaPToFCo.Full.ScopedPathResolution

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open PathPackageZipper

/-- Exact proper-path output at its current Church-elimination focus. The
aligned current `ScopeModel` keeps later source-variable lookups available
without fabricating interfaces in the root context. -/
structure FocusedProperPathPackage
    {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {rootSig : Sig} (rootContext : SystemFCoExt.Ctx rootSig)
    (rootScope : ScopeModel sourceContext rootContext)
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty referent)) : Type where
  currentSig : Sig
  currentContext : SystemFCoExt.Ctx currentSig
  zipper : ResultZipper rootContext currentContext
  currentScope : ScopeModel sourceContext currentContext
  scopeAlignment : ScopeAlignment
    (rootScope.view.rename zipper.weakening zipper.weakeningTyped)
    currentScope.view
  plan : ValuePlan currentSig
  modeled : ProducerPlanModel sourceContext currentContext currentScope.view
    referent plan
  package : PathPackageZipper.CompiledPackage currentContext plan

namespace FocusedProperPathPackage

/-- Forget only the source model and expose the low zipper result. -/
noncomputable def toPathResult
    (result : FocusedProperPathPackage sourceContext rootContext rootScope
      precise) : PathResult rootContext where
  currentSig := result.currentSig
  currentContext := result.currentContext
  zipper := result.zipper
  plan := result.plan
  package := result.package

/-- The exact additional evidence required to recover the existing
root-scoped `ProperPathPackage` ABI. The root plan is structurally certified;
the focus-local adapter is a computational obligation, not a derived plan
equality. -/
structure RootAdaptation
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    {rootScope : ScopeModel sourceContext rootContext}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.ty referent)}
    (result : FocusedProperPathPackage sourceContext rootContext rootScope
      precise) : Type where
  rootModel : Sigma fun rootPlan : ValuePlan rootSig =>
    ProducerPlanModel sourceContext rootContext rootScope.view referent rootPlan
  adapter : StableIdentity.Adapter result.currentContext result.plan
    (rootModel.1.rename result.zipper.weakening)

/-- First adapt the focused package to a renamed root plan, then discharge
all retained Church eliminations with `PathResult.close`. -/
noncomputable def close
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    {rootScope : ScopeModel sourceContext rootContext}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.ty referent)}
    (result : FocusedProperPathPackage sourceContext rootContext rootScope
      precise)
    (adaptation : RootAdaptation result) :
    ProperPathPackage sourceContext rootContext rootScope precise := by
  let adaptedPackage : PathPackageZipper.CompiledPackage result.currentContext
      (adaptation.rootModel.1.rename result.zipper.weakening) :=
    TranslationInterfaces.CompiledPackage.adapt result.package
      adaptation.adapter
  let adaptedResult : PathResult rootContext :=
    { currentSig := result.currentSig
      currentContext := result.currentContext
      zipper := result.zipper
      plan := adaptation.rootModel.1.rename result.zipper.weakening
      package := adaptedPackage }
  exact
    { model := adaptation.rootModel
      package := adaptedResult.close adaptation.rootModel.1 rfl }

end FocusedProperPathPackage

/-- Exact interval-path output at its current Church-elimination focus. The
selected representation remains existential inside `descriptor`. The lower
endpoint is negative and the upper endpoint positive. Raw `Path.Ty` supplies
neither the opposite model polarities nor the nonempty bound proof required
by `IntervalProducerOrigin`, so neither is stored here. -/
structure FocusedIntervalPathTranslation
    {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {rootSig : Sig} (rootContext : SystemFCoExt.Ctx rootSig)
    (rootScope : ScopeModel sourceContext rootContext)
    {path : LambdaPFC.Path n} {lower upper : LambdaPFC.Ty n}
    (precise : LambdaPFC.Path.Ty sourceContext path (.intv lower upper)) : Type where
  currentSig : Sig
  currentContext : SystemFCoExt.Ctx currentSig
  zipper : ResultZipper rootContext currentContext
  currentScope : ScopeModel sourceContext currentContext
  scopeAlignment : ScopeAlignment
    (rootScope.view.rename zipper.weakening zipper.weakeningTyped)
    currentScope.view
  lower : NegativePlan sourceContext currentContext currentScope.view lower
  upper : PositivePlan sourceContext currentContext currentScope.view upper
  descriptor : TranslationModelCore.IntervalDescriptor sourceContext
    currentContext (.negative lower.toCore) (.positive upper.toCore)

namespace FocusedIntervalPathTranslation

/-- Explicit extra evidence needed to upgrade an exact positive interval path
to the stronger bidirectional endpoint contract used by Wf-plan synthesis.
Neither field follows from the path producer itself. -/
structure BidirectionalUpgrade
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    {rootScope : ScopeModel sourceContext rootContext}
    {path : LambdaPFC.Path n} {lower upper : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.intv lower upper)}
    (result : FocusedIntervalPathTranslation sourceContext rootContext
      rootScope precise) : Type where
  lowerPositive : ProducerPlanModel sourceContext result.currentContext
    result.currentScope.view lower result.lower.plan
  upperNegative : DemandPlanModel sourceContext result.currentContext
    result.currentScope.view upper result.upper.plan

def BidirectionalUpgrade.lowerModel
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    {rootScope : ScopeModel sourceContext rootContext}
    {path : LambdaPFC.Path n} {lower upper : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.intv lower upper)}
    {result : FocusedIntervalPathTranslation sourceContext rootContext
      rootScope precise}
    (upgrade : BidirectionalUpgrade result) :
    BidirectionalPlanModel sourceContext result.currentContext
      result.currentScope.view lower result.lower.plan :=
  .both upgrade.lowerPositive result.lower.modeled

def BidirectionalUpgrade.upperModel
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    {rootScope : ScopeModel sourceContext rootContext}
    {path : LambdaPFC.Path n} {lower upper : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.intv lower upper)}
    {result : FocusedIntervalPathTranslation sourceContext rootContext
      rootScope precise}
    (upgrade : BidirectionalUpgrade result) :
    BidirectionalPlanModel sourceContext result.currentContext
      result.currentScope.view upper result.upper.plan :=
  .both result.upper.modeled upgrade.upperNegative

/-- The separate source-origin obligation needed when a consumer wants the
high `IntervalProducer` ABI. In the selection case its `nonempty` proof comes
from Wf/subtyping, not from raw path typing. -/
structure ProducerUpgrade
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    {rootScope : ScopeModel sourceContext rootContext}
    {path : LambdaPFC.Path n} {lower upper : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.intv lower upper)}
    (result : FocusedIntervalPathTranslation sourceContext rootContext
      rootScope precise) : Type where
  origin : IntervalProducerOrigin sourceContext lower upper

def ProducerUpgrade.producer
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {rootSig : Sig} {rootContext : SystemFCoExt.Ctx rootSig}
    {rootScope : ScopeModel sourceContext rootContext}
    {path : LambdaPFC.Path n} {lower upper : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.intv lower upper)}
    {result : FocusedIntervalPathTranslation sourceContext rootContext
      rootScope precise}
    (upgrade : ProducerUpgrade result) :
    IntervalProducer sourceContext result.currentContext result.currentScope
      lower upper where
  origin := upgrade.origin
  lower := result.lower
  upper := result.upper
  descriptor := result.descriptor

end FocusedIntervalPathTranslation

/-- Honest path-compiler boundary. Neither method promises that a dependent
focus-local plan can be named at the root. Consumers continue under the
returned zipper or supply an explicit root adaptation. -/
structure Resolver : Type where
  proper :
    {n : Nat} -> {sourceContext : LambdaPFC.Ctx n} ->
    {rootSig : Sig} -> {rootContext : SystemFCoExt.Ctx rootSig} ->
    (rootScope : ScopeModel sourceContext rootContext) ->
    {path : LambdaPFC.Path n} -> {referent : LambdaPFC.Ty n} ->
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty referent)) ->
    FocusedProperPathPackage sourceContext rootContext rootScope precise
  interval :
    {n : Nat} -> {sourceContext : LambdaPFC.Ctx n} ->
    {rootSig : Sig} -> {rootContext : SystemFCoExt.Ctx rootSig} ->
    (rootScope : ScopeModel sourceContext rootContext) ->
    {path : LambdaPFC.Path n} -> {lower upper : LambdaPFC.Ty n} ->
    (precise : LambdaPFC.Path.Ty sourceContext path (.intv lower upper)) ->
    FocusedIntervalPathTranslation sourceContext rootContext rootScope precise

end LambdaPToFCo.Full.ScopedPathResolution
