import LambdaPToFCo.Full.IntervalPairIntroductionV2

/-!
# Exact first-component widening for V2 interval pairs

This rule is deliberately narrow: it consumes an exact V2 type-pair result,
the literal resolved-variable widening, and target endpoint evidence at the
already chosen endpoint plan.  The target package plan is unchanged, so the
descriptor and package certificate are retained rather than reconstructed.
-/

namespace LambdaPToFCo.Full.IntervalPairFirstWidenV2

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
variable {scope : ScopeModel sourceContext targetContext}
variable {first : Fin n} {label : LambdaPFC.Name}
variable {witness : LambdaPFC.Ty n}
variable {witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)}
variable {witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness}
variable {source : IntervalPairIntroductionV2.ExactTypePairResult scope first
  label witnessWf witnessPlan}
variable {referent : LambdaPFC.Ty n}
variable {precise : LambdaPFC.Path.Ty sourceContext (.var first) (.ty referent)}
variable {targetEndpoint : BidirectionalPlanModel
  (sourceContext.snoc referent)
  (source.capability.firstPlan.context targetContext)
  (ScopeView.bindPlan scope.view source.capability.firstPlan)
  witness.weaken witnessPlan.plan}

/-- Sealed literal `.pair (.widen precise) .refl` result. -/
structure Result
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness))
    (witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness)
    (source : IntervalPairIntroductionV2.ExactTypePairResult scope first label
      witnessWf witnessPlan)
    {referent : LambdaPFC.Ty n}
    (precise : LambdaPFC.Path.Ty sourceContext (.var first) (.ty referent))
    (targetEndpoint : BidirectionalPlanModel
      (sourceContext.snoc referent)
      (source.capability.firstPlan.context targetContext)
      (ScopeView.bindPlan scope.view source.capability.firstPlan)
      witness.weaken witnessPlan.plan) : Type where
  private mk ::
  exactSource : IntervalPairIntroductionV2.ExactTypePairResult scope first
    label witnessWf witnessPlan
  sourceType : LambdaPFC.Ty n
  targetType : LambdaPFC.Ty n
  plan : ValuePlan sig
  subtyping : LambdaPFC.Tau.Sub sourceContext (.ty sourceType)
    (.ty targetType)
  origin : ProducerOrigin sourceContext targetType
  adapter : StableIdentity.Adapter targetContext plan plan
  package : PathPackageZipper.CompiledPackage targetContext plan
  firstModel : ProducerPlanModel sourceContext targetContext scope.view
    referent source.capability.firstPlan

namespace Result

noncomputable def compile
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness))
    (witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness)
    (source : IntervalPairIntroductionV2.ExactTypePairResult scope first label
      witnessWf witnessPlan)
    {referent : LambdaPFC.Ty n}
    (precise : LambdaPFC.Path.Ty sourceContext (.var first) (.ty referent))
    (targetEndpoint : BidirectionalPlanModel
      (sourceContext.snoc referent)
      (source.capability.firstPlan.context targetContext)
      (ScopeView.bindPlan scope.view source.capability.firstPlan)
      witness.weaken witnessPlan.plan) :
    Result scope first label witnessWf witnessPlan source precise
      targetEndpoint := by
  let sourceType := source.sourceType
  let targetType : LambdaPFC.Ty n :=
    .Pair referent label ((Tau.intv witness witness).weaken)
  let subtyping : LambdaPFC.Tau.Sub sourceContext (.ty sourceType)
      (.ty targetType) := by
    simpa only [sourceType, targetType,
      IntervalPairIntroductionV2.ExactTypePairResult.sourceType] using
      (LambdaPFC.Tau.Sub.pair (LambdaPFC.Tau.Sub.widen precise)
        (LambdaPFC.Tau.Sub.refl : LambdaPFC.Tau.Sub
          (sourceContext.snoc (.Single (.var first)))
          (.intv witness.weaken witness.weaken)
          (.intv witness.weaken witness.weaken)))
  let adapter := StableIdentity.Adapter.identity targetContext source.plan
  refine
    { exactSource := source
      sourceType := sourceType
      targetType := targetType
      plan := source.plan
      subtyping := subtyping
      origin := .push subtyping source.origin
      adapter := adapter
      package := TranslationInterfaces.CompiledPackage.adapt source.package
        adapter
      firstModel := ?_ }
  cases precise
  exact scope.slot first

end Result

/-- Target positive capability.  Its descriptor is inherited only from the
sealed exact source certificate. -/
structure Capability
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty n}
    {witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)}
    {witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness}
    {source : IntervalPairIntroductionV2.ExactTypePairResult scope first label
      witnessWf witnessPlan}
    {referent : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext (.var first) (.ty referent)}
    {targetEndpoint : BidirectionalPlanModel
      (sourceContext.snoc referent)
      (source.capability.firstPlan.context targetContext)
      (ScopeView.bindPlan scope.view source.capability.firstPlan)
      witness.weaken witnessPlan.plan}
    (result : Result scope first label witnessWf witnessPlan source precise
      targetEndpoint) : Type where
  private mk ::
  firstModel : ProducerPlanModel sourceContext targetContext scope.view
    referent source.capability.firstPlan
  endpointModel : BidirectionalPlanModel (sourceContext.snoc referent)
    (source.capability.firstPlan.context targetContext)
    (ScopeView.bindPlan scope.view source.capability.firstPlan)
    witness.weaken witnessPlan.plan

namespace Capability

variable {result : Result scope first label witnessWf witnessPlan source precise
  targetEndpoint}

noncomputable def make
    (result : Result scope first label witnessWf witnessPlan source precise
      targetEndpoint) : Capability result where
  firstModel := result.firstModel
  endpointModel := targetEndpoint

noncomputable def descriptor
    (_capability : Capability result) : IntervalDescriptorV2.Descriptor
      (source.capability.firstPlan.context targetContext)
      witnessPlan.plan witnessPlan.plan :=
  source.capability.descriptor

end Capability

noncomputable def Result.capability
    (result : Result scope first label witnessWf witnessPlan source precise
      targetEndpoint) : Capability result :=
  Capability.make result

/-- The adapted producer is indexed by the complete sealed widening result;
clients cannot replace its origin, descriptor, adapter, or package. -/
structure Producer
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty n}
    {witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)}
    {witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness}
    {source : IntervalPairIntroductionV2.ExactTypePairResult scope first label
      witnessWf witnessPlan}
    {referent : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext (.var first) (.ty referent)}
    {targetEndpoint : BidirectionalPlanModel
      (sourceContext.snoc referent)
      (source.capability.firstPlan.context targetContext)
      (ScopeView.bindPlan scope.view source.capability.firstPlan)
      witness.weaken witnessPlan.plan}
    (result : Result scope first label witnessWf witnessPlan source precise
      targetEndpoint) : Type where
  private mk ::
  sealed : Unit

namespace Producer

variable {result : Result scope first label witnessWf witnessPlan source precise
  targetEndpoint}

noncomputable def make
    (result : Result scope first label witnessWf witnessPlan source precise
      targetEndpoint) : Producer result :=
  .mk ()

def origin (_producer : Producer result) :
    ProducerOrigin sourceContext result.targetType :=
  result.origin

noncomputable def capability (_producer : Producer result) :
    Capability result :=
  result.capability

noncomputable def package (_producer : Producer result) :
    PathPackageZipper.CompiledPackage targetContext result.plan :=
  result.package

end Producer

noncomputable def Result.producer
    (result : Result scope first label witnessWf witnessPlan source precise
      targetEndpoint) : Producer result :=
  Producer.make result

/-- Honest bound overlay for the widened source type. -/
structure BoundScope
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty n}
    {witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)}
    {witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness}
    {source : IntervalPairIntroductionV2.ExactTypePairResult scope first label
      witnessWf witnessPlan}
    {referent : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext (.var first) (.ty referent)}
    {targetEndpoint : BidirectionalPlanModel
      (sourceContext.snoc referent)
      (source.capability.firstPlan.context targetContext)
      (ScopeView.bindPlan scope.view source.capability.firstPlan)
      witness.weaken witnessPlan.plan}
    (result : Result scope first label witnessWf witnessPlan source precise
      targetEndpoint)
    (producer : Producer result) : Type where
  private mk ::
  predecessor : ScopeModel sourceContext targetContext

namespace BoundScope

variable {result : Result scope first label witnessWf witnessPlan source precise
  targetEndpoint}
variable {producer : Producer result}

noncomputable def bind
    (result : Result scope first label witnessWf witnessPlan source precise
      targetEndpoint) : BoundScope result result.producer :=
  .mk scope

noncomputable def view
    (_bound : BoundScope result producer) :
    ScopeView (n + 1) (result.plan.context targetContext) :=
  ScopeView.bindPlan scope.view result.plan

noncomputable def newestInterface
    (bound : BoundScope result producer) :
    ValueInterface (result.plan.context targetContext) :=
  bound.view 0

noncomputable def newestPackage
    (bound : BoundScope result producer) :
    PathPackageZipper.CompiledPackage (result.plan.context targetContext)
      (result.plan.rename result.plan.telescope.weaken) := by
  simpa only [newestInterface, view, ScopeView.bindPlan_here,
    TranslationInterfaces.ValueInterface.ofArguments_plan] using
    PathPackageZipper.CompiledPackage.ofInterface bound.newestInterface

def newestTyping
    (_bound : BoundScope result producer) :
    LambdaPFC.Path.Ty (sourceContext.snoc result.targetType) (.var 0)
      (.ty result.targetType.weaken) :=
  .var

structure OlderSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty n}
    {witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)}
    {witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness}
    {source : IntervalPairIntroductionV2.ExactTypePairResult scope first label
      witnessWf witnessPlan}
    {referent : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext (.var first) (.ty referent)}
    {targetEndpoint : BidirectionalPlanModel
      (sourceContext.snoc referent)
      (source.capability.firstPlan.context targetContext)
      (ScopeView.bindPlan scope.view source.capability.firstPlan)
      witness.weaken witnessPlan.plan}
    {result : Result scope first label witnessWf witnessPlan source precise
      targetEndpoint}
    {producer : Producer result}
    (_bound : BoundScope result producer) (index : Fin n) : Type where
  original : ProducerPlanModel sourceContext targetContext scope.view
    (sourceContext.lookup index) (scope.view index).plan
  interface : ValueInterface (result.plan.context targetContext)

noncomputable def olderSlot
    (bound : BoundScope result producer) (index : Fin n) :
    OlderSlot bound index where
  original := scope.slot index
  interface := (scope.view index).rename result.plan.telescope.weaken
    (result.plan.telescope.weaken_typed targetContext)

@[simp] theorem olderSlot_interface
    (bound : BoundScope result producer) (index : Fin n) :
    (bound.olderSlot index).interface = bound.view index.succ := by
  rfl

end BoundScope

noncomputable def Result.bind
    (result : Result scope first label witnessWf witnessPlan source precise
      targetEndpoint) : BoundScope result result.producer :=
  BoundScope.bind result

end LambdaPToFCo.Full.IntervalPairFirstWidenV2
