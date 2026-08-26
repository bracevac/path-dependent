import LambdaPToFCo.Full.IntervalPairModelV2
import LambdaPToFCo.Full.PairIntroductionCompiler

/-!
# Exact V2 interval-pair introduction provenance

This module keeps the V1 source-indexed model untouched.  A V2 positive
capability is sealed to an exact type-pair introduction, and `BoundScope`
records the honest overlay obtained by opening that package without claiming
that the V2 plan inhabits the V1 `ProducerPlanModel` family.
-/

namespace LambdaPToFCo.Full.IntervalPairIntroductionV2

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

/-- Positive V2 interval-pair shape at one exact source/target index.  Its
constructor is private; the exact introduction below is the first root. -/
structure Capability
    {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (scope : ScopeModel sourceContext targetContext)
    (sourceType : LambdaPFC.Ty n) (plan : ValuePlan sig) : Type where
  private mk ::
  firstType : LambdaPFC.Ty n
  label : LambdaPFC.Name
  lower : LambdaPFC.Ty (n + 1)
  upper : LambdaPFC.Ty (n + 1)
  source_eq : sourceType = .Pair firstType label (.intv lower upper)
  firstPlan : ValuePlan sig
  lowerPlan : ValuePlan firstPlan.scope
  upperPlan : ValuePlan firstPlan.scope
  plan_eq : plan = Pair.IntervalV2.plan firstPlan lowerPlan.inputTy
    upperPlan.inputTy
  firstModel : ProducerPlanModel sourceContext targetContext scope.view
    firstType firstPlan
  lowerModel : DemandPlanModel (sourceContext.snoc firstType)
    (firstPlan.context targetContext) (ScopeView.bindPlan scope.view firstPlan)
    lower lowerPlan
  upperModel : ProducerPlanModel (sourceContext.snoc firstType)
    (firstPlan.context targetContext) (ScopeView.bindPlan scope.view firstPlan)
    upper upperPlan
  descriptor : IntervalDescriptorV2.Descriptor
    (firstPlan.context targetContext) lowerPlan upperPlan

namespace Capability

/-- Exact `[T,T]` capability.  The retained descriptor is the same sealed
descriptor used by the concrete package result. -/
private noncomputable def exact
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    {witness : LambdaPFC.Ty n}
    (witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness)
    (result : IntervalDescriptorV2.ExactResult targetContext
      (PairIntroductionCompiler.variableSingleton scope first).plan
      witnessPlan.plan) :
    Capability sourceContext targetContext scope
      (.Pair (.Single (.var first)) label
        ((Tau.intv witness witness).weaken))
      (Pair.IntervalV2.plan
        (PairIntroductionCompiler.variableSingleton scope first).plan
        witnessPlan.plan.inputTy witnessPlan.plan.inputTy) where
  firstType := .Single (.var first)
  label := label
  lower := witness.weaken
  upper := witness.weaken
  source_eq := rfl
  firstPlan := (PairIntroductionCompiler.variableSingleton scope first).plan
  lowerPlan := witnessPlan.plan
  upperPlan := witnessPlan.plan
  plan_eq := rfl
  firstModel := (PairIntroductionCompiler.variableSingleton scope first).modeled
  lowerModel := witnessPlan.model.demand
  upperModel := witnessPlan.model.producer
  descriptor := result.descriptor

end Capability

/-- An exact direct type-pair compilation.  Construction takes no target
package, representation, coercion, or equality. -/
structure ExactTypePairResult
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness))
    (witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness) :
    Type where
  private mk ::
  exact : IntervalDescriptorV2.ExactResult targetContext
    (PairIntroductionCompiler.variableSingleton scope first).plan
    witnessPlan.plan

namespace ExactTypePairResult

noncomputable def compile
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness))
    (witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness) :
    ExactTypePairResult scope first label witnessWf witnessPlan :=
  .mk (IntervalDescriptorV2.ExactResult.make targetContext
    (PairIntroductionCompiler.variableSingleton scope first).plan
    witnessPlan.plan (scope.view first).arguments)

def firstArguments
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty n}
    {witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)}
    {witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness}
    (result : ExactTypePairResult scope first label witnessWf witnessPlan) :
    Telescope.Args targetContext
      (PairIntroductionCompiler.variableSingleton scope first).plan.telescope :=
  result.exact.firstArguments

@[simp] theorem compile_firstArguments
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    {witness : LambdaPFC.Ty n}
    (witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness))
    (witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness) :
    (compile scope first label witnessWf witnessPlan).firstArguments =
      (scope.view first).arguments := by
  rfl

def sourceType
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty n}
    {witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)}
    {witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness}
    (_result : ExactTypePairResult scope first label witnessWf witnessPlan) :
    LambdaPFC.Ty n :=
  .Pair (.Single (.var first)) label ((Tau.intv witness witness).weaken)

noncomputable def plan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty n}
    {witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)}
    {witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness}
    (_result : ExactTypePairResult scope first label witnessWf witnessPlan) :
    ValuePlan sig :=
  Pair.IntervalV2.plan
    (PairIntroductionCompiler.variableSingleton scope first).plan
    witnessPlan.plan.inputTy witnessPlan.plan.inputTy

def origin
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty n}
    {witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)}
    {witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness}
    (_result : ExactTypePairResult scope first label witnessWf witnessPlan) :
    ProducerOrigin sourceContext
      (.Pair (.Single (.var first)) label
        ((Tau.intv witness witness).weaken)) :=
  .value (Tm.Ty.tpair (y := first) (A := label) witnessWf) .pair

noncomputable def capability
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty n}
    {witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)}
    {witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness}
    (result : ExactTypePairResult scope first label witnessWf witnessPlan) :
    Capability sourceContext targetContext scope result.sourceType result.plan :=
  Capability.exact scope first label witnessPlan result.exact

noncomputable def package
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty n}
    {witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)}
    {witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness}
    (result : ExactTypePairResult scope first label witnessWf witnessPlan) :
    PathPackageZipper.CompiledPackage targetContext result.plan :=
  by
    simpa only [plan] using result.exact.package

end ExactTypePairResult

/-- The exact ordinary producer projection.  Its constructor is private, and
the package is always computed from the retained `ExactTypePairResult`. -/
structure Producer
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    (sourceType : LambdaPFC.Ty n) (plan : ValuePlan sig) : Type where
  private mk ::
  origin : ProducerOrigin sourceContext sourceType
  capability : Capability sourceContext targetContext scope sourceType plan
  package : PathPackageZipper.CompiledPackage targetContext plan

noncomputable def ExactTypePairResult.producer
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty n}
    {witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)}
    {witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness}
    (result : ExactTypePairResult scope first label witnessWf witnessPlan) :
    Producer scope result.sourceType result.plan where
  origin := result.origin
  capability := result.capability
  package := result.package

/-- Honest V2 binding overlay.  It retains the predecessor V1 scope and the
V2 producer separately; it does not claim to be a V1 `ScopeModel`. -/
structure BoundScope
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (producer : Producer scope sourceType plan) : Type where
  private mk ::
  predecessor : ScopeModel sourceContext targetContext

namespace BoundScope

noncomputable def bind
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (producer : Producer scope sourceType plan) :
    BoundScope scope producer :=
  .mk scope

noncomputable def view
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {producer : Producer scope sourceType plan}
    (_bound : BoundScope scope producer) :
    ScopeView (n + 1) (plan.context targetContext) :=
  ScopeView.bindPlan scope.view plan

noncomputable def newestInterface
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {producer : Producer scope sourceType plan}
    (bound : BoundScope scope producer) :
    ValueInterface (plan.context targetContext) :=
  bound.view 0

noncomputable def newestPackage
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {producer : Producer scope sourceType plan}
    (bound : BoundScope scope producer) :
    PathPackageZipper.CompiledPackage (plan.context targetContext)
      (plan.rename plan.telescope.weaken) := by
  simpa only [newestInterface, view, ScopeView.bindPlan_here,
    TranslationInterfaces.ValueInterface.ofArguments_plan] using
    PathPackageZipper.CompiledPackage.ofInterface bound.newestInterface

def newestTyping
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {producer : Producer scope sourceType plan}
    (_bound : BoundScope scope producer) :
    LambdaPFC.Path.Ty (sourceContext.snoc sourceType) (.var 0)
      (.ty sourceType.weaken) :=
  .var

/-- Older V1 slots are retained only through their exact predecessor model
and target-renamed interface.  No V1 model in the extended source context is
fabricated. -/
structure OlderSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {producer : Producer scope sourceType plan}
    (_bound : BoundScope scope producer) (index : Fin n) : Type where
  original : ProducerPlanModel sourceContext targetContext scope.view
    (sourceContext.lookup index) (scope.view index).plan
  interface : ValueInterface (plan.context targetContext)

noncomputable def olderSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {producer : Producer scope sourceType plan}
    (bound : BoundScope scope producer) (index : Fin n) :
    OlderSlot bound index where
  original := scope.slot index
  interface := (scope.view index).rename plan.telescope.weaken
    (plan.telescope.weaken_typed targetContext)

@[simp] theorem olderSlot_interface
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    {producer : Producer scope sourceType plan}
    (bound : BoundScope scope producer) (index : Fin n) :
    (bound.olderSlot index).interface = bound.view index.succ := by
  rfl

end BoundScope

noncomputable def ExactTypePairResult.bind
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {first : Fin n} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty n}
    {witnessWf : LambdaPFC.Tau.Wf sourceContext (.ty witness)}
    {witnessPlan : PairIntroductionCompiler.WitnessPlan scope first witness}
    (result : ExactTypePairResult scope first label witnessWf witnessPlan) :
    BoundScope scope result.producer :=
  BoundScope.bind scope result.producer

end LambdaPToFCo.Full.IntervalPairIntroductionV2
