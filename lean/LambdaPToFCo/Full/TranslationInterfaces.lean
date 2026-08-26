import LambdaPToFCo.Full.FunctionInterface
import LambdaPToFCo.Full.OriginConstruction
import LambdaPToFCo.Full.PairInterface
import LambdaPToFCo.Full.PathPackageZipper
import LambdaPToFCo.Full.StableIdentityReduction
import LambdaPToFCo.Full.TranslationModelCore

/-!
# Sealed full-translation interfaces

This module is the source-indexed public boundary above
`TranslationModelCore`. Plans are projections of closed structural model
evidence; callers cannot supply a free target plan. Compiled packages are
kept separate from opened value interfaces, and source variables are tracked
by a `ScopeModel` which certifies every target slot.

This is a carrier layer, not yet the term/path compiler correctness theorem.
It certifies source-indexed plan shape and target typing; the later compiler
layer must additionally show that each package was generated from its stated
source origin. In particular, exact singleton/path package aliasing is exposed
by `ProperPathPackage.singletonProducer` rather than inferred from target
typing alone.

Ordinary and absurd producers are distinct. The ordinary operational record
requires an actual reduction to ready interfaces. The absurd branch retains
only its Bottom package and makes no open-context reduction claim.
-/

namespace LambdaPToFCo.Full.TranslationInterfaces

open LambdaPFC
open SystemFCoExt

namespace ScopeView

/-- Open one complete target plan and install its canonical opened interface
as the newest source slot. -/
noncomputable def bindPlan
    {n : Nat} {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (view : ScopeView n base) (plan : ValuePlan sig) :
    ScopeView (n + 1) (plan.context base) :=
  (view.rename plan.telescope.weaken
      (plan.telescope.weaken_typed base)).snocExisting
    (ValueInterface.ofArguments (plan.rename plan.telescope.weaken)
      (Telescope.Args.identity plan.telescope base))

@[simp] theorem bindPlan_here
    {n : Nat} {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (view : ScopeView n base) (plan : ValuePlan sig) :
    bindPlan view plan 0 =
      ValueInterface.ofArguments (plan.rename plan.telescope.weaken)
        (Telescope.Args.identity plan.telescope base) := by
  rfl

@[simp] theorem bindPlan_there
    {n : Nat} {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (view : ScopeView n base) (plan : ValuePlan sig) (index : Fin n) :
    bindPlan view plan index.succ =
      (view index).rename plan.telescope.weaken
        (plan.telescope.weaken_typed base) := by
  rfl

end ScopeView

/-! ## Closed structural plan models -/

mutual

/-- Positive structural meaning of a proper source type at one target plan.
The relation contains plans only; target expressions and opened interfaces
live in the separate package layer below. -/
inductive ProducerPlanModel :
    {n : Nat} -> (sourceContext : LambdaPFC.Ctx n) ->
    {sig : Sig} -> (targetContext : SystemFCoExt.Ctx sig) ->
    (view : ScopeView n targetContext) ->
    (sourceType : LambdaPFC.Ty n) -> ValuePlan sig -> Type where
  | bottom :
      ProducerPlanModel sourceContext targetContext view .Bot (Bot.plan _)
  | top :
      ProducerPlanModel sourceContext targetContext view .Top (Top.plan _)
  | singleton
      (precise : LambdaPFC.Path.Ty sourceContext path (.ty referent))
      (referentModel : ProducerPlanModel sourceContext targetContext view
        referent plan) :
      ProducerPlanModel sourceContext targetContext view (.Single path) plan
  | selection
      (model : SelectionPlanModel sourceContext targetContext view origin plan) :
      ProducerPlanModel sourceContext targetContext view
        (.TSel path label) plan
  | function
      (domainModel : BidirectionalPlanModel sourceContext targetContext view
        domain domainPlan)
      (codomainModel : ProducerPlanModel (sourceContext.snoc domain)
        (domainPlan.context targetContext)
        (ScopeView.bindPlan view domainPlan) codomain codomainPlan) :
      ProducerPlanModel sourceContext targetContext view (.Fun domain codomain)
        (Function.plan domainPlan codomainPlan)
  | properPair
      (firstModel : ProducerPlanModel sourceContext targetContext view
        first firstPlan)
      (memberModel : ProducerPlanModel (sourceContext.snoc first)
        (firstPlan.context targetContext)
        (ScopeView.bindPlan view firstPlan) member memberPlan) :
      ProducerPlanModel sourceContext targetContext view
        (.Pair first label (.ty member))
        (Pair.Proper.plan firstPlan memberPlan)
  | intervalPair
      (firstModel : ProducerPlanModel sourceContext targetContext view
        first firstPlan)
      (memberModel : IntervalProducerPlanModel (sourceContext.snoc first)
        (firstPlan.context targetContext)
        (ScopeView.bindPlan view firstPlan) lower upper lowerPlan upperPlan) :
      ProducerPlanModel sourceContext targetContext view
        (.Pair first label (.intv lower upper))
        (Pair.Interval.plan firstPlan lowerPlan.inputTy upperPlan.inputTy)
  | bound
      (boundModel : ProducerPlanModel sourceContext targetContext view
        sourceType plan) :
      ProducerPlanModel (sourceContext.snoc sourceType)
        (plan.context targetContext) (ScopeView.bindPlan view plan)
        sourceType.weaken (plan.rename plan.telescope.weaken)
  | underBinding
      (boundModel : ProducerPlanModel sourceContext targetContext view
        boundType boundPlan)
      (olderModel : ProducerPlanModel sourceContext targetContext view
        olderType olderPlan) :
      ProducerPlanModel (sourceContext.snoc boundType)
        (boundPlan.context targetContext) (ScopeView.bindPlan view boundPlan)
        olderType.weaken (olderPlan.rename boundPlan.telescope.weaken)
  | targetRename
      {sourceSig targetSig : Sig}
      {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
      {targetTargetContext : SystemFCoExt.Ctx targetSig}
      {sourceView : ScopeView n sourceTargetContext}
      {sourceType : LambdaPFC.Ty n} {sourcePlan : ValuePlan sourceSig}
      (model : ProducerPlanModel sourceContext sourceTargetContext sourceView
        sourceType sourcePlan)
      (mapping : Rename sourceSig targetSig)
      (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
      ProducerPlanModel sourceContext targetTargetContext
        (sourceView.rename mapping typed) sourceType
        (sourcePlan.rename mapping)

/-- Negative structural meaning. `opaque` is the only constructor that can
model an arbitrary raw source type, and fixes its plan to Top. -/
inductive DemandPlanModel :
    {n : Nat} -> (sourceContext : LambdaPFC.Ctx n) ->
    {sig : Sig} -> (targetContext : SystemFCoExt.Ctx sig) ->
    (view : ScopeView n targetContext) ->
    (sourceType : LambdaPFC.Ty n) -> ValuePlan sig -> Type where
  | opaque (sourceType : LambdaPFC.Ty n) :
      DemandPlanModel sourceContext targetContext view sourceType
        (Top.plan _)
  | bottom :
      DemandPlanModel sourceContext targetContext view .Bot (Bot.plan _)
  | singleton
      (precise : LambdaPFC.Path.Ty sourceContext path (.ty referent))
      (referentModel : ProducerPlanModel sourceContext targetContext view
        referent plan) :
      DemandPlanModel sourceContext targetContext view (.Single path) plan
  | selection
      (model : SelectionPlanModel sourceContext targetContext view origin plan) :
      DemandPlanModel sourceContext targetContext view (.TSel path label) plan
  | function
      (domainModel : ProducerPlanModel sourceContext targetContext view
        domain domainPlan)
      (codomainModel : DemandPlanModel (sourceContext.snoc domain)
        (domainPlan.context targetContext)
        (ScopeView.bindPlan view domainPlan) codomain codomainPlan) :
      DemandPlanModel sourceContext targetContext view (.Fun domain codomain)
        (Function.plan domainPlan codomainPlan)
  | properPair
      (firstModel : BidirectionalPlanModel sourceContext targetContext view
        first firstPlan)
      (memberModel : BidirectionalPlanModel (sourceContext.snoc first)
        (firstPlan.context targetContext)
        (ScopeView.bindPlan view firstPlan) member memberPlan) :
      DemandPlanModel sourceContext targetContext view
        (.Pair first label (.ty member))
        (Pair.Proper.plan firstPlan memberPlan)
  | intervalPair
      (firstModel : BidirectionalPlanModel sourceContext targetContext view
        first firstPlan)
      (memberModel : IntervalBidirectionalPlanModel (sourceContext.snoc first)
        (firstPlan.context targetContext)
        (ScopeView.bindPlan view firstPlan) lower upper lowerPlan upperPlan) :
      DemandPlanModel sourceContext targetContext view
        (.Pair first label (.intv lower upper))
        (Pair.Interval.plan firstPlan lowerPlan.inputTy upperPlan.inputTy)
  | underBinding
      (boundModel : ProducerPlanModel sourceContext targetContext view
        boundType boundPlan)
      (olderModel : DemandPlanModel sourceContext targetContext view olderType
        olderPlan) :
      DemandPlanModel (sourceContext.snoc boundType)
        (boundPlan.context targetContext) (ScopeView.bindPlan view boundPlan)
        olderType.weaken (olderPlan.rename boundPlan.telescope.weaken)
  | targetRename
      {sourceSig targetSig : Sig}
      {sourceTargetContext : SystemFCoExt.Ctx sourceSig}
      {targetTargetContext : SystemFCoExt.Ctx targetSig}
      {sourceView : ScopeView n sourceTargetContext}
      {sourceType : LambdaPFC.Ty n} {sourcePlan : ValuePlan sourceSig}
      (model : DemandPlanModel sourceContext sourceTargetContext sourceView
        sourceType sourcePlan)
      (mapping : Rename sourceSig targetSig)
      (typed : Rename.Typed sourceTargetContext targetTargetContext mapping) :
      DemandPlanModel sourceContext targetTargetContext
        (sourceView.rename mapping typed) sourceType
        (sourcePlan.rename mapping)

/-- A binder-facing plan supports both observation polarities at the exact
same target plan. Function domains and negative proper-pair fields use this
certificate so opening a consumer package never fabricates positive path
capability. -/
inductive BidirectionalPlanModel :
    {n : Nat} -> (sourceContext : LambdaPFC.Ctx n) ->
    {sig : Sig} -> (targetContext : SystemFCoExt.Ctx sig) ->
    (view : ScopeView n targetContext) ->
    (sourceType : LambdaPFC.Ty n) -> ValuePlan sig -> Type where
  | both
      (positive : ProducerPlanModel sourceContext targetContext view
        sourceType plan)
      (negative : DemandPlanModel sourceContext targetContext view
        sourceType plan) :
      BidirectionalPlanModel sourceContext targetContext view sourceType plan

/-- A selected proper plan has no free witness identity. It is bracketed by
the concrete positive lower and negative upper endpoint plans. -/
inductive SelectionPlanModel :
    {n : Nat} -> (sourceContext : LambdaPFC.Ctx n) ->
    {sig : Sig} -> (targetContext : SystemFCoExt.Ctx sig) ->
    (view : ScopeView n targetContext) ->
    {path : LambdaPFC.Path n} -> {label : LambdaPFC.Name} ->
    (origin : SelectionOrigin sourceContext path label) ->
    ValuePlan sig -> Type where
  | between
      (bounds : IntervalDemandPlanModel sourceContext targetContext view
        origin.lower origin.upper lowerPlan upperPlan)
      (lowerToSelected : StableIdentity.Adapter targetContext lowerPlan
        selectedPlan)
      (selectedToUpper : StableIdentity.Adapter targetContext selectedPlan
        upperPlan) :
      SelectionPlanModel sourceContext targetContext view origin selectedPlan

/-- Positive interval plans retain the lower-negative/upper-positive polarity.
The hidden witness and package adapters are carried later by an interval
producer descriptor. -/
inductive IntervalProducerPlanModel :
    {n : Nat} -> (sourceContext : LambdaPFC.Ctx n) ->
    {sig : Sig} -> (targetContext : SystemFCoExt.Ctx sig) ->
    (view : ScopeView n targetContext) ->
    (lower upper : LambdaPFC.Ty n) ->
    ValuePlan sig -> ValuePlan sig -> Type where
  | bounds
      (lowerModel : DemandPlanModel sourceContext targetContext view
        lower lowerPlan)
      (upperModel : ProducerPlanModel sourceContext targetContext view
        upper upperPlan) :
      IntervalProducerPlanModel sourceContext targetContext view lower upper
        lowerPlan upperPlan

/-- Dual interval demands have no selected witness and fix only their external
lower-positive/upper-negative plans. -/
inductive IntervalDemandPlanModel :
    {n : Nat} -> (sourceContext : LambdaPFC.Ctx n) ->
    {sig : Sig} -> (targetContext : SystemFCoExt.Ctx sig) ->
    (view : ScopeView n targetContext) ->
    (lower upper : LambdaPFC.Ty n) ->
    ValuePlan sig -> ValuePlan sig -> Type where
  | bounds
      (lowerModel : ProducerPlanModel sourceContext targetContext view
        lower lowerPlan)
      (upperModel : DemandPlanModel sourceContext targetContext view
        upper upperPlan) :
      IntervalDemandPlanModel sourceContext targetContext view lower upper
        lowerPlan upperPlan

/-- Interval members opened from a negative pair must support both the
positive descriptor view used by path selection and the dual demand view used
by contravariant bounds translation, at the same external endpoint plans. -/
inductive IntervalBidirectionalPlanModel :
    {n : Nat} -> (sourceContext : LambdaPFC.Ctx n) ->
    {sig : Sig} -> (targetContext : SystemFCoExt.Ctx sig) ->
    (view : ScopeView n targetContext) ->
    (lower upper : LambdaPFC.Ty n) ->
    ValuePlan sig -> ValuePlan sig -> Type where
  | both
      (positive : IntervalProducerPlanModel sourceContext targetContext view
        lower upper lowerPlan upperPlan)
      (negative : IntervalDemandPlanModel sourceContext targetContext view
        lower upper lowerPlan upperPlan) :
      IntervalBidirectionalPlanModel sourceContext targetContext view lower
        upper lowerPlan upperPlan

end

namespace BidirectionalPlanModel

def producer
    (model : BidirectionalPlanModel sourceContext targetContext view sourceType
      plan) :
    ProducerPlanModel sourceContext targetContext view sourceType plan :=
  match model with
  | .both positive _ => positive

def demand
    (model : BidirectionalPlanModel sourceContext targetContext view sourceType
      plan) :
    DemandPlanModel sourceContext targetContext view sourceType plan :=
  match model with
  | .both _ negative => negative

end BidirectionalPlanModel

namespace IntervalBidirectionalPlanModel

def producer
    (model : IntervalBidirectionalPlanModel sourceContext targetContext view
      lower upper lowerPlan upperPlan) :
    IntervalProducerPlanModel sourceContext targetContext view lower upper
      lowerPlan upperPlan :=
  match model with
  | .both positive _ => positive

def demand
    (model : IntervalBidirectionalPlanModel sourceContext targetContext view
      lower upper lowerPlan upperPlan) :
    IntervalDemandPlanModel sourceContext targetContext view lower upper
      lowerPlan upperPlan :=
  match model with
  | .both _ negative => negative

end IntervalBidirectionalPlanModel

/-! ## Certified plan polarity endpoints -/

/-- Positive structural plan evidence with no source term or target package.
This is the endpoint needed by interval upper bounds. -/
structure PositivePlan {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (view : ScopeView n targetContext)
    (sourceType : LambdaPFC.Ty n) : Type where
  model : Sigma fun plan =>
    ProducerPlanModel sourceContext targetContext view sourceType plan

namespace PositivePlan

def plan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext} {sourceType : LambdaPFC.Ty n}
    (endpoint : PositivePlan sourceContext targetContext view sourceType) :
    ValuePlan sig :=
  endpoint.model.1

def modeled
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext} {sourceType : LambdaPFC.Ty n}
    (endpoint : PositivePlan sourceContext targetContext view sourceType) :
    ProducerPlanModel sourceContext targetContext view sourceType
      endpoint.plan :=
  endpoint.model.2

def toCore
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext} {sourceType : LambdaPFC.Ty n}
    (endpoint : PositivePlan sourceContext targetContext view sourceType) :
    TranslationModelCore.PositivePlan sourceContext targetContext view
      sourceType where
  plan := endpoint.plan

end PositivePlan

/-- Negative structural plan evidence with no demand trace. This is the
endpoint needed by interval lower bounds and dual interval consumers. -/
structure NegativePlan {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (view : ScopeView n targetContext)
    (sourceType : LambdaPFC.Ty n) : Type where
  model : Sigma fun plan =>
    DemandPlanModel sourceContext targetContext view sourceType plan

namespace NegativePlan

def plan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext} {sourceType : LambdaPFC.Ty n}
    (endpoint : NegativePlan sourceContext targetContext view sourceType) :
    ValuePlan sig :=
  endpoint.model.1

def modeled
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext} {sourceType : LambdaPFC.Ty n}
    (endpoint : NegativePlan sourceContext targetContext view sourceType) :
    DemandPlanModel sourceContext targetContext view sourceType
      endpoint.plan :=
  endpoint.model.2

def toCore
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {view : ScopeView n targetContext} {sourceType : LambdaPFC.Ty n}
    (endpoint : NegativePlan sourceContext targetContext view sourceType) :
    TranslationModelCore.NegativePlan sourceContext targetContext view
      sourceType where
  plan := endpoint.plan

end NegativePlan


/-! ## Packages and source-typed scopes -/

/-- The shared path/compiler package ABI. Unlike an opened interface, this
contains no claim that hidden fields are available in the base context. -/
abbrev CompiledPackage {sig : Sig} (base : SystemFCoExt.Ctx sig)
    (plan : ValuePlan sig) :=
  PathPackageZipper.CompiledPackage base plan

namespace CompiledPackage

noncomputable def ofInterface
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (interface : ValueInterface base) : CompiledPackage base interface.plan where
  expression := interface.package
  typing := interface.package_hasType

/-- The interface made available only after the package telescope has been
opened by a continuation. -/
noncomputable def openedInterface
    {sig : Sig} {base : SystemFCoExt.Ctx sig} {plan : ValuePlan sig}
    (_package : CompiledPackage base plan) :
    ValueInterface (plan.context base) :=
  ValueInterface.ofArguments (plan.rename plan.telescope.weaken)
    (Telescope.Args.identity plan.telescope base)

/-- Eliminate a compiled package without allowing its hidden fields to escape
the continuation result type. -/
noncomputable def consume
    {sig : Sig} {base : SystemFCoExt.Ctx sig} {plan : ValuePlan sig}
    (package : CompiledPackage base plan) (result : Ty sig)
    (body : Exp plan.scope) : Exp sig :=
  plan.unpack package.expression result body

noncomputable def consume_hasType
    {sig : Sig} {base : SystemFCoExt.Ctx sig} {plan : ValuePlan sig}
    (package : CompiledPackage base plan) (result : Ty sig)
    (body : Exp plan.scope)
    (bodyTyping : Exp.HasType (plan.context base) body
      (result.rename plan.telescope.weaken)) :
    Exp.HasType base (package.consume result body) result :=
  plan.unpack_hasType package.typing bodyTyping

/-- Apply a static stable-identity adapter to the whole compiled package. -/
noncomputable def adapt
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    {source target : ValuePlan sig}
    (package : CompiledPackage base source)
    (adapter : StableIdentity.Adapter base source target) :
    CompiledPackage base target where
  expression := adapter.apply package.expression
  typing := adapter.apply_hasType package.typing

end CompiledPackage

@[simp] theorem ValueInterface.ofArguments_plan
    {sig : Sig} {base : SystemFCoExt.Ctx sig}
    (plan : ValuePlan sig)
    (arguments : Telescope.Args base plan.telescope) :
    (ValueInterface.ofArguments plan arguments).plan = plan := by
  cases arguments with
  | tvar identity rest =>
      cases rest with
      | var payload payloadTyping observations => rfl

/-- A target scope view certified against every source lookup. This is the
missing invariant that turns a target slot into structural source evidence. -/
structure ScopeModel {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig) : Type where
  view : ScopeView n targetContext
  slot : (index : Fin n) ->
    ProducerPlanModel sourceContext targetContext view
      (sourceContext.lookup index) (view index).plan

namespace ScopeModel

/-- The source-empty scope over an arbitrary target context. -/
def empty {sig : Sig} (targetContext : SystemFCoExt.Ctx sig) :
    ScopeModel LambdaPFC.Ctx.nil targetContext where
  view index := Fin.elim0 index
  slot index := Fin.elim0 index

noncomputable def package
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (index : Fin n) :
    CompiledPackage targetContext (scope.view index).plan :=
  .ofInterface (scope.view index)

/-- Bind a certified positive plan. A negative demand alone is insufficient:
the opened source variable must support positive path elimination at this
same plan. Older slots are reindexed through the new package telescope. -/
noncomputable def bind
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : ProducerPlanModel sourceContext targetContext scope.view sourceType
      plan) :
    ScopeModel (sourceContext.snoc sourceType) (plan.context targetContext) where
  view := ScopeView.bindPlan scope.view plan
  slot index := by
    refine Fin.cases ?_ (fun older => ?_) index
    · simpa [LambdaPFC.Ctx.lookup, ScopeView.bindPlan,
        ValueInterface.ofArguments_plan] using
        (ProducerPlanModel.bound model)
    · simpa [LambdaPFC.Ctx.lookup, ScopeView.bindPlan,
        ValueInterface.rename] using
        (ProducerPlanModel.underBinding model (scope.slot older))

/-- Bind a domain/field plan which carries both polarities, using its
certified positive projection for source-variable lookup. -/
noncomputable def bindBidirectional
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext)
    {sourceType : LambdaPFC.Ty n} {plan : ValuePlan sig}
    (model : BidirectionalPlanModel sourceContext targetContext scope.view
      sourceType plan) :
    ScopeModel (sourceContext.snoc sourceType) (plan.context targetContext) :=
  scope.bind model.producer

end ScopeModel

/-! ## Refined endpoints -/

/-- An ordinary positive endpoint consists of certified plan shape plus an
actual typed package expression. -/
structure OrdinaryProducer {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (scope : ScopeModel sourceContext targetContext)
    (sourceType : LambdaPFC.Ty n) : Type where
  origin : ProducerOrigin sourceContext sourceType
  model : Sigma fun plan =>
    ProducerPlanModel sourceContext targetContext scope.view sourceType plan
  package : CompiledPackage targetContext model.1

namespace OrdinaryProducer

def plan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n}
    (producer : OrdinaryProducer sourceContext targetContext scope
    sourceType) : ValuePlan sig :=
  producer.model.1

def modeled
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n}
    (producer : OrdinaryProducer sourceContext targetContext scope
    sourceType) :
    ProducerPlanModel sourceContext targetContext scope.view sourceType
      producer.plan :=
  producer.model.2

def positivePlan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n}
    (producer : OrdinaryProducer sourceContext targetContext scope sourceType) :
    PositivePlan sourceContext targetContext scope.view sourceType where
  model := producer.model

end OrdinaryProducer

/-- Scope-independent positive Bottom capability. Its target plan need not be
the canonical `Bot.plan`: a bound/path Bottom may have been transported
through surrounding binders. The retained positive model certifies Bottom at
the original view, while absurd propagation only preserves this same
plan/package and never exports it as structural evidence for the advertised
target type. -/
structure BottomProducer {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig) : Type where
  origin : ProducerOrigin sourceContext (.Bot : LambdaPFC.Ty n)
  plan : ValuePlan sig
  view : ScopeView n targetContext
  modeled : ProducerPlanModel sourceContext targetContext view .Bot plan
  package : CompiledPackage targetContext plan

namespace BottomProducer

/-- Forget only the ambient scope index of an ordinary Bottom producer. -/
def ofOrdinary
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    (bottom : OrdinaryProducer sourceContext targetContext scope .Bot) :
    BottomProducer sourceContext targetContext where
  origin := bottom.origin
  plan := bottom.plan
  view := scope.view
  modeled := bottom.modeled
  package := bottom.package

end BottomProducer

/-- Absurd positives retain the underlying Bottom package and expose no
structural model at the advertised raw type. -/
inductive ProperProducer {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (scope : ScopeModel sourceContext targetContext) :
    LambdaPFC.Ty n -> Type where
  | ordinary
      (producer : OrdinaryProducer sourceContext targetContext scope sourceType) :
      ProperProducer sourceContext targetContext scope sourceType
  | absurd
      (bottom : BottomProducer sourceContext targetContext)
      (advertised : LambdaPFC.Ty n) :
      ProperProducer sourceContext targetContext scope advertised

namespace ProperProducer

def origin
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n}
    (producer : ProperProducer sourceContext targetContext scope
    sourceType) : ProducerOrigin sourceContext sourceType :=
  match producer with
  | .ordinary producer => producer.origin
  | .absurd bottom advertised => .absurd bottom.origin advertised

def plan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n}
    (producer : ProperProducer sourceContext targetContext scope
    sourceType) : ValuePlan sig :=
  match producer with
  | .ordinary producer => producer.plan
  | .absurd bottom _ => bottom.plan

def package
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n}
    (producer : ProperProducer sourceContext targetContext scope
    sourceType) : CompiledPackage targetContext producer.plan :=
  match producer with
  | .ordinary producer => producer.package
  | .absurd bottom _ => bottom.package

def toCore
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n}
    (producer : ProperProducer sourceContext targetContext scope sourceType) :
    TranslationModelCore.PositivePlan sourceContext targetContext scope.view
      sourceType where
  plan := producer.plan

end ProperProducer

/-- A negative endpoint projects its plan from closed demand-model evidence. -/
structure ProperDemand {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (scope : ScopeModel sourceContext targetContext)
    (sourceType : LambdaPFC.Ty n) : Type where
  trace : DemandTrace sourceContext sourceType
  model : Sigma fun plan =>
    DemandPlanModel sourceContext targetContext scope.view sourceType plan

namespace ProperDemand

def plan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n}
    (demand : ProperDemand sourceContext targetContext scope sourceType) :
    ValuePlan sig :=
  demand.model.1

def modeled
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n}
    (demand : ProperDemand sourceContext targetContext scope sourceType) :
    DemandPlanModel sourceContext targetContext scope.view sourceType
      demand.plan :=
  demand.model.2

def negativePlan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n}
    (demand : ProperDemand sourceContext targetContext scope sourceType) :
    NegativePlan sourceContext targetContext scope.view sourceType where
  model := demand.model

def toCore
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {sourceType : LambdaPFC.Ty n}
    (demand : ProperDemand sourceContext targetContext scope sourceType) :
    TranslationModelCore.NegativePlan sourceContext targetContext scope.view
      sourceType where
  plan := demand.plan

end ProperDemand

/-! ## Exact path packages -/

/-- A precise path result is a certified structural plan plus a package in
the base target context. It does not claim that nested pair fields are already
an opened `ValueInterface`. -/
structure ProperPathPackage {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (scope : ScopeModel sourceContext targetContext)
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    (precise : LambdaPFC.Path.Ty sourceContext path (.ty referent)) : Type where
  model : Sigma fun plan =>
    ProducerPlanModel sourceContext targetContext scope.view referent plan
  package : CompiledPackage targetContext model.1

namespace ProperPathPackage

def plan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.ty referent)}
    (result : ProperPathPackage sourceContext targetContext scope precise) :
    ValuePlan sig :=
  result.model.1

def modeled
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.ty referent)}
    (result : ProperPathPackage sourceContext targetContext scope precise) :
    ProducerPlanModel sourceContext targetContext scope.view referent
      result.plan :=
  result.model.2

/-- Forget the source model only at the low path-elimination boundary. The
package remains in the root context and becomes the base zipper focus. -/
noncomputable def toPathResult
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.ty referent)}
    (result : ProperPathPackage sourceContext targetContext scope precise) :
    PathPackageZipper.PathResult targetContext :=
  PathPackageZipper.PathResult.rootPackage result.package

/-- The singleton introduction and the synthesized referent share the exact
same package and complete target plan. -/
def singletonProducer
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.ty referent)}
    (result : ProperPathPackage sourceContext targetContext scope precise) :
    OrdinaryProducer sourceContext targetContext scope (.Single path) where
  origin := ProducerOrigin.ofPathSingleton precise
  model := ⟨result.plan, .singleton precise result.modeled⟩
  package := result.package

def preciseProducer
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.ty referent)}
    (result : ProperPathPackage sourceContext targetContext scope precise) :
    OrdinaryProducer sourceContext targetContext scope referent where
  origin := ProducerOrigin.ofPrecisePath precise
  model := result.model
  package := result.package

@[simp] theorem singleton_plan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {path : LambdaPFC.Path n} {referent : LambdaPFC.Ty n}
    {precise : LambdaPFC.Path.Ty sourceContext path (.ty referent)}
    (result : ProperPathPackage sourceContext targetContext scope precise) :
    result.singletonProducer.plan = result.plan := by
  rfl

end ProperPathPackage

/-- Variable lookup is the base case of path compilation. ScopeModel supplies
both its source structural model and its concrete repackaged slot expression. -/
noncomputable def ScopeModel.variablePath
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (index : Fin n) :
    ProperPathPackage sourceContext targetContext scope
      (LambdaPFC.Path.Ty.var (x := index)) where
  model := ⟨(scope.view index).plan, scope.slot index⟩
  package := scope.package index

/-! ## Refined interval endpoints -/

/-- A positive interval descriptor retains its exact hidden witness only in
the low descriptor, while both external endpoint plans are structurally
certified. -/
structure IntervalProducer {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (scope : ScopeModel sourceContext targetContext)
    (lowerType upperType : LambdaPFC.Ty n) : Type where
  origin : IntervalProducerOrigin sourceContext lowerType upperType
  lower : NegativePlan sourceContext targetContext scope.view lowerType
  upper : PositivePlan sourceContext targetContext scope.view upperType
  descriptor : TranslationModelCore.IntervalDescriptor sourceContext
    targetContext (.negative lower.toCore) (.positive upper.toCore)

namespace IntervalProducer

def modeled
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {lowerType upperType : LambdaPFC.Ty n}
    (producer : IntervalProducer sourceContext targetContext scope lowerType
      upperType) :
    IntervalProducerPlanModel sourceContext targetContext scope.view lowerType
      upperType producer.lower.plan producer.upper.plan :=
  .bounds producer.lower.modeled producer.upper.modeled

def toCore
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {lowerType upperType : LambdaPFC.Ty n}
    (producer : IntervalProducer sourceContext targetContext scope lowerType
      upperType) :
    TranslationModelCore.IntervalProducer sourceContext targetContext
      scope.view lowerType upperType where
  origin := producer.origin
  lower := producer.lower.toCore
  upper := producer.upper.toCore
  descriptor := producer.descriptor

end IntervalProducer

/-- A dual interval demand fixes its external lower/upper plans but contains
no selected witness representation. -/
structure IntervalDemand {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (scope : ScopeModel sourceContext targetContext)
    (lowerType upperType : LambdaPFC.Ty n) : Type where
  trace : IntervalDemandTrace sourceContext lowerType upperType
  lower : PositivePlan sourceContext targetContext scope.view lowerType
  upper : NegativePlan sourceContext targetContext scope.view upperType

namespace IntervalDemand

def modeled
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {lowerType upperType : LambdaPFC.Ty n}
    (demand : IntervalDemand sourceContext targetContext scope lowerType
      upperType) :
    IntervalDemandPlanModel sourceContext targetContext scope.view lowerType
      upperType demand.lower.plan demand.upper.plan :=
  .bounds demand.lower.modeled demand.upper.modeled

def toCore
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {scope : ScopeModel sourceContext targetContext}
    {lowerType upperType : LambdaPFC.Ty n}
    (demand : IntervalDemand sourceContext targetContext scope lowerType
      upperType) :
    TranslationModelCore.IntervalDemand sourceContext targetContext scope.view
      lowerType upperType where
  trace := demand.trace
  lower := demand.lower.toCore
  upper := demand.upper.toCore

end IntervalDemand

/-! ## Static maps, push/pull, and satisfaction -/

/-- Static proper satisfaction. Operational readiness is not part of this
record and Bottom elimination can inhabit it only under separate absurd
provenance. -/
structure ProperSatisfaction
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {producerScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment producerScope.view demandScope.view)
    {sourceType : LambdaPFC.Ty n}
    (producer : ProperProducer sourceContext targetContext producerScope
      sourceType)
    (demand : ProperDemand sourceContext targetContext demandScope sourceType) :
    Type where
  adapter : StableIdentity.Adapter targetContext producer.plan demand.plan

namespace ProperSatisfaction

def toCore
    (satisfaction : ProperSatisfaction alignment producer demand) :
    TranslationModelCore.ProperSatisfaction alignment producer.toCore
      demand.toCore where
  adapter := satisfaction.adapter

end ProperSatisfaction

/-- Static satisfaction between plan-only polarity endpoints. This is the
relation used by interval bounds, where no source term/package inhabits either
endpoint. -/
structure PlanSatisfaction
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {producerScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment producerScope.view demandScope.view)
    {sourceType : LambdaPFC.Ty n}
    (producer : PositivePlan sourceContext targetContext producerScope.view
      sourceType)
    (demand : NegativePlan sourceContext targetContext demandScope.view
      sourceType) : Type where
  adapter : StableIdentity.Adapter targetContext producer.plan demand.plan

namespace PlanSatisfaction

def toCore
    (satisfaction : PlanSatisfaction alignment producer demand) :
    TranslationModelCore.ProperSatisfaction alignment producer.toCore
      demand.toCore where
  adapter := satisfaction.adapter

end PlanSatisfaction

/-- Covariant result indexed by the exact full source derivation and the
heterogeneous stable-slot alignment. An ordinary result constructs its target
package by applying the recorded adapter and fixes the target origin to the
exact push. Bottom and already-absurd sources instead retain their underlying
Bottom package without fabricating a structural model for the advertised
target type. -/
inductive ProperPushEvidence
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    : {sourceType targetType : LambdaPFC.Ty n} ->
    (subtyping : LambdaPFC.Tau.Sub sourceContext (.ty sourceType)
      (.ty targetType)) ->
    (source : ProperProducer sourceContext targetContext sourceScope
      sourceType) ->
    (target : ProperProducer sourceContext targetContext targetScope
      targetType) ->
    (adapter : StableIdentity.Adapter targetContext source.plan target.plan) ->
    Type where
  | ordinary
      (source : OrdinaryProducer sourceContext targetContext sourceScope
        sourceType)
      (model : Sigma fun plan =>
        ProducerPlanModel sourceContext targetContext targetScope.view
          targetType plan)
      (adapter : StableIdentity.Adapter targetContext source.plan model.1) :
      ProperPushEvidence alignment subtyping (.ordinary source)
        (.ordinary
          { origin := .push subtyping source.origin
            model := model
            package := source.package.adapt adapter })
        adapter
  | throughBottom
      (source : OrdinaryProducer sourceContext targetContext sourceScope
        sourceType)
      (first : LambdaPFC.Tau.Sub sourceContext (.ty sourceType) (.ty .Bot))
      (second : LambdaPFC.Tau.Sub sourceContext (.ty .Bot) (.ty targetType))
      (model : Sigma fun plan =>
        ProducerPlanModel sourceContext targetContext targetScope.view .Bot plan)
      (adapter : StableIdentity.Adapter targetContext source.plan model.1) :
      ProperPushEvidence alignment (.trans first second) (.ordinary source)
        (.absurd
          { origin := .push first source.origin
            plan := model.1
            view := targetScope.view
            modeled := model.2
            package := source.package.adapt adapter }
          targetType)
        adapter
  | fromBottom
      (source : OrdinaryProducer sourceContext targetContext sourceScope .Bot)
      (subtyping : LambdaPFC.Tau.Sub sourceContext (.ty .Bot)
        (.ty targetType)) :
      ProperPushEvidence alignment subtyping
        (.ordinary source) (.absurd (BottomProducer.ofOrdinary source) targetType)
        (StableIdentity.Adapter.identity targetContext source.plan)
  | fromAbsurd
      (bottom : BottomProducer sourceContext targetContext)
      (subtyping : LambdaPFC.Tau.Sub sourceContext (.ty advertised)
        (.ty targetType)) :
      ProperPushEvidence alignment subtyping (.absurd bottom advertised)
        (.absurd bottom targetType)
        (StableIdentity.Adapter.identity targetContext bottom.plan)

/-- A sealed covariant result. `evidence` is constructible only when the
target origin/package and adapter have one of the three forms above. -/
structure ProperPushResult
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : LambdaPFC.Tau.Sub sourceContext (.ty sourceType)
      (.ty targetType))
    (source : ProperProducer sourceContext targetContext sourceScope
      sourceType) : Type where
  target : ProperProducer sourceContext targetContext targetScope targetType
  adapter : StableIdentity.Adapter targetContext source.plan target.plan
  evidence : ProperPushEvidence alignment subtyping source target adapter

namespace ProperPushResult

/-- Ordinary push smart constructor. The result package is definitionally the
adapter applied to the source package. -/
noncomputable def ordinary
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : LambdaPFC.Tau.Sub sourceContext (.ty sourceType)
      (.ty targetType))
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      sourceType)
    (model : Sigma fun plan =>
      ProducerPlanModel sourceContext targetContext targetScope.view
        targetType plan)
    (adapter : StableIdentity.Adapter targetContext source.plan model.1) :
    ProperPushResult alignment subtyping (.ordinary source) :=
  { target :=
      .ordinary
        { origin := .push subtyping source.origin
          model := model
          package := source.package.adapt adapter }
    adapter := adapter
    evidence := .ordinary source model adapter }

/-- Push an ordinary source to a certified Bottom plan, then retain that
exact adapter-produced package as absurd provenance for the second leg. -/
noncomputable def throughBottom
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType targetType : LambdaPFC.Ty n}
    (first : LambdaPFC.Tau.Sub sourceContext (.ty sourceType) (.ty .Bot))
    (second : LambdaPFC.Tau.Sub sourceContext (.ty .Bot) (.ty targetType))
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      sourceType)
    (model : Sigma fun plan =>
      ProducerPlanModel sourceContext targetContext targetScope.view .Bot plan)
    (adapter : StableIdentity.Adapter targetContext source.plan model.1) :
    ProperPushResult alignment (.trans first second) (.ordinary source) :=
  let bottom : BottomProducer sourceContext targetContext :=
    { origin := .push first source.origin
      plan := model.1
      view := targetScope.view
      modeled := model.2
      package := source.package.adapt adapter }
  { target := .absurd bottom targetType
    adapter := adapter
    evidence := .throughBottom source first second model adapter }

/-- Push canonical Bottom to an arbitrary advertised raw target while
retaining the same Bottom capability. -/
noncomputable def fromBottom
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {targetType : LambdaPFC.Ty n}
    (subtyping : LambdaPFC.Tau.Sub sourceContext (.ty .Bot)
      (.ty targetType))
    (source : OrdinaryProducer sourceContext targetContext sourceScope .Bot) :
    ProperPushResult alignment subtyping (.ordinary source) :=
  { target := .absurd (BottomProducer.ofOrdinary source) targetType
    adapter := StableIdentity.Adapter.identity targetContext source.plan
    evidence := .fromBottom source subtyping }

/-- Propagate an already-absurd producer without re-entering the ordinary
structural branch. -/
noncomputable def fromAbsurd
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : LambdaPFC.Tau.Sub sourceContext (.ty sourceType)
      (.ty targetType))
    (bottom : BottomProducer sourceContext targetContext) :
    ProperPushResult alignment subtyping (.absurd bottom sourceType) :=
  { target := .absurd bottom targetType
    adapter := StableIdentity.Adapter.identity targetContext bottom.plan
    evidence := .fromAbsurd bottom subtyping }

end ProperPushResult

/-- Contravariant result. The pulled trace is forced by construction and its
plan comes from closed demand-model evidence. -/
structure ProperPullResult
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceType targetType : LambdaPFC.Ty n}
    (subtyping : LambdaPFC.Tau.Sub sourceContext (.ty sourceType)
      (.ty targetType))
    (target : ProperDemand sourceContext targetContext targetScope targetType) :
    Type where
  model : Sigma fun plan =>
    DemandPlanModel sourceContext targetContext sourceScope.view sourceType plan
  adapter : StableIdentity.Adapter targetContext model.1 target.plan

namespace ProperPullResult

def source
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view targetScope.view}
    {sourceType targetType : LambdaPFC.Ty n}
    {subtyping : LambdaPFC.Tau.Sub sourceContext (.ty sourceType)
      (.ty targetType)}
    {target : ProperDemand sourceContext targetContext targetScope targetType}
    (result : ProperPullResult alignment subtyping target) :
    ProperDemand sourceContext targetContext sourceScope sourceType where
  trace := .pull subtyping target.trace
  model := result.model

end ProperPullResult

/-- Positive interval push retains the producer-selected descriptor. The
external endpoint models are certified here; `target` below fixes the exact
push origin and obtains its descriptor only by mapping the source descriptor,
so a caller cannot replace the hidden witness. -/
structure IntervalPushResult
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
    (subtyping : LambdaPFC.Tau.Sub sourceContext
      (.intv sourceLower sourceUpper) (.intv targetLower targetUpper))
    (source : IntervalProducer sourceContext targetContext sourceScope
      sourceLower sourceUpper) : Type where
  lower : NegativePlan sourceContext targetContext targetScope.view targetLower
  upper : PositivePlan sourceContext targetContext targetScope.view targetUpper
  lowerAdapter : StableIdentity.Adapter targetContext lower.plan
    source.lower.plan
  upperAdapter : StableIdentity.Adapter targetContext source.upper.plan
    upper.plan

namespace IntervalPushResult

/-- The forced positive interval target. Its descriptor retains the exact
existential representation selected by `source`. -/
noncomputable def target
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view targetScope.view}
    {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
    {subtyping : LambdaPFC.Tau.Sub sourceContext
      (.intv sourceLower sourceUpper) (.intv targetLower targetUpper)}
    {source : IntervalProducer sourceContext targetContext sourceScope
      sourceLower sourceUpper}
    (result : IntervalPushResult alignment subtyping source) :
    IntervalProducer sourceContext targetContext targetScope targetLower
      targetUpper := by
  let mapping : TranslationModelCore.IntervalDescriptor.Map alignment.symm
      alignment (.negative source.lower.toCore)
      (.positive source.upper.toCore)
      (.negative result.lower.toCore)
      (.positive result.upper.toCore) :=
    { lower := result.lowerAdapter
      upper := result.upperAdapter }
  exact
    { origin := .push subtyping source.origin
      lower := result.lower
      upper := result.upper
      descriptor := source.descriptor.map mapping }

end IntervalPushResult

/-- Contravariant interval pull fixes no witness and forces the exact trace. -/
structure IntervalPullResult
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view)
    {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
    (subtyping : LambdaPFC.Tau.Sub sourceContext
      (.intv sourceLower sourceUpper) (.intv targetLower targetUpper))
    (target : IntervalDemand sourceContext targetContext targetScope targetLower
      targetUpper) : Type where
  lower : PositivePlan sourceContext targetContext sourceScope.view sourceLower
  upper : NegativePlan sourceContext targetContext sourceScope.view sourceUpper
  lowerAdapter : StableIdentity.Adapter targetContext target.lower.plan
    lower.plan
  upperAdapter : StableIdentity.Adapter targetContext upper.plan
    target.upper.plan

namespace IntervalPullResult

def source
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment sourceScope.view targetScope.view}
    {sourceLower sourceUpper targetLower targetUpper : LambdaPFC.Ty n}
    {subtyping : LambdaPFC.Tau.Sub sourceContext
      (.intv sourceLower sourceUpper) (.intv targetLower targetUpper)}
    {target : IntervalDemand sourceContext targetContext targetScope targetLower
      targetUpper}
    (result : IntervalPullResult alignment subtyping target) :
    IntervalDemand sourceContext targetContext sourceScope sourceLower
      sourceUpper where
  trace := .pull subtyping target.trace
  lower := result.lower
  upper := result.upper

end IntervalPullResult

/-- Dual interval satisfaction is exactly the two endpoint satisfactions. -/
structure IntervalSatisfaction
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {producerScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment producerScope.view demandScope.view)
    {lowerType upperType : LambdaPFC.Ty n}
    (producer : IntervalProducer sourceContext targetContext producerScope
      lowerType upperType)
    (demand : IntervalDemand sourceContext targetContext demandScope lowerType
      upperType) : Type where
  lower : PlanSatisfaction alignment.symm demand.lower producer.lower
  upper : PlanSatisfaction alignment producer.upper demand.upper

namespace IntervalSatisfaction

noncomputable def descriptor
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {producerScope demandScope : ScopeModel sourceContext targetContext}
    {alignment : ScopeAlignment producerScope.view demandScope.view}
    {lowerType upperType : LambdaPFC.Ty n}
    {producer : IntervalProducer sourceContext targetContext producerScope
      lowerType upperType}
    {demand : IntervalDemand sourceContext targetContext demandScope lowerType
      upperType}
    (satisfaction : IntervalSatisfaction alignment producer demand) :
    TranslationModelCore.IntervalDescriptor sourceContext targetContext
      (.positive demand.lower.toCore) (.negative demand.upper.toCore) :=
  TranslationModelCore.IntervalDemand.satisfy producer.toCore demand.toCore
    alignment satisfaction.lower.toCore satisfaction.upper.toCore

end IntervalSatisfaction

/-! ## Kind-complete recursion ABI -/

inductive TauProducer {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (scope : ScopeModel sourceContext targetContext) :
    {kind : LambdaPFC.Kind} -> LambdaPFC.Tau n kind -> Type where
  | proper
      (producer : ProperProducer sourceContext targetContext scope sourceType) :
      TauProducer sourceContext targetContext scope (.ty sourceType)
  | interval
      (producer : IntervalProducer sourceContext targetContext scope lower upper) :
      TauProducer sourceContext targetContext scope (.intv lower upper)

inductive TauDemand {n : Nat} (sourceContext : LambdaPFC.Ctx n)
    {sig : Sig} (targetContext : SystemFCoExt.Ctx sig)
    (scope : ScopeModel sourceContext targetContext) :
    {kind : LambdaPFC.Kind} -> LambdaPFC.Tau n kind -> Type where
  | proper
      (demand : ProperDemand sourceContext targetContext scope sourceType) :
      TauDemand sourceContext targetContext scope (.ty sourceType)
  | interval
      (demand : IntervalDemand sourceContext targetContext scope lower upper) :
      TauDemand sourceContext targetContext scope (.intv lower upper)

inductive TauPushResult
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view) :
    {kind : LambdaPFC.Kind} ->
    {sourceType targetType : LambdaPFC.Tau n kind} ->
    (subtyping : LambdaPFC.Tau.Sub sourceContext sourceType targetType) ->
    TauProducer sourceContext targetContext sourceScope sourceType -> Type where
  | proper
      (result : ProperPushResult alignment subtyping source) :
      TauPushResult alignment subtyping (.proper source)
  | interval
      (result : IntervalPushResult alignment subtyping source) :
      TauPushResult alignment subtyping (.interval source)

inductive TauPullResult
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceScope targetScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment sourceScope.view targetScope.view) :
    {kind : LambdaPFC.Kind} ->
    {sourceType targetType : LambdaPFC.Tau n kind} ->
    (subtyping : LambdaPFC.Tau.Sub sourceContext sourceType targetType) ->
    TauDemand sourceContext targetContext targetScope targetType -> Type where
  | proper
      (result : ProperPullResult alignment subtyping target) :
      TauPullResult alignment subtyping (.proper target)
  | interval
      (result : IntervalPullResult alignment subtyping target) :
      TauPullResult alignment subtyping (.interval target)

inductive TauSatisfaction
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {producerScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment producerScope.view demandScope.view) :
    {kind : LambdaPFC.Kind} -> {sourceType : LambdaPFC.Tau n kind} ->
    TauProducer sourceContext targetContext producerScope sourceType ->
    TauDemand sourceContext targetContext demandScope sourceType -> Type where
  | proper
      (satisfaction : ProperSatisfaction alignment producer demand) :
      TauSatisfaction alignment (.proper producer) (.proper demand)
  | interval
      (satisfaction : IntervalSatisfaction alignment producer demand) :
      TauSatisfaction alignment (.interval producer) (.interval demand)

/-! ## Separate operational evidence -/

/-- Ordinary execution starts from the compiled source package, reaches a
ready opened source interface, and runs exactly the statically selected
stable-identity adapter to a ready target interface. -/
structure OrdinarySatisfactionExecution
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {producerScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment producerScope.view demandScope.view)
    {sourceType : LambdaPFC.Ty n}
    (producer : OrdinaryProducer sourceContext targetContext producerScope
      sourceType)
    (demand : ProperDemand sourceContext targetContext demandScope sourceType)
    (static : ProperSatisfaction alignment (.ordinary producer) demand) :
    Type where
  source : StableIdentityReduction.ReadyInterface sig targetContext
  sourcePlan_eq : source.interface.plan = producer.plan
  sourceSteps : Exp.Steps producer.package.expression source.package
  target : StableIdentityReduction.ReadyInterface sig targetContext
  targetPlan_eq : target.interface.plan = demand.plan
  adapter : StableIdentity.Adapter targetContext source.interface.plan
    target.interface.plan
  adapter_heq : HEq adapter static.adapter
  execution : StableIdentityReduction.Ordinary source target adapter

/-- The operational boundary cannot silently treat static Bottom synthesis as
an ordinary reduction. Ordinary producers require full ready execution;
absurd producers expose only their Bottom provenance and must be eliminated by
the later closed/coherent impossibility theorem. -/
inductive ProperExecutionEvidence
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {producerScope demandScope : ScopeModel sourceContext targetContext}
    (alignment : ScopeAlignment producerScope.view demandScope.view) :
    {sourceType : LambdaPFC.Ty n} ->
    (producer : ProperProducer sourceContext targetContext producerScope
      sourceType) ->
    (demand : ProperDemand sourceContext targetContext demandScope sourceType) ->
    ProperSatisfaction alignment producer demand -> Type where
  | ordinary
      (execution : OrdinarySatisfactionExecution alignment producer demand
        static) :
      ProperExecutionEvidence alignment (.ordinary producer) demand static
  | absurd
      (bottom : BottomProducer sourceContext targetContext)
      (advertised : LambdaPFC.Ty n)
      (demand : ProperDemand sourceContext targetContext demandScope advertised)
      (static : ProperSatisfaction alignment (.absurd bottom advertised)
        demand) :
      ProperExecutionEvidence alignment (.absurd bottom advertised) demand
        static

/-! ## Focused checks -/

noncomputable example
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) (index : Fin n) :
    CompiledPackage targetContext (scope.view index).plan :=
  scope.package index

noncomputable example
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (scope : ScopeModel sourceContext targetContext)
    (producer : OrdinaryProducer sourceContext targetContext scope sourceType) :
    ScopeModel (sourceContext.snoc sourceType)
      (producer.plan.context targetContext) :=
  scope.bind producer.modeled

end LambdaPToFCo.Full.TranslationInterfaces
