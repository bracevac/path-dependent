import LambdaPToFCo.Full.RecordFirstLetPlanningRegression
import LambdaPToFCo.Full.DemandDirectedPairSubtyping
import LambdaPToFCo.Full.TargetModelRenaming

/-!
# Static compilation of the first Record value

This leaf compiles `LambdaPFC.RecordRegression.firstValue` after the actual
implementation package has been opened by the enclosing source `let`.  The
direct type-member pair is constructed from one demand-local witness plan and
then adapted along the source regression's literal
`.pair (.widen .var) .refl` derivation to `firstRecord`.

The first widening is sealed to the exact translated variable package and
its resolved referent plan.  The reflexive interval member crosses only the
corresponding singleton-to-referent binder relation; both observed Function
endpoint plans are target-renamed into the rank-2 bridge context and use the
rule-specific heterogeneous reflexivity evidence.  No resolver, selection
witness, target adapter, coercion, package callback, readiness claim, or
restricted-calculus premise is supplied.
-/

namespace LambdaPToFCo.Full.RecordFirstValueStaticRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open DemandDirectedSubtyping
open IntervalPairSubtypingRuleConstruction
open DemandDirectedPairSubtyping

noncomputable section

abbrev SourceContext := RecordIntroductionStaticRegression.Source.context1

abbrev TargetContext :=
  RecordImplementationStaticRegression.compiled.plan.context
    SystemFCoExt.Ctx.empty

/-- The independently developed constructor scope is definitionally the
scope obtained by opening the actual compiled implementation package. -/
theorem bodyScope_eq : RecordImplementationStaticRegression.letBodyScope =
    RecordIntroductionStaticRegression.context1Scope :=
  RecordFirstLetPlanningRegression.bodyScope_eq

abbrev BodyScope := RecordIntroductionStaticRegression.context1Scope

abbrev SourceFirst : LambdaPFC.Ty 1 := .Single (.var 0)
abbrev TargetFirst : LambdaPFC.Ty 1 :=
  LambdaPFC.RecordRegression.implementationType
abbrev Endpoint : LambdaPFC.Ty 2 :=
  LambdaPFC.RecordRegression.implementationType.weaken

abbrev SourcePair : LambdaPFC.Ty 1 :=
  .Pair SourceFirst LambdaPFC.RecordRegression.typeLabel
    (.intv Endpoint Endpoint)
abbrev TargetPair : LambdaPFC.Ty 1 :=
  .Pair TargetFirst LambdaPFC.RecordRegression.typeLabel
    (.intv Endpoint Endpoint)

/-- The source first component is the exact variable path installed by the
compiled implementation binding. -/
def firstPrecise : Path.Ty SourceContext (.var 0) (.ty TargetFirst) := by
  exact .var

noncomputable def firstPath := BodyScope.variablePath (0 : Fin 1)

noncomputable def witnessBoundScope :=
  PairIntroductionCompiler.bindVariableSingleton BodyScope (0 : Fin 1)

/-- `implementationType` is path-free, so its weakened witness is compiled
structurally in exactly the singleton-bound scope demanded by `tpair`. -/
noncomputable def witnessPlan :
    PairIntroductionCompiler.WitnessPlan BodyScope (0 : Fin 1)
      LambdaPFC.RecordRegression.implementationType := by
  simpa [LambdaPFC.RecordRegression.implementationType,
    LambdaPFC.Ty.weaken, LambdaPFC.Ty.rename] using
    (RecordIntroductionStaticRegression.implementationResult witnessBoundScope)

/-- Direct compilation of the existing source `firstValue`, before its
enclosing subsumption. -/
noncomputable def source : OrdinaryProducer SourceContext TargetContext
    BodyScope SourcePair := by
  simpa [SourcePair, SourceFirst, Endpoint, LambdaPFC.Tau.weaken,
    LambdaPFC.Ty.weaken, LambdaPFC.Tau.rename, LambdaPFC.Ty.rename] using
    (PairIntroductionCompiler.typePairFromWitnessPlan BodyScope (0 : Fin 1)
      LambdaPFC.RecordRegression.typeLabel
      LambdaPFC.RecordRegression.implementationTypeWf witnessPlan)

def firstSubtyping : Tau.Sub SourceContext (.ty SourceFirst) (.ty TargetFirst) :=
  .widen firstPrecise

def memberSubtyping : Tau.Sub (SourceContext.snoc SourceFirst)
    (.intv Endpoint Endpoint) (.intv Endpoint Endpoint) :=
  .refl

/-- The proof is intentionally the literal source derivation; the member is
not replaced by an extensionally equivalent `.bounds` proof. -/
def pairSubtyping : Tau.Sub SourceContext (.ty SourcePair) (.ty TargetPair) :=
  .pair firstSubtyping memberSubtyping

/-! ## A firstRecord demand sharing the translated variable plan -/

/-- Both polarities of the implementation binding after its actual package
has been opened.  The plan is exactly `firstPath.plan`, so widening introduces
no independent representation or selected witness. -/
noncomputable def openedTargetFirstModel : BidirectionalPlanModel
    SourceContext TargetContext BodyScope.view TargetFirst firstPath.plan := by
  unfold BodyScope RecordIntroductionStaticRegression.context1Scope
  unfold ScopeModel.bindBidirectional
  simpa [TargetFirst, LambdaPFC.RecordRegression.implementationType,
    LambdaPFC.Ty.weaken, LambdaPFC.Ty.rename, ScopeModel.variablePath,
    ProperPathPackage.plan, ValueInterface.ofArguments_plan] using
    (BidirectionalPlanModel.both
      (ProducerPlanModel.bound
        RecordIntroductionStaticRegression.rootImplementation.model.producer)
      (DemandPlanModel.underBinding
        RecordIntroductionStaticRegression.rootImplementation.model.producer
        RecordIntroductionStaticRegression.rootImplementation.model.demand))

noncomputable def targetFirstResult : WfPlan.Proper SourceContext
    TargetContext BodyScope TargetFirst where
  wf := LambdaPFC.RecordRegression.implementationTypeWf
  plan := firstPath.plan
  model := openedTargetFirstModel

noncomputable def targetBoundScope :=
  BodyScope.bindBidirectional targetFirstResult.model

noncomputable def targetEndpointResult :=
  RecordIntroductionStaticRegression.implementationResult targetBoundScope

noncomputable def targetMemberResult : WfPlan.Interval
    (SourceContext.snoc TargetFirst)
    (targetFirstResult.plan.context TargetContext) targetBoundScope
    Endpoint Endpoint := by
  simpa [Endpoint, LambdaPFC.RecordRegression.implementationType,
    LambdaPFC.Ty.weaken, LambdaPFC.Ty.rename] using
    (WfPlan.Interval.bounds targetBoundScope targetEndpointResult
      targetEndpointResult Tau.Sub.refl)

/-- A valid bidirectional `firstRecord` result whose first observation plan
is the exact resolved implementation-variable plan. -/
noncomputable def targetResult : WfPlan.Proper SourceContext TargetContext
    BodyScope TargetPair :=
  WfPlan.Proper.intervalPair BodyScope targetFirstResult targetMemberResult

noncomputable def demand := targetResult.demand

noncomputable def endpoints : EndpointModels source demand where
  sourceFirstPlan := firstPath.plan
  sourceLowerPlan := witnessPlan.plan
  sourceUpperPlan := witnessPlan.plan
  sourceFirstModel :=
    (PairIntroductionCompiler.variableSingleton BodyScope (0 : Fin 1)).modeled
  sourceMemberModel := .bounds witnessPlan.model.demand
    witnessPlan.model.producer
  sourceModel_eq := rfl
  targetFirstPlan := targetFirstResult.plan
  targetLowerPlan := targetEndpointResult.plan
  targetUpperPlan := targetEndpointResult.plan
  targetFirstModel := targetFirstResult.model
  targetMemberModel := targetMemberResult.model
  demandModel_eq := rfl

/-- The direct `tpair` and target Wf construction share the first plan. -/
theorem firstPlans_eq : endpoints.sourceFirstPlan =
    endpoints.targetFirstPlan := by
  rfl

/-- Their path-free Function endpoint plans are also definitionally equal
before the rank-2 representation bridge renames them. -/
theorem endpointPlans_eq : endpoints.sourceLowerPlan =
    endpoints.targetLowerPlan := by
  rfl

/-! ## Sealed first-field widening -/

noncomputable def firstFused : FusedAdaptation
    (ScopeAlignment.identity BodyScope.view) firstSubtyping
    (.ordinary firstPath.singletonProducer) targetFirstResult.demand :=
  FusedAdaptation.widenResolved (ScopeAlignment.identity BodyScope.view)
    firstPrecise firstPath (DemandTrace.ofWf targetFirstResult.wf)
    targetFirstResult.model.demand

noncomputable def first : FirstAdaptation endpoints firstSubtyping where
  producerScope := BodyScope
  consumerScope := BodyScope
  alignment := ScopeAlignment.identity BodyScope.view
  producer := .ordinary firstPath.singletonProducer
  consumer := targetFirstResult.demand
  adaptation := firstFused
  producerPlan_eq := rfl
  consumerPlan_eq := rfl

/-! ## Exact endpoint models in the rank-2 common context -/

noncomputable abbrev SourceFirstPlan := endpoints.sourceFirstPlan
noncomputable abbrev SourceLowerPlan := endpoints.sourceLowerPlan
noncomputable abbrev SourceUpperPlan := endpoints.sourceUpperPlan
noncomputable abbrev TargetFirstPlan := endpoints.targetFirstPlan

noncomputable abbrev SourceRepresentation :=
  Pair.Interval.representation SourceFirstPlan SourceLowerPlan.inputTy
    SourceUpperPlan.inputTy

noncomputable abbrev SourceMemberAtBinder :=
  IntervalPairRepresentationBridgeConstruction.sourceMemberAtBinder
    SourceFirstPlan SourceLowerPlan SourceUpperPlan

noncomputable abbrev TargetFirstAtSource :=
  IntervalPairRepresentationBridgeConstruction.targetFirstAtSource
    SourceFirstPlan SourceLowerPlan SourceUpperPlan TargetFirstPlan

/-- The literal composition through which an endpoint plan is renamed: open
the source representation's first telescope, pass its interval-member
telescope, then open the adapted target first package. -/
noncomputable def endpointMapping : Rename SourceFirstPlan.scope
    TargetFirstAtSource.scope :=
  ((SourceFirstPlan.telescope.liftRename (Rename.weaken .var)).comp
    SourceMemberAtBinder.weaken).comp
    TargetFirstAtSource.telescope.weaken

noncomputable def endpointMappingTyped : Rename.Typed
    (SourceFirstPlan.context TargetContext)
    (CommonEndpointContext endpoints) endpointMapping := by
  apply Rename.Typed.comp
  · apply Rename.Typed.comp
    · exact SourceFirstPlan.telescope.liftRename_typed
        (Rename.Typed.weaken TargetContext (.var SourceRepresentation.existsTy))
    · exact SourceMemberAtBinder.weaken_typed
        ((IntervalPairRepresentationBridgeConstruction.sourceFirstAtBinder
          SourceFirstPlan).context
          (TargetContext.bindVar SourceRepresentation.existsTy))
  · exact TargetFirstAtSource.telescope.weaken_typed
      (IntervalPairRepresentationBridgeConstruction.sourceOpenedContext
        TargetContext SourceFirstPlan SourceLowerPlan SourceUpperPlan)

/-- Producer-side scope under the singleton binder, renamed to the bridge's
common context with its full structural Function endpoint models intact. -/
noncomputable def leftScope : ScopeModel
    (SourceContext.snoc SourceFirst) (CommonEndpointContext endpoints) :=
  witnessBoundScope.targetRename endpointMapping endpointMappingTyped

/-- Demand-side scope under the widened implementation binder, renamed by
the same proof-relevant target mapping. -/
noncomputable def rightScope : ScopeModel
    (SourceContext.snoc TargetFirst) (CommonEndpointContext endpoints) :=
  targetBoundScope.targetRename endpointMapping endpointMappingTyped

noncomputable def lowerAlignment : ScopeAlignment rightScope.view
    leftScope.view :=
  ScopeAlignment.identity leftScope.view

noncomputable def upperAlignment : ScopeAlignment leftScope.view
    rightScope.view :=
  ScopeAlignment.identity leftScope.view

noncomputable def lowerProducer : PositivePlan
    (SourceContext.snoc TargetFirst) (CommonEndpointContext endpoints)
    rightScope.view Endpoint where
  model := ⟨targetEndpointResult.plan.rename endpointMapping,
    TargetModelRenaming.producer targetEndpointResult.model.producer
      endpointMapping endpointMappingTyped⟩

noncomputable def lowerDemand : NegativePlan
    (SourceContext.snoc SourceFirst) (CommonEndpointContext endpoints)
    leftScope.view Endpoint where
  model := ⟨witnessPlan.plan.rename endpointMapping,
    TargetModelRenaming.demand witnessPlan.model.demand endpointMapping
      endpointMappingTyped⟩

noncomputable def upperProducer : PositivePlan
    (SourceContext.snoc SourceFirst) (CommonEndpointContext endpoints)
    leftScope.view Endpoint where
  model := ⟨witnessPlan.plan.rename endpointMapping,
    TargetModelRenaming.producer witnessPlan.model.producer endpointMapping
      endpointMappingTyped⟩

noncomputable def upperDemand : NegativePlan
    (SourceContext.snoc TargetFirst) (CommonEndpointContext endpoints)
    rightScope.view Endpoint where
  model := ⟨targetEndpointResult.plan.rename endpointMapping,
    TargetModelRenaming.demand targetEndpointResult.model.demand
      endpointMapping endpointMappingTyped⟩

theorem lowerProducerPlan_eq : lowerProducer.plan =
    IntervalPairRepresentationBridgeConstruction.targetLowerAtSource
      endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan
      endpoints.targetLowerPlan := by
  rfl

theorem lowerDemandPlan_eq : lowerDemand.plan =
    IntervalPairRepresentationBridgeConstruction.sourceLowerAtTargetFirst
      endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan := by
  rfl

theorem upperProducerPlan_eq : upperProducer.plan =
    IntervalPairRepresentationBridgeConstruction.sourceUpperAtTargetFirst
      endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan := by
  rfl

theorem upperDemandPlan_eq : upperDemand.plan =
    IntervalPairRepresentationBridgeConstruction.targetUpperAtSource
      endpoints.sourceFirstPlan endpoints.sourceLowerPlan
      endpoints.sourceUpperPlan endpoints.targetFirstPlan
      endpoints.targetUpperPlan := by
  rfl

theorem lowerCommonPlan_eq : lowerDemand.plan = lowerProducer.plan := by
  rfl

theorem upperCommonPlan_eq : upperDemand.plan = upperProducer.plan := by
  rfl

/-- Contravariant lower-endpoint reflexivity under exactly the first
singleton widening. -/
noncomputable def lowerAdaptation :
    ContravariantHeterogeneousPlanAdaptation
      (CommonEndpointContext endpoints)
      (ContextSubtyping.underBinder firstSubtyping) lowerAlignment
      (.refl (τ := .ty Endpoint)) lowerProducer lowerDemand :=
  ContravariantHeterogeneousPlanAdaptation.underWidenReflexive firstPrecise
    lowerAlignment lowerProducer lowerDemand lowerProducer.plan rfl
    lowerCommonPlan_eq

/-- Covariant upper-endpoint reflexivity under the same exact binder
relation. -/
noncomputable def upperAdaptation : HeterogeneousPlanAdaptation
    (CommonEndpointContext endpoints)
    (ContextSubtyping.underBinder firstSubtyping) upperAlignment
    (.refl (τ := .ty Endpoint)) upperProducer upperDemand :=
  HeterogeneousPlanAdaptation.underWidenReflexive firstPrecise upperAlignment
    upperProducer upperDemand upperProducer.plan rfl upperCommonPlan_eq

noncomputable def endpointInput : HeterogeneousEndpointInput endpoints
    firstSubtyping (.refl (τ := .ty Endpoint))
    (.refl (τ := .ty Endpoint)) (.refl (τ := .ty Endpoint)) where
  lowerProducerScope := rightScope
  lowerDemandScope := leftScope
  lowerAlignment := lowerAlignment
  lowerProducer := lowerProducer
  lowerDemand := lowerDemand
  lowerAdaptation := lowerAdaptation
  lowerProducerPlan_eq := lowerProducerPlan_eq
  lowerDemandPlan_eq := lowerDemandPlan_eq
  upperProducerScope := leftScope
  upperDemandScope := rightScope
  upperAlignment := upperAlignment
  upperProducer := upperProducer
  upperDemand := upperDemand
  upperAdaptation := upperAdaptation
  upperProducerPlan_eq := upperProducerPlan_eq
  upperDemandPlan_eq := upperDemandPlan_eq

noncomputable def member : ReflexiveUnderWidenEndpointInput endpoints
    firstPrecise where
  input := endpointInput

/-! ## Exact outer source rule and concrete target package -/

noncomputable def adaptation : PairFusedAdaptation
    (ScopeAlignment.identity BodyScope.view) pairSubtyping source demand :=
  PairFusedAdaptation.ofIntervalReflexiveUnderWiden
    (ScopeAlignment.identity BodyScope.view) firstPrecise source demand
    endpoints first member

/-- The exact target spelling is the existing source regression's
`firstRecord`. -/
theorem targetPair_eq : TargetPair =
    LambdaPFC.RecordRegression.firstRecord := by
  rfl

/-- Full compilation of `RecordRegression.firstValue` through its literal
subsumption into an ordinary producer for `firstRecord`. -/
noncomputable def compiled : OrdinaryProducer SourceContext TargetContext
    BodyScope LambdaPFC.RecordRegression.firstRecord := by
  rw [← targetPair_eq]
  exact adaptation.toOrdinary targetResult.model.producer

/-- The source term retained by the direct introduction is literally the
existing `firstValue`. -/
def exactIntroductionTyping : Tm.Ty SourceContext
    LambdaPFC.RecordRegression.firstValue SourcePair := by
  simpa [LambdaPFC.RecordRegression.firstValue, SourcePair, SourceFirst,
    Endpoint, LambdaPFC.Tau.weaken, LambdaPFC.Ty.weaken,
    LambdaPFC.Tau.rename, LambdaPFC.Ty.rename] using
    (Tm.Ty.tpair (y := (0 : Fin 1))
      (A := LambdaPFC.RecordRegression.typeLabel)
      LambdaPFC.RecordRegression.implementationTypeWf)

def sourceTyping : Tm.Ty SourceContext
    LambdaPFC.RecordRegression.firstValue
    LambdaPFC.RecordRegression.firstRecord := by
  rw [← targetPair_eq]
  exact .sub exactIntroductionTyping pairSubtyping targetResult.wf

/-- The direct compiler retained the literal existing source term and its
type-member introduction proof. -/
theorem source_origin_eq : source.origin =
    ProducerOrigin.value exactIntroductionTyping .pair := by
  rfl

/-- The final producer keeps the exact push derivation and direct source
introduction origin. -/
theorem compiled_origin_eq : compiled.origin =
    ProducerOrigin.push pairSubtyping
      (ProducerOrigin.value exactIntroductionTyping .pair) := by
  rfl

noncomputable def targetTerm := compiled.package.expression

/-- Concrete SystemFCoExt typing for the compiled first-record package. -/
noncomputable def targetTerm_hasType :
    Exp.HasType TargetContext targetTerm compiled.plan.inputTy :=
  compiled.package.typing

end

end LambdaPToFCo.Full.RecordFirstValueStaticRegression
