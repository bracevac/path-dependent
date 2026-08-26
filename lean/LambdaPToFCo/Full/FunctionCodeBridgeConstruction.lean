import LambdaPToFCo.Full.DemandDirectedSubtyping
import LambdaPToFCo.Full.StableIdentitySubstitution

/-!
# Demand-directed dependent-function code bridges

This module constructs the code coercion required by
`DemandDirectedSubtyping.FunctionCodeBridge`.  It does not accept an opaque
prebuilt coercion.  Instead it packages the received target-domain argument
interface, adapts that package to the source domain, opens the adapted package
to apply the retained source code, and finally applies one exact indexed
codomain adapter in the common opened context.

The source function plan still carries a bidirectional domain model.  Only the
target demand's positive domain package is needed by this wrapper.  Bottom
execution and source-selection provenance remain outside this static bridge.
-/

namespace LambdaPToFCo.Full.FunctionCodeBridgeConstruction

open SystemFCoExt
open TranslationInterfaces

private theorem ValuePlan.rename_asSubst
    (plan : ValuePlan source) (mapping : Rename source target) :
    plan.rename mapping = plan.subst mapping.asSubst := by
  cases plan with
  | mk observations =>
      apply congrArg ValuePlan.mk
      rw [Telescope.rename_asSubst]
      simp only [Rename.asSubst_lift]

private noncomputable def Subst.Typed.ofRename
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {mapping : Rename source target}
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Subst.Typed sourceContext targetContext mapping.asSubst where
  lookup := by
    intro kind index binding lookup
    have renamed := typed.lookup lookup
    cases binding with
    | var type =>
        simpa only [Subst.Realizes, Ty.subst_asSubst] using
          (Exp.HasType.var renamed)
    | tvar => exact PUnit.unit
    | cvar source result =>
        simpa only [Subst.Realizes, Ty.subst_asSubst] using
          (Co.HasType.cvar renamed)

private noncomputable def reindexAdapter
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {sourcePlan targetPlan : ValuePlan source}
    (adapter : StableIdentity.Adapter sourceContext sourcePlan targetPlan)
    (mapping : Rename source target)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    StableIdentity.Adapter targetContext (sourcePlan.rename mapping)
      (targetPlan.rename mapping) := by
  have result := adapter.subst mapping.asSubst
    (Subst.Typed.ofRename typed)
  simpa only [← ValuePlan.rename_asSubst] using result

/-! ## The two nested argument scopes -/

def sourceDomainOuter (sourceDomain : ValuePlan sig) :
    ValuePlan (sig ,, .var) :=
  sourceDomain.rename (Rename.weaken .var)

def sourceCodomainOuter (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope) :
    ValuePlan (sourceDomainOuter sourceDomain).scope :=
  Function.renameCodomain sourceDomain sourceCodomain (Rename.weaken .var)

def targetDomainOuter (targetDomain : ValuePlan sig) :
    ValuePlan (sig ,, .var) :=
  targetDomain.rename (Rename.weaken .var)

def targetCodomainOuter (targetDomain : ValuePlan sig)
    (targetCodomain : ValuePlan targetDomain.scope) :
    ValuePlan (targetDomainOuter targetDomain).scope :=
  Function.renameCodomain targetDomain targetCodomain (Rename.weaken .var)

def codeContext (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope) : Ctx (sig ,, .var) :=
  base.bindVar (Function.codeTy sourceDomain sourceCodomain)

def commonContext (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig) :
    Ctx (targetDomainOuter targetDomain).scope :=
  (targetDomainOuter targetDomain).context
    (codeContext base sourceDomain sourceCodomain)

def sourceDomainCommon (sourceDomain targetDomain : ValuePlan sig) :
    ValuePlan (targetDomainOuter targetDomain).scope :=
  (sourceDomainOuter sourceDomain).rename
    (targetDomainOuter targetDomain).telescope.weaken

def targetDomainCommon (targetDomain : ValuePlan sig) :
    ValuePlan (targetDomainOuter targetDomain).scope :=
  (targetDomainOuter targetDomain).rename
    (targetDomainOuter targetDomain).telescope.weaken

def sourceCodomainCommon (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig) :
    ValuePlan (sourceDomainCommon sourceDomain targetDomain).scope :=
  Function.renameCodomain (sourceDomainOuter sourceDomain)
    (sourceCodomainOuter sourceDomain sourceCodomain)
    (targetDomainOuter targetDomain).telescope.weaken

def sourceDomainOpened (sourceDomain targetDomain : ValuePlan sig) :
    ValuePlan (sourceDomainCommon sourceDomain targetDomain).scope :=
  (sourceDomainCommon sourceDomain targetDomain).rename
    (sourceDomainCommon sourceDomain targetDomain).telescope.weaken

def sourceCodomainOpened (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig) :
    ValuePlan (sourceDomainOpened sourceDomain targetDomain).scope :=
  Function.renameCodomain (sourceDomainCommon sourceDomain targetDomain)
    (sourceCodomainCommon sourceDomain sourceCodomain targetDomain)
    (sourceDomainCommon sourceDomain targetDomain).telescope.weaken

noncomputable def sourceArguments (base : Ctx sig)
    (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig) :
    Telescope.Args
      ((sourceDomainCommon sourceDomain targetDomain).context
        (commonContext base sourceDomain sourceCodomain targetDomain))
      (sourceDomainOpened sourceDomain targetDomain).telescope := by
  simpa only [sourceDomainOpened, ValuePlan.telescope_rename] using
    Telescope.Args.identity
      (sourceDomainCommon sourceDomain targetDomain).telescope
      (commonContext base sourceDomain sourceCodomain targetDomain)

noncomputable def sourceResultPlan (base : Ctx sig)
    (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig) :
    ValuePlan (sourceDomainCommon sourceDomain targetDomain).scope :=
  (sourceCodomainOpened sourceDomain sourceCodomain targetDomain).subst
    (sourceArguments base sourceDomain sourceCodomain targetDomain).substitution

def targetResultPlan (sourceDomain targetDomain : ValuePlan sig)
    (targetCodomain : ValuePlan targetDomain.scope) :
    ValuePlan (sourceDomainCommon sourceDomain targetDomain).scope :=
  (targetCodomainOuter targetDomain targetCodomain).rename
    (sourceDomainCommon sourceDomain targetDomain).telescope.weaken

/-- The only dependent codomain seam.  It is fixed at the exact result of
applying the source code to the repackaged source-domain interface and at the
target codomain reindexed into that same opened context. -/
structure ResultAdapter (base : Ctx sig)
    (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (targetCodomain : ValuePlan targetDomain.scope) : Type where
  adapter : StableIdentity.Adapter
    ((sourceDomainCommon sourceDomain targetDomain).context
      (commonContext base sourceDomain sourceCodomain targetDomain))
    (sourceResultPlan base sourceDomain sourceCodomain targetDomain)
    (targetResultPlan sourceDomain targetDomain targetCodomain)

/-! ## Repackage the received target arguments as a source-domain package -/

noncomputable def targetArguments (base : Ctx sig)
    (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig) :
    Telescope.Args (commonContext base sourceDomain sourceCodomain targetDomain)
      (targetDomainCommon targetDomain).telescope := by
  simpa only [targetDomainCommon, ValuePlan.telescope_rename] using
    Telescope.Args.identity (targetDomainOuter targetDomain).telescope
      (codeContext base sourceDomain sourceCodomain)

noncomputable def targetPackage (base : Ctx sig)
    (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig) :
    CompiledPackage (commonContext base sourceDomain sourceCodomain
      targetDomain) (targetDomainCommon targetDomain) where
  expression := (targetDomainCommon targetDomain).pack
    (targetArguments base sourceDomain sourceCodomain targetDomain)
  typing := (targetDomainCommon targetDomain).pack_hasType
    (targetArguments base sourceDomain sourceCodomain targetDomain)

noncomputable def domainAdapterOuter
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (adapter : StableIdentity.Adapter base targetDomain sourceDomain) :
    StableIdentity.Adapter (codeContext base sourceDomain sourceCodomain)
      (targetDomainOuter targetDomain) (sourceDomainOuter sourceDomain) := by
  simpa only [targetDomainOuter, sourceDomainOuter] using
    reindexAdapter adapter (Rename.weaken .var)
      (Rename.Typed.weaken base
        (.var (Function.codeTy sourceDomain sourceCodomain)))

noncomputable def domainAdapterCommon
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (adapter : StableIdentity.Adapter base targetDomain sourceDomain) :
    StableIdentity.Adapter
      (commonContext base sourceDomain sourceCodomain targetDomain)
      (targetDomainCommon targetDomain)
      (sourceDomainCommon sourceDomain targetDomain) := by
  have renamed := reindexAdapter
    (domainAdapterOuter base sourceDomain sourceCodomain targetDomain adapter)
      (targetDomainOuter targetDomain).telescope.weaken
      ((targetDomainOuter targetDomain).telescope.weaken_typed
        (codeContext base sourceDomain sourceCodomain))
  simpa only [targetDomainCommon, sourceDomainCommon] using renamed

noncomputable def sourcePackage
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (adapter : StableIdentity.Adapter base targetDomain sourceDomain) :
    CompiledPackage (commonContext base sourceDomain sourceCodomain
      targetDomain) (sourceDomainCommon sourceDomain targetDomain) :=
  (targetPackage base sourceDomain sourceCodomain targetDomain).adapt
    (domainAdapterCommon base sourceDomain sourceCodomain targetDomain adapter)

/-! ## Apply the retained source code in the twice-opened scope -/

def sourceCodeOuter (sourceDomain : ValuePlan sig)
    (_sourceCodomain : ValuePlan sourceDomain.scope) : Exp (sig ,, .var) :=
  .var .here

noncomputable def sourceCodeOuter_hasType
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope) :
    Exp.HasType (codeContext base sourceDomain sourceCodomain)
      (sourceCodeOuter sourceDomain sourceCodomain)
      (Function.codeTy (sourceDomainOuter sourceDomain)
        (sourceCodomainOuter sourceDomain sourceCodomain)) := by
  have typed : Exp.HasType (codeContext base sourceDomain sourceCodomain)
      (.var .here)
      ((Function.codeTy sourceDomain sourceCodomain).weaken .var) :=
    .var Ctx.Lookup.here
  simpa only [sourceCodeOuter, Ty.weaken, Function.codeTy_rename,
    sourceDomainOuter, sourceCodomainOuter] using typed

def sourceCodeCommon (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig) :
    Exp (targetDomainOuter targetDomain).scope :=
  (sourceCodeOuter sourceDomain sourceCodomain).rename
    (targetDomainOuter targetDomain).telescope.weaken

noncomputable def sourceCodeCommon_hasType
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig) :
    Exp.HasType (commonContext base sourceDomain sourceCodomain targetDomain)
      (sourceCodeCommon sourceDomain sourceCodomain targetDomain)
      (Function.codeTy (sourceDomainCommon sourceDomain targetDomain)
        (sourceCodomainCommon sourceDomain sourceCodomain targetDomain)) := by
  have typed := (sourceCodeOuter_hasType base sourceDomain sourceCodomain).rename
    ((targetDomainOuter targetDomain).telescope.weaken_typed
      (codeContext base sourceDomain sourceCodomain))
  simpa only [sourceCodeCommon, Function.codeTy_rename,
    sourceDomainCommon, sourceCodomainCommon] using typed

def sourceCodeOpened (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig) :
    Exp (sourceDomainCommon sourceDomain targetDomain).scope :=
  (sourceCodeCommon sourceDomain sourceCodomain targetDomain).rename
    (sourceDomainCommon sourceDomain targetDomain).telescope.weaken

noncomputable def sourceCodeOpened_hasType
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig) :
    Exp.HasType
      ((sourceDomainCommon sourceDomain targetDomain).context
        (commonContext base sourceDomain sourceCodomain targetDomain))
      (sourceCodeOpened sourceDomain sourceCodomain targetDomain)
      (Function.codeTy (sourceDomainOpened sourceDomain targetDomain)
        (sourceCodomainOpened sourceDomain sourceCodomain targetDomain)) := by
  have typed := (sourceCodeCommon_hasType base sourceDomain sourceCodomain
    targetDomain).rename
      ((sourceDomainCommon sourceDomain targetDomain).telescope.weaken_typed
        (commonContext base sourceDomain sourceCodomain targetDomain))
  simpa only [sourceCodeOpened, Function.codeTy_rename,
    sourceDomainOpened, sourceCodomainOpened] using typed

noncomputable def appliedSource (base : Ctx sig)
    (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig) :
    Exp (sourceDomainCommon sourceDomain targetDomain).scope :=
  Function.apply (sourceDomainOpened sourceDomain targetDomain)
    (sourceArguments base sourceDomain sourceCodomain targetDomain)
    (sourceCodeOpened sourceDomain sourceCodomain targetDomain)

noncomputable def appliedSource_hasType
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig) :
    Exp.HasType
      ((sourceDomainCommon sourceDomain targetDomain).context
        (commonContext base sourceDomain sourceCodomain targetDomain))
      (appliedSource base sourceDomain sourceCodomain targetDomain)
      (sourceResultPlan base sourceDomain sourceCodomain targetDomain).inputTy :=
  by
    have typed := Function.apply_hasType
      (sourceDomainOpened sourceDomain targetDomain)
      (sourceCodomainOpened sourceDomain sourceCodomain targetDomain)
      (sourceArguments base sourceDomain sourceCodomain targetDomain)
      (sourceCodeOpened sourceDomain sourceCodomain targetDomain)
      (sourceCodeOpened_hasType base sourceDomain sourceCodomain targetDomain)
    simpa only [appliedSource, sourceResultPlan,
      ValuePlan.inputTy_subst] using typed

/-! ## Adapt the dependent result and close both telescopes -/

noncomputable def adaptedResult
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (targetCodomain : ValuePlan targetDomain.scope)
    (resultAdapter : ResultAdapter base sourceDomain sourceCodomain
      targetDomain targetCodomain) :
    Exp (sourceDomainCommon sourceDomain targetDomain).scope :=
  resultAdapter.adapter.apply
    (appliedSource base sourceDomain sourceCodomain targetDomain)

noncomputable def adaptedResult_hasType
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (targetCodomain : ValuePlan targetDomain.scope)
    (resultAdapter : ResultAdapter base sourceDomain sourceCodomain
      targetDomain targetCodomain) :
    Exp.HasType
      ((sourceDomainCommon sourceDomain targetDomain).context
        (commonContext base sourceDomain sourceCodomain targetDomain))
      (adaptedResult base sourceDomain sourceCodomain targetDomain
        targetCodomain resultAdapter)
      ((targetCodomainOuter targetDomain targetCodomain).inputTy.rename
        (sourceDomainCommon sourceDomain targetDomain).telescope.weaken) := by
  have typed := resultAdapter.adapter.apply_hasType
    (appliedSource_hasType base sourceDomain sourceCodomain targetDomain)
  simpa only [adaptedResult, targetResultPlan,
    ValuePlan.inputTy_rename] using typed

noncomputable def targetBody
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (targetCodomain : ValuePlan targetDomain.scope)
    (domainAdapter : StableIdentity.Adapter base targetDomain sourceDomain)
    (resultAdapter : ResultAdapter base sourceDomain sourceCodomain
      targetDomain targetCodomain) :
    Exp (targetDomainOuter targetDomain).scope :=
  (sourcePackage base sourceDomain sourceCodomain targetDomain
      domainAdapter).consume
    (targetCodomainOuter targetDomain targetCodomain).inputTy
    (adaptedResult base sourceDomain sourceCodomain targetDomain
      targetCodomain resultAdapter)

noncomputable def targetBody_hasType
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (targetCodomain : ValuePlan targetDomain.scope)
    (domainAdapter : StableIdentity.Adapter base targetDomain sourceDomain)
    (resultAdapter : ResultAdapter base sourceDomain sourceCodomain
      targetDomain targetCodomain) :
    Exp.HasType (commonContext base sourceDomain sourceCodomain targetDomain)
      (targetBody base sourceDomain sourceCodomain targetDomain targetCodomain
        domainAdapter resultAdapter)
      (targetCodomainOuter targetDomain targetCodomain).inputTy :=
  (sourcePackage base sourceDomain sourceCodomain targetDomain
      domainAdapter).consume_hasType
    (targetCodomainOuter targetDomain targetCodomain).inputTy
    (adaptedResult base sourceDomain sourceCodomain targetDomain
      targetCodomain resultAdapter)
    (adaptedResult_hasType base sourceDomain sourceCodomain targetDomain
      targetCodomain resultAdapter)

noncomputable def wrapperBody
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (targetCodomain : ValuePlan targetDomain.scope)
    (domainAdapter : StableIdentity.Adapter base targetDomain sourceDomain)
    (resultAdapter : ResultAdapter base sourceDomain sourceCodomain
      targetDomain targetCodomain) : Exp (sig ,, .var) :=
  Function.abstraction (targetDomainOuter targetDomain)
    (targetBody base sourceDomain sourceCodomain targetDomain targetCodomain
      domainAdapter resultAdapter)

noncomputable def wrapperBody_hasType
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (targetCodomain : ValuePlan targetDomain.scope)
    (domainAdapter : StableIdentity.Adapter base targetDomain sourceDomain)
    (resultAdapter : ResultAdapter base sourceDomain sourceCodomain
      targetDomain targetCodomain) :
    Exp.HasType (codeContext base sourceDomain sourceCodomain)
      (wrapperBody base sourceDomain sourceCodomain targetDomain
        targetCodomain domainAdapter resultAdapter)
      ((Function.codeTy targetDomain targetCodomain).weaken .var) := by
  have typed := Function.abstraction_hasType
    (targetDomainOuter targetDomain)
    (targetCodomainOuter targetDomain targetCodomain)
    (targetBody base sourceDomain sourceCodomain targetDomain targetCodomain
      domainAdapter resultAdapter)
    (targetBody_hasType base sourceDomain sourceCodomain targetDomain
      targetCodomain domainAdapter resultAdapter)
  simpa only [wrapperBody, Ty.weaken, Function.codeTy_rename,
    targetDomainOuter, targetCodomainOuter] using typed

noncomputable def codeCoercion
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (targetCodomain : ValuePlan targetDomain.scope)
    (domainAdapter : StableIdentity.Adapter base targetDomain sourceDomain)
    (resultAdapter : ResultAdapter base sourceDomain sourceCodomain
      targetDomain targetCodomain) : Co sig :=
  .adapter (Function.codeTy sourceDomain sourceCodomain)
    (wrapperBody base sourceDomain sourceCodomain targetDomain targetCodomain
      domainAdapter resultAdapter)

noncomputable def codeCoercion_hasType
    (base : Ctx sig) (sourceDomain : ValuePlan sig)
    (sourceCodomain : ValuePlan sourceDomain.scope)
    (targetDomain : ValuePlan sig)
    (targetCodomain : ValuePlan targetDomain.scope)
    (domainAdapter : StableIdentity.Adapter base targetDomain sourceDomain)
    (resultAdapter : ResultAdapter base sourceDomain sourceCodomain
      targetDomain targetCodomain) :
    Co.HasType base
      (codeCoercion base sourceDomain sourceCodomain targetDomain
        targetCodomain domainAdapter resultAdapter)
      (Function.codeTy sourceDomain sourceCodomain)
      (Function.codeTy targetDomain targetCodomain) :=
  Co.HasType.adapter
    (wrapperBody_hasType base sourceDomain sourceCodomain targetDomain
      targetCodomain domainAdapter resultAdapter)

/-! ## Sealed source/demand bridge -/

/-- All non-code fields of a demand-directed function bridge.  Separating
these endpoint models from code construction makes the two computational
inputs visible: the contravariant domain package adapter and the exact
dependent result adapter above. -/
structure EndpointModels
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    (source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain))
    (demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain)) : Type where
  sourceDomainPlan : ValuePlan sig
  sourceCodomainPlan : ValuePlan sourceDomainPlan.scope
  sourceDomainModel : BidirectionalPlanModel sourceContext targetContext
    sourceScope.view sourceDomain sourceDomainPlan
  sourceCodomainModel : ProducerPlanModel
    (sourceContext.snoc sourceDomain)
    (sourceDomainPlan.context targetContext)
    (ScopeView.bindPlan sourceScope.view sourceDomainPlan)
    sourceCodomain sourceCodomainPlan
  sourceModel_eq : source.model =
    ⟨Function.plan sourceDomainPlan sourceCodomainPlan,
      .function sourceDomainModel sourceCodomainModel⟩
  targetDomainPlan : ValuePlan sig
  targetCodomainPlan : ValuePlan targetDomainPlan.scope
  targetDomainModel : ProducerPlanModel sourceContext targetContext
    demandScope.view targetDomain targetDomainPlan
  targetCodomainModel : DemandPlanModel
    (sourceContext.snoc targetDomain)
    (targetDomainPlan.context targetContext)
    (ScopeView.bindPlan demandScope.view targetDomainPlan)
    targetCodomain targetCodomainPlan
  demandModel_eq : demand.model =
    ⟨Function.plan targetDomainPlan targetCodomainPlan,
      .function targetDomainModel targetCodomainModel⟩

/-- Construct the complete sealed bridge without accepting an arbitrary code
coercion.  Its coercion is definitionally the wrapper assembled above. -/
noncomputable def bridge
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {sourceDomain targetDomain : LambdaPFC.Ty n}
    {sourceCodomain targetCodomain : LambdaPFC.Ty (n + 1)}
    {source : OrdinaryProducer sourceContext targetContext sourceScope
      (.Fun sourceDomain sourceCodomain)}
    {demand : ProperDemand sourceContext targetContext demandScope
      (.Fun targetDomain targetCodomain)}
    (endpoints : EndpointModels source demand)
    (domainAdapter : StableIdentity.Adapter targetContext
      endpoints.targetDomainPlan endpoints.sourceDomainPlan)
    (resultAdapter : ResultAdapter targetContext
      endpoints.sourceDomainPlan endpoints.sourceCodomainPlan
      endpoints.targetDomainPlan endpoints.targetCodomainPlan) :
    DemandDirectedSubtyping.FunctionCodeBridge source demand where
  sourceDomainPlan := endpoints.sourceDomainPlan
  sourceCodomainPlan := endpoints.sourceCodomainPlan
  sourceDomainModel := endpoints.sourceDomainModel
  sourceCodomainModel := endpoints.sourceCodomainModel
  sourceModel_eq := endpoints.sourceModel_eq
  targetDomainPlan := endpoints.targetDomainPlan
  targetCodomainPlan := endpoints.targetCodomainPlan
  targetDomainModel := endpoints.targetDomainModel
  targetCodomainModel := endpoints.targetCodomainModel
  demandModel_eq := endpoints.demandModel_eq
  coercion := codeCoercion targetContext endpoints.sourceDomainPlan
    endpoints.sourceCodomainPlan endpoints.targetDomainPlan
    endpoints.targetCodomainPlan domainAdapter resultAdapter
  typing := codeCoercion_hasType targetContext endpoints.sourceDomainPlan
    endpoints.sourceCodomainPlan endpoints.targetDomainPlan
    endpoints.targetCodomainPlan domainAdapter resultAdapter

/-! A focused closed example exercises the actual wrapper syntax.  The
codomain is observation-free, so its exact instantiated adapter is identity;
the construction still packages and reopens the complete domain interface. -/
namespace Regression

def domain : ValuePlan ([] : Sig) := Top.plan []

def codomain : ValuePlan domain.scope := Top.plan domain.scope

noncomputable def domainAdapter :
    StableIdentity.Adapter Ctx.empty domain domain :=
  StableIdentity.Adapter.identity Ctx.empty domain

noncomputable def resultAdapter :
    ResultAdapter Ctx.empty domain codomain domain codomain where
  adapter := StableIdentity.Adapter.identity
    ((sourceDomainCommon domain domain).context
      (commonContext Ctx.empty domain codomain domain))
    (sourceResultPlan Ctx.empty domain codomain domain)

noncomputable def coercion : Co ([] : Sig) :=
  codeCoercion Ctx.empty domain codomain domain codomain
    domainAdapter resultAdapter

noncomputable def coercion_hasType :
    Co.HasType Ctx.empty coercion
      (Function.codeTy domain codomain)
      (Function.codeTy domain codomain) :=
  codeCoercion_hasType Ctx.empty domain codomain domain codomain
    domainAdapter resultAdapter

end Regression

end LambdaPToFCo.Full.FunctionCodeBridgeConstruction
