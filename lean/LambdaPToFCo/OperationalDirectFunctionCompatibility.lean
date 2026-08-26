import LambdaPToFCo.OperationalFunctionPathSpine
import LambdaPToFCo.TermTranslationNaturality

/-!
# Directly allocated function-slot compatibility

This module is an external companion to `StoreEnvironment`.  It records and
generates the narrow direct-allocation facts needed by the exact-core
application theorem without changing the store, admissibility, or machine
image definitions.
-/

namespace LambdaPToFCo
namespace OperationalDirectFunctionCompatibility

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalEnvironment
open OperationalBindingView
open OperationalApplication
open OperationalApplicationTranslation
open OperationalApplicationSpine
open OperationalStoreEnvironment
open OperationalPathCoherence
open OperationalTypedPathView
open OperationalResultContext
open OperationalFunctionPathSpine

/-! ## One-call application wrappers -/

@[simp] theorem application_context_transport
    {plan : Interface.BinderPlan []} {body : Exp plan.scope}
    {first second argument : Exp []} (equal : first = second)
    (application : ApplicationView body first argument) :
    (equal ▸ application).context = application.context := by
  cases equal
  rfl

theorem equality_transport_irrel {source target : Sort u}
    (first second : target = source) (value : source) :
    Eq.mpr first value = Eq.mpr second value := by
  have proof_eq : first = second := Subsingleton.elim _ _
  cases proof_eq
  rfl

theorem equality_transport_symm_irrel {source target : Sort u}
    (forward : source = target) (backward : target = source)
    (value : source) :
    Eq.mpr backward value = Eq.mp forward value := by
  cases forward
  have proof_eq : backward = rfl := Subsingleton.elim _ _
  cases proof_eq
  rfl

namespace DirectNativeCompatibility

/-- The endpoint application built from direct native compatibility carries
the generated result-context normalization property. -/
noncomputable def generatedApplication
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    {store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment}
    {functionPath argumentPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    {functionTyping : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken)}
    {spine : FunctionPathSpine functionTyping}
    {native : NativeFunctionImage
      (store.lookup
        (typedPathReferent functionTyping)).compiled.slot.behavior.argument}
    {argumentTyping : Fragment.HasType sourceContext (.path argumentPath)
      domain}
    (compatibility : DirectNativeCompatibility store spine native)
    (coherent : StorePathCoherence store)
    (functionImage : ClosedPathView scope functionTyping environment)
    (argumentImage : ClosedPathView scope argumentTyping environment) :
    GeneratedApplicationView
      (compatibility.endpointApplication coherent functionImage
        argumentImage) := by
  let evidence := spine.closedArgumentEvidence scope environment native.value
    compatibility.baseEvidence argumentImage
  let canonical :=
    (spine.closedView scope environment native.value).normalize.value
      |>.application evidence.toArgumentView
  let endpointEq :
      (spine.closedView scope environment native.value).normalize.value.expression =
        functionImage.view.argument :=
    spine.canonical_eq_pathArgument scope environment native.value
      (compatibility.base_eq coherent) functionImage
  have application_eq :
      compatibility.endpointApplication coherent functionImage
          argumentImage =
        endpointEq ▸ canonical := by
    simp only [DirectNativeCompatibility.endpointApplication,
      FunctionPathSpine.endpointApplication, canonical, evidence]
    rw [eq_mpr_eq_cast]
    apply eq_of_heq
    exact (cast_heq _ _).trans
      (@eqRec_heq (Exp [])
        (fun function => ApplicationView native.body function
          argumentImage.view.argument) _ _ endpointEq
        ((spine.closedView scope environment native.value).normalize.value
          |>.application
            (spine.closedArgumentEvidence scope environment native.value
              compatibility.baseEvidence argumentImage).toArgumentView)).symm
  have context_eq :
      (compatibility.endpointApplication coherent functionImage
        argumentImage).context = canonical.context := by
    rw [application_eq]
    exact application_context_transport endpointEq canonical
  change GeneratedResultContext
    (compatibility.endpointApplication coherent functionImage
      argumentImage).context
  rw [context_eq]
  exact (spine.closedView scope environment native.value).normalize.value
    |>.generatedApplication evidence.toArgumentView

/-- Complete target steps for the closed source application, specialized to
one store compatibility witness. -/
theorem closedApplication_steps
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    {store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment}
    {functionPath argumentPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    {functionTyping : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken)}
    {spine : FunctionPathSpine functionTyping}
    {native : NativeFunctionImage
      (store.lookup
        (typedPathReferent functionTyping)).compiled.slot.behavior.argument}
    {argumentTyping : Fragment.HasType sourceContext (.path argumentPath)
      domain}
    (codomainWf : Fragment.Wf sourceContext codomain)
    (compatibility : DirectNativeCompatibility store spine native)
    (coherent : StorePathCoherence store)
    (functionImage : ClosedPathView scope functionTyping environment)
    (argumentImage : ClosedPathView scope argumentTyping environment) :
    let application := compatibility.endpointApplication coherent functionImage
      argumentImage
    Exp.Steps
      (environment.closeExp
        (TermTranslation.elaborate scope
          (.app functionTyping argumentTyping codomainWf)))
      (application.context.plug
        (native.body.subst application.elimination.substitution)) := by
  simpa only [DirectNativeCompatibility.endpointApplication] using
    spine.closedApplication_steps codomainWf scope environment native.value
      (compatibility.base_eq coherent) compatibility.baseEvidence functionImage
      argumentImage

end DirectNativeCompatibility

namespace DirectNativeCompatibility

/-- A native-only heap growth preserves direct lexical/native compatibility.
Neither lexical target behavior nor the function's independently retained
native closure changes. -/
noncomputable def nativeWeaken
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    {store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment}
    {functionPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    {functionTyping : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken)}
    {spine : FunctionPathSpine functionTyping}
    {native : NativeFunctionImage
      (store.lookup
        (typedPathReferent functionTyping)).compiled.slot.behavior.argument}
    (compatibility : DirectNativeCompatibility store spine native)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    DirectNativeCompatibility
      (store.nativeWeaken runtimeValue runtimeReady) spine native := by
  exact
    { lexicalBehavior_eq := compatibility.lexicalBehavior_eq
      domainPlan_eq := compatibility.domainPlan_eq }

end DirectNativeCompatibility

/-! ## A directly allocated newest function variable -/

namespace DirectAllocation

noncomputable def ordinaryShapeWeaken
    {sourceType : LambdaPFC.Ty n} (shape : OrdinaryShape sourceType) :
    OrdinaryShape sourceType.weaken := by
  cases shape <;> constructor

@[simp] theorem pathReferentIndex_of_var
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {index : Fin n} {sourceType : LambdaPFC.Ty n}
    (typing : Fragment.PathTy sourceContext (.var index) sourceType) :
    pathReferentIndex typing = index := by
  cases typing
  rfl

/-- The generated typing and source-only spine for the newest variable
introduced at a precise function type.  Keeping the derivation and its spine
together avoids assuming proof irrelevance for `Fragment.HasType`. -/
structure GeneratedPath
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {domain codomain : LambdaPFC.Ty n}
    (domainWf : Fragment.Wf sourceContext domain)
    (codomainWf : Fragment.Wf sourceContext codomain)
    (domainShape : OrdinaryShape domain) : Type where
  typing : Fragment.HasType
      (sourceContext.snoc (.Fun domain codomain.weaken))
      (.path (.var 0))
      (.Fun domain.weaken codomain.weaken.weaken)
  spine : FunctionPathSpine typing

noncomputable def generatedPath
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {domain codomain : LambdaPFC.Ty n}
    (domainWf : Fragment.Wf sourceContext domain)
    (codomainWf : Fragment.Wf sourceContext codomain)
    (domainShape : OrdinaryShape domain) :
    GeneratedPath domainWf codomainWf domainShape := by
  let pathTyping : Fragment.PathTy
      (sourceContext.snoc (.Fun domain codomain.weaken)) (.var 0)
      (.Fun domain.weaken codomain.weaken.weaken) := by
    let raw := Fragment.PathTy.var
      (Γ := sourceContext.snoc (.Fun domain codomain.weaken)) (x := 0)
    change Fragment.PathTy
      (sourceContext.snoc (.Fun domain codomain.weaken)) (.var 0)
      (.Fun domain.weaken
        (codomain.weaken.rename LambdaPFC.FinFun.weaken.ext)) at raw
    rw [← LambdaPFC.Ty.weaken_rename codomain LambdaPFC.FinFun.weaken]
      at raw
    exact raw
  let typing := Fragment.HasType.sub (.path pathTyping)
    (.widen pathTyping
      (.arrow (domainWf.weaken (.Fun domain codomain.weaken))
        (codomainWf.weaken (.Fun domain codomain.weaken))))
  exact
    { typing := typing
      spine := .widen pathTyping
        (domainWf.weaken (.Fun domain codomain.weaken))
        (codomainWf.weaken (.Fun domain codomain.weaken))
        (ordinaryShapeWeaken domainShape) }

@[simp] theorem generatedPath_referent
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {domain codomain : LambdaPFC.Ty n}
    (domainWf : Fragment.Wf sourceContext domain)
    (codomainWf : Fragment.Wf sourceContext codomain)
    (domainShape : OrdinaryShape domain) :
    typedPathReferent
      (generatedPath domainWf codomainWf domainShape).typing = 0 := by
  unfold generatedPath
  simp only [typedPathReferent, pathReferentIndex_of_var]

/-- Complete external data for a direct function allocation.

`nativeBehavior_eq` and `domainPlan_eq` are deliberately local to this
function-head witness; the generic store environment keeps native closed
values separate from adapted lexical behavior.  The latter equality records
that the current lexical function domain and the independently closed native
function domain select the same target binder plan. -/
structure Evidence
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : ClosingEnv sig []}
    (older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing)
    {sourceTerm : LambdaPFC.Tm lexical}
    {domain codomain : LambdaPFC.Ty lexical}
    (typing : Fragment.HasType sourceContext sourceTerm
      (.Fun domain codomain.weaken))
    (domainWf : Fragment.Wf sourceContext domain)
    (codomainWf : Fragment.Wf sourceContext codomain)
    (domainShape : OrdinaryShape domain)
    {nativeArity : Nat} {nativeContext : LambdaPFC.Ctx nativeArity}
    {nativeDomain nativeAdvertisedDomain nativeCodomain :
      LambdaPFC.Ty nativeArity}
    {nativeBody : LambdaPFC.Tm (nativeArity + 1)}
    (nativeTyping : Fragment.HasType nativeContext
      (.abs nativeDomain nativeBody)
      (.Fun nativeAdvertisedDomain nativeCodomain.weaken))
    (nativeValuation : SourceValuation nativeArity current)
    (nativeSpine : ApplicationSpine nativeTyping)
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    (nativeScope : Scope nativeContext nativeTargetContext)
    (nativeClosing : ClosingEnv nativeSig [])
    (nativeEnvironment : StoreEnvironment nativeContext sourceStore
      nativeValuation nativeTargetContext nativeScope nativeClosing)
    {runtimeValue : LambdaPFC.Tm current}
    (runtimeReady : runtimeValue.IsValue) : Type where
  nativeReady :
    (ApplicationValueEvidence.function nativeSpine).ClosedReady nativeScope
      nativeClosing
  nativeAdmissible :
    OperationalAdmissibility.OperationallyAdmissible nativeTyping
  runtime_eq : runtimeValue =
    (LambdaPFC.Tm.abs nativeDomain nativeBody).rename nativeValuation
  memberCell : MemberCell (.Fun domain codomain.weaken)
    (.val sourceStore runtimeValue runtimeReady) valuation.weaken 0
  functionCell : FunctionCell (.Fun domain codomain.weaken)
    (.val sourceStore runtimeValue runtimeReady) valuation.weaken 0
  behavior : EliminationView
    ((TermTranslation.compileBinder scope typing.typeWf).plan.subst
      olderClosing.substitution)
  nativeBehavior_eq :
    ((ApplicationValueEvidence.function nativeSpine).closedView nativeScope
      nativeClosing nativeReady).view.argument = behavior.argument
  normalizes : Exp.Steps
    (olderClosing.closeExp (TermTranslation.elaborate scope typing))
    behavior.argument
  domainPlan_eq :
    closedPlan
        (TermTranslation.compileBinder scope typing.typeWf).extended
        (extendClosing olderClosing
          (TermTranslation.compileBinder scope typing.typeWf).plan behavior)
        (generatedPath domainWf codomainWf domainShape).spine.baseDomainWf =
      closedPlan nativeScope nativeClosing nativeSpine.domainWf

namespace Evidence

variable
    {lexical current : Nat}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation lexical current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {olderClosing : ClosingEnv sig []}
    (older : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope olderClosing)
    {sourceTerm : LambdaPFC.Tm lexical}
    {domain codomain : LambdaPFC.Ty lexical}
    (typing : Fragment.HasType sourceContext sourceTerm
      (.Fun domain codomain.weaken))
    (domainWf : Fragment.Wf sourceContext domain)
    (codomainWf : Fragment.Wf sourceContext codomain)
    (domainShape : OrdinaryShape domain)
    {nativeArity : Nat} {nativeContext : LambdaPFC.Ctx nativeArity}
    {nativeDomain nativeAdvertisedDomain nativeCodomain :
      LambdaPFC.Ty nativeArity}
    {nativeBody : LambdaPFC.Tm (nativeArity + 1)}
    (nativeTyping : Fragment.HasType nativeContext
      (.abs nativeDomain nativeBody)
      (.Fun nativeAdvertisedDomain nativeCodomain.weaken))
    (nativeValuation : SourceValuation nativeArity current)
    (nativeSpine : ApplicationSpine nativeTyping)
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    (nativeScope : Scope nativeContext nativeTargetContext)
    (nativeClosing : ClosingEnv nativeSig [])
    (nativeEnvironment : StoreEnvironment nativeContext sourceStore
      nativeValuation nativeTargetContext nativeScope nativeClosing)
    {runtimeValue : LambdaPFC.Tm current}
    (runtimeReady : runtimeValue.IsValue)

/-- The actual store extension described by direct allocation evidence. -/
noncomputable def store
    (allocation : Evidence older typing domainWf codomainWf domainShape
      nativeTyping nativeValuation nativeSpine nativeScope nativeClosing
      nativeEnvironment runtimeReady) :
    StoreEnvironment
      (sourceContext.snoc (.Fun domain codomain.weaken))
      (.val sourceStore runtimeValue runtimeReady) valuation.ext
      ((TermTranslation.compileBinder scope typing.typeWf).plan.context
        targetContext)
      (TermTranslation.compileBinder scope typing.typeWf).extended
      (extendClosing olderClosing
        (TermTranslation.compileBinder scope typing.typeWf).plan
        allocation.behavior) :=
  .extend older typing (TypedCode.ofTyping nativeTyping) nativeValuation
    allocation.nativeAdmissible (.function nativeSpine) nativeEnvironment
    allocation.nativeReady
    runtimeReady allocation.runtime_eq allocation.memberCell
    allocation.functionCell allocation.behavior allocation.normalizes

/-- Closed native function image generated directly from the retained
function branch and `nativeBehavior_eq`, before reindexing it to the physical
cell exposed by lookup. -/
noncomputable def behaviorImage
    (allocation : Evidence older typing domainWf codomainWf domainShape
      nativeTyping nativeValuation nativeSpine nativeScope nativeClosing
      nativeEnvironment runtimeReady) :
    NativeFunctionImage allocation.behavior.argument :=
  NativeFunctionImage.ofApplicationSpine nativeSpine nativeScope nativeClosing
    allocation.nativeReady allocation.behavior.argument
    allocation.nativeBehavior_eq

@[simp] theorem lookup_compiledBehavior_eq
    (allocation : Evidence older typing domainWf codomainWf domainShape
      nativeTyping nativeValuation nativeSpine nativeScope nativeClosing
      nativeEnvironment runtimeReady) :
    ((allocation.store.lookup
      (typedPathReferent
        (generatedPath domainWf codomainWf domainShape).typing)).compiled.slot.behavior.argument) =
      allocation.behavior.argument := by
  rw [generatedPath_referent]
  rfl

@[simp] theorem lookup_lexicalBehavior_eq
    (allocation : Evidence older typing domainWf codomainWf domainShape
      nativeTyping nativeValuation nativeSpine nativeScope nativeClosing
      nativeEnvironment runtimeReady) :
    ((allocation.store.lookup
      (typedPathReferent
        (generatedPath domainWf codomainWf domainShape).typing)).slot.behavior.argument) =
      allocation.behavior.argument := by
  rw [generatedPath_referent]
  rfl

/-- The same native image, indexed exactly by the physical compiled slot
returned from lookup of the newly allocated variable. -/
noncomputable def nativeImage
    (allocation : Evidence older typing domainWf codomainWf domainShape
      nativeTyping nativeValuation nativeSpine nativeScope nativeClosing
      nativeEnvironment runtimeReady) :
    NativeFunctionImage
      ((allocation.store.lookup
        (typedPathReferent
          (generatedPath domainWf codomainWf domainShape).typing)).compiled.slot.behavior.argument) := by
  exact NativeFunctionImage.ofApplicationSpine nativeSpine nativeScope
    nativeClosing allocation.nativeReady _
    (allocation.nativeBehavior_eq.trans
      allocation.lookup_compiledBehavior_eq.symm)

/-- A direct newest allocation satisfies lexical/native endpoint equality
definitionally; the retained `domainPlan_eq` supplies the second field. -/
noncomputable def compatibility
    (allocation : Evidence older typing domainWf codomainWf domainShape
      nativeTyping nativeValuation nativeSpine nativeScope nativeClosing
      nativeEnvironment runtimeReady) :
    DirectNativeCompatibility allocation.store
      (generatedPath domainWf codomainWf domainShape).spine
      allocation.nativeImage := by
  refine
    { lexicalBehavior_eq := ?_
      domainPlan_eq := ?_ }
  · rw [allocation.lookup_lexicalBehavior_eq,
      allocation.lookup_compiledBehavior_eq]
  · simpa only [nativeImage, NativeFunctionImage.ofApplicationSpine] using
      allocation.domainPlan_eq

end Evidence
end DirectAllocation

end OperationalDirectFunctionCompatibility
end LambdaPToFCo
