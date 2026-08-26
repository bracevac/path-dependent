import LambdaPToFCo.OperationalApplicationState
import LambdaPToFCo.OperationalApplicationPathCoherence
import LambdaPToFCo.OperationalTypedPathCoherence

/-!
# Direct-abstraction application successors

This module specializes the premise-driven application image to a native
function allocated directly from `HasType.abs`.  The first lemmas expose the
dependent target body and binder plan intentionally forgotten by
`NativeFunctionImage`; they are the syntactic equations needed to construct
the CK beta successor with `StoreEnvironment.bindLocation`.
-/

namespace LambdaPToFCo
namespace OperationalDirectApplicationExecution

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalEnvironment
open OperationalBindingView
open OperationalApplication
open OperationalApplicationSpine
open OperationalValueEvidence
open OperationalStoreEnvironment
open OperationalFunctionPathSpine
open OperationalAdmissibility
open OperationalMachineImage
open OperationalPathCoherence
open OperationalPathCoherenceGenerated
open OperationalApplicationPathCoherence
open OperationalTypedPathCoherence
open OperationalEnvironmentCoherence
open OperationalStateImage
open OperationalDirectFunctionCompatibility

@[simp] theorem application_elimination_transport
    {plan : Interface.BinderPlan []} {body : Exp plan.scope}
    {first second argument : Exp []} (equal : first = second)
    (application : ApplicationView body first argument) :
    (equal ▸ application).elimination = application.elimination := by
  cases equal
  rfl

@[simp] theorem FunctionValue.application_elimination_eq
    {plan : Interface.BinderPlan []} {result : Ty []}
    {body : Exp plan.scope} {argument : Exp []}
    (function : FunctionValue plan result body)
    (view : ArgumentView function argument) :
    (function.application view).elimination = view.elimination := by
  induction view with
  | lambda => rfl
  | arrow _ _ _ ih => exact ih

namespace FunctionPathSpine

/-- Every restricted function-path spine supplies the path-only
admissibility derivation expected by the executable core. -/
noncomputable def admissible
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {domain codomain : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path path)
      (.Fun domain codomain.weaken)}
    (spine : FunctionPathSpine typing) :
    OperationallyAdmissible typing :=
  .functionPath spine

end FunctionPathSpine

namespace NonCanonicalResultShape

/-- A noncanonical ordinary source type cannot demand abstraction-head
provenance from a physical cell. -/
theorem functionCell
    (shape : NonCanonicalResultShape sourceType) :
    FunctionCell sourceType sourceStore valuation location := by
  intro domain codomain type_eq
  exact (shape.notArrow
    { domain := domain
      codomain := codomain.weaken
      equality := type_eq }).elim

end NonCanonicalResultShape

namespace NativeFunctionImage

/-- A direct abstraction's erased native image retains exactly the closed
compiled binder plan. -/
@[simp] theorem ofApplicationSpine_abs_plan
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {nativeDomain nativeCodomain : LambdaPFC.Ty n}
    {sourceBody : LambdaPFC.Tm (n + 1)}
    (bodyTyping : Fragment.HasType (sourceContext.snoc nativeDomain)
      sourceBody nativeCodomain.weaken)
    (domainWf : Fragment.Wf sourceContext nativeDomain)
    (codomainWf : Fragment.Wf sourceContext nativeCodomain)
    (domainShape : NonCanonicalResultShape nativeDomain)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (ready : ApplicationValueEvidence.ClosedReady
      (ApplicationValueEvidence.function
        (ApplicationSpine.abs bodyTyping domainWf codomainWf domainShape))
      scope environment)
    (behavior : Exp [])
    (behavior_eq :
      (ApplicationValueEvidence.closedView
        (ApplicationValueEvidence.function
          (ApplicationSpine.abs bodyTyping domainWf codomainWf domainShape))
        scope environment ready).view.argument = behavior) :
    (NativeFunctionImage.ofApplicationSpine
      (ApplicationSpine.abs bodyTyping domainWf codomainWf domainShape)
      scope environment ready behavior behavior_eq).plan =
      (TermTranslation.compileBinder scope domainWf).plan.subst
        environment.substitution := by
  rfl

/-- A direct abstraction's erased native image body is the ordinary/exact
binder body closed in its retained native environment. -/
@[simp] theorem ofApplicationSpine_abs_body
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {nativeDomain nativeCodomain : LambdaPFC.Ty n}
    {sourceBody : LambdaPFC.Tm (n + 1)}
    (bodyTyping : Fragment.HasType (sourceContext.snoc nativeDomain)
      sourceBody nativeCodomain.weaken)
    (domainWf : Fragment.Wf sourceContext nativeDomain)
    (codomainWf : Fragment.Wf sourceContext nativeCodomain)
    (domainShape : NonCanonicalResultShape nativeDomain)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (environment : ClosingEnv sig [])
    (ready : ApplicationValueEvidence.ClosedReady
      (ApplicationValueEvidence.function
        (ApplicationSpine.abs bodyTyping domainWf codomainWf domainShape))
      scope environment)
    (behavior : Exp [])
    (behavior_eq :
      (ApplicationValueEvidence.closedView
        (ApplicationValueEvidence.function
          (ApplicationSpine.abs bodyTyping domainWf codomainWf domainShape))
        scope environment ready).view.argument = behavior) :
    (NativeFunctionImage.ofApplicationSpine
      (ApplicationSpine.abs bodyTyping domainWf codomainWf domainShape)
      scope environment ready behavior behavior_eq).body =
      environment.closeBody
        (TermTranslation.compileBinder scope domainWf).plan
        (TermTranslation.elaborate
          (TermTranslation.compileBinder scope domainWf).extended
          bodyTyping) := by
  rfl

end NativeFunctionImage

/-! ## Existing-location binding for a direct native body -/

namespace DirectBody

/-- The newest cell of a direct abstraction allocation exposes the original
body under the weakened native valuation. -/
theorem functionBinds
    {nativeArity current : Nat}
    {sourceStore : LambdaPFC.Store current}
    {nativeValuation : SourceValuation nativeArity current}
    {nativeDomain : LambdaPFC.Ty nativeArity}
    {sourceBody : LambdaPFC.Tm (nativeArity + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    (runtimeReady : runtimeValue.IsValue)
    (runtime_eq : runtimeValue =
      (LambdaPFC.Tm.abs nativeDomain sourceBody).rename nativeValuation) :
    LambdaPFC.Store.Binds (.val sourceStore runtimeValue runtimeReady) 0
      (.abs (nativeDomain.rename nativeValuation).weaken
        (sourceBody.rename nativeValuation.weaken.ext)) := by
  subst runtimeValue
  simpa only [LambdaPFC.Tm.rename, LambdaPFC.Tm.weaken,
    SourceValuation.rename_ext_weaken] using
      (LambdaPFC.Store.Binds.here
        (sigma := sourceStore)
        (v := (LambdaPFC.Tm.abs nativeDomain sourceBody).rename
          nativeValuation)
        (vv := runtimeReady))

/-- Install an already allocated argument location in a direct native
abstraction's lexical environment.  The noncanonical-domain restriction
discharges both possible source head obligations syntactically. -/
noncomputable def environment
    {nativeArity current : Nat}
    {nativeContext : LambdaPFC.Ctx nativeArity}
    {sourceStore : LambdaPFC.Store current}
    {nativeValuation : SourceValuation nativeArity current}
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope nativeContext nativeTargetContext}
    {nativeClosing : ClosingEnv nativeSig []}
    (older : StoreEnvironment nativeContext sourceStore nativeValuation
      nativeTargetContext nativeScope nativeClosing)
    {nativeDomain : LambdaPFC.Ty nativeArity}
    (domainWf : Fragment.Wf nativeContext nativeDomain)
    (domainShape : NonCanonicalResultShape nativeDomain)
    (location : Fin current)
    {runtimeValue : LambdaPFC.Tm current}
    (binds : LambdaPFC.Store.Binds sourceStore location runtimeValue)
    (compiled : CompiledBinding runtimeValue)
    {argumentSig : Sig} {argumentTargetContext : Ctx argumentSig}
    {argumentScope : Scope compiled.native.context argumentTargetContext}
    {argumentClosing : ClosingEnv argumentSig []}
    (argumentEnvironment : StoreEnvironment compiled.native.context sourceStore
      compiled.nativeValuation argumentTargetContext argumentScope
      argumentClosing)
    (behavior : EliminationView
      ((TermTranslation.compileBinder nativeScope domainWf).plan.subst
        nativeClosing.substitution)) :
    StoreEnvironment (nativeContext.snoc nativeDomain) sourceStore
      (nativeValuation.bind location)
      ((TermTranslation.compileBinder nativeScope domainWf).plan.context
        nativeTargetContext)
      (TermTranslation.compileBinder nativeScope domainWf).extended
      (extendClosing nativeClosing
        (TermTranslation.compileBinder nativeScope domainWf).plan behavior) :=
  .bindLocation older domainWf location binds compiled argumentEnvironment
    (MemberCell.ofNotMember domainShape.notMember)
    (OperationalDirectApplicationExecution.NonCanonicalResultShape.functionCell
      (valuation := nativeValuation) domainShape)
    behavior

/-- Recursive coherence for the direct native body environment. -/
noncomputable def coherent
    {nativeArity current : Nat}
    {nativeContext : LambdaPFC.Ctx nativeArity}
    {sourceStore : LambdaPFC.Store current}
    {nativeValuation : SourceValuation nativeArity current}
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope nativeContext nativeTargetContext}
    {nativeClosing : ClosingEnv nativeSig []}
    (older : StoreEnvironment nativeContext sourceStore nativeValuation
      nativeTargetContext nativeScope nativeClosing)
    (olderCoherent : EnvironmentCoherence older)
    {nativeDomain : LambdaPFC.Ty nativeArity}
    (domainWf : Fragment.Wf nativeContext nativeDomain)
    (domainShape : NonCanonicalResultShape nativeDomain)
    (location : Fin current)
    {runtimeValue : LambdaPFC.Tm current}
    (binds : LambdaPFC.Store.Binds sourceStore location runtimeValue)
    (compiled : CompiledBinding runtimeValue)
    {argumentSig : Sig} {argumentTargetContext : Ctx argumentSig}
    {argumentScope : Scope compiled.native.context argumentTargetContext}
    {argumentClosing : ClosingEnv argumentSig []}
    (argumentEnvironment : StoreEnvironment compiled.native.context sourceStore
      compiled.nativeValuation argumentTargetContext argumentScope
      argumentClosing)
    (argumentCoherent : EnvironmentCoherence argumentEnvironment)
    (behavior : EliminationView
      ((TermTranslation.compileBinder nativeScope domainWf).plan.subst
        nativeClosing.substitution))
    (laws : BehaviorPathCoherence nativeScope domainWf nativeClosing behavior
      (storeArguments older)) :
    EnvironmentCoherence
      (environment older domainWf domainShape location binds compiled
        argumentEnvironment behavior) :=
  olderCoherent.bindLocationGenerated domainWf domainShape location binds compiled
    argumentEnvironment argumentCoherent
    (MemberCell.ofNotMember domainShape.notMember)
    (OperationalDirectApplicationExecution.NonCanonicalResultShape.functionCell
      (valuation := nativeValuation) domainShape)
    behavior laws

/-- Direct code environment of the opened source body. -/
noncomputable def code
    {nativeArity current : Nat}
    {nativeContext : LambdaPFC.Ctx nativeArity}
    {sourceStore : LambdaPFC.Store current}
    {nativeValuation : SourceValuation nativeArity current}
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope nativeContext nativeTargetContext}
    {nativeClosing : ClosingEnv nativeSig []}
    (older : StoreEnvironment nativeContext sourceStore nativeValuation
      nativeTargetContext nativeScope nativeClosing)
    {nativeDomain nativeCodomain : LambdaPFC.Ty nativeArity}
    {sourceBody : LambdaPFC.Tm (nativeArity + 1)}
    (bodyTyping : Fragment.HasType (nativeContext.snoc nativeDomain)
      sourceBody nativeCodomain.weaken)
    (bodyAdmissible : OperationallyAdmissible bodyTyping)
    (domainWf : Fragment.Wf nativeContext nativeDomain)
    (domainShape : NonCanonicalResultShape nativeDomain)
    (location : Fin current)
    {runtimeValue : LambdaPFC.Tm current}
    (binds : LambdaPFC.Store.Binds sourceStore location runtimeValue)
    (compiled : CompiledBinding runtimeValue)
    {argumentSig : Sig} {argumentTargetContext : Ctx argumentSig}
    {argumentScope : Scope compiled.native.context argumentTargetContext}
    {argumentClosing : ClosingEnv argumentSig []}
    (argumentEnvironment : StoreEnvironment compiled.native.context sourceStore
      compiled.nativeValuation argumentTargetContext argumentScope
      argumentClosing)
    (behavior : EliminationView
      ((TermTranslation.compileBinder nativeScope domainWf).plan.subst
        nativeClosing.substitution))
    (runtimeTerm : LambdaPFC.Tm current)
    (runtime_eq : runtimeTerm =
      sourceBody.rename (nativeValuation.bind location)) :
    DirectCodeEnvironment sourceStore runtimeTerm where
  original := TypedCode.ofTyping bodyTyping
  valuation := nativeValuation.bind location
  runtime_eq := runtime_eq
  admissible := bodyAdmissible
  targetSig := (TermTranslation.compileBinder nativeScope domainWf).plan.scope
  targetContext :=
    (TermTranslation.compileBinder nativeScope domainWf).plan.context
      nativeTargetContext
  scope := (TermTranslation.compileBinder nativeScope domainWf).extended
  closing := extendClosing nativeClosing
    (TermTranslation.compileBinder nativeScope domainWf).plan behavior
  environment := environment older domainWf domainShape location binds compiled
    argumentEnvironment behavior

/-- The closed successor body is exactly substitution by the application's
base elimination view. -/
theorem code_closed_eq
    {nativeArity current : Nat}
    {nativeContext : LambdaPFC.Ctx nativeArity}
    {sourceStore : LambdaPFC.Store current}
    {nativeValuation : SourceValuation nativeArity current}
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope nativeContext nativeTargetContext}
    {nativeClosing : ClosingEnv nativeSig []}
    (older : StoreEnvironment nativeContext sourceStore nativeValuation
      nativeTargetContext nativeScope nativeClosing)
    {nativeDomain nativeCodomain : LambdaPFC.Ty nativeArity}
    {sourceBody : LambdaPFC.Tm (nativeArity + 1)}
    (bodyTyping : Fragment.HasType (nativeContext.snoc nativeDomain)
      sourceBody nativeCodomain.weaken)
    (bodyAdmissible : OperationallyAdmissible bodyTyping)
    (domainWf : Fragment.Wf nativeContext nativeDomain)
    (domainShape : NonCanonicalResultShape nativeDomain)
    (location : Fin current)
    {runtimeValue : LambdaPFC.Tm current}
    (binds : LambdaPFC.Store.Binds sourceStore location runtimeValue)
    (compiled : CompiledBinding runtimeValue)
    {argumentSig : Sig} {argumentTargetContext : Ctx argumentSig}
    {argumentScope : Scope compiled.native.context argumentTargetContext}
    {argumentClosing : ClosingEnv argumentSig []}
    (argumentEnvironment : StoreEnvironment compiled.native.context sourceStore
      compiled.nativeValuation argumentTargetContext argumentScope
      argumentClosing)
    (behavior : EliminationView
      ((TermTranslation.compileBinder nativeScope domainWf).plan.subst
        nativeClosing.substitution))
    (runtimeTerm : LambdaPFC.Tm current)
    (runtime_eq : runtimeTerm =
      sourceBody.rename (nativeValuation.bind location)) :
    OperationalStateImage.StateImage.directClosed
      (code older bodyTyping bodyAdmissible domainWf domainShape location binds
        compiled argumentEnvironment behavior runtimeTerm runtime_eq) =
      (nativeClosing.closeBody
        (TermTranslation.compileBinder nativeScope domainWf).plan
        (TermTranslation.elaborate
          (TermTranslation.compileBinder nativeScope domainWf).extended
          bodyTyping)).subst behavior.substitution := by
  simp only [OperationalStateImage.StateImage.directClosed, code,
    OperationalStoreEnvironment.closeExp_extendClosing,
    EliminationView.instantiate, TypedCode.ofTyping]
  rfl

end DirectBody

/-! ## Smart direct-allocation application execution -/

namespace SmartDirectApplication

/-- Build the complete premise-driven application execution for the first
executable core: the operator is the newest directly allocated function, its
native spine is a direct abstraction, and its native binder domain is
noncanonical.  Typed-path and generated-application coherence discharge the
base argument elimination laws syntactically. -/
noncomputable def execution
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
    {nativeDomain nativeCodomain : LambdaPFC.Ty nativeArity}
    {nativeBody : LambdaPFC.Tm (nativeArity + 1)}
    (bodyTyping : Fragment.HasType (nativeContext.snoc nativeDomain)
      nativeBody nativeCodomain.weaken)
    (bodyAdmissible : OperationallyAdmissible bodyTyping)
    (nativeDomainWf : Fragment.Wf nativeContext nativeDomain)
    (nativeCodomainWf : Fragment.Wf nativeContext nativeCodomain)
    (nativeDomainShape : NonCanonicalResultShape nativeDomain)
    (nativeValuation : SourceValuation nativeArity current)
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    (nativeScope : Scope nativeContext nativeTargetContext)
    (nativeClosing : ClosingEnv nativeSig [])
    (nativeEnvironment : StoreEnvironment nativeContext sourceStore
      nativeValuation nativeTargetContext nativeScope nativeClosing)
    {runtimeValue : LambdaPFC.Tm current}
    (runtimeReady : runtimeValue.IsValue)
    (allocation :
      OperationalDirectFunctionCompatibility.DirectAllocation.Evidence older
        typing domainWf codomainWf domainShape
        (.abs bodyTyping nativeDomainWf nativeCodomainWf)
        nativeValuation
        (.abs bodyTyping nativeDomainWf nativeCodomainWf nativeDomainShape)
        nativeScope nativeClosing nativeEnvironment runtimeReady)
    (coherent : EnvironmentCoherence allocation.store)
    {argumentPath : LambdaPFC.Path (lexical + 1)}
    (argumentTyping : Fragment.HasType
      (sourceContext.snoc (.Fun domain codomain.weaken))
      (.path argumentPath) domain.weaken)
    (argumentAdmissible : OperationallyAdmissible argumentTyping) :
    let generated :=
      OperationalDirectFunctionCompatibility.DirectAllocation.generatedPath
        domainWf codomainWf domainShape
    let functionAdmissible :=
      OperationalDirectApplicationExecution.FunctionPathSpine.admissible
        generated.spine
    let functionLocation : Fin (current + 1) := 0
    let argumentLocation : Fin (current + 1) :=
      valuation.ext (typedPathReferent argumentTyping)
    let functionResolution : LambdaPFC.Path.Resolve
        ((.var 0 : LambdaPFC.Path (lexical + 1)).rename valuation.ext)
        (.val sourceStore runtimeValue runtimeReady)
        (.loc functionLocation) := .var
    let argumentResolution : LambdaPFC.Path.Resolve
        (argumentPath.rename valuation.ext)
        (.val sourceStore runtimeValue runtimeReady)
        (.loc argumentLocation) :=
      OperationalApplicationSourceEndpoint.resolveTypedPath allocation.store
        argumentTyping
    ApplicationExecution generated.typing argumentTyping generated.spine
      functionAdmissible argumentAdmissible allocation.store coherent
      functionLocation argumentLocation functionResolution
      argumentResolution := by
  dsimp only
  let generated :=
    OperationalDirectFunctionCompatibility.DirectAllocation.generatedPath
      domainWf codomainWf domainShape
  let functionAdmissible :=
    OperationalDirectApplicationExecution.FunctionPathSpine.admissible
      generated.spine
  let functionLocation : Fin (current + 1) := 0
  let argumentIndex := typedPathReferent argumentTyping
  let argumentLocation : Fin (current + 1) := valuation.ext argumentIndex
  let functionResolution : LambdaPFC.Path.Resolve
      ((.var 0 : LambdaPFC.Path (lexical + 1)).rename valuation.ext)
      (.val sourceStore runtimeValue runtimeReady)
      (.loc functionLocation) := .var
  let argumentResolution : LambdaPFC.Path.Resolve
      (argumentPath.rename valuation.ext)
      (.val sourceStore runtimeValue runtimeReady)
      (.loc argumentLocation) :=
    OperationalApplicationSourceEndpoint.resolveTypedPath allocation.store
      argumentTyping
  let application := exactApplication generated.spine functionAdmissible
    argumentAdmissible allocation.store coherent allocation.nativeImage
    allocation.compatibility
  have argumentRaw : RawSlot
      (closedArgumentPath argumentTyping argumentAdmissible allocation.store
        coherent).view := by
    exact OperationalTypedPathCoherence.build_rawSlot argumentAdmissible
      allocation.store coherent.pathCoherence
  have eliminationRaw : RawSlot application.elimination := by
    let functionImage := closedFunctionPath generated.typing
      functionAdmissible allocation.store coherent
    let argumentImage := closedArgumentPath argumentTyping argumentAdmissible
      allocation.store coherent
    let currentScope :=
      (TermTranslation.compileBinder scope typing.typeWf).extended
    let currentClosing := extendClosing olderClosing
      (TermTranslation.compileBinder scope typing.typeWf).plan
      allocation.behavior
    let outerPlan_eq :=
      OperationalTypedPathView.ClosedPathView.applicationPlan_eq
      (scope := currentScope)
      (typing := argumentTyping)
      (environment := currentClosing)
      generated.spine.domainWf generated.spine.domainShape
    let evidence := generated.spine.closedArgumentEvidence
      currentScope currentClosing
      allocation.nativeImage.value allocation.compatibility.baseEvidence
      argumentImage
    let canonical :=
      (generated.spine.closedView currentScope currentClosing
        allocation.nativeImage.value).normalize.value
        |>.application evidence.toArgumentView
    let endpointEq :
        (generated.spine.closedView currentScope currentClosing
          allocation.nativeImage.value).normalize.value.expression =
          functionImage.view.argument :=
      generated.spine.canonical_eq_pathArgument currentScope currentClosing
        allocation.nativeImage.value
        (allocation.compatibility.base_eq coherent.pathCoherence) functionImage
    have evidenceRaw : RawSlot evidence.toArgumentView.elimination := by
      have baseRaw :=
        OperationalApplicationPathCoherence.NativeFunctionImage.ofApplicationSpine_argumentEvidence_rawSlot
          (.abs bodyTyping nativeDomainWf nativeCodomainWf nativeDomainShape)
          nativeScope nativeClosing allocation.nativeReady _
          (allocation.nativeBehavior_eq.trans
            allocation.lookup_compiledBehavior_eq.symm)
          argumentImage.view
          (outerPlan_eq.trans allocation.compatibility.domainPlan_eq)
          argumentRaw
      simpa only [evidence, generated,
        OperationalDirectFunctionCompatibility.DirectAllocation.generatedPath,
        FunctionPathSpine.closedArgumentEvidence,
        FunctionPathSpine.argumentEvidence,
        DirectNativeCompatibility.baseEvidence] using baseRaw
    have application_eq : application = endpointEq ▸ canonical := by
      simp only [application, exactApplication,
        DirectNativeCompatibility.endpointApplication,
        FunctionPathSpine.endpointApplication, canonical, evidence]
      rw [eq_mpr_eq_cast]
      apply eq_of_heq
      exact (cast_heq _ _).trans
        (@eqRec_heq (Exp [])
          (fun function => ApplicationView allocation.nativeImage.body
            function argumentImage.view.argument) _ _ endpointEq
          ((generated.spine.closedView currentScope currentClosing
            allocation.nativeImage.value).normalize.value
            |>.application evidence.toArgumentView)).symm
    have elimination_eq : application.elimination =
        evidence.toArgumentView.elimination := by
      calc
        application.elimination = (endpointEq ▸ canonical).elimination :=
          congrArg ApplicationView.elimination application_eq
        _ = canonical.elimination :=
          application_elimination_transport endpointEq canonical
        _ = evidence.toArgumentView.elimination := by
          exact FunctionValue.application_elimination_eq _ _
    rw [elimination_eq]
    exact evidenceRaw
  let argumentFound := allocation.store.lookup argumentIndex
  let nativeAfter := nativeEnvironment.nativeWeaken runtimeValue runtimeReady
  let runtimeBody := nativeBody.rename nativeValuation.weaken.ext
  have runtimeBodyEq : runtimeBody.open argumentLocation =
      nativeBody.rename (nativeValuation.weaken.bind argumentLocation) :=
    SourceValuation.rename_ext_openAt nativeBody nativeValuation.weaken
      argumentLocation
  let successor := DirectBody.code nativeAfter bodyTyping bodyAdmissible
    nativeDomainWf nativeDomainShape argumentLocation argumentFound.binds
    argumentFound.compiled argumentFound.nativeEnvironment
    application.elimination (runtimeBody.open argumentLocation) runtimeBodyEq
  have nativeAfterCoherent : EnvironmentCoherence nativeAfter := by
    simpa only [nativeAfter,
      OperationalDirectFunctionCompatibility.DirectAllocation.generatedPath_referent]
      using coherent.lookupNative (0 : Fin (lexical + 1))
  have argumentCoherent : EnvironmentCoherence argumentFound.nativeEnvironment :=
    coherent.lookupNative argumentIndex
  have successorCoherent : EnvironmentCoherence successor.environment := by
    have generatedPathLaws :
        BehaviorPathCoherence nativeScope nativeDomainWf nativeClosing
          application.elimination (storeArguments nativeAfter) := by
      exact
        OperationalApplicationPathCoherence.BehaviorPathCoherence.ofRawNonCanonical
          nativeScope nativeDomainWf nativeDomainShape nativeClosing
          application.elimination (storeArguments nativeAfter) eliminationRaw
    exact DirectBody.coherent nativeAfter nativeAfterCoherent nativeDomainWf
      nativeDomainShape argumentLocation argumentFound.binds
      argumentFound.compiled argumentFound.nativeEnvironment argumentCoherent
      application.elimination generatedPathLaws
  refine
    { runtimeDomain := (nativeDomain.rename nativeValuation).weaken
      runtimeBody := runtimeBody
      functionBinds := ?_
      native := allocation.nativeImage
      compatibility := allocation.compatibility
      successor := successor
      successorCoherent := successorCoherent
      body_eq := ?_ }
  · exact DirectBody.functionBinds runtimeReady allocation.runtime_eq
  · calc
      OperationalStateImage.StateImage.directClosed successor =
          (nativeClosing.closeBody
            (TermTranslation.compileBinder nativeScope nativeDomainWf).plan
            (TermTranslation.elaborate
              (TermTranslation.compileBinder nativeScope
                nativeDomainWf).extended bodyTyping)).subst
            application.elimination.substitution := by
        exact DirectBody.code_closed_eq nativeAfter bodyTyping bodyAdmissible
          nativeDomainWf nativeDomainShape argumentLocation
          argumentFound.binds argumentFound.compiled
          argumentFound.nativeEnvironment application.elimination
          (runtimeBody.open argumentLocation) runtimeBodyEq
      _ = allocation.nativeImage.body.subst
            application.elimination.substitution := by
        rfl

end SmartDirectApplication

end OperationalDirectApplicationExecution
end LambdaPToFCo
