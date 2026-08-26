import LambdaPToFCo.OperationalDirectApplicationExecution
import LambdaPToFCo.OperationalLexicalFunctionCompatibility
import LambdaPToFCo.OperationalCurrentFunctionProvenance

/-!
# Wrapper-aware application successors

This module is the application-side consumer of recursive function
provenance.  The current lexical slot may expose structural arrow casts, so
the target application is built from `LexicalFunctionCompatibility`; the
separate structural alignment identifies the retained source closure with
the physical binding selected by the CK machine.
-/

namespace LambdaPToFCo
namespace OperationalWrapperApplicationExecution

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalEnvironment
open OperationalBindingView
open OperationalApplication
open OperationalApplicationSpine
open OperationalStoreEnvironment
open OperationalFunctionPathSpine
open OperationalAdmissibility
open OperationalMachineImage
open OperationalPathCoherence
open OperationalTypedPathView
open OperationalTypedPathCoherence
open OperationalEnvironmentCoherence
open OperationalStateImage
open OperationalExpectedResult
open OperationalResultContext
open OperationalLexicalFunctionCompatibility
open OperationalFunctionResultProvenance
open OperationalFunctionEnvironmentCoherence
open OperationalCurrentFunctionProvenance

namespace LexicalFunctionCompatibility

/-- The wrapper-aware endpoint application carries the same generated-result
context invariant as the underlying canonical `FunctionValue.application`.
-/
noncomputable def generatedApplication
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    {store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing}
    {functionPath argumentPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    {functionTyping : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken)}
    {spine : FunctionPathSpine functionTyping}
    {argumentTyping : Fragment.HasType sourceContext (.path argumentPath)
      domain}
    (compatibility : LexicalFunctionCompatibility store spine)
    (coherent : StorePathCoherence store)
    (functionImage : ClosedPathView scope functionTyping closing)
    (argumentImage : ClosedPathView scope argumentTyping closing) :
    GeneratedApplicationView
      (compatibility.endpointApplication coherent functionImage
        argumentImage) := by
  let evidence := spine.closedArgumentEvidence scope closing
    compatibility.image.value compatibility.baseEvidence argumentImage
  let canonical :=
    (spine.closedView scope closing compatibility.image.value).normalize.value
      |>.application evidence.toArgumentView
  let endpointEq :
      (spine.closedView scope closing
        compatibility.image.value).normalize.value.expression =
        functionImage.view.argument :=
    spine.canonical_eq_pathArgument scope closing compatibility.image.value
      (compatibility.base_eq coherent) functionImage
  have application_eq :
      compatibility.endpointApplication coherent functionImage
          argumentImage = endpointEq ▸ canonical := by
    simp only [LexicalFunctionCompatibility.endpointApplication,
      FunctionPathSpine.endpointApplication, canonical, evidence]
    rw [eq_mpr_eq_cast]
    apply eq_of_heq
    exact (cast_heq _ _).trans
      (@eqRec_heq (Exp [])
        (fun function => ApplicationView compatibility.image.body
          function argumentImage.view.argument) _ _ endpointEq
        ((spine.closedView scope closing
          compatibility.image.value).normalize.value
          |>.application
            (spine.closedArgumentEvidence scope closing
              compatibility.image.value compatibility.baseEvidence
              argumentImage).toArgumentView)).symm
  have context_eq :
      (compatibility.endpointApplication coherent functionImage
        argumentImage).context = canonical.context := by
    rw [application_eq]
    exact
      OperationalDirectFunctionCompatibility.application_context_transport
        endpointEq canonical
  change GeneratedResultContext
    (compatibility.endpointApplication coherent functionImage
      argumentImage).context
  rw [context_eq]
  exact (spine.closedView scope closing
    compatibility.image.value).normalize.value
      |>.generatedApplication evidence.toArgumentView

end LexicalFunctionCompatibility

namespace ApplicationSpine

/-- The native binder well-formedness retained below every surrounding
function coercion. -/
private def nativeDomainWf
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {nativeDomain domain codomain : LambdaPFC.Ty n}
    {sourceBody : LambdaPFC.Tm (n + 1)}
    {typing : Fragment.HasType sourceContext
      (.abs nativeDomain sourceBody) (.Fun domain codomain.weaken)} :
    ApplicationSpine typing -> Fragment.Wf sourceContext nativeDomain
  | .abs _ domainWf _ _ => domainWf
  | .sub inner _ => nativeDomainWf inner

/-- The executable noncanonical shape of the native binder retained below
every surrounding function coercion. -/
private def nativeDomainShape
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {nativeDomain domain codomain : LambdaPFC.Ty n}
    {sourceBody : LambdaPFC.Tm (n + 1)}
    {typing : Fragment.HasType sourceContext
      (.abs nativeDomain sourceBody) (.Fun domain codomain.weaken)} :
    ApplicationSpine typing -> NonCanonicalResultShape nativeDomain
  | .abs _ _ _ shape => shape
  | .sub inner _ => nativeDomainShape inner

/-- Closing the retained source spine never changes its native binder plan;
function coercions only wrap the corresponding function value. -/
private theorem basePlan_eq
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {nativeDomain domain codomain : LambdaPFC.Ty n}
    {sourceBody : LambdaPFC.Tm (n + 1)}
    {typing : Fragment.HasType sourceContext
      (.abs nativeDomain sourceBody) (.Fun domain codomain.weaken)}
    {sig : Sig} {targetContext : Ctx sig}
    (spine : ApplicationSpine typing)
    (scope : Scope sourceContext targetContext)
    (closing : ClosingEnv sig []) :
    (spine.functionSpine.close scope closing).image.plan =
      (TermTranslation.compileBinder scope
        (nativeDomainWf spine)).plan.subst closing.substitution := by
  induction spine with
  | abs => rfl
  | sub inner coercion ih => exact ih

/-- Closing the retained source spine never changes its native binder body;
function coercions only wrap the corresponding function value. -/
private theorem baseBody_heq
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {nativeDomain domain codomain : LambdaPFC.Ty n}
    {sourceBody : LambdaPFC.Tm (n + 1)}
    {typing : Fragment.HasType sourceContext
      (.abs nativeDomain sourceBody) (.Fun domain codomain.weaken)}
    {sig : Sig} {targetContext : Ctx sig}
    (spine : ApplicationSpine typing)
    (scope : Scope sourceContext targetContext)
    (closing : ClosingEnv sig []) :
    HEq (spine.functionSpine.close scope closing).image.body
      (closing.closeBody
        (TermTranslation.compileBinder scope (nativeDomainWf spine)).plan
        (TermTranslation.elaborate
          (TermTranslation.compileBinder scope (nativeDomainWf spine)).extended
          spine.functionSpine.bodyTyping.2)) := by
  induction spine with
  | abs => exact HEq.rfl
  | sub inner coercion ih => exact ih

end ApplicationSpine

/-- Substitution respects simultaneous dependent transport of a binder plan
and its body. -/
private theorem body_subst_castPlan_eq
    {first second : Interface.BinderPlan []}
    {firstBody : Exp first.scope} {secondBody : Exp second.scope}
    (plan_eq : first = second) (body_heq : HEq firstBody secondBody)
    (view : EliminationView first) :
    secondBody.subst (EliminationView.castPlan plan_eq view).substitution =
      firstBody.subst view.substitution := by
  cases plan_eq
  cases body_heq
  rfl

/-- Raw-slot coherence is invariant under dependent binder-plan transport. -/
private theorem rawSlot_castPlan
    {first second : Interface.BinderPlan []} (plan_eq : first = second)
    (view : EliminationView first) (raw : RawSlot view) :
    RawSlot (EliminationView.castPlan plan_eq view) := by
  cases plan_eq
  exact raw

/-- Complete physical origin of a retained source function.  Packaging the
dependent indices lets alignment transport native source code to the exact
store/context returned by lookup without eliminating outer state indices. -/
private structure PackedFunctionOrigin where
  current : Nat
  sourceStore : LambdaPFC.Store current
  runtimeValue : LambdaPFC.Tm current
  nativeArity : Nat
  nativeContext : LambdaPFC.Ctx nativeArity
  nativeValuation : SourceValuation nativeArity current
  nativeSig : Sig
  nativeTargetContext : Ctx nativeSig
  nativeScope : Scope nativeContext nativeTargetContext
  nativeClosing : ClosingEnv nativeSig []
  nativeEnvironment : StoreEnvironment nativeContext sourceStore
    nativeValuation nativeTargetContext nativeScope nativeClosing

namespace PackedFunctionOrigin

private noncomputable def ofClosure
    (closure : SourceFunctionClosure behavior) : PackedFunctionOrigin := by
  cases closure with
  | mk sourceArity sourceContext nativeDomain domain codomain sourceBody
      typing spine bodyAdmissible current sourceStore valuation targetSig
      targetContext scope closing nativeEnvironment runtimeValue runtimeReady
      runtime_eq ready image plan_eq body_heq argumentRaw =>
      exact
        { current := current
          sourceStore := sourceStore
          runtimeValue := runtimeValue
          nativeArity := sourceArity
          nativeContext := sourceContext
          nativeValuation := valuation
          nativeSig := targetSig
          nativeTargetContext := targetContext
          nativeScope := scope
          nativeClosing := closing
          nativeEnvironment := nativeEnvironment }

private noncomputable def ofPhysical
    {current : Nat} (sourceStore : LambdaPFC.Store current)
    (runtimeValue : LambdaPFC.Tm current)
    {nativeArity : Nat} {nativeContext : LambdaPFC.Ctx nativeArity}
    {nativeValuation : SourceValuation nativeArity current}
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope nativeContext nativeTargetContext}
    {nativeClosing : ClosingEnv nativeSig []}
    (nativeEnvironment : StoreEnvironment nativeContext sourceStore
      nativeValuation nativeTargetContext nativeScope nativeClosing) :
    PackedFunctionOrigin :=
  { current := current
    sourceStore := sourceStore
    runtimeValue := runtimeValue
    nativeArity := nativeArity
    nativeContext := nativeContext
    nativeValuation := nativeValuation
    nativeSig := nativeSig
    nativeTargetContext := nativeTargetContext
    nativeScope := nativeScope
    nativeClosing := nativeClosing
    nativeEnvironment := nativeEnvironment }

end PackedFunctionOrigin

/-- Source code and wrapper laws reindexed over a packaged physical origin. -/
private structure NativeClosureData
    (origin : PackedFunctionOrigin) (behavior : Exp [])
    (image : NativeFunctionImage behavior) where
  nativeDomain : LambdaPFC.Ty origin.nativeArity
  domain : LambdaPFC.Ty origin.nativeArity
  codomain : LambdaPFC.Ty origin.nativeArity
  sourceBody : LambdaPFC.Tm (origin.nativeArity + 1)
  typing : Fragment.HasType origin.nativeContext
    (.abs nativeDomain sourceBody) (.Fun domain codomain.weaken)
  spine : ApplicationSpine typing
  bodyAdmissible : OperationallyAdmissible
    spine.functionSpine.bodyTyping.2
  runtime_eq : origin.runtimeValue =
    (LambdaPFC.Tm.abs nativeDomain sourceBody).rename
      origin.nativeValuation
  plan_eq : image.plan =
    (spine.functionSpine.close origin.nativeScope
      origin.nativeClosing).image.plan
  body_heq : HEq image.body
    (spine.functionSpine.close origin.nativeScope
      origin.nativeClosing).image.body
  argumentRaw :
    {outerPlan : Interface.BinderPlan []} ->
    (outer : EliminationView outerPlan) ->
    (outerPlan_eq : outerPlan = image.domainPlan) ->
    RawSlot outer ->
    RawSlot
      ((image.argumentEvidence outer outerPlan_eq).toArgumentView.elimination)

namespace NativeClosureData

private noncomputable def ofClosure
    (closure : SourceFunctionClosure behavior) :
    NativeClosureData (PackedFunctionOrigin.ofClosure closure) behavior
      closure.image := by
  cases closure with
  | mk sourceArity sourceContext nativeDomain domain codomain sourceBody
      typing spine bodyAdmissible current sourceStore valuation targetSig
      targetContext scope closing nativeEnvironment runtimeValue runtimeReady
      runtime_eq ready image plan_eq body_heq argumentRaw =>
      exact
        { nativeDomain := nativeDomain
          domain := domain
          codomain := codomain
          sourceBody := sourceBody
          typing := typing
          spine := spine
          bodyAdmissible := bodyAdmissible
          runtime_eq := runtime_eq
          plan_eq := plan_eq
          body_heq := body_heq
          argumentRaw := argumentRaw }

end NativeClosureData

namespace FunctionClosureAlignment

/-- Structural alignment identifies the complete dependent native-origin
package, not merely its target expression. -/
private theorem packedFunctionOrigin_eq
    {closure : SourceFunctionClosure behavior}
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeValue : LambdaPFC.Tm current}
    {nativeLexical : Nat}
    {nativeContext : LambdaPFC.Ctx nativeLexical}
    {nativeValuation : SourceValuation nativeLexical current}
    {nativeSig : Sig} {nativeTargetContext : Ctx nativeSig}
    {nativeScope : Scope nativeContext nativeTargetContext}
    {nativeClosing : ClosingEnv nativeSig []}
    {nativeEnvironment : StoreEnvironment nativeContext sourceStore
      nativeValuation nativeTargetContext nativeScope nativeClosing}
    (alignment : FunctionClosureAlignment closure sourceStore runtimeValue
      nativeEnvironment) :
    PackedFunctionOrigin.ofClosure closure =
      PackedFunctionOrigin.ofPhysical sourceStore runtimeValue
        nativeEnvironment := by
  induction alignment with
  | direct => rfl
  | nativeWeaken older allocatedValue allocatedReady current_eq ih =>
      cases current_eq
      cases ih
      rfl

end FunctionClosureAlignment

/-- The wrapper-aware application selected by the current lexical function
slot and the closed operator/argument paths. -/
noncomputable def wrapperApplication
    {n current : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {functionPath argumentPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    (functionTyping : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken))
    (argumentTyping : Fragment.HasType sourceContext (.path argumentPath)
      domain)
    (functionSpine : FunctionPathSpine functionTyping)
    (functionAdmissible : OperationallyAdmissible functionTyping)
    (argumentAdmissible : OperationallyAdmissible argumentTyping)
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : EnvironmentCoherence environment)
    (compatibility : LexicalFunctionCompatibility environment functionSpine) :
    ApplicationView compatibility.image.body
      (OperationalStateImage.closedFunctionPath functionTyping
        functionAdmissible environment coherent).view.argument
      (OperationalStateImage.closedArgumentPath argumentTyping
        argumentAdmissible environment coherent).view.argument :=
  compatibility.endpointApplication coherent.pathCoherence
    (OperationalStateImage.closedFunctionPath functionTyping
      functionAdmissible environment coherent)
    (OperationalStateImage.closedArgumentPath argumentTyping
      argumentAdmissible environment coherent)

/-- Complete target reduction for a wrapper-aware lexical application. -/
theorem wrapperApplication_steps
    {n current : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {functionPath argumentPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    (functionTyping : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken))
    (argumentTyping : Fragment.HasType sourceContext (.path argumentPath)
      domain)
    (resultWf : Fragment.Wf sourceContext codomain)
    (functionSpine : FunctionPathSpine functionTyping)
    (functionAdmissible : OperationallyAdmissible functionTyping)
    (argumentAdmissible : OperationallyAdmissible argumentTyping)
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : EnvironmentCoherence environment)
    (compatibility : LexicalFunctionCompatibility environment functionSpine) :
    Exp.Steps
      (closing.closeExp
        (TermTranslation.elaborate scope
          (.app functionTyping argumentTyping resultWf)))
      ((wrapperApplication functionTyping argumentTyping functionSpine
        functionAdmissible argumentAdmissible environment coherent
        compatibility).context.plug
        (compatibility.image.body.subst
          (wrapperApplication functionTyping argumentTyping functionSpine
            functionAdmissible argumentAdmissible environment coherent
            compatibility).elimination.substitution)) := by
  simpa only [wrapperApplication] using
    compatibility.closedApplication_steps resultWf coherent.pathCoherence
      (OperationalStateImage.closedFunctionPath functionTyping
        functionAdmissible environment coherent)
      (OperationalStateImage.closedArgumentPath argumentTyping
        argumentAdmissible environment coherent)

/-- Local evidence needed to enter the opened native body of a wrapper-aware
function application. -/
structure WrapperApplicationExecution
    {n current : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {functionPath argumentPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    (functionTyping : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken))
    (argumentTyping : Fragment.HasType sourceContext (.path argumentPath)
      domain)
    (functionSpine : FunctionPathSpine functionTyping)
    (functionAdmissible : OperationallyAdmissible functionTyping)
    (argumentAdmissible : OperationallyAdmissible argumentTyping)
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : EnvironmentCoherence environment)
    (functionLocation argumentLocation : Fin current)
    (functionResolution : LambdaPFC.Path.Resolve
      (functionPath.rename valuation) sourceStore (.loc functionLocation))
    (argumentResolution : LambdaPFC.Path.Resolve
      (argumentPath.rename valuation) sourceStore (.loc argumentLocation)) :
    Type where
  runtimeDomain : LambdaPFC.Ty current
  runtimeBody : LambdaPFC.Tm (current + 1)
  functionBinds : LambdaPFC.Store.Binds sourceStore functionLocation
    (.abs runtimeDomain runtimeBody)
  compatibility : LexicalFunctionCompatibility environment functionSpine
  successor : DirectCodeEnvironment sourceStore
    (runtimeBody.open argumentLocation)
  successorCoherent : EnvironmentCoherence successor.environment
  body_eq : OperationalStateImage.StateImage.directClosed successor =
    compatibility.image.body.subst
      (wrapperApplication functionTyping argumentTyping functionSpine
        functionAdmissible argumentAdmissible environment coherent
        compatibility).elimination.substitution

namespace WrapperApplicationExecution

/-- Recover the complete wrapper-aware beta successor from recursive lexical
function provenance and the two CK path resolutions.  Structural alignment
identifies the retained source closure with the physical function binding;
the wrapper image itself is used only for target application and body
transport. -/
noncomputable def ofImage
    {n current : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {functionPath argumentPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    (functionTyping : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken))
    (argumentTyping : Fragment.HasType sourceContext (.path argumentPath)
      domain)
    (functionSpine : FunctionPathSpine functionTyping)
    (functionAdmissible : OperationallyAdmissible functionTyping)
    (argumentAdmissible : OperationallyAdmissible argumentTyping)
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : EnvironmentCoherence environment)
    (functionLocation argumentLocation : Fin current)
    (functionResolution : LambdaPFC.Path.Resolve
      (functionPath.rename valuation) sourceStore (.loc functionLocation))
    (argumentResolution : LambdaPFC.Path.Resolve
      (argumentPath.rename valuation) sourceStore (.loc argumentLocation))
    {runtimeDomain : LambdaPFC.Ty current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (functionBinds : LambdaPFC.Store.Binds sourceStore functionLocation
      (.abs runtimeDomain runtimeBody)) :
    WrapperApplicationExecution functionTyping argumentTyping functionSpine
      functionAdmissible argumentAdmissible environment coherent
      functionLocation argumentLocation functionResolution
      argumentResolution := by
  have functionLocation_eq :=
    OperationalApplicationSourceEndpoint.resolvedLocation_eq environment
      functionTyping functionResolution
  have argumentLocation_eq :=
    OperationalApplicationSourceEndpoint.resolvedLocation_eq environment
      argumentTyping argumentResolution
  let functionIndex := typedPathReferent functionTyping
  let argumentIndex := typedPathReferent argumentTyping
  let witness := Classical.choice
    (coherent.functionCoherence.lookupFunctionPath functionSpine)
  let closure := witness.provenance.closure
  let compatibility : LexicalFunctionCompatibility environment functionSpine :=
    { image := closure.image
      domainPlan_eq := witness.provenance.domainPlan_eq }
  let lookup := environment.lookup functionIndex
  let functionBindsAtLookup : LambdaPFC.Store.Binds sourceStore
      (valuation functionIndex) (.abs runtimeDomain runtimeBody) :=
    functionLocation_eq ▸ functionBinds
  let physicalOrigin := PackedFunctionOrigin.ofPhysical sourceStore
    lookup.runtimeValue lookup.nativeEnvironment
  have origin_eq : PackedFunctionOrigin.ofClosure closure = physicalOrigin :=
    FunctionClosureAlignment.packedFunctionOrigin_eq witness.alignment
  let native : NativeClosureData physicalOrigin
      (environment.lookup functionIndex).slot.behavior.argument
      closure.image :=
    Eq.mp
      (congrArg
        (fun origin => NativeClosureData origin
          (environment.lookup functionIndex).slot.behavior.argument
          closure.image)
        origin_eq)
      (NativeClosureData.ofClosure closure)
  have nativeCoherent : EnvironmentCoherence
      physicalOrigin.nativeEnvironment := by
    simpa only [physicalOrigin, lookup] using
      coherent.lookupNative functionIndex
  have abstraction_eq :
      (.abs runtimeDomain runtimeBody : LambdaPFC.Tm current) =
        (LambdaPFC.Tm.abs native.nativeDomain
          native.sourceBody).rename physicalOrigin.nativeValuation :=
    (lookup.binds.unique functionBindsAtLookup).symm.trans native.runtime_eq
  change (.abs runtimeDomain runtimeBody : LambdaPFC.Tm current) =
    .abs (native.nativeDomain.rename physicalOrigin.nativeValuation)
      (native.sourceBody.rename physicalOrigin.nativeValuation.ext) at abstraction_eq
  have runtimeBody_source_eq : runtimeBody =
      native.sourceBody.rename physicalOrigin.nativeValuation.ext := by
    cases abstraction_eq
    rfl
  let application := wrapperApplication functionTyping argumentTyping
    functionSpine functionAdmissible argumentAdmissible environment coherent
    compatibility
  have argumentRaw : RawSlot
      (OperationalStateImage.closedArgumentPath argumentTyping
        argumentAdmissible environment coherent).view :=
    OperationalTypedPathCoherence.build_rawSlot argumentAdmissible environment
      coherent.pathCoherence
  have eliminationRaw : RawSlot application.elimination := by
    let functionImage := OperationalStateImage.closedFunctionPath
      functionTyping functionAdmissible environment coherent
    let argumentImage := OperationalStateImage.closedArgumentPath
      argumentTyping argumentAdmissible environment coherent
    let evidence := functionSpine.closedArgumentEvidence scope closing
      compatibility.image.value compatibility.baseEvidence argumentImage
    let canonical :=
      (functionSpine.closedView scope closing
        compatibility.image.value).normalize.value
        |>.application evidence.toArgumentView
    let endpointEq :
        (functionSpine.closedView scope closing
          compatibility.image.value).normalize.value.expression =
          functionImage.view.argument :=
      functionSpine.canonical_eq_pathArgument scope closing
        compatibility.image.value
        (compatibility.base_eq coherent.pathCoherence) functionImage
    have baseRaw :
        {outerPlan : Interface.BinderPlan []} ->
        (outer : EliminationView outerPlan) ->
        (outerPlan_eq : outerPlan =
          closedPlan scope closing functionSpine.baseDomainWf) ->
        RawSlot outer ->
        RawSlot ((compatibility.baseEvidence outer
          outerPlan_eq).toArgumentView.elimination) := by
      intro outerPlan outer outerPlan_eq outerRaw
      simpa only [LexicalFunctionCompatibility.baseEvidence] using
        native.argumentRaw outer
          (outerPlan_eq.trans compatibility.domainPlan_eq) outerRaw
    have evidenceRaw : RawSlot evidence.toArgumentView.elimination := by
      exact
        OperationalApplicationPathCoherence.FunctionPathSpine.argumentEvidence_rawSlot
          functionSpine scope closing compatibility.image.value
          compatibility.baseEvidence baseRaw argumentImage.view
          (OperationalTypedPathView.ClosedPathView.applicationPlan_eq
            (scope := scope) (typing := argumentTyping)
            (environment := closing) functionSpine.domainWf
            functionSpine.domainShape)
          argumentRaw
    have application_eq : application = endpointEq ▸ canonical := by
      simp only [application, wrapperApplication,
        LexicalFunctionCompatibility.endpointApplication,
        FunctionPathSpine.endpointApplication, canonical, evidence]
      rw [eq_mpr_eq_cast]
      apply eq_of_heq
      exact (cast_heq _ _).trans
        (@eqRec_heq (Exp [])
          (fun function => ApplicationView compatibility.image.body
            function argumentImage.view.argument) _ _ endpointEq
          ((functionSpine.closedView scope closing
            compatibility.image.value).normalize.value
            |>.application evidence.toArgumentView)).symm
    have elimination_eq : application.elimination =
        evidence.toArgumentView.elimination := by
      calc
        application.elimination = (endpointEq ▸ canonical).elimination :=
          congrArg ApplicationView.elimination application_eq
        _ = canonical.elimination :=
          OperationalDirectApplicationExecution.application_elimination_transport
            endpointEq canonical
        _ = evidence.toArgumentView.elimination :=
          OperationalDirectApplicationExecution.FunctionValue.application_elimination_eq
            _ _
    rw [elimination_eq]
    exact evidenceRaw
  let nativeDomainWf := ApplicationSpine.nativeDomainWf native.spine
  let nativeDomainShape := ApplicationSpine.nativeDomainShape native.spine
  let nativePlan_eq : compatibility.image.plan =
      (TermTranslation.compileBinder physicalOrigin.nativeScope
        nativeDomainWf).plan.subst
        physicalOrigin.nativeClosing.substitution :=
    native.plan_eq.trans
      (ApplicationSpine.basePlan_eq native.spine
        physicalOrigin.nativeScope physicalOrigin.nativeClosing)
  let nativeElimination :=
    EliminationView.castPlan nativePlan_eq application.elimination
  have nativeEliminationRaw : RawSlot nativeElimination :=
    rawSlot_castPlan nativePlan_eq application.elimination eliminationRaw
  let argumentFound := environment.lookup argumentIndex
  let argumentBinds : LambdaPFC.Store.Binds sourceStore argumentLocation
      argumentFound.runtimeValue :=
    argumentLocation_eq.symm ▸ argumentFound.binds
  have argumentCoherent :
      EnvironmentCoherence argumentFound.nativeEnvironment :=
    coherent.lookupNative argumentIndex
  have runtimeBody_eq :
      runtimeBody.open argumentLocation =
        native.sourceBody.rename
          (physicalOrigin.nativeValuation.bind argumentLocation) :=
    (congrArg (fun body => body.open argumentLocation)
      runtimeBody_source_eq).trans
      (SourceValuation.rename_ext_openAt native.sourceBody
        physicalOrigin.nativeValuation argumentLocation)
  let successor := OperationalDirectApplicationExecution.DirectBody.code
    physicalOrigin.nativeEnvironment native.spine.functionSpine.bodyTyping.2
    native.bodyAdmissible nativeDomainWf nativeDomainShape
    argumentLocation argumentBinds argumentFound.compiled
    argumentFound.nativeEnvironment nativeElimination
    (runtimeBody.open argumentLocation) runtimeBody_eq
  have successorCoherent : EnvironmentCoherence successor.environment := by
    have generatedPathLaws :
        OperationalPathCoherenceGenerated.BehaviorPathCoherence
        physicalOrigin.nativeScope nativeDomainWf
        physicalOrigin.nativeClosing nativeElimination
        (storeArguments physicalOrigin.nativeEnvironment) :=
      OperationalApplicationPathCoherence.BehaviorPathCoherence.ofRawNonCanonical
        physicalOrigin.nativeScope nativeDomainWf nativeDomainShape
        physicalOrigin.nativeClosing nativeElimination
        (storeArguments physicalOrigin.nativeEnvironment) nativeEliminationRaw
    exact OperationalDirectApplicationExecution.DirectBody.coherent
      physicalOrigin.nativeEnvironment nativeCoherent nativeDomainWf
      nativeDomainShape argumentLocation argumentBinds
      argumentFound.compiled argumentFound.nativeEnvironment argumentCoherent
      nativeElimination generatedPathLaws
  refine
    { runtimeDomain := runtimeDomain
      runtimeBody := runtimeBody
      functionBinds := functionBinds
      compatibility := compatibility
      successor := successor
      successorCoherent := successorCoherent
      body_eq := ?_ }
  let nativeBody := physicalOrigin.nativeClosing.closeBody
    (TermTranslation.compileBinder physicalOrigin.nativeScope
      nativeDomainWf).plan
    (TermTranslation.elaborate
      (TermTranslation.compileBinder physicalOrigin.nativeScope
        nativeDomainWf).extended
      native.spine.functionSpine.bodyTyping.2)
  have imageBody_heq : HEq compatibility.image.body nativeBody :=
    native.body_heq.trans
      (ApplicationSpine.baseBody_heq native.spine
        physicalOrigin.nativeScope physicalOrigin.nativeClosing)
  calc
    OperationalStateImage.StateImage.directClosed successor =
        nativeBody.subst nativeElimination.substitution := by
      exact OperationalDirectApplicationExecution.DirectBody.code_closed_eq
        physicalOrigin.nativeEnvironment
        native.spine.functionSpine.bodyTyping.2 native.bodyAdmissible
        nativeDomainWf nativeDomainShape
        argumentLocation argumentBinds argumentFound.compiled
        argumentFound.nativeEnvironment nativeElimination
        (runtimeBody.open argumentLocation) runtimeBody_eq
    _ = compatibility.image.body.subst
          application.elimination.substitution :=
      body_subst_castPlan_eq nativePlan_eq imageBody_heq
        application.elimination

end WrapperApplicationExecution

end OperationalWrapperApplicationExecution
end LambdaPToFCo
