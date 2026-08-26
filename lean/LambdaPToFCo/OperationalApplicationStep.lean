import LambdaPToFCo.OperationalWrapperApplicationExecution
import LambdaPToFCo.OperationalNonApplicationStep

/-!
# Structural source application images

This module isolates the source-dependent inversion needed by the application
case.  A runtime application in a direct current image necessarily comes from
the exact admissible application constructor; the executable fragment excludes
subsumption around application syntax.
-/

namespace LambdaPToFCo
namespace OperationalApplicationStep

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalEnvironment
open OperationalApplication
open OperationalStoreEnvironment
open OperationalAdmissibility
open OperationalApplicationSpine
open OperationalFunctionPathSpine
open OperationalEnvironmentCoherence
open OperationalExpectedResult
open OperationalMachineImage
open OperationalPathCoherence
open OperationalResultContext
open OperationalStateImage
open OperationalNonApplicationStep
open OperationalWrapperApplicationExecution

/-- Exact source/compiler decomposition of a direct runtime application. -/
inductive DirectApplicationOriginView
    {current : Nat} {sourceStore : LambdaPFC.Store current} :
    (origin : CurrentOrigin sourceStore) ->
    LambdaPFC.Path current -> LambdaPFC.Path current -> Type where
  | exact
      {n : Nat} {sourceContext : LambdaPFC.Ctx n}
      {valuation : OperationalCode.SourceValuation n current}
      {functionPath argumentPath : LambdaPFC.Path n}
      {domain codomain : LambdaPFC.Ty n}
      (functionTyping : Fragment.HasType sourceContext (.path functionPath)
        (.Fun domain codomain.weaken))
      (argumentTyping : Fragment.HasType sourceContext (.path argumentPath)
        domain)
      (resultWf : Fragment.Wf sourceContext codomain)
      (functionAdmissible : OperationallyAdmissible functionTyping)
      (functionSpine : FunctionPathSpine functionTyping)
      (argumentAdmissible : OperationallyAdmissible argumentTyping)
      (resultShape : NonCanonicalResultShape codomain)
      {sig : SystemFCo.Sig} {targetContext : SystemFCo.Ctx sig}
      {scope : StaticTranslation.Scope sourceContext targetContext}
      {closing : OperationalEnvironment.ClosingEnv sig []}
      (environment : OperationalStoreEnvironment.StoreEnvironment sourceContext
        sourceStore valuation targetContext scope closing)
      (coherent : OperationalEnvironmentCoherence.EnvironmentCoherence
        environment)
      {runtimeFunction runtimeArgument : LambdaPFC.Path current}
      (function_eq : runtimeFunction = functionPath.rename valuation)
      (argument_eq : runtimeArgument = argumentPath.rename valuation) :
      DirectApplicationOriginView
        (CurrentOrigin.ofEnvironment
          (.app functionTyping argumentTyping resultWf)
          (.app functionAdmissible functionSpine argumentAdmissible resultShape)
          valuation environment coherent)
        runtimeFunction runtimeArgument

namespace DirectApplicationOriginView

/-- Invert a direct runtime application without assuming anything about its
target image. -/
theorem exists_of_runtime
    (origin : CurrentOrigin sourceStore)
    (runtime_eq : LambdaPFC.Tm.app runtimeFunction runtimeArgument =
      origin.original.term.rename origin.valuation) :
    Nonempty
      (DirectApplicationOriginView origin runtimeFunction runtimeArgument) := by
  rcases origin with
    ⟨⟨arity, sourceContext, sourceTerm, sourceType, typing⟩, valuation,
      admissible, targetSig, targetContext, scope, closing, environment,
      coherent⟩
  cases sourceTerm with
  | path => cases runtime_eq
  | abs => cases runtime_eq
  | pair => cases runtime_eq
  | app functionPath argumentPath =>
      cases typing with
      | app functionTyping argumentTyping resultWf =>
          cases admissible with
          | app functionAdmissible functionSpine argumentAdmissible
              resultShape =>
              cases runtime_eq
              exact ⟨.exact functionTyping argumentTyping resultWf
                functionAdmissible functionSpine argumentAdmissible resultShape
                environment coherent rfl rfl⟩
      | sub =>
          cases admissible with
          | neutralSub neutral => cases neutral
  | «let» => cases runtime_eq

/-- Type-valued application inversion selected noncomputably from the
propositional runtime equality. -/
noncomputable def ofRuntime
    (origin : CurrentOrigin sourceStore)
    (runtime_eq : LambdaPFC.Tm.app runtimeFunction runtimeArgument =
      origin.original.term.rename origin.valuation) :
    DirectApplicationOriginView origin runtimeFunction runtimeArgument :=
  Classical.choice (exists_of_runtime origin runtime_eq)

end DirectApplicationOriginView

/-! ## Wrapper-aware successor image -/

/-- Enter the physical source closure selected by a lexical function path,
while the target executes the wrapper-aware function image exposed by that
path. -/
noncomputable def afterWrapperApplication
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
    (functionAdmissible : OperationallyAdmissible functionTyping)
    (functionSpine : FunctionPathSpine functionTyping)
    (argumentAdmissible : OperationallyAdmissible argumentTyping)
    (resultShape : NonCanonicalResultShape codomain)
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : EnvironmentCoherence environment)
    {runtimeCont : LambdaPFC.Tm.Cont current}
    {activeOrigin : Exp []}
    {activeBoundary : ResultBoundary.{0}}
    (stack : ExecutionStack sourceStore runtimeCont activeOrigin activeBoundary)
    (running : ExecutionRunning activeOrigin
      (closing.closeExp
        (TermTranslation.elaborate scope
          (.app functionTyping argumentTyping resultWf)))
      (sourceBoundary scope resultWf closing
        (storeArguments environment)) activeBoundary)
    (capability : ActiveResultCapability
      (CurrentOrigin.ofEnvironment
        (.app functionTyping argumentTyping resultWf)
        (.app functionAdmissible functionSpine argumentAdmissible resultShape)
        valuation environment coherent)
      stack)
    (functionLocation argumentLocation : Fin current)
    (functionResolution : LambdaPFC.Path.Resolve
      (functionPath.rename valuation) sourceStore (.loc functionLocation))
    (argumentResolution : LambdaPFC.Path.Resolve
      (argumentPath.rename valuation) sourceStore (.loc argumentLocation))
    (execution : WrapperApplicationExecution functionTyping argumentTyping
      functionSpine functionAdmissible argumentAdmissible environment coherent
      functionLocation argumentLocation functionResolution
      argumentResolution) :
    StateImage
      (LambdaPFC.State.mk sourceStore runtimeCont
        (execution.runtimeBody.open argumentLocation)) :=
  let application := wrapperApplication functionTyping argumentTyping
    functionSpine functionAdmissible argumentAdmissible environment coherent
    execution.compatibility
  let origin := CurrentOrigin.ofDirect execution.successor
    execution.successorCoherent
  let applicationGenerated :=
    OperationalWrapperApplicationExecution.LexicalFunctionCompatibility.generatedApplication
      execution.compatibility coherent.pathCoherence
      (closedFunctionPath functionTyping functionAdmissible environment
        coherent)
      (closedArgumentPath argumentTyping argumentAdmissible environment
        coherent)
  let applicationAdapter := ofGeneratedOrdinary applicationGenerated
    (OperationalStateImage.DirectCodeEnvironment.resultBoundary
      execution.successor) scope resultWf resultShape
    closing (storeArguments environment)
  have applicationSteps : Exp.Steps
      (closing.closeExp
        (TermTranslation.elaborate scope
          (.app functionTyping argumentTyping resultWf)))
      (application.context.plug (StateImage.directClosed
        execution.successor)) := by
    rw [execution.body_eq]
    exact wrapperApplication_steps functionTyping argumentTyping resultWf
      functionSpine functionAdmissible argumentAdmissible environment coherent
      execution.compatibility
  let successorRunning : ExecutionRunning activeOrigin
      (StateImage.directClosed execution.successor) origin.resultBoundary
        activeBoundary :=
    { context := running.context.compose application.context
      generated := running.generated.compose applicationGenerated
      adapter := running.adapter.compose applicationAdapter
      reductions := running.reductions.trans
        (running.context.steps applicationSteps) }
  let applicationTyping : Fragment.HasType sourceContext
      (.app functionPath argumentPath) codomain :=
    .app functionTyping argumentTyping resultWf
  let applicationAdmissible : OperationallyAdmissible applicationTyping :=
    .app functionAdmissible functionSpine argumentAdmissible resultShape
  let inputCapability : ActiveResultCapability
      (CurrentOrigin.ofEnvironment applicationTyping applicationAdmissible
        valuation environment coherent) stack := by
    simpa only [applicationTyping, applicationAdmissible] using capability
  let successorCapability : ActiveResultCapability origin stack :=
    inputCapability.replaceInput origin resultShape
  { focus := StateImage.directClosed execution.successor
    activeOrigin := activeOrigin
    activeBoundary := activeBoundary
    current := StateImage.currentOfDirect execution.successor
      execution.successorCoherent
    stack := stack
    running := successorRunning
    capability := successorCapability
    functionCapability := by
      simpa only [successorCapability] using
        (ActiveFunctionCapability.ofReplaceInput inputCapability origin
          resultShape (running := successorRunning)) }

/-- Target execution corresponding to a wrapper-aware source application. -/
theorem wrapperApplication_target_steps
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
    (functionAdmissible : OperationallyAdmissible functionTyping)
    (functionSpine : FunctionPathSpine functionTyping)
    (argumentAdmissible : OperationallyAdmissible argumentTyping)
    (resultShape : NonCanonicalResultShape codomain)
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : EnvironmentCoherence environment)
    {runtimeCont : LambdaPFC.Tm.Cont current}
    {activeOrigin : Exp []}
    {activeBoundary : ResultBoundary.{0}}
    (stack : ExecutionStack sourceStore runtimeCont activeOrigin activeBoundary)
    (running : ExecutionRunning activeOrigin
      (closing.closeExp
        (TermTranslation.elaborate scope
          (.app functionTyping argumentTyping resultWf)))
      (sourceBoundary scope resultWf closing
        (storeArguments environment)) activeBoundary)
    (capability : ActiveResultCapability
      (CurrentOrigin.ofEnvironment
        (.app functionTyping argumentTyping resultWf)
        (.app functionAdmissible functionSpine argumentAdmissible resultShape)
        valuation environment coherent)
      stack)
    (functionLocation argumentLocation : Fin current)
    (functionResolution : LambdaPFC.Path.Resolve
      (functionPath.rename valuation) sourceStore (.loc functionLocation))
    (argumentResolution : LambdaPFC.Path.Resolve
      (argumentPath.rename valuation) sourceStore (.loc argumentLocation))
    (execution : WrapperApplicationExecution functionTyping argumentTyping
      functionSpine functionAdmissible argumentAdmissible environment coherent
      functionLocation argumentLocation functionResolution
      argumentResolution) :
    Exp.Steps
      (StateImage.beforeApplication functionTyping argumentTyping resultWf
        functionAdmissible functionSpine argumentAdmissible resultShape
        environment coherent stack running capability).target
      (afterWrapperApplication functionTyping argumentTyping resultWf
        functionAdmissible functionSpine argumentAdmissible resultShape
        environment coherent stack running capability functionLocation
        argumentLocation functionResolution argumentResolution execution).target := by
  let application := wrapperApplication functionTyping argumentTyping
    functionSpine functionAdmissible argumentAdmissible environment coherent
    execution.compatibility
  have applicationSteps : Exp.Steps
      (closing.closeExp
        (TermTranslation.elaborate scope
          (.app functionTyping argumentTyping resultWf)))
      (application.context.plug (StateImage.directClosed
        execution.successor)) := by
    rw [execution.body_eq]
    exact wrapperApplication_steps functionTyping argumentTyping resultWf
      functionSpine functionAdmissible argumentAdmissible environment coherent
      execution.compatibility
  have localSteps := running.context.steps applicationSteps
  have lifted := stack.plug_steps localSteps
  simpa only [StateImage.beforeApplication, afterWrapperApplication,
    StateImage.target, ResultContext.compose_plug] using lifted

/-! ## Complete application-step lift -/

namespace ApplicationStep

/-- The reconstructed target expression is insensitive to transport of a
state image along equality of its source-state index. -/
private theorem target_transport
    {current : Nat} {first second : LambdaPFC.State current}
    (equal : first = second) (image : StateImage first) :
    (equal ▸ image).target = image.target := by
  cases equal
  rfl

/-- Lift the remaining CK constructor.  Runtime application syntax forces a
direct current origin; recursive function provenance then supplies the exact
physical closure selected by the CK binding premise. -/
noncomputable def lift
    (before : StateImage beforeState)
    {step : LambdaPFC.State.Step beforeState afterState}
    (supported : ApplicationStep step) :
    ImageStep before afterState := by
  cases supported with
  | @app sourceStore runtimeCont runtimeFunction runtimeArgument
      functionLocation argumentLocation runtimeDomain runtimeBody
      functionResolution argumentResolution functionBinds =>
      rcases before with
        ⟨focus, activeOrigin, activeBoundary, currentCode, stack, running,
          capability, functionCapability⟩
      rcases currentCode with ⟨origin, form⟩
      cases form with
      | direct runtime_eq =>
          cases DirectApplicationOriginView.ofRuntime origin runtime_eq with
          | exact functionTyping argumentTyping resultWf functionAdmissible
              functionSpine argumentAdmissible resultShape environment coherent
              function_eq argument_eq =>
              have sourceFunctionResolution : LambdaPFC.Path.Resolve
                  _ _ _ := function_eq ▸ functionResolution
              have sourceArgumentResolution : LambdaPFC.Path.Resolve
                  _ _ _ := argument_eq ▸ argumentResolution
              let execution := WrapperApplicationExecution.ofImage
                functionTyping argumentTyping functionSpine functionAdmissible
                argumentAdmissible environment coherent _ _
                sourceFunctionResolution sourceArgumentResolution functionBinds
              have execution_runtimeBody : execution.runtimeBody =
                  runtimeBody := by
                exact (LambdaPFC.Tm.abs.inj
                  (execution.functionBinds.unique functionBinds)).2
              let after := afterWrapperApplication functionTyping
                argumentTyping resultWf functionAdmissible functionSpine
                argumentAdmissible resultShape environment coherent stack
                running capability _ _ sourceFunctionResolution
                sourceArgumentResolution execution
              have successorState_eq :
                  LambdaPFC.State.mk sourceStore runtimeCont
                      (execution.runtimeBody.open argumentLocation) =
                    LambdaPFC.State.mk sourceStore runtimeCont
                      (runtimeBody.open argumentLocation) :=
                congrArg
                  (fun body => LambdaPFC.State.mk sourceStore runtimeCont
                    (body.open argumentLocation)) execution_runtimeBody
              let transportedAfter := successorState_eq ▸ after
              exact
                { after := transportedAfter
                  targetSteps := by
                    have lifted :=
                      wrapperApplication_target_steps functionTyping
                        argumentTyping resultWf functionAdmissible functionSpine
                        argumentAdmissible resultShape environment coherent stack
                        running capability _ _ sourceFunctionResolution
                        sourceArgumentResolution execution
                    rw [target_transport successorState_eq after]
                    simpa only [StateImage.beforeApplication,
                      StateImage.target, CurrentOrigin.closedExpression,
                      CurrentOrigin.ofEnvironment] using lifted }

end ApplicationStep

end OperationalApplicationStep
end LambdaPToFCo
