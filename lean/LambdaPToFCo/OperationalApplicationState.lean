import LambdaPToFCo.OperationalStateImage
import LambdaPToFCo.OperationalDirectFunctionCompatibility

/-!
# Exact-core application images

This module gives the premise-driven CK application image used by the final
one-step dispatcher.  The source admissibility derivation retains an exact
`FunctionPathSpine`; the current recursive environment supplies both closed
typed-path views; and `DirectNativeCompatibility` states the two syntactic
facts connecting the current lexical function slot to its physical native
closure.

The source/target body boundary is deliberately explicit.
`ApplicationExecution.successor` is the direct source-code environment of
the opened CK body, and `body_eq` identifies its closed compilation with the
body/substitution exposed by the target application macro.  The downstream
wrapper-aware application construction discharges this interface, including
surviving structural arrow casts.  No semantic realization is hidden in it.
-/

namespace LambdaPToFCo
namespace OperationalStateImage

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalEnvironment
open OperationalBindingView
open OperationalStoreEnvironment
open OperationalAdmissibility
open OperationalApplication
open OperationalApplicationSpine
open OperationalApplicationStore
open OperationalResultContext
open OperationalMachineImage
open OperationalPathCoherence
open OperationalTypedPathView
open OperationalEnvironmentCoherence
open OperationalFunctionPathSpine
open OperationalDirectFunctionCompatibility
open OperationalExpectedResult

/-! ## Closed target endpoint selected by an admissible source application -/

/-- Closed view of the operator path at its final advertised arrow type. -/
noncomputable def closedFunctionPath
    {n current : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {functionPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    (typing : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken))
    (admissible : OperationallyAdmissible typing)
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : EnvironmentCoherence environment) :
    ClosedPathView scope typing closing :=
  OperationalTypedPathView.build admissible environment
    coherent.pathCoherence

/-- Closed view of the argument path at the function's advertised domain. -/
noncomputable def closedArgumentPath
    {n current : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {argumentPath : LambdaPFC.Path n}
    {domain : LambdaPFC.Ty n}
    (typing : Fragment.HasType sourceContext (.path argumentPath) domain)
    (admissible : OperationallyAdmissible typing)
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : EnvironmentCoherence environment) :
    ClosedPathView scope typing closing :=
  OperationalTypedPathView.build admissible environment
    coherent.pathCoherence

/-- Target application view obtained from the exact operator spine and the
two closed typed paths. -/
noncomputable def exactApplication
    {n current : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {functionPath argumentPath : LambdaPFC.Path n}
    {domain codomain : LambdaPFC.Ty n}
    {functionTyping : Fragment.HasType sourceContext (.path functionPath)
      (.Fun domain codomain.weaken)}
    (functionSpine : FunctionPathSpine functionTyping)
    (functionAdmissible : OperationallyAdmissible functionTyping)
    {argumentTyping : Fragment.HasType sourceContext (.path argumentPath)
      domain}
    (argumentAdmissible : OperationallyAdmissible argumentTyping)
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : EnvironmentCoherence environment)
    (native : NativeFunctionImage
      (environment.lookup
        (typedPathReferent functionTyping)).compiled.slot.behavior.argument)
    (compatibility : DirectNativeCompatibility environment functionSpine
      native) :
    ApplicationView native.body
      (closedFunctionPath functionTyping functionAdmissible environment
        coherent).view.argument
      (closedArgumentPath argumentTyping argumentAdmissible environment
        coherent).view.argument :=
  compatibility.endpointApplication coherent.pathCoherence
    (closedFunctionPath functionTyping functionAdmissible environment coherent)
    (closedArgumentPath argumentTyping argumentAdmissible environment coherent)

/-- The derivation-directed closed application reaches the exact behavioral
application endpoint selected above. -/
theorem exactApplication_steps
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
    (native : NativeFunctionImage
      (environment.lookup
        (typedPathReferent functionTyping)).compiled.slot.behavior.argument)
    (compatibility : DirectNativeCompatibility environment functionSpine
      native) :
    let application := exactApplication functionSpine functionAdmissible
      argumentAdmissible environment coherent native compatibility
    Exp.Steps
      (closing.closeExp
        (TermTranslation.elaborate scope
          (.app functionTyping argumentTyping resultWf)))
      (application.context.plug
        (native.body.subst application.elimination.substitution)) := by
  dsimp only
  simpa only [exactApplication, closedFunctionPath, closedArgumentPath] using
    OperationalDirectFunctionCompatibility.DirectNativeCompatibility.closedApplication_steps
      resultWf compatibility coherent.pathCoherence
      (closedFunctionPath functionTyping functionAdmissible environment
        coherent)
      (closedArgumentPath argumentTyping argumentAdmissible environment
        coherent)

/-! ## Source/target body boundary for one CK application -/

/-- All local evidence needed to enter the opened source function body.

The successor environment is indexed by the actual CK endpoint.  Its closed
body equality is purely syntactic and is consumed by the wrapper-aware smart
constructor built from the retained native `ApplicationSpine`. -/
structure ApplicationExecution
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
  native : NativeFunctionImage
    (environment.lookup
      (typedPathReferent functionTyping)).compiled.slot.behavior.argument
  compatibility : DirectNativeCompatibility environment functionSpine native
  successor : DirectCodeEnvironment sourceStore
    (runtimeBody.open argumentLocation)
  successorCoherent : EnvironmentCoherence successor.environment
  body_eq : StateImage.directClosed successor =
    native.body.subst
      (exactApplication functionSpine functionAdmissible argumentAdmissible
        environment coherent native compatibility).elimination.substitution

/-! ## Complete before/after state images -/

namespace StateImage

/-- Image of a direct, exact-core source application before its CK step. -/
noncomputable def beforeApplication
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
      stack) :
    StateImage
      (LambdaPFC.State.mk sourceStore runtimeCont
        (.app (functionPath.rename valuation)
          (argumentPath.rename valuation))) :=
  let typing : Fragment.HasType sourceContext
      (.app functionPath argumentPath) codomain :=
    .app functionTyping argumentTyping resultWf
  let admissible : OperationallyAdmissible typing :=
    .app functionAdmissible functionSpine argumentAdmissible resultShape
  let origin := CurrentOrigin.ofEnvironment typing admissible valuation
    environment coherent
  let originRunning : ExecutionRunning activeOrigin origin.closedExpression
      origin.resultBoundary activeBoundary := by
    simpa only [origin, CurrentOrigin.closedExpression,
      CurrentOrigin.ofEnvironment, typing] using running
  let originCapability : ActiveResultCapability origin stack := by
    simpa only [origin, typing, admissible] using capability
  { focus := origin.closedExpression
    activeOrigin := activeOrigin
    activeBoundary := activeBoundary
    current := .direct origin rfl
    stack := stack
    running := originRunning
    capability := originCapability
    functionCapability :=
      ActiveFunctionCapability.ofNonCanonicalInput originCapability
        resultShape }

/-- Enter the opened source body while retaining the application macro's
residual target context inside the active execution history. -/
noncomputable def afterApplication
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
    (execution : ApplicationExecution functionTyping argumentTyping
      functionSpine functionAdmissible argumentAdmissible environment coherent
      functionLocation argumentLocation functionResolution
      argumentResolution) :
    StateImage
      (LambdaPFC.State.mk sourceStore runtimeCont
        (execution.runtimeBody.open argumentLocation)) :=
  let application := exactApplication functionSpine functionAdmissible
    argumentAdmissible environment coherent execution.native
    execution.compatibility
  let origin := CurrentOrigin.ofDirect execution.successor
    execution.successorCoherent
  let applicationGenerated :=
    OperationalDirectFunctionCompatibility.DirectNativeCompatibility.generatedApplication
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
      (application.context.plug (directClosed execution.successor)) := by
    rw [execution.body_eq]
    exact exactApplication_steps functionTyping argumentTyping resultWf
      functionSpine functionAdmissible argumentAdmissible environment coherent
      execution.native execution.compatibility
  let successorRunning : ExecutionRunning activeOrigin
      (directClosed execution.successor) origin.resultBoundary activeBoundary :=
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
  { focus := directClosed execution.successor
    activeOrigin := activeOrigin
    activeBoundary := activeBoundary
    current := currentOfDirect execution.successor execution.successorCoherent
    stack := stack
    running := successorRunning
    capability := successorCapability
    functionCapability := by
      simpa only [successorCapability] using
        (ActiveFunctionCapability.ofReplaceInput inputCapability origin
          resultShape (running := successorRunning)) }

/-- The native source application step represented by
`ApplicationExecution`. -/
theorem application_source_step
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeCont : LambdaPFC.Tm.Cont current}
    {functionPath argumentPath : LambdaPFC.Path current}
    {functionLocation argumentLocation : Fin current}
    (functionResolution : LambdaPFC.Path.Resolve functionPath sourceStore
      (.loc functionLocation))
    (argumentResolution : LambdaPFC.Path.Resolve argumentPath sourceStore
      (.loc argumentLocation))
    {runtimeDomain : LambdaPFC.Ty current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (functionBinds : LambdaPFC.Store.Binds sourceStore functionLocation
      (.abs runtimeDomain runtimeBody)) :
    LambdaPFC.State.Step
      (LambdaPFC.State.mk sourceStore runtimeCont
        (.app functionPath argumentPath))
      (LambdaPFC.State.mk sourceStore runtimeCont
        (runtimeBody.open argumentLocation)) :=
  .app functionResolution argumentResolution functionBinds

/-- Target execution corresponding to the single premise-driven source
application step. -/
theorem application_target_steps
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
    (execution : ApplicationExecution functionTyping argumentTyping
      functionSpine functionAdmissible argumentAdmissible environment coherent
      functionLocation argumentLocation functionResolution
      argumentResolution) :
    Exp.Steps
      (beforeApplication functionTyping argumentTyping resultWf
        functionAdmissible functionSpine argumentAdmissible resultShape
        environment coherent stack running capability).target
      (afterApplication functionTyping argumentTyping resultWf
        functionAdmissible functionSpine argumentAdmissible resultShape environment
        coherent stack running capability functionLocation argumentLocation
        functionResolution argumentResolution execution).target := by
  let application := exactApplication functionSpine functionAdmissible
    argumentAdmissible environment coherent execution.native
    execution.compatibility
  have applicationSteps : Exp.Steps
      (closing.closeExp
        (TermTranslation.elaborate scope
          (.app functionTyping argumentTyping resultWf)))
      (application.context.plug (directClosed execution.successor)) := by
    rw [execution.body_eq]
    exact exactApplication_steps functionTyping argumentTyping resultWf
      functionSpine functionAdmissible argumentAdmissible environment coherent
      execution.native execution.compatibility
  have localSteps := running.context.steps applicationSteps
  have lifted := stack.plug_steps localSteps
  simpa only [beforeApplication, afterApplication, StateImage.target,
    ResultContext.compose_plug] using lifted

end StateImage

end OperationalStateImage
end LambdaPToFCo
