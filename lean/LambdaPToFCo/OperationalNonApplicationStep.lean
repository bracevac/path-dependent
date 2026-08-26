import LambdaPToFCo.OperationalAutomaticReturn
import LambdaPToFCo.OperationalCurrentFunctionProvenance
import LambdaPToFCo.OperationalPathResultInterface

/-!
# Non-application source steps from complete machine images

This module is the structural dispatcher for the executable core cases whose
source and target evidence is now internal to `StateImage`: direct `let_push`,
typed path resolution, value allocation, and existing-location return.
Application is classified separately and handled by
`OperationalApplicationStep`, whose wrapper-aware compatibility accounts for
surviving structural arrow casts.  Together the two dispatchers cover every
native CK constructor admitted by the executable core.
-/

namespace LambdaPToFCo
namespace OperationalNonApplicationStep

open SystemFCo
open OperationalAdmissibility
open OperationalApplicationSpine
open OperationalApplication
open OperationalExpectedResult
open OperationalMachineImage
open OperationalPathCoherence
open OperationalPathCoherenceGenerated
open OperationalStateImage
open OperationalStateImage.StateImage
open OperationalTypedPathView
open OperationalTypedPathCoherence
open OperationalAutomaticReturn
open OperationalFunctionPathSpine

/-- Exact source/compiler decomposition of a direct runtime `let`.  Packaging
the dependent origin as an indexed view keeps later target-rich state
inversion separate from source admissibility inversion. -/
inductive DirectLetOriginView
    {current : Nat} {sourceStore : LambdaPFC.Store current} :
    (origin : CurrentOrigin sourceStore) ->
    LambdaPFC.Tm current -> LambdaPFC.Tm (current + 1) -> Type where
  | exact
      {n : Nat} {sourceContext : LambdaPFC.Ctx n}
      {valuation : OperationalCode.SourceValuation n current}
      {bound : LambdaPFC.Tm n} {body : LambdaPFC.Tm (n + 1)}
      {boundType resultType : LambdaPFC.Ty n}
      (boundTyping : Fragment.HasType sourceContext bound boundType)
      (resultWf : Fragment.Wf sourceContext resultType)
      (bodyTyping : Fragment.HasType (sourceContext.snoc boundType) body
        resultType.weaken)
      (boundAdmissible : OperationallyAdmissible boundTyping)
      (boundPolicy : LetBoundPolicy boundTyping)
      (bodyAdmissible : OperationallyAdmissible bodyTyping)
      (resultShape : NonCanonicalResultShape resultType)
      {sig : Sig} {targetContext : Ctx sig}
      {scope : StaticTranslation.Scope sourceContext targetContext}
      {closing : OperationalEnvironment.ClosingEnv sig []}
      (environment : OperationalStoreEnvironment.StoreEnvironment sourceContext
        sourceStore valuation targetContext scope closing)
      (coherent : OperationalEnvironmentCoherence.EnvironmentCoherence
        environment) :
      DirectLetOriginView
        (CurrentOrigin.ofEnvironment
          (.let boundTyping resultWf bodyTyping)
          (.let boundAdmissible boundPolicy bodyAdmissible resultShape)
          valuation environment coherent)
        (bound.rename valuation) (body.rename valuation.ext)

namespace DirectLetOriginView

/-- Every admitted origin whose runtime closure is syntactically a `let` has
the exact direct-let view. -/
theorem exists_of_runtime
    (origin : CurrentOrigin sourceStore)
    (runtime_eq : LambdaPFC.Tm.let runtimeBound runtimeBody =
      origin.original.term.rename origin.valuation) :
    Nonempty (DirectLetOriginView origin runtimeBound runtimeBody) := by
  rcases origin with
    ⟨⟨arity, sourceContext, sourceTerm, sourceType, typing⟩, valuation,
      admissible, targetSig, targetContext, scope, closing, environment,
      coherent⟩
  cases sourceTerm with
  | path => cases runtime_eq
  | abs => cases runtime_eq
  | pair => cases runtime_eq
  | app => cases runtime_eq
  | «let» bound body =>
      cases typing with
      | @«let» typingArity typingContext typingBound boundType resultType
          typingBody boundTyping resultWf bodyTyping =>
          cases admissible with
          | «let» boundAdmissible boundPolicy bodyAdmissible resultShape =>
              cases runtime_eq
              exact ⟨.exact boundTyping resultWf bodyTyping boundAdmissible
                boundPolicy bodyAdmissible resultShape environment coherent⟩
      | sub =>
          cases admissible with
          | neutralSub neutral => cases neutral

noncomputable def ofRuntime
    (origin : CurrentOrigin sourceStore)
    (runtime_eq : LambdaPFC.Tm.let runtimeBound runtimeBody =
      origin.original.term.rename origin.valuation) :
    DirectLetOriginView origin runtimeBound runtimeBody :=
  Classical.choice (exists_of_runtime origin runtime_eq)

end DirectLetOriginView

/-- Exact source/compiler decomposition of a direct runtime path. -/
inductive DirectPathOriginView
    {current : Nat} {sourceStore : LambdaPFC.Store current} :
    (origin : CurrentOrigin sourceStore) -> LambdaPFC.Path current -> Type where
  | exact
      {n : Nat} {sourceContext : LambdaPFC.Ctx n}
      {valuation : OperationalCode.SourceValuation n current}
      {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
      {runtimePath : LambdaPFC.Path current}
      (typing : Fragment.HasType sourceContext (.path path) sourceType)
      (admissible : OperationallyAdmissible typing)
      {sig : Sig} {targetContext : Ctx sig}
      {scope : StaticTranslation.Scope sourceContext targetContext}
      {closing : OperationalEnvironment.ClosingEnv sig []}
      (environment : OperationalStoreEnvironment.StoreEnvironment sourceContext
        sourceStore valuation targetContext scope closing)
      (coherent : OperationalEnvironmentCoherence.EnvironmentCoherence
        environment)
      (path_eq : runtimePath = path.rename valuation) :
      DirectPathOriginView
        (CurrentOrigin.ofEnvironment typing admissible valuation environment
          coherent)
        runtimePath

namespace DirectPathOriginView

theorem exists_of_runtime
    (origin : CurrentOrigin sourceStore)
    (runtime_eq : LambdaPFC.Tm.path runtimePath =
      origin.original.term.rename origin.valuation) :
    Nonempty (DirectPathOriginView origin runtimePath) := by
  rcases origin with
    ⟨⟨arity, sourceContext, sourceTerm, sourceType, typing⟩, valuation,
      admissible, targetSig, targetContext, scope, closing, environment,
      coherent⟩
  cases sourceTerm with
  | path path =>
      have path_eq : runtimePath = path.rename valuation := by
        injection runtime_eq
      exact ⟨.exact typing admissible environment coherent path_eq⟩
  | abs => cases runtime_eq
  | pair => cases runtime_eq
  | app => cases runtime_eq
  | «let» => cases runtime_eq

noncomputable def ofRuntime
    (origin : CurrentOrigin sourceStore)
    (runtime_eq : LambdaPFC.Tm.path runtimePath =
      origin.original.term.rename origin.valuation) :
    DirectPathOriginView origin runtimePath :=
  Classical.choice (exists_of_runtime origin runtime_eq)

end DirectPathOriginView

/-- Complete target result data for any admitted typed path.  Noncanonical
paths use the generated ordinary endpoint directly; the dedicated arrow-path
case recovers the retained lexical function provenance before exposing the
same endpoint as a function result. -/
structure PathResultImage
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation n current}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path path) sourceType}
    (admissible : OperationallyAdmissible typing)
    {sig : Sig} {targetContext : Ctx sig}
    {scope : StaticTranslation.Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (environment : OperationalStoreEnvironment.StoreEnvironment sourceContext
      sourceStore valuation targetContext scope closing)
    (coherent : OperationalEnvironmentCoherence.EnvironmentCoherence
      environment) : Type where
  interface : ResultInterface
    (sourceBoundary scope typing.typeWf closing (storeArguments environment))
  argument_eq : interface.view.argument =
    (OperationalTypedPathView.build admissible environment
      coherent.pathCoherence).view.argument

namespace PathResultImage

/-- Build the complete path interface from the source admissibility split.
The function case is the only one which consumes lexical function
coherence. -/
noncomputable def build
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : OperationalCode.SourceValuation n current}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path path) sourceType}
    (admissible : OperationallyAdmissible typing)
    {sig : Sig} {targetContext : Ctx sig}
    {scope : StaticTranslation.Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (environment : OperationalStoreEnvironment.StoreEnvironment sourceContext
      sourceStore valuation targetContext scope closing)
    (coherent : OperationalEnvironmentCoherence.EnvironmentCoherence
      environment) :
    PathResultImage admissible environment coherent := by
  cases admissible with
  | path pathTyping =>
      exact
        { interface :=
            OperationalPathResultInterface.ofNonCanonical
              (.path pathTyping) .singleton environment
              coherent.pathCoherence
          argument_eq := rfl }
  | functionPath spine =>
      let base := Classical.choice
        (coherent.functionCoherence.functionPathProvenance spine)
      exact
        { interface := OperationalPathResultInterface.ofFunctionPath spine
            environment coherent.pathCoherence base
          argument_eq := by
            simpa only [OperationalTypedPathView.build] using
              OperationalPathResultInterface.ofFunctionPath_argument spine
                environment coherent.pathCoherence base }
  | neutralSub neutral inner subtype targetShape =>
      cases neutral
      exact
        { interface :=
            OperationalPathResultInterface.ofNonCanonical
              (.neutralSub .path inner subtype targetShape) targetShape
              environment coherent.pathCoherence
          argument_eq := rfl }

end PathResultImage

/-- A source successor image together with the target suffix implementing the
single source transition. -/
structure ImageStep
    {beforeArity afterArity : Nat}
    {beforeState : LambdaPFC.State beforeArity}
    (before : StateImage beforeState)
    (afterState : LambdaPFC.State afterArity) : Type where
  after : StateImage afterState
  targetSteps : Exp.Steps before.target after.target

namespace StateImage

/-- Structural lifting of the direct `let_push` CK transition. -/
noncomputable def liftLetPush
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {runtimeBound : LambdaPFC.Tm current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (before : StateImage
      (LambdaPFC.State.mk sourceStore runtimeRest
        (.let runtimeBound runtimeBody))) :
    ImageStep before
      (LambdaPFC.State.mk sourceStore (runtimeBody :: runtimeRest)
        runtimeBound) := by
  rcases before with
    ⟨focus, activeOrigin, activeBoundary, currentCode, stack, running,
      capability, functionCapability⟩
  rcases currentCode with ⟨origin, form⟩
  cases form with
  | direct runtime_eq =>
      cases DirectLetOriginView.ofRuntime origin runtime_eq with
      | exact boundTyping resultWf bodyTyping boundAdmissible boundPolicy
          bodyAdmissible resultShape environment coherent =>
          let after := OperationalStateImage.StateImage.letPush
            boundTyping resultWf bodyTyping boundAdmissible boundPolicy
            bodyAdmissible resultShape environment coherent stack running
            capability
          exact
            { after := after
              targetSteps :=
                (OperationalStateImage.StateImage.letPush_target_eq
                  boundTyping resultWf bodyTyping boundAdmissible boundPolicy
                  bodyAdmissible resultShape environment coherent stack running
                  capability) ▸ .refl }

/-- Structural lifting of a non-variable source path-resolution step. -/
noncomputable def liftPath
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeCont : LambdaPFC.Tm.Cont current}
    {runtimePath : LambdaPFC.Path current} {location : Fin current}
    (before : StateImage
      (LambdaPFC.State.mk sourceStore runtimeCont (.path runtimePath)))
    (resolution : LambdaPFC.Path.Resolve runtimePath sourceStore (.loc location))
    (notVariable : Not runtimePath.IsVar) :
    ImageStep before
      (LambdaPFC.State.mk sourceStore runtimeCont (.path (.var location))) := by
  rcases before with
    ⟨focus, activeOrigin, activeBoundary, currentCode, stack, running,
      capability, functionCapability⟩
  rcases currentCode with ⟨origin, form⟩
  cases form with
  | resolvedPath path resolvedLocation resolved =>
      exact (notVariable .var).elim
  | direct runtime_eq =>
      cases DirectPathOriginView.ofRuntime origin runtime_eq with
      | exact typing admissible environment coherent path_eq =>
          have sourceResolution : LambdaPFC.Path.Resolve
              _ sourceStore (.loc location) := path_eq ▸ resolution
          let result := PathResultImage.build admissible environment coherent
          let after := OperationalStateImage.StateImage.path typing admissible
            environment coherent stack running capability functionCapability
            result.interface result.argument_eq sourceResolution
          exact
            { after := after
              targetSteps :=
                OperationalStateImage.StateImage.path_target_steps typing
                  admissible environment coherent stack running capability
                  functionCapability result.interface result.argument_eq
                  sourceResolution }

/-- Structural lifting of source value allocation.  Readiness rules out a
resolved-path current form; the nonempty source continuation exposes exactly
one captured zipper frame. -/
noncomputable def liftAllocate
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    (before : StateImage
      (LambdaPFC.State.mk sourceStore (runtimeBody :: runtimeRest)
        runtimeValue))
    (runtimeReady : runtimeValue.IsValue) :
    ImageStep before
      (LambdaPFC.State.mk (.val sourceStore runtimeValue runtimeReady)
        runtimeRest.weaken runtimeBody) := by
  rcases before with
    ⟨focus, activeOrigin, activeBoundary, currentCode, stack, running,
      capability, functionCapability⟩
  rcases currentCode with ⟨origin, form⟩
  cases stack with
  | cons frame saved tail =>
      cases form with
      | resolvedPath =>
          have impossible : False := by cases runtimeReady
          exact impossible.elim
      | direct runtime_eq =>
          rcases origin with
            ⟨original, valuation, admissible, targetSig, targetContext,
              scope, closing, environment, coherent⟩
          let origin : CurrentOrigin sourceStore :=
            { original := original
              valuation := valuation
              admissible := admissible
              targetSig := targetSig
              targetContext := targetContext
              scope := scope
              closing := closing
              environment := environment
              coherent := coherent }
          let native : DirectCodeEnvironment sourceStore runtimeValue :=
            { original := origin.original
              valuation := origin.valuation
              runtime_eq := runtime_eq
              admissible := origin.admissible
              targetSig := origin.targetSig
              targetContext := origin.targetContext
              scope := origin.scope
              closing := origin.closing
              environment := origin.environment }
          let active : ActiveResultCapability
              (CurrentOrigin.ofDirect native origin.coherent)
              (.cons frame saved tail) := by
            simpa only [native, CurrentOrigin.ofDirect] using capability
          let nativeRunning : ExecutionRunning (frameBoundClosed frame)
              (directClosed native)
              (OperationalStateImage.DirectCodeEnvironment.resultBoundary native)
              (OperationalStateImage.CapturedFrame.boundBoundary frame) := by
            simpa only [native, directClosed, CurrentOrigin.closedExpression,
              OperationalStateImage.DirectCodeEnvironment.resultBoundary,
              CurrentOrigin.resultBoundary] using running
          have activeFunction : ActiveFunctionCapability
              (CurrentOrigin.ofDirect native origin.coherent)
              (.cons frame saved tail) nativeRunning active := by
            simpa only [origin, native, active, nativeRunning, directClosed,
              CurrentOrigin.ofDirect, CurrentOrigin.closedExpression,
              OperationalStateImage.DirectCodeEnvironment.resultBoundary]
              using functionCapability
          let execution := AllocationExecution.ofImage
            (native := native) (runtimeReady := runtimeReady)
            (running := nativeRunning) (tail := tail)
            saved origin.coherent active activeFunction
          let after := OperationalStateImage.StateImage.allocate frame saved tail
            native runtimeReady nativeRunning execution active
          exact
            { after := after
              targetSteps := by
                have localSteps :=
                  saved.surrounding.steps execution.frame_steps
                have lifted := tail.plug_steps localSteps
                simpa only [native, nativeRunning, after, StateImage.target,
                  OperationalStateImage.StateImage.allocate,
                  directClosed, CurrentOrigin.closedExpression,
                  CapturedFrame.afterAllocationCode,
                  ExecutionStack.plug, restoreAfterAllocation,
                  ResultContext.compose_plug, ResultContext.ofResume_plug,
                  ExecutionStack.plug_nativeWeaken] using lifted }

/-- Structural lifting of an existing-location return.  A direct variable
path first performs the target normalization normally associated with path
resolution; this is target administration only and is composed with the
single source `return` transition. -/
noncomputable def liftReturn
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (location : Fin current)
    (before : StateImage
      (LambdaPFC.State.mk sourceStore (runtimeBody :: runtimeRest)
        (.path (.var location)))) :
    ImageStep before
      (LambdaPFC.State.mk sourceStore runtimeRest (runtimeBody.open location)) := by
  rcases before with
    ⟨focus, activeOrigin, activeBoundary, currentCode, stack, running,
      capability, functionCapability⟩
  rcases currentCode with ⟨origin, form⟩
  cases stack with
  | cons frame saved tail =>
      cases form with
      | resolvedPath sourcePath resolvedLocation resolved =>
          let execution :=
            OperationalAutomaticReturn.ReturnExecution.automatic
              (tail := tail) (resolved := resolved) (running := running)
              saved capability
          let after := OperationalStateImage.StateImage.afterReturn frame saved
            tail origin sourcePath location resolved running execution
            capability
          exact
            { after := after
              targetSteps :=
                OperationalStateImage.StateImage.return_target_steps frame saved
                  tail origin sourcePath location resolved running
                  execution capability functionCapability }
      | direct runtime_eq =>
          cases DirectPathOriginView.ofRuntime origin runtime_eq with
          | @exact pathArity pathContext valuation sourcePath sourceType
              runtimePath typing admissible targetSig targetContext scope
              closing environment coherent path_eq =>
              let resolution := path_eq ▸
                (LambdaPFC.Path.Resolve.var : LambdaPFC.Path.Resolve
                  (.var location) sourceStore (.loc location))
              let normalizedOrigin := CurrentOrigin.ofEnvironment typing
                admissible valuation environment coherent
              let target := OperationalTypedPathView.build admissible
                environment coherent.pathCoherence
              let result := PathResultImage.build admissible environment
                coherent
              have targetSteps : Exp.Steps normalizedOrigin.closedExpression
                  target.view.argument := by
                simpa only [normalizedOrigin, CurrentOrigin.closedExpression,
                  CurrentOrigin.ofEnvironment, target, target.argument_eq] using
                  target.normalization.reductions
              let resolved : ResolvedPathView normalizedOrigin sourcePath
                  location :=
                { term_eq := rfl
                  typing := typing
                  typing_eq := rfl
                  admissible := admissible
                  resolution := resolution
                  location_eq :=
                    OperationalApplicationSourceEndpoint.resolvedLocation_eq
                      environment typing resolution
                  target := target
                  interface := result.interface
                  interface_argument := result.argument_eq
                  normalizes := targetSteps }
              let normalizedRunning : ExecutionRunning (frameBoundClosed frame)
                  resolved.target.view.argument normalizedOrigin.resultBoundary
                  (OperationalStateImage.CapturedFrame.boundBoundary frame) :=
                { context := running.context
                  generated := running.generated
                  adapter := running.adapter
                  reductions := running.reductions.trans
                    (running.context.steps targetSteps) }
              have normalizationSteps :=
                OperationalStateImage.StateImage.path_target_steps typing
                  admissible environment coherent (.cons frame saved tail)
                  running capability functionCapability result.interface
                  result.argument_eq resolution
              let normalizedImage := OperationalStateImage.StateImage.path
                typing admissible environment coherent
                (.cons frame saved tail) running capability
                functionCapability result.interface result.argument_eq
                resolution
              have normalizedFunctionCapability : ActiveFunctionCapability
                  normalizedOrigin (.cons frame saved tail)
                  normalizedRunning capability := by
                simpa only [normalizedImage,
                  OperationalStateImage.StateImage.path, normalizedOrigin,
                  normalizedRunning, resolved, target] using
                  normalizedImage.functionCapability
              let execution :=
                OperationalAutomaticReturn.ReturnExecution.automatic
                  (tail := tail) (resolved := resolved)
                  (running := normalizedRunning) saved capability
              let after := OperationalStateImage.StateImage.afterReturn
                frame saved tail normalizedOrigin sourcePath location resolved
                normalizedRunning execution capability
              exact
                { after := after
                  targetSteps := normalizationSteps.trans
                    (OperationalStateImage.StateImage.return_target_steps frame
                      saved tail normalizedOrigin sourcePath location resolved
                      normalizedRunning execution capability
                      normalizedFunctionCapability) }

end StateImage

/-! ## Proof-relevant source-step classification and dispatcher -/

/-- The four CK constructors whose complete image transitions are discharged
by this module. -/
inductive NonApplicationStep :
    {beforeArity afterArity : Nat} ->
    {beforeState : LambdaPFC.State beforeArity} ->
    {afterState : LambdaPFC.State afterArity} ->
    LambdaPFC.State.Step beforeState afterState -> Type where
  | path
      {current : Nat} {sourceStore : LambdaPFC.Store current}
      {runtimeCont : LambdaPFC.Tm.Cont current}
      {runtimePath : LambdaPFC.Path current} {location : Fin current}
      (resolution : LambdaPFC.Path.Resolve runtimePath sourceStore
        (.loc location))
      (notVariable : Not runtimePath.IsVar) :
      NonApplicationStep
        (LambdaPFC.State.Step.path (k := runtimeCont) resolution notVariable)
  | letPush
      {current : Nat} {sourceStore : LambdaPFC.Store current}
      {runtimeRest : LambdaPFC.Tm.Cont current}
      {runtimeBound : LambdaPFC.Tm current}
      {runtimeBody : LambdaPFC.Tm (current + 1)} :
      NonApplicationStep
        (LambdaPFC.State.Step.let_push (sigma := sourceStore)
          (k := runtimeRest) (s := runtimeBound) (body := runtimeBody))
  | returnStep
      {current : Nat} {sourceStore : LambdaPFC.Store current}
      {runtimeRest : LambdaPFC.Tm.Cont current}
      {runtimeBody : LambdaPFC.Tm (current + 1)}
      {location : Fin current} :
      NonApplicationStep
        (LambdaPFC.State.Step.return (sigma := sourceStore)
          (body := runtimeBody) (k := runtimeRest) (x := location))
  | allocate
      {current : Nat} {sourceStore : LambdaPFC.Store current}
      {runtimeRest : LambdaPFC.Tm.Cont current}
      {runtimeBody : LambdaPFC.Tm (current + 1)}
      {runtimeValue : LambdaPFC.Tm current}
      (runtimeReady : runtimeValue.IsValue) :
      NonApplicationStep
        (LambdaPFC.State.Step.allocate (sigma := sourceStore)
          (body := runtimeBody) (k := runtimeRest) runtimeReady)

namespace NonApplicationStep

/-- Dispatch any classified non-application CK step to its complete source and
target image transition. -/
noncomputable def lift
    (before : StateImage beforeState)
    {step : LambdaPFC.State.Step beforeState afterState}
    (supported : NonApplicationStep step) :
    ImageStep before afterState := by
  cases supported with
  | path resolution notVariable =>
      exact StateImage.liftPath before resolution notVariable
  | letPush => exact StateImage.liftLetPush before
  | returnStep => exact StateImage.liftReturn _ before
  | allocate runtimeReady => exact StateImage.liftAllocate before runtimeReady

end NonApplicationStep

/-- The application constructor delegated to the wrapper-aware application
dispatcher. -/
inductive ApplicationStep :
    {beforeArity afterArity : Nat} ->
    {beforeState : LambdaPFC.State beforeArity} ->
    {afterState : LambdaPFC.State afterArity} ->
    LambdaPFC.State.Step beforeState afterState -> Type where
  | app
      {current : Nat} {sourceStore : LambdaPFC.Store current}
      {runtimeCont : LambdaPFC.Tm.Cont current}
      {functionPath argumentPath : LambdaPFC.Path current}
      {functionLocation argumentLocation : Fin current}
      {runtimeDomain : LambdaPFC.Ty current}
      {runtimeBody : LambdaPFC.Tm (current + 1)}
      (functionResolution : LambdaPFC.Path.Resolve functionPath sourceStore
        (.loc functionLocation))
      (argumentResolution : LambdaPFC.Path.Resolve argumentPath sourceStore
        (.loc argumentLocation))
      (functionBinds : LambdaPFC.Store.Binds sourceStore functionLocation
        (.abs runtimeDomain runtimeBody)) :
      ApplicationStep
        (LambdaPFC.State.Step.app (k := runtimeCont) functionResolution
          argumentResolution functionBinds)

/-- Every native CK step is either implemented by the non-application
dispatcher or belongs to the separately implemented application class. -/
inductive StepClass :
    {beforeArity afterArity : Nat} ->
    {beforeState : LambdaPFC.State beforeArity} ->
    {afterState : LambdaPFC.State afterArity} ->
    (step : LambdaPFC.State.Step beforeState afterState) -> Type where
  | application (evidence : ApplicationStep step) : StepClass step
  | nonApplication (evidence : NonApplicationStep step) : StepClass step

namespace StepClass

theorem classify_nonempty
    (step : LambdaPFC.State.Step beforeState afterState) :
    Nonempty (StepClass step) := by
  cases step with
  | app functionResolution argumentResolution functionBinds =>
      exact ⟨.application (.app functionResolution argumentResolution
        functionBinds)⟩
  | path resolution notVariable =>
      exact ⟨.nonApplication (.path resolution notVariable)⟩
  | let_push => exact ⟨.nonApplication .letPush⟩
  | «return» => exact ⟨.nonApplication .returnStep⟩
  | allocate runtimeReady =>
      exact ⟨.nonApplication (.allocate runtimeReady)⟩

/-- Noncomputable only because native CK steps live in `Prop`, while the
classifier retains the constructor evidence in `Type` for the dispatcher. -/
noncomputable def classify
    (step : LambdaPFC.State.Step beforeState afterState) :
    StepClass step :=
  Classical.choice (classify_nonempty step)

end StepClass

end OperationalNonApplicationStep
end LambdaPToFCo
