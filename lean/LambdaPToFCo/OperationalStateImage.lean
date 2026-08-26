import LambdaPToFCo.OperationalMachineImage
import LambdaPToFCo.OperationalPathCoherenceGenerated
import LambdaPToFCo.OperationalTypedPathView
import LambdaPToFCo.OperationalTypedPathCoherence
import LambdaPToFCo.OperationalApplicationSourceEndpoint
import LambdaPToFCo.OperationalFrameElimination
import LambdaPToFCo.OperationalEnvironmentCoherence
import LambdaPToFCo.OperationalExpectedResult
import LambdaPToFCo.OperationalDirectFunctionBinding

/-!
# Zipper-shaped images of source CK states

Application administration and source `let` frames alternate during an
execution.  A flat list of compiled frames loses that ordering: if an
application body is a `let`, the application's residual target context lies
between the newly pushed frame and the older source frame.

This module therefore represents a continuation as an execution zipper.
Every pushed frame retains the *parent computation's* residual
`ResultContext`, its generated value-normalization proof, and the local target
steps which reached the freshly decomposed frame.  Popping that frame can
later append binder-elimination steps and recover the parent computation
without inverting a global reduction trace.

The complete image below supports direct `let_push`, typed path resolution,
allocation, return, and wrapper-aware application.  A resolved path keeps the
runtime location tied to the same immutable typed origin while its target
focus records an explicit value normalization of the closed compilation.
The downstream one-step dispatcher preserves this image for every CK
constructor in the operationally admissible core.  Source progress is derived
from the image's source origin/store evidence; the accumulated target steps
are retained as compiler-correctness evidence rather than used to manufacture
source progress.
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
open OperationalValueEvidence
open OperationalResultContext
open OperationalMachineImage
open OperationalPathCoherence
open OperationalPathCoherenceGenerated
open OperationalTypedPathView
open OperationalTypedPathCoherence
open OperationalFrameElimination
open OperationalEnvironmentCoherence
open OperationalExpectedResult
open OperationalDirectFunctionBinding

namespace NonCanonicalResultShape

/-- Noncanonical source shapes survive lexical weakening. -/
def weaken
    {sourceType : LambdaPFC.Ty n}
    (shape : NonCanonicalResultShape sourceType) :
    NonCanonicalResultShape sourceType.weaken := by
  cases shape <;> constructor

end NonCanonicalResultShape

/-! ## Immutable source-code origins and their current target focus -/

/-- The immutable typed source code and lexical compiler environment carried
by a current CK computation.  Source path coherence is an explicit syntactic
invariant of the lexical environment. -/
structure CurrentOrigin {current : Nat}
    (sourceStore : LambdaPFC.Store current) : Type where
  original : TypedCode
  valuation : SourceValuation original.arity current
  admissible : OperationallyAdmissible original.typing
  targetSig : Sig
  targetContext : Ctx targetSig
  scope : Scope original.context targetContext
  closing : ClosingEnv targetSig []
  environment : StoreEnvironment original.context sourceStore valuation
    targetContext scope closing
  coherent : EnvironmentCoherence environment

namespace CurrentOrigin

/-- The current lexical path invariant projected from the recursive
coherence needed when execution later re-enters a stored native origin. -/
noncomputable def pathCoherent
    (origin : CurrentOrigin sourceStore) :
    StorePathCoherence origin.environment :=
  origin.coherent.pathCoherence

/-- Behavioral result boundary selected by the current source typing and
lexical target environment. -/
noncomputable def resultBoundary
    (origin : CurrentOrigin sourceStore) : ResultBoundary :=
  sourceBoundary origin.scope origin.original.typing.typeWf origin.closing
    (storeArguments origin.environment)

/-- Closed target compilation of the immutable typed source origin. -/
noncomputable def closedExpression
    (origin : CurrentOrigin sourceStore) : Exp [] :=
  origin.closing.closeExp
    (TermTranslation.elaborate origin.scope origin.original.typing)

/-- Package a typed source computation interpreted in an existing compiled
lexical environment. -/
def ofEnvironment
    {current lexical : Nat}
    {sourceStore : LambdaPFC.Store current}
    {sourceContext : LambdaPFC.Ctx lexical}
    {sourceTerm : LambdaPFC.Tm lexical}
    {sourceType : LambdaPFC.Ty lexical}
    (typing : Fragment.HasType sourceContext sourceTerm sourceType)
    (admissible : OperationallyAdmissible typing)
    (valuation : SourceValuation lexical current)
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : EnvironmentCoherence environment) :
    CurrentOrigin sourceStore where
  original := TypedCode.ofTyping typing
  valuation := valuation
  admissible := admissible
  targetSig := sig
  targetContext := targetContext
  scope := scope
  closing := closing
  environment := environment
  coherent := coherent

/-- The canonical origin of a closed admissible program. -/
def initial
    {term : LambdaPFC.Tm 0} {sourceType : LambdaPFC.Ty 0}
    (typing : Fragment.HasType LambdaPFC.Ctx.nil term sourceType)
    (admissible : OperationallyAdmissible typing) :
    CurrentOrigin LambdaPFC.Store.empty :=
  ofEnvironment typing admissible SourceValuation.identity
    StoreEnvironment.initial EnvironmentCoherence.initial

/-- Recover a full current origin from the allocation-oriented direct code
environment once its external path invariant is supplied. -/
def ofDirect
    (code : DirectCodeEnvironment sourceStore runtimeTerm)
    (coherent : EnvironmentCoherence code.environment) :
    CurrentOrigin sourceStore where
  original := code.original
  valuation := code.valuation
  admissible := code.admissible
  targetSig := code.targetSig
  targetContext := code.targetContext
  scope := code.scope
  closing := code.closing
  environment := code.environment
  coherent := coherent

/-- A source origin survives a physical allocation hidden from its lexical
context.  Its target closure is unchanged while its source valuation and
recursive store environment weaken. -/
noncomputable def nativeWeaken
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    (origin : CurrentOrigin sourceStore)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    CurrentOrigin (.val sourceStore runtimeValue runtimeReady) where
  original := origin.original
  valuation := origin.valuation.weaken
  admissible := origin.admissible
  targetSig := origin.targetSig
  targetContext := origin.targetContext
  scope := origin.scope
  closing := origin.closing
  environment := origin.environment.nativeWeaken runtimeValue runtimeReady
  coherent := origin.coherent.weaken runtimeValue runtimeReady

/-- Repackage the immutable current origin as direct code at a concrete
runtime valuation closure. -/
noncomputable def directCode
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    (origin : CurrentOrigin sourceStore)
    (runtimeTerm : LambdaPFC.Tm current)
    (runtime_eq : runtimeTerm =
      origin.original.term.rename origin.valuation) :
    DirectCodeEnvironment sourceStore runtimeTerm where
  original := origin.original
  valuation := origin.valuation
  runtime_eq := runtime_eq
  admissible := origin.admissible
  targetSig := origin.targetSig
  targetContext := origin.targetContext
  scope := origin.scope
  closing := origin.closing
  environment := origin.environment

/-- Canonical direct result interface selected by a current origin once its
runtime closure is known to be a value. -/
noncomputable def directResultInterface
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    (origin : CurrentOrigin sourceStore)
    (runtimeTerm : LambdaPFC.Tm current)
    (runtime_eq : runtimeTerm =
      origin.original.term.rename origin.valuation)
    (runtimeReady : runtimeTerm.IsValue) :
    ResultInterface origin.resultBoundary := by
  let code := origin.directCode runtimeTerm runtime_eq
  let interface : ResultInterface
      (sourceBoundary code.scope code.original.typing.typeWf code.closing
        (storeArguments code.environment)) :=
    { view :=
        (OperationalDirectFunctionBinding.DirectCodeEnvironment.acceptedClosedView
          code runtimeReady origin.coherent).view
      accepted :=
        OperationalDirectFunctionBinding.DirectCodeEnvironment.sourceAcceptance
          code runtimeReady origin.coherent }
  simpa only [code, CurrentOrigin.directCode,
    CurrentOrigin.resultBoundary] using
    interface

end CurrentOrigin

namespace DirectCodeEnvironment

/-- Behavioral result boundary of direct immutable source code. -/
noncomputable def resultBoundary
    (code : DirectCodeEnvironment sourceStore runtimeTerm) : ResultBoundary :=
  sourceBoundary code.scope code.original.typing.typeWf code.closing
    (storeArguments code.environment)

end DirectCodeEnvironment

namespace CapturedFrame

/-- Interface expected from the computation in a captured frame's hole. -/
noncomputable def boundBoundary
    (frame : CapturedFrame sourceStore runtimeBody) : ResultBoundary :=
  sourceBoundary frame.scope frame.boundTyping.typeWf frame.closing
    (storeArguments frame.environment)

/-- Interface of the complete let expression outside its bound hole. -/
noncomputable def resultBoundary
    (frame : CapturedFrame sourceStore runtimeBody) : ResultBoundary :=
  sourceBoundary frame.scope frame.image.resultWf frame.closing
    (storeArguments frame.environment)

end CapturedFrame

/-! ## Source-only result provenance -/

/-- The immutable typed source closure relevant to physical head
provenance.  Target compilation and coherence fields are deliberately
absent. -/
structure SourceClosure (current : Nat) : Type where
  original : TypedCode
  valuation : SourceValuation original.arity current

namespace SourceClosure

def ofOrigin
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    (origin : CurrentOrigin sourceStore) : SourceClosure current :=
  ⟨origin.original, origin.valuation⟩

def ofDirect
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeValue : LambdaPFC.Tm current}
    (native : DirectCodeEnvironment sourceStore runtimeValue) :
    SourceClosure current :=
  ⟨native.original, native.valuation⟩

def ofBound
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody) : SourceClosure current :=
  ⟨TypedCode.ofTyping frame.boundTyping, frame.image.valuation⟩

def ofResult
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody) : SourceClosure current :=
  ⟨TypedCode.ofTyping
      (.let frame.boundTyping frame.image.resultWf frame.image.bodyTyping),
    frame.image.valuation⟩

def weaken {current : Nat}
    (closure : SourceClosure current) : SourceClosure (current + 1) :=
  ⟨closure.original, closure.valuation.weaken⟩

end SourceClosure

/-- The honest post-resolution image of a typed source path.

The advertised target view is indexed by the path's *final* typing
derivation, so path-only subsumption may adapt the raw lexical slot.  The
physical location remains tied separately to the derivation's static
referent; no equality between the adapted view and the raw physical slot is
assumed. -/
structure ResolvedPathView
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    (origin : CurrentOrigin sourceStore)
    (path : LambdaPFC.Path origin.original.arity)
    (location : Fin current) : Type where
  term_eq : origin.original.term = .path path
  typing : Fragment.HasType origin.original.context (.path path)
    origin.original.resultType
  typing_eq : (term_eq ▸ origin.original.typing) = typing
  admissible : OperationallyAdmissible typing
  resolution : LambdaPFC.Path.Resolve
    (path.rename origin.valuation) sourceStore (.loc location)
  location_eq : location =
    origin.valuation (typedPathReferent typing)
  target : ClosedPathView origin.scope typing origin.closing
  interface : ResultInterface origin.resultBoundary
  interface_argument : interface.view.argument = target.view.argument
  normalizes : Exp.Steps origin.closedExpression target.view.argument

namespace ResolvedPathView

/-- Native cell at the statically retained referent of a resolved path. -/
noncomputable def located
    (resolved : ResolvedPathView origin path location) :
    StoreEnvironment.LocatedBinding origin.environment
      (typedPathReferent resolved.typing) :=
  origin.environment.lookup (typedPathReferent resolved.typing)

/-- Rebuild the ready resolved endpoint as the ordinary interface advertised
by the immutable origin.  Supported path results are ordinary by the
operational-admissibility restriction, so no member provenance is invented
here. -/
noncomputable def resultInterface
    (resolved : ResolvedPathView origin path location) :
    ResultInterface origin.resultBoundary :=
  resolved.interface

@[simp] theorem resultInterface_argument
    (resolved : ResolvedPathView origin path location) :
    resolved.resultInterface.view.argument =
      resolved.target.view.argument := by
  exact resolved.interface_argument

end ResolvedPathView

/-- Runtime syntax and target focus associated with one immutable source
origin.

The direct form is an ordinary valuation closure.  The resolved-path form
does not assert that the runtime location is a renaming of the original path;
it retains the source resolution and the target normalization separately. -/
inductive CurrentFocusImage
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    (origin : CurrentOrigin sourceStore) :
    LambdaPFC.Tm current -> Exp [] -> Type where
  | direct
      (runtime_eq : runtimeTerm =
        origin.original.term.rename origin.valuation) :
      CurrentFocusImage origin runtimeTerm origin.closedExpression
  | resolvedPath
      (path : LambdaPFC.Path origin.original.arity)
      (location : Fin current)
      (resolved : ResolvedPathView origin path location) :
      CurrentFocusImage origin (.path (.var location))
        resolved.target.view.argument

/-- Complete current-code image, indexed by both native runtime syntax and
the closed target expression occupying the active hole of the zipper. -/
structure CurrentCodeEnvironment
    {current : Nat} (sourceStore : LambdaPFC.Store current)
    (runtimeTerm : LambdaPFC.Tm current) (focus : Exp []) : Type where
  origin : CurrentOrigin sourceStore
  form : CurrentFocusImage origin runtimeTerm focus

namespace CurrentCodeEnvironment

/-- Build the direct current-code form selected by a valuation equality. -/
def direct
    (origin : CurrentOrigin sourceStore)
    (runtime_eq : runtimeTerm =
      origin.original.term.rename origin.valuation) :
    CurrentCodeEnvironment sourceStore runtimeTerm origin.closedExpression :=
  ⟨origin, .direct runtime_eq⟩

end CurrentCodeEnvironment

/-! ## Local computation histories -/

/-- Target execution local to one active source computation.

`origin` is the closed target term from which this computation started.  The
residual context is kept separate from the current focus so it can be moved
across a source `let_push` without changing their order. -/
structure ExecutionRunning
    (origin focus : Exp []) (input output : ResultBoundary.{0}) : Type where
  context : ResultContext []
  generated : GeneratedResultContext context
  adapter : ExpectedResultAdapter context input output
  reductions : Exp.Steps origin (context.plug focus)

namespace ExecutionRunning

/-- A newly entered computation has the identity residual context. -/
def start (origin : Exp []) (boundary : ResultBoundary.{0}) :
    ExecutionRunning origin origin boundary boundary where
  context := .identity
  generated := .identity
  adapter := .identity boundary
  reductions := .refl

end ExecutionRunning

/-- Closed compilation of the source computation originally placed in this
frame's hole. -/
noncomputable def frameBoundClosed
    (frame : CapturedFrame sourceStore runtimeBody) : Exp [] :=
  frame.closing.closeExp
    (TermTranslation.elaborate frame.scope frame.boundTyping)

/-- A compiled source frame preserves a multi-step reduction in its active
argument. -/
theorem frame_fill_steps
    (frame : OperationalContexts.Frame [])
    (steps : Exp.Steps current current') :
    Exp.Steps (frame.fill current) (frame.fill current') := by
  induction steps with
  | refl => exact .refl
  | tail step steps ih => exact .tail (frame.fill_step step) ih

/-- Native store weakening changes source indices but leaves the closed bound
compilation unchanged. -/
@[simp] theorem frameBoundClosed_nativeWeaken
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    frameBoundClosed (frame.nativeWeaken runtimeValue runtimeReady) =
      frameBoundClosed frame := by
  rfl

/-- A pushed frame together with the parent computation history suspended
around it.  The saved context sits immediately outside this frame and inside
every older frame. -/
structure SuspendedExecution
    (frame : CapturedFrame sourceStore runtimeBody)
    (parentOrigin : Exp [])
    (parentBoundary : ResultBoundary.{0}) : Type where
  resultShape : NonCanonicalResultShape frame.image.resultType
  surrounding : ResultContext []
  generated : GeneratedResultContext surrounding
  adapter : ExpectedResultAdapter surrounding
    (OperationalStateImage.CapturedFrame.resultBoundary frame) parentBoundary
  coherent : EnvironmentCoherence frame.environment
  reductions : Exp.Steps parentOrigin
    (surrounding.plug
      (frame.compilation.closeFrame.fill (frameBoundClosed frame)))

/-! ## The heterogeneous execution zipper -/

/-- A source continuation indexed by the closed origin of its active head
computation.  Each `cons` changes that origin to the newly pushed frame's
bound computation and stores the parent origin in its suspended history. -/
inductive ExecutionStack {current : Nat}
    (sourceStore : LambdaPFC.Store current) :
    LambdaPFC.Tm.Cont current -> Exp [] -> ResultBoundary.{0} -> Type where
  | nil (origin : Exp []) (boundary : ResultBoundary.{0}) :
      ExecutionStack sourceStore [] origin boundary
  | cons
      {runtimeBody : LambdaPFC.Tm (current + 1)}
      {runtimeRest : LambdaPFC.Tm.Cont current}
      {parentOrigin : Exp []}
      {parentBoundary : ResultBoundary.{0}}
      (frame : CapturedFrame sourceStore runtimeBody)
      (saved : SuspendedExecution frame parentOrigin parentBoundary)
      (tail : ExecutionStack sourceStore runtimeRest parentOrigin
        parentBoundary) :
      ExecutionStack sourceStore (runtimeBody :: runtimeRest)
        (frameBoundClosed frame)
        (OperationalStateImage.CapturedFrame.boundBoundary frame)

namespace ExecutionStack

/-- Reconstruct the whole target evaluation context represented by the
alternating source frames and generated result contexts. -/
noncomputable def plug :
    {runtimeCont : LambdaPFC.Tm.Cont current} ->
    {activeOrigin : Exp []} ->
    {activeBoundary : ResultBoundary.{0}} ->
    ExecutionStack sourceStore runtimeCont activeOrigin activeBoundary ->
    Exp [] -> Exp []
  | [], _, _, .nil _ _ => fun current => current
  | _ :: _, _, _, .cons frame saved tail => fun current =>
      tail.plug
        (saved.surrounding.plug
          (frame.compilation.closeFrame.fill current))

/-- Target reduction in the active hole is preserved by every alternating
layer of the execution zipper. -/
theorem plug_steps
    (stack : ExecutionStack sourceStore runtimeCont activeOrigin
      activeBoundary)
    (steps : Exp.Steps current current') :
    Exp.Steps (stack.plug current) (stack.plug current') := by
  induction stack generalizing current current' with
  | nil => exact steps
  | cons frame saved tail ih =>
      exact ih
        (saved.surrounding.steps
          (frame_fill_steps frame.compilation.closeFrame steps))

/-- The oldest target origin represented by a zipper. -/
noncomputable def rootOrigin :
    {runtimeCont : LambdaPFC.Tm.Cont current} ->
    {activeOrigin : Exp []} ->
    {activeBoundary : ResultBoundary.{0}} ->
    ExecutionStack sourceStore runtimeCont activeOrigin activeBoundary -> Exp []
  | [], _, _, .nil origin _ => origin
  | _ :: _, _, _, .cons _ _ tail => tail.rootOrigin

/-- The saved local histories compose to a reduction from the root origin to
the zipper filled with its active origin. -/
theorem prefix_steps
    (stack : ExecutionStack sourceStore runtimeCont activeOrigin
      activeBoundary) :
    Exp.Steps stack.rootOrigin (stack.plug activeOrigin) := by
  induction stack with
  | nil => exact .refl
  | cons frame saved tail ih =>
      exact ih.trans (tail.plug_steps saved.reductions)

/-- Every suspended source frame and local history crosses a physical
allocation.  Closed target syntax and all saved target reductions remain
unchanged. -/
noncomputable def nativeWeaken
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    {runtimeCont : LambdaPFC.Tm.Cont current} ->
    {activeOrigin : Exp []} ->
    {activeBoundary : ResultBoundary.{0}} ->
    ExecutionStack sourceStore runtimeCont activeOrigin activeBoundary ->
    ExecutionStack (.val sourceStore runtimeValue runtimeReady)
      runtimeCont.weaken activeOrigin activeBoundary
  | [], _, _, .nil origin boundary => .nil origin boundary
  | _ :: _, _, _, .cons frame saved tail =>
      let weakenedFrame := frame.nativeWeaken runtimeValue runtimeReady
      let weakenedSaved : SuspendedExecution weakenedFrame _ _ :=
        { resultShape := saved.resultShape
          surrounding := saved.surrounding
          generated := saved.generated
          adapter := by
            simpa only [weakenedFrame, CapturedFrame.resultBoundary,
              CapturedFrame.nativeWeaken] using saved.adapter
          coherent := saved.coherent.weaken runtimeValue runtimeReady
          reductions := by
            simpa only [weakenedFrame,
              CapturedFrame.closeFrame_nativeWeaken,
              frameBoundClosed_nativeWeaken] using saved.reductions }
      .cons weakenedFrame weakenedSaved
        (tail.nativeWeaken runtimeValue runtimeReady)

/-- Native weakening is invisible to the target expression reconstructed by
the zipper. -/
@[simp] theorem plug_nativeWeaken
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeCont : LambdaPFC.Tm.Cont current}
    {activeOrigin : Exp []}
    {activeBoundary : ResultBoundary.{0}}
    (stack : ExecutionStack sourceStore runtimeCont activeOrigin
      activeBoundary)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue)
    (focus : Exp []) :
    (@nativeWeaken current sourceStore runtimeValue runtimeReady runtimeCont
      activeOrigin activeBoundary stack).plug focus =
      stack.plug focus := by
  induction stack generalizing focus with
  | nil => rfl
  | cons frame saved tail ih =>
      change
        (tail.nativeWeaken runtimeValue runtimeReady).plug
            (saved.surrounding.plug
              ((frame.nativeWeaken runtimeValue runtimeReady).compilation.closeFrame.fill
                focus)) =
          tail.plug
            (saved.surrounding.plug
              (frame.compilation.closeFrame.fill focus))
      rw [CapturedFrame.closeFrame_nativeWeaken]
      exact ih _

end ExecutionStack

/-! ## Source provenance aligned with the execution zipper -/

private noncomputable def nonCanonical_of_closure_eq
    {left right : SourceClosure current}
    (shape : NonCanonicalResultShape left.original.resultType)
    (equal : left = right) :
    NonCanonicalResultShape right.original.resultType := by
  cases equal
  exact shape

/-- The current source-side demand at one nonempty zipper level. -/
inductive ActiveHeadCapability
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    (origin : CurrentOrigin sourceStore)
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody) : Type where
  | same
      (closure_eq : SourceClosure.ofOrigin origin =
        SourceClosure.ofBound frame) :
      ActiveHeadCapability origin frame
  | nonCanonical
      (shape : NonCanonicalResultShape frame.image.holeType) :
      ActiveHeadCapability origin frame

/-- Source-only physical-head provenance recursively aligned with the zipper.

This is a structurally recursive family rather than a second dependent
inductive.  Matching the zipper first avoids requiring injectivity of
target-rich captured frames when a level is popped. -/
noncomputable def ActiveResultCapability
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    (origin : CurrentOrigin sourceStore) :
    {runtimeCont : LambdaPFC.Tm.Cont current} ->
    {activeOrigin : Exp []} -> {activeBoundary : ResultBoundary.{0}} ->
    ExecutionStack sourceStore runtimeCont activeOrigin activeBoundary ->
    Type
  | [], _, _, .nil _ _ => PUnit
  | _ :: _, _, _, .cons frame _ tail =>
      (parentSourceOrigin : CurrentOrigin sourceStore) ×'
        ActiveResultCapability parentSourceOrigin tail ×'
        (SourceClosure.ofOrigin parentSourceOrigin =
          SourceClosure.ofResult frame) ×'
        ActiveHeadCapability origin frame

namespace ActiveResultCapability

/-- Empty zipper provenance. -/
noncomputable def nil
    (origin : CurrentOrigin sourceStore)
    (rootOrigin : Exp []) (rootBoundary : ResultBoundary.{0}) :
    ActiveResultCapability origin (.nil rootOrigin rootBoundary) :=
  PUnit.unit

/-- Enter a frame with the original bound source closure. -/
noncomputable def same
    {frame : CapturedFrame sourceStore runtimeBody}
    {saved : SuspendedExecution frame parentTargetOrigin parentBoundary}
    {tail : ExecutionStack sourceStore runtimeRest parentTargetOrigin
      parentBoundary}
    {origin parentSourceOrigin : CurrentOrigin sourceStore}
    (parent : ActiveResultCapability parentSourceOrigin tail)
    (parent_eq : SourceClosure.ofOrigin parentSourceOrigin =
      SourceClosure.ofResult frame)
    (closure_eq : SourceClosure.ofOrigin origin = SourceClosure.ofBound frame) :
    ActiveResultCapability origin (.cons frame saved tail) :=
  ⟨parentSourceOrigin, parent, parent_eq, .same closure_eq⟩

/-- Enter a frame whose current advertised result is noncanonical. -/
noncomputable def nonCanonical
    {frame : CapturedFrame sourceStore runtimeBody}
    {saved : SuspendedExecution frame parentTargetOrigin parentBoundary}
    {tail : ExecutionStack sourceStore runtimeRest parentTargetOrigin
      parentBoundary}
    {origin parentSourceOrigin : CurrentOrigin sourceStore}
    (parent : ActiveResultCapability parentSourceOrigin tail)
    (parent_eq : SourceClosure.ofOrigin parentSourceOrigin =
      SourceClosure.ofResult frame)
    (shape : NonCanonicalResultShape frame.image.holeType) :
    ActiveResultCapability origin (.cons frame saved tail) :=
  ⟨parentSourceOrigin, parent, parent_eq, .nonCanonical shape⟩

/-- Change the current source origin after an operation whose advertised
result is noncanonical.  An outer noncanonical demand is preserved; an exact
same-origin demand receives the transported result shape. -/
noncomputable def replaceInput
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeCont : LambdaPFC.Tm.Cont current}
    {activeOrigin : Exp []} {activeBoundary : ResultBoundary.{0}}
    {origin : CurrentOrigin sourceStore}
    {stack : ExecutionStack sourceStore runtimeCont activeOrigin activeBoundary}
    (capability : ActiveResultCapability origin stack)
    (newOrigin : CurrentOrigin sourceStore)
    (shape : NonCanonicalResultShape origin.original.resultType) :
    ActiveResultCapability newOrigin stack := by
  cases stack with
  | nil root boundary => exact PUnit.unit
  | cons frame saved tail =>
      rcases capability with ⟨parentOrigin, parent, parent_eq, head⟩
      refine ⟨parentOrigin, parent, parent_eq, ?_⟩
      cases head with
      | same closure_eq =>
          exact .nonCanonical
            (nonCanonical_of_closure_eq shape closure_eq)
      | nonCanonical outputShape => exact .nonCanonical outputShape

/-- Every saved source provenance tree weakens together with the native
store and heterogeneous execution stack. -/
noncomputable def nativeWeaken
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeCont : LambdaPFC.Tm.Cont current}
    {activeOrigin : Exp []} {activeBoundary : ResultBoundary.{0}}
    {origin : CurrentOrigin sourceStore}
    {stack : ExecutionStack sourceStore runtimeCont activeOrigin activeBoundary}
    (capability : ActiveResultCapability origin stack)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    ActiveResultCapability
      (origin.nativeWeaken runtimeValue runtimeReady)
      (stack.nativeWeaken runtimeValue runtimeReady) := by
  induction stack generalizing origin with
  | nil => exact PUnit.unit
  | cons frame saved tail ih =>
      rcases capability with ⟨parentOrigin, parent, parent_eq, head⟩
      refine ⟨parentOrigin.nativeWeaken runtimeValue runtimeReady,
        ih parent, congrArg SourceClosure.weaken parent_eq, ?_⟩
      cases head with
      | same closure_eq =>
          exact .same (congrArg SourceClosure.weaken closure_eq)
      | nonCanonical shape => exact .nonCanonical shape

/-- Pop a source frame without changing the physical store.  The parent
provenance is restored and its complete-let result is noncanonical in the
restricted executable core. -/
noncomputable def pop
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {parentTargetOrigin : Exp []}
    {parentBoundary : ResultBoundary.{0}}
    {frame : CapturedFrame sourceStore runtimeBody}
    {saved : SuspendedExecution frame parentTargetOrigin parentBoundary}
    {tail : ExecutionStack sourceStore runtimeRest parentTargetOrigin
      parentBoundary}
    {origin : CurrentOrigin sourceStore}
    (capability : ActiveResultCapability origin (.cons frame saved tail))
    (newOrigin : CurrentOrigin sourceStore)
    (shape : NonCanonicalResultShape frame.image.resultType) :
    ActiveResultCapability newOrigin tail :=
  capability.2.1.replaceInput newOrigin
    (nonCanonical_of_closure_eq shape capability.2.2.1.symm)

/-- Allocation pops a frame while weakening the restored parent provenance
through the newly allocated physical cell. -/
noncomputable def popNative
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {parentTargetOrigin : Exp []}
    {parentBoundary : ResultBoundary.{0}}
    {frame : CapturedFrame sourceStore runtimeBody}
    {saved : SuspendedExecution frame parentTargetOrigin parentBoundary}
    {tail : ExecutionStack sourceStore runtimeRest parentTargetOrigin
      parentBoundary}
    {origin : CurrentOrigin sourceStore}
    (capability : ActiveResultCapability origin (.cons frame saved tail))
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue)
    (newOrigin : CurrentOrigin (.val sourceStore runtimeValue runtimeReady))
    (shape : NonCanonicalResultShape frame.image.resultType) :
    ActiveResultCapability newOrigin
      (tail.nativeWeaken runtimeValue runtimeReady) :=
  (capability.2.1.nativeWeaken runtimeValue runtimeReady).replaceInput
    newOrigin (nonCanonical_of_closure_eq shape capability.2.2.1.symm)

end ActiveResultCapability

/-! ## Function provenance at the active zipper head -/

/-- Exact aligned function evidence after mapping the current direct result
interface through the active result adapter.  Unlike
`SourceResultAcceptance.function`, this callback retains the physical native
origin of the current runtime value. -/
abbrev ActiveFunctionTransformer
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    (origin : CurrentOrigin sourceStore)
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody)
    {focus : Exp []}
    (running : ExecutionRunning (frameBoundClosed frame) focus
      origin.resultBoundary
      (OperationalStateImage.CapturedFrame.boundBoundary frame)) : Prop :=
  (runtimeTerm : LambdaPFC.Tm current) ->
  (runtime_eq : runtimeTerm =
    origin.original.term.rename origin.valuation) ->
  (runtimeReady : runtimeTerm.IsValue) ->
  {domain codomain : LambdaPFC.Ty frame.image.originalArity} ->
  (type_eq : frame.image.holeType = .Fun domain codomain.weaken) ->
  Nonempty
    (OperationalFunctionEnvironmentCoherence.FunctionBindingWitness
      frame.scope frame.closing
      (running.adapter.map
        (origin.directResultInterface runtimeTerm runtime_eq
          runtimeReady)).view
      domain sourceStore runtimeTerm origin.environment)

/-- Function evidence required by one active zipper head.  Same-closure
heads retain an exact adapter transformer; a noncanonical expected result has
no arrow case and therefore carries no data. -/
inductive ActiveHeadFunctionCapability
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    (origin : CurrentOrigin sourceStore)
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody)
    {focus : Exp []}
    (running : ExecutionRunning (frameBoundClosed frame) focus
      origin.resultBoundary
      (OperationalStateImage.CapturedFrame.boundBoundary frame)) :
    ActiveHeadCapability origin frame -> Type where
  | same
      {closure_eq : SourceClosure.ofOrigin origin =
        SourceClosure.ofBound frame}
      (transform : ActiveFunctionTransformer origin frame running) :
      ActiveHeadFunctionCapability origin frame running (.same closure_eq)
  | nonCanonical
      {shape : NonCanonicalResultShape frame.image.holeType} :
      ActiveHeadFunctionCapability origin frame running (.nonCanonical shape)

/-- Active-only function provenance.  Older zipper levels need no function
tree: every pop advertises a noncanonical complete-let result, while the
current same-closure head retains the sole transformer allocation consumes.
-/
noncomputable def ActiveFunctionCapability
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    (origin : CurrentOrigin sourceStore) :
    {runtimeCont : LambdaPFC.Tm.Cont current} ->
    {activeOrigin : Exp []} -> {activeBoundary : ResultBoundary.{0}} ->
    (stack : ExecutionStack sourceStore runtimeCont activeOrigin
      activeBoundary) ->
    {focus : Exp []} ->
    (running : ExecutionRunning activeOrigin focus origin.resultBoundary
      activeBoundary) ->
    ActiveResultCapability origin stack -> Type
  | [], _, _, .nil _ _, _, _, _ => PUnit
  | _ :: _, _, _, .cons frame _ _, _, running, capability =>
      ActiveHeadFunctionCapability origin frame running capability.2.2.2

namespace ActiveFunctionCapability

/-- Empty execution has no allocation frame and hence no active function
obligation. -/
noncomputable def nil
    (origin : CurrentOrigin sourceStore) :
    ActiveFunctionCapability origin
      (.nil origin.closedExpression origin.resultBoundary)
      (.start origin.closedExpression origin.resultBoundary)
      (ActiveResultCapability.nil origin origin.closedExpression
        origin.resultBoundary) :=
  PUnit.unit

/-- A noncanonical current result makes a same-head function callback
vacuous; an already noncanonical head remains vacuous. -/
noncomputable def ofNonCanonicalInput
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeCont : LambdaPFC.Tm.Cont current}
    {activeOrigin focus : Exp []}
    {activeBoundary : ResultBoundary.{0}}
    {origin : CurrentOrigin sourceStore}
    {stack : ExecutionStack sourceStore runtimeCont activeOrigin
      activeBoundary}
    {running : ExecutionRunning activeOrigin focus origin.resultBoundary
      activeBoundary}
    (capability : ActiveResultCapability origin stack)
    (shape : NonCanonicalResultShape origin.original.resultType) :
    ActiveFunctionCapability origin stack running capability := by
  cases stack with
  | nil => exact PUnit.unit
  | cons frame saved tail =>
      rcases capability with
        ⟨parentOrigin, parent, parent_eq, head⟩
      cases head with
      | same closure_eq =>
          refine .same (fun runtimeTerm runtime_eq runtimeReady => ?_)
          intro domain codomain type_eq
          have frameShape := nonCanonical_of_closure_eq shape closure_eq
          exact (frameShape.notArrow
            { domain := domain
              codomain := codomain.weaken
              equality := type_eq }).elim
      | nonCanonical => exact .nonCanonical

/-- Replacing an active input at a noncanonical source result always leaves a
noncanonical active head.  Thus no function transformer is required for the
new origin, independently of its own result type. -/
noncomputable def ofReplaceInput
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeCont : LambdaPFC.Tm.Cont current}
    {activeOrigin focus : Exp []}
    {activeBoundary : ResultBoundary.{0}}
    {origin : CurrentOrigin sourceStore}
    {stack : ExecutionStack sourceStore runtimeCont activeOrigin
      activeBoundary}
    (capability : ActiveResultCapability origin stack)
    (newOrigin : CurrentOrigin sourceStore)
    (shape : NonCanonicalResultShape origin.original.resultType)
    {running : ExecutionRunning activeOrigin focus newOrigin.resultBoundary
      activeBoundary} :
    ActiveFunctionCapability newOrigin stack running
      (capability.replaceInput newOrigin shape) := by
  cases stack with
  | nil => exact PUnit.unit
  | cons frame saved tail =>
      rcases capability with
        ⟨parentOrigin, parent, parent_eq, head⟩
      cases head <;> exact .nonCanonical

end ActiveFunctionCapability

/-! ## Images of complete CK states -/

/-- A complete source-state image.  The active current-code focus is indexed
by a local execution history, and the zipper explains how that history is
nested in every suspended source frame. -/
structure StateImage {current : Nat}
    (state : LambdaPFC.State current) : Type where
  focus : Exp []
  activeOrigin : Exp []
  activeBoundary : ResultBoundary.{0}
  current : CurrentCodeEnvironment state.store state.term focus
  stack : ExecutionStack state.store state.cont activeOrigin activeBoundary
  running : ExecutionRunning activeOrigin focus current.origin.resultBoundary
    activeBoundary
  capability : ActiveResultCapability current.origin stack
  functionCapability :
    ActiveFunctionCapability current.origin stack running capability

namespace StateImage

/-- The complete current target expression selected by a state image. -/
noncomputable def target (image : StateImage state) : Exp [] :=
  image.stack.plug (image.running.context.plug image.focus)

/-- Every state image retains a syntactic target execution from the oldest
root origin to its current target expression. -/
theorem target_steps (image : StateImage state) :
    Exp.Steps image.stack.rootOrigin image.target :=
  image.stack.prefix_steps.trans
    (image.stack.plug_steps image.running.reductions)

/-- Initial image of a closed admissible source program. -/
noncomputable def initial
    {term : LambdaPFC.Tm 0} {sourceType : LambdaPFC.Ty 0}
    (typing : Fragment.HasType LambdaPFC.Ctx.nil term sourceType)
    (admissible : OperationallyAdmissible typing) :
    StateImage (LambdaPFC.State.initial term) :=
  let origin := CurrentOrigin.initial typing admissible
  have runtime_eq : term = origin.original.term.rename origin.valuation := by
    simpa only [origin, CurrentOrigin.initial, CurrentOrigin.ofEnvironment,
      TypedCode.ofTyping] using (LambdaPFC.Tm.rename_id term).symm
  { focus := origin.closedExpression
    activeOrigin := origin.closedExpression
    activeBoundary := origin.resultBoundary
    current := .direct origin runtime_eq
    stack := .nil origin.closedExpression origin.resultBoundary
    running := .start origin.closedExpression origin.resultBoundary
    capability := ActiveResultCapability.nil origin origin.closedExpression
      origin.resultBoundary
    functionCapability := PUnit.unit }

/-! ### Exact direct `let_push` -/

/-- Build the state image immediately before an exact direct `let_push`.
This helper makes the executable-core restriction explicit: the current
typing derivation itself ends in `HasType.let`, rather than a surrounding
subsumption layer. -/
noncomputable def directLet
    {n current : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
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
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : EnvironmentCoherence environment)
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {parentOrigin : Exp []}
    {parentBoundary : ResultBoundary.{0}}
    (stack : ExecutionStack sourceStore runtimeRest parentOrigin
      parentBoundary)
    (running : ExecutionRunning parentOrigin
      (closing.closeExp
        (TermTranslation.elaborate scope
          (.let boundTyping resultWf bodyTyping)))
      (sourceBoundary scope resultWf closing
        (storeArguments environment)) parentBoundary)
    (capability : ActiveResultCapability
      (CurrentOrigin.ofEnvironment
        (.let boundTyping resultWf bodyTyping)
        (.let boundAdmissible boundPolicy bodyAdmissible resultShape)
        valuation environment coherent)
      stack) :
    StateImage
      (LambdaPFC.State.mk sourceStore runtimeRest
        (.let (bound.rename valuation) (body.rename valuation.ext))) :=
  let typing : Fragment.HasType sourceContext (.let bound body) resultType :=
    .let boundTyping resultWf bodyTyping
  let admissible : OperationallyAdmissible typing :=
    .let boundAdmissible boundPolicy bodyAdmissible resultShape
  let origin := CurrentOrigin.ofEnvironment typing admissible valuation
    environment coherent
  let originRunning : ExecutionRunning parentOrigin origin.closedExpression
      origin.resultBoundary parentBoundary := by
    simpa only [origin, CurrentOrigin.closedExpression,
      CurrentOrigin.ofEnvironment, typing] using running
  let originCapability : ActiveResultCapability origin stack := by
    simpa only [origin, typing, admissible] using capability
  { focus := origin.closedExpression
    activeOrigin := parentOrigin
    activeBoundary := parentBoundary
    current := .direct origin rfl
    stack := stack
    running := originRunning
    capability := originCapability
    functionCapability :=
      ActiveFunctionCapability.ofNonCanonicalInput originCapability
        resultShape }

/-- Execute the exact direct `let_push` image transition.  The parent's whole
local history is stored next to the new frame; the active computation resets
to the newly entered bound term with an identity result context. -/
noncomputable def letPush
    {n current : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
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
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : EnvironmentCoherence environment)
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {parentOrigin : Exp []}
    {parentBoundary : ResultBoundary.{0}}
    (stack : ExecutionStack sourceStore runtimeRest parentOrigin
      parentBoundary)
    (running : ExecutionRunning parentOrigin
      (closing.closeExp
        (TermTranslation.elaborate scope
          (.let boundTyping resultWf bodyTyping)))
      (sourceBoundary scope resultWf closing
        (storeArguments environment)) parentBoundary)
    (parentCapability : ActiveResultCapability
      (CurrentOrigin.ofEnvironment
        (.let boundTyping resultWf bodyTyping)
        (.let boundAdmissible boundPolicy bodyAdmissible resultShape)
        valuation environment coherent)
      stack) :
    StateImage
      (LambdaPFC.State.mk sourceStore
        (body.rename valuation.ext :: runtimeRest)
        (bound.rename valuation)) :=
  let frame := CapturedFrame.ofLet boundTyping resultWf bodyTyping
    boundAdmissible boundPolicy bodyAdmissible environment
  let surrounding := running.context
  let surroundingGenerated : GeneratedResultContext surrounding :=
    running.generated
  have parentSteps : Exp.Steps parentOrigin
      (surrounding.plug
        (closing.closeExp
          (TermTranslation.elaborate scope
            (.let boundTyping resultWf bodyTyping)))) :=
    running.reductions
  let saved : SuspendedExecution frame parentOrigin parentBoundary :=
    { resultShape := resultShape
      surrounding := surrounding
      generated := surroundingGenerated
      adapter := running.adapter
      coherent := coherent
      reductions := by
        refine parentSteps.trans ?_
        have decomposition := CapturedFrame.letPush_eq boundTyping resultWf
          bodyTyping boundAdmissible boundPolicy bodyAdmissible environment
        exact (congrArg surrounding.plug decomposition) ▸ .refl }
  let boundOrigin := CurrentOrigin.ofEnvironment boundTyping boundAdmissible
    valuation environment coherent
  let boundRunning : ExecutionRunning (frameBoundClosed frame)
      boundOrigin.closedExpression boundOrigin.resultBoundary
      (OperationalStateImage.CapturedFrame.boundBoundary frame) := by
    have sameOrigin : boundOrigin.closedExpression = frameBoundClosed frame := by
      rfl
    cases sameOrigin
    exact .start (frameBoundClosed frame)
      (OperationalStateImage.CapturedFrame.boundBoundary frame)
  let boundCapability : ActiveResultCapability boundOrigin
      (.cons frame saved stack) := by
    refine .same parentCapability ?_ ?_
    · rfl
    · rfl
  let boundFunctionCapability : ActiveFunctionCapability boundOrigin
      (.cons frame saved stack) boundRunning boundCapability := by
    change ActiveHeadFunctionCapability boundOrigin frame boundRunning
      (.same rfl)
    refine .same (fun runtimeTerm runtime_eq runtimeReady => ?_)
    intro domain codomain type_eq
    let code := boundOrigin.directCode runtimeTerm runtime_eq
    simpa only [boundRunning, ExecutionRunning.start,
      ExpectedResultAdapter.identity_map, boundOrigin, frame,
      CurrentOrigin.directResultInterface, code] using
      LambdaPToFCo.OperationalDirectFunctionBinding.DirectCodeEnvironment.functionBinding
        code runtimeReady coherent type_eq
  { focus := boundOrigin.closedExpression
    activeOrigin := frameBoundClosed frame
    activeBoundary :=
      OperationalStateImage.CapturedFrame.boundBoundary frame
    current := .direct boundOrigin rfl
    stack := .cons frame saved stack
    running := boundRunning
    capability := boundCapability
    functionCapability := boundFunctionCapability }

/-- `let_push` changes only the zipper decomposition of the current target
expression; it performs no target reduction. -/
theorem letPush_target_eq
    {n current : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
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
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (coherent : EnvironmentCoherence environment)
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {parentOrigin : Exp []}
    {parentBoundary : ResultBoundary.{0}}
    (stack : ExecutionStack sourceStore runtimeRest parentOrigin
      parentBoundary)
    (running : ExecutionRunning parentOrigin
      (closing.closeExp
        (TermTranslation.elaborate scope
          (.let boundTyping resultWf bodyTyping)))
      (sourceBoundary scope resultWf closing
        (storeArguments environment)) parentBoundary)
    (capability : ActiveResultCapability
      (CurrentOrigin.ofEnvironment
        (.let boundTyping resultWf bodyTyping)
        (.let boundAdmissible boundPolicy bodyAdmissible resultShape)
        valuation environment coherent)
      stack) :
    (letPush boundTyping resultWf bodyTyping boundAdmissible boundPolicy
      bodyAdmissible resultShape environment coherent stack running
      capability).target =
    (directLet boundTyping resultWf bodyTyping boundAdmissible boundPolicy
      bodyAdmissible resultShape environment coherent stack running
      capability).target := by
  simp only [letPush, directLet, StateImage.target, ExecutionStack.plug,
    ExecutionRunning.start]
  apply congrArg stack.plug
  apply congrArg running.context.plug
  exact (CapturedFrame.letPush_eq boundTyping resultWf bodyTyping
    boundAdmissible boundPolicy bodyAdmissible environment).symm

/-! ### Typed path resolution -/

/-- Direct image immediately before a supported CK path-resolution step. -/
noncomputable def beforePath
    {n current : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (typing : Fragment.HasType sourceContext (.path path) sourceType)
    (admissible : OperationallyAdmissible typing)
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
      (closing.closeExp (TermTranslation.elaborate scope typing))
      (sourceBoundary scope typing.typeWf closing
        (storeArguments environment)) activeBoundary)
    (capability : ActiveResultCapability
      (CurrentOrigin.ofEnvironment typing admissible valuation environment
        coherent)
      stack)
    (functionCapability : ActiveFunctionCapability
      (CurrentOrigin.ofEnvironment typing admissible valuation environment
        coherent) stack running capability) :
    StateImage
      (LambdaPFC.State.mk sourceStore runtimeCont
        (.path (path.rename valuation))) :=
  let origin := CurrentOrigin.ofEnvironment typing admissible valuation
    environment coherent
  { focus := origin.closedExpression
    activeOrigin := activeOrigin
    activeBoundary := activeBoundary
    current := .direct origin rfl
    stack := stack
    running := by
      simpa only [origin, CurrentOrigin.closedExpression,
        CurrentOrigin.ofEnvironment] using running
    capability := by simpa only [origin] using capability
    functionCapability := by
      simpa only [origin, CurrentOrigin.closedExpression,
        CurrentOrigin.ofEnvironment] using functionCapability }

/-- Execute a supported source path step.  The immutable typed source origin
is retained, while its current form changes from valuation closure to a
resolved-path view at the final advertised source type. -/
noncomputable def path
    {n current : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {sourcePath : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (typing : Fragment.HasType sourceContext (.path sourcePath) sourceType)
    (admissible : OperationallyAdmissible typing)
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
      (closing.closeExp (TermTranslation.elaborate scope typing))
      (sourceBoundary scope typing.typeWf closing
        (storeArguments environment)) activeBoundary)
    (capability : ActiveResultCapability
      (CurrentOrigin.ofEnvironment typing admissible valuation environment
        coherent)
      stack)
    (functionCapability : ActiveFunctionCapability
      (CurrentOrigin.ofEnvironment typing admissible valuation environment
        coherent) stack running capability)
    (resultInterface : ResultInterface
      (sourceBoundary scope typing.typeWf closing
        (storeArguments environment)))
    (resultInterface_argument : resultInterface.view.argument =
      (OperationalTypedPathView.build admissible environment
        coherent.pathCoherence).view.argument)
    {location : Fin current}
    (resolution : LambdaPFC.Path.Resolve
      (sourcePath.rename valuation) sourceStore (.loc location)) :
    StateImage
      (LambdaPFC.State.mk sourceStore runtimeCont (.path (.var location))) :=
  let origin := CurrentOrigin.ofEnvironment typing admissible valuation
    environment coherent
  let target := OperationalTypedPathView.build admissible environment
    coherent.pathCoherence
  have targetSteps : Exp.Steps origin.closedExpression
      target.view.argument := by
    simpa only [origin, CurrentOrigin.closedExpression,
      CurrentOrigin.ofEnvironment, target, target.argument_eq] using
      target.normalization.reductions
  let resolved : ResolvedPathView origin sourcePath location :=
    { term_eq := rfl
      typing := typing
      typing_eq := rfl
      admissible := admissible
      resolution := resolution
      location_eq :=
        OperationalApplicationSourceEndpoint.resolvedLocation_eq environment
          typing resolution
      target := target
      interface := resultInterface
      interface_argument := by
        simpa only [target] using resultInterface_argument
      normalizes := targetSteps }
  let originCapability : ActiveResultCapability origin stack := by
    exact capability
  let pathRunning : ExecutionRunning activeOrigin
      resolved.target.view.argument origin.resultBoundary activeBoundary :=
    { context := running.context
      generated := running.generated
      adapter := running.adapter
      reductions := by
        refine running.reductions.trans ?_
        simpa only [resolved] using running.context.steps targetSteps }
  let originFunctionCapability : ActiveFunctionCapability origin stack
      pathRunning originCapability := by
    cases stack with
    | nil => exact PUnit.unit
    | cons frame saved tail =>
        have old : ActiveHeadFunctionCapability origin frame running
            capability.2.2.2 := by
          simpa only [origin, ActiveFunctionCapability] using
            functionCapability
        change ActiveHeadFunctionCapability origin frame pathRunning
          capability.2.2.2
        cases head_eq : capability.2.2.2 with
        | same closure_eq =>
            rw [head_eq] at old
            change ActiveHeadFunctionCapability origin frame running
              (.same closure_eq) at old
            change ActiveHeadFunctionCapability origin frame pathRunning
              (.same closure_eq)
            cases old with
            | same transform =>
                exact .same (by simpa only [pathRunning] using transform)
        | nonCanonical shape =>
            exact .nonCanonical
  { focus := resolved.target.view.argument
    activeOrigin := activeOrigin
    activeBoundary := activeBoundary
    current :=
      ⟨origin, @CurrentFocusImage.resolvedPath current sourceStore origin
        sourcePath location resolved⟩
    stack := stack
    running := pathRunning
    capability := originCapability
    functionCapability := originFunctionCapability }

/-- One native source path transition at the supported typed shape. -/
theorem path_source_step
    {current : Nat}
    {sourceStore : LambdaPFC.Store current}
    {runtimeCont : LambdaPFC.Tm.Cont current}
    {sourcePath : LambdaPFC.Path current}
    {location : Fin current}
    (resolution : LambdaPFC.Path.Resolve sourcePath sourceStore (.loc location))
    (notVariable : Not sourcePath.IsVar) :
    LambdaPFC.State.Step
      (LambdaPFC.State.mk sourceStore runtimeCont (.path sourcePath))
      (LambdaPFC.State.mk sourceStore runtimeCont (.path (.var location))) :=
  .path resolution notVariable

/-- Target normalization corresponding to one source path step. -/
theorem path_target_steps
    {n current : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {sourcePath : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (typing : Fragment.HasType sourceContext (.path sourcePath) sourceType)
    (admissible : OperationallyAdmissible typing)
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
      (closing.closeExp (TermTranslation.elaborate scope typing))
      (sourceBoundary scope typing.typeWf closing
        (storeArguments environment)) activeBoundary)
    (capability : ActiveResultCapability
      (CurrentOrigin.ofEnvironment typing admissible valuation environment
        coherent)
      stack)
    (functionCapability : ActiveFunctionCapability
      (CurrentOrigin.ofEnvironment typing admissible valuation environment
        coherent) stack running capability)
    (resultInterface : ResultInterface
      (sourceBoundary scope typing.typeWf closing
        (storeArguments environment)))
    (resultInterface_argument : resultInterface.view.argument =
      (OperationalTypedPathView.build admissible environment
        coherent.pathCoherence).view.argument)
    {location : Fin current}
    (resolution : LambdaPFC.Path.Resolve
      (sourcePath.rename valuation) sourceStore (.loc location)) :
    Exp.Steps
      (beforePath typing admissible environment coherent stack
        running capability functionCapability).target
      (path typing admissible environment coherent stack running capability
        functionCapability resultInterface resultInterface_argument
        resolution).target := by
  let target := OperationalTypedPathView.build admissible environment
    coherent.pathCoherence
  have targetSteps : Exp.Steps
      (closing.closeExp (TermTranslation.elaborate scope typing))
      target.view.argument := by
    simpa only [target, target.argument_eq] using
      target.normalization.reductions
  have localSteps := running.context.steps targetSteps
  have lifted := stack.plug_steps localSteps
  simpa only [beforePath, path, StateImage.target, target,
    CurrentOrigin.closedExpression, CurrentOrigin.ofEnvironment] using lifted

/-! ### Zipper pop for allocation -/

/-- Closed target compilation retained by an allocation-oriented direct code
environment. -/
noncomputable def directClosed
    (code : DirectCodeEnvironment sourceStore runtimeTerm) : Exp [] :=
  code.closing.closeExp
    (TermTranslation.elaborate code.scope code.original.typing)

namespace DirectCodeEnvironment

/-- Closed readiness follows from readiness of every lexical argument.  This
is the source-value-shaped core behind `closedReady`; only exact packages
inspect an argument. -/
noncomputable def closedReadyOfArguments
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext term sourceType}
    (evidence : ApplicationValueEvidence typing)
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (closing : ClosingEnv sig [])
    (arguments : ClosedArguments n)
    (agreement : ClosedPathAgreement scope closing arguments)
    (ready : forall index, Exp.IsValue (arguments index)) :
    evidence.ClosedReady scope closing := by
  cases evidence with
  | function _ => trivial
  | @package first _ _ _ _ _ =>
      change Exp.IsValue
        (closing.closeExp
          (translatePath scope
            (Fragment.PathTy.var
              (Γ := sourceContext) (x := first))).expression)
      rw [agreement (Fragment.PathTy.var
        (Γ := sourceContext) (x := first))]
      exact ready first

/-- Readiness of the native closed source-value view follows syntactically
from recursive environment coherence.  Functions need no extra closed
payload.  An exact package retains a lexical `first` path, whose closed
translation is the ready behavioral argument of the corresponding store
slot. -/
noncomputable def closedReady
    (code : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (coherent : EnvironmentCoherence code.environment) :
    (code.valueEvidence runtimeReady).ClosedReady code.scope code.closing :=
  OperationalDirectFunctionBinding.DirectCodeEnvironment.acceptedClosedReady
    code runtimeReady coherent

/-- Canonical closed value view generated from the direct source value and
its recursively coherent lexical environment. -/
noncomputable def closedView
    (code : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (coherent : EnvironmentCoherence code.environment) :
    OperationalPackageBehavior.ClosedView code.scope code.original.typing
      code.closing :=
  OperationalDirectFunctionBinding.DirectCodeEnvironment.acceptedClosedView
    code runtimeReady coherent

/-- A direct native source value supplies the accepted input interface
consumed by the current computation's expected-result adapter. -/
noncomputable def resultInterface
    (code : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (coherent : EnvironmentCoherence code.environment) :
    ResultInterface
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary code) where
  view :=
    (closedView code runtimeReady coherent).view
  accepted :=
    OperationalDirectFunctionBinding.DirectCodeEnvironment.sourceAcceptance
      code runtimeReady coherent

/-- The direct compilation normalizes to the argument advertised by its
canonical accepted result interface. -/
theorem resultInterface_steps
    (code : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (coherent : EnvironmentCoherence code.environment) :
    Exp.Steps (directClosed code)
      (resultInterface code runtimeReady coherent).view.argument := by
  exact (closedView code runtimeReady coherent).normalizes

end DirectCodeEnvironment

/-- Canonical current-code image of a direct code environment. -/
noncomputable def currentOfDirect
    (code : DirectCodeEnvironment sourceStore runtimeTerm)
    (coherent : EnvironmentCoherence code.environment) :
    CurrentCodeEnvironment sourceStore runtimeTerm (directClosed code) where
  origin := CurrentOrigin.ofDirect code coherent
  form := .direct code.runtime_eq

/-! ## Source provenance of an allocating result -/

private theorem memberCell_of_closure_eq
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeValue : LambdaPFC.Tm current}
    {left right : SourceClosure current}
    (evidence : ApplicationValueEvidence left.original.typing)
    (runtimeReady : runtimeValue.IsValue)
    (runtime_eq : runtimeValue =
      left.original.term.rename left.valuation)
    (closure_eq : left = right) :
    MemberCell right.original.resultType
      (.val sourceStore runtimeValue runtimeReady)
      right.valuation.weaken 0 := by
  cases closure_eq
  exact
    OperationalAdmissibility.ApplicationValueEvidence.allocateMemberCell
      evidence runtimeReady runtime_eq

private theorem functionCell_of_closure_eq
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeValue : LambdaPFC.Tm current}
    {left right : SourceClosure current}
    (evidence : ApplicationValueEvidence left.original.typing)
    (runtimeReady : runtimeValue.IsValue)
    (runtime_eq : runtimeValue =
      left.original.term.rename left.valuation)
    (closure_eq : left = right) :
    FunctionCell right.original.resultType
      (.val sourceStore runtimeValue runtimeReady)
      right.valuation.weaken 0 := by
  cases closure_eq
  exact
    OperationalAdmissibility.ApplicationValueEvidence.allocateFunctionCell
      evidence runtimeReady runtime_eq

/-- Source-only evidence that the native value has every physical head
required by a captured frame's hole type.

The `same` case identifies the native typed closure with the frame's own
lexical bound closure.  The `nonCanonical` case records that the
advertised hole type demands neither a member-package nor an abstraction
head.  No target behavior or store realization appears in this predicate. -/
inductive AllocationResultCapability
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    (frame : CapturedFrame sourceStore runtimeBody)
    (native : DirectCodeEnvironment sourceStore runtimeValue) : Type where
  | same
      (closure_eq : SourceClosure.ofDirect native =
        SourceClosure.ofBound frame) :
      AllocationResultCapability frame native
  | nonCanonical
      (shape : NonCanonicalResultShape frame.image.holeType) :
      AllocationResultCapability frame native

namespace AllocationResultCapability

/-- A source allocation capability discharges the exact-member physical
head required by the captured lexical hole. -/
theorem memberCell
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    {frame : CapturedFrame sourceStore runtimeBody}
    {native : DirectCodeEnvironment sourceStore runtimeValue}
    (capability : AllocationResultCapability frame native)
    (runtimeReady : runtimeValue.IsValue) :
    MemberCell frame.image.holeType
      (.val sourceStore runtimeValue runtimeReady)
      frame.image.valuation.weaken 0 := by
  cases capability with
  | same closure_eq =>
      exact memberCell_of_closure_eq (sourceStore := sourceStore)
        (native.valueEvidence runtimeReady) runtimeReady native.runtime_eq
        closure_eq
  | nonCanonical shape =>
      exact MemberCell.ofNotMember shape.notMember

/-- A source allocation capability likewise discharges the abstraction-head
obligation.  Noncanonical result types make it vacuous. -/
theorem functionCell
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    {frame : CapturedFrame sourceStore runtimeBody}
    {native : DirectCodeEnvironment sourceStore runtimeValue}
    (capability : AllocationResultCapability frame native)
    (runtimeReady : runtimeValue.IsValue) :
    FunctionCell frame.image.holeType
      (.val sourceStore runtimeValue runtimeReady)
      frame.image.valuation.weaken 0 := by
  cases capability with
  | same closure_eq =>
      exact functionCell_of_closure_eq (sourceStore := sourceStore)
        (native.valueEvidence runtimeReady) runtimeReady native.runtime_eq
        closure_eq
  | nonCanonical shape =>
      intro domain codomain typeEq
      exact (shape.notArrow
        { domain := domain
          codomain := codomain.weaken
          equality := typeEq }).elim

end AllocationResultCapability

namespace ActiveResultCapability

/-- The active zipper head itself supplies the physical-head capability
needed by allocation. -/
noncomputable def allocationResult
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {runtimeValue : LambdaPFC.Tm current}
    {frame : CapturedFrame sourceStore runtimeBody}
    {saved : SuspendedExecution frame parentOrigin parentBoundary}
    {tail : ExecutionStack sourceStore runtimeRest parentOrigin parentBoundary}
    {native : DirectCodeEnvironment sourceStore runtimeValue}
    {nativeCoherent : EnvironmentCoherence native.environment}
    (capability : ActiveResultCapability
      (CurrentOrigin.ofDirect native nativeCoherent) (.cons frame saved tail)) :
    AllocationResultCapability frame native := by
  cases capability.2.2.2 with
  | same closure_eq => exact .same closure_eq
  | nonCanonical shape => exact .nonCanonical shape

end ActiveResultCapability

/-- Complete local evidence for one allocating CK state.

`suffix` starts at the target expression represented by the *current* state,
whereas `slot.normalizes` starts at the saved frame's original bound
compilation and is retained by the extended lexical environment.  Keeping
both directions explicit prevents a source step from replaying old target
reductions. -/
structure AllocationExecution
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    (frame : CapturedFrame sourceStore runtimeBody)
    (native : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (running : ExecutionRunning (frameBoundClosed frame)
      (directClosed native)
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary native)
      (OperationalStateImage.CapturedFrame.boundBoundary frame)) : Type where
  nativeCoherent : EnvironmentCoherence native.environment
  slot : AllocationSlot frame native runtimeReady
  suffix : Exp.Steps
    (running.context.plug (directClosed native)) slot.behavior.argument
  pathLaws : BehaviorPathCoherence frame.scope frame.boundTyping.typeWf
    frame.closing slot.behavior (storeArguments frame.environment)
  functionBinding :
    {domain codomain : LambdaPFC.Ty frame.image.originalArity} ->
    frame.image.holeType = .Fun domain codomain.weaken ->
    Nonempty
      (OperationalFunctionEnvironmentCoherence.FunctionBindingWitness
        frame.scope frame.closing slot.behavior domain sourceStore
        runtimeValue native.environment)
  resumeAdapter : ExpectedResultAdapter
    (.ofResume
      (slot.behavior.resume
        ((translateType frame.scope frame.image.resultWf).subst
          frame.closing.substitution)))
    (OperationalStateImage.DirectCodeEnvironment.resultBoundary
      (frame.afterAllocationCode native runtimeReady slot))
    (OperationalStateImage.CapturedFrame.resultBoundary frame)

namespace AllocationExecution

/-- Construct allocation evidence from a genuine suffix normalization. -/
noncomputable def ofSuffix
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    {frame : CapturedFrame sourceStore runtimeBody}
    {native : DirectCodeEnvironment sourceStore runtimeValue}
    {runtimeReady : runtimeValue.IsValue}
    {running : ExecutionRunning (frameBoundClosed frame)
      (directClosed native)
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary native)
      (OperationalStateImage.CapturedFrame.boundBoundary frame)}
    (behavior : EliminationView
      ((TermTranslation.compileBinder frame.scope
        frame.boundTyping.typeWf).plan.subst frame.closing.substitution))
    (suffix : Exp.Steps
      (running.context.plug (directClosed native)) behavior.argument)
    (nativeCoherent : EnvironmentCoherence native.environment)
    (nativeReady : (native.valueEvidence runtimeReady).ClosedReady
      native.scope native.closing)
    (memberCell : MemberCell frame.image.holeType
      (.val sourceStore runtimeValue runtimeReady)
      frame.image.valuation.weaken 0)
    (functionCell : FunctionCell frame.image.holeType
      (.val sourceStore runtimeValue runtimeReady)
      frame.image.valuation.weaken 0)
    (pathLaws : BehaviorPathCoherence frame.scope
      frame.boundTyping.typeWf frame.closing behavior
      (storeArguments frame.environment))
    (functionBinding :
      {domain codomain : LambdaPFC.Ty frame.image.originalArity} ->
      frame.image.holeType = .Fun domain codomain.weaken ->
      Nonempty
        (OperationalFunctionEnvironmentCoherence.FunctionBindingWitness
          frame.scope frame.closing behavior domain sourceStore runtimeValue
          native.environment))
    (resumeAdapter : ExpectedResultAdapter
      (.ofResume
        (behavior.resume
          ((translateType frame.scope frame.image.resultWf).subst
            frame.closing.substitution)))
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary
        (frame.afterAllocationCode native runtimeReady
        { behavior := behavior
          nativeReady := nativeReady
          normalizes := running.reductions.trans suffix
          memberCell := memberCell
          functionCell := functionCell }))
      (OperationalStateImage.CapturedFrame.resultBoundary frame)) :
    AllocationExecution frame native runtimeReady running where
  nativeCoherent := nativeCoherent
  slot :=
    { behavior := behavior
      nativeReady := nativeReady
      normalizes := running.reductions.trans suffix
      memberCell := memberCell
      functionCell := functionCell }
  suffix := suffix
  pathLaws := pathLaws
  functionBinding := functionBinding
  resumeAdapter := resumeAdapter

/-- Derive all target-interface evidence for allocation from the active
expected-result adapter.  The only remaining premises are source/store head
facts: recursive coherence of the native origin and the member/function
capabilities demanded by the captured hole type. -/
noncomputable def ofImage
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    {frame : CapturedFrame sourceStore runtimeBody}
    {native : DirectCodeEnvironment sourceStore runtimeValue}
    {runtimeReady : runtimeValue.IsValue}
    {running : ExecutionRunning (frameBoundClosed frame)
      (directClosed native)
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary native)
      (OperationalStateImage.CapturedFrame.boundBoundary frame)}
    {parentOrigin : Exp []} {parentBoundary : ResultBoundary.{0}}
    (saved : SuspendedExecution frame parentOrigin parentBoundary)
    (nativeCoherent : EnvironmentCoherence native.environment)
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {tail : ExecutionStack sourceStore runtimeRest parentOrigin parentBoundary}
    (capability : ActiveResultCapability
      (CurrentOrigin.ofDirect native nativeCoherent) (.cons frame saved tail))
    (functionCapability : ActiveFunctionCapability
      (CurrentOrigin.ofDirect native nativeCoherent) (.cons frame saved tail)
      running capability) :
    AllocationExecution frame native runtimeReady running :=
  let input :=
    LambdaPToFCo.OperationalStateImage.StateImage.DirectCodeEnvironment.resultInterface native
      runtimeReady nativeCoherent
  let output := running.adapter.map input
  let suffix : Exp.Steps
      (running.context.plug (directClosed native)) output.view.argument :=
    (running.context.steps
      (LambdaPToFCo.OperationalStateImage.StateImage.DirectCodeEnvironment.resultInterface_steps
        native runtimeReady nativeCoherent)).trans
      (running.adapter.steps input)
  let nativeReady :=
    LambdaPToFCo.OperationalStateImage.StateImage.DirectCodeEnvironment.closedReady native
      runtimeReady nativeCoherent
  let allocationCapability :=
    ActiveResultCapability.allocationResult capability
  let functionBinding :
      {domain codomain : LambdaPFC.Ty frame.image.originalArity} ->
      frame.image.holeType = .Fun domain codomain.weaken ->
      Nonempty
        (OperationalFunctionEnvironmentCoherence.FunctionBindingWitness
          frame.scope frame.closing output.view domain sourceStore runtimeValue
          native.environment) := by
    intro domain codomain type_eq
    rcases capability with
      ⟨parentSourceOrigin, parent, parent_eq, head⟩
    cases head with
    | same closure_eq =>
        cases functionCapability with
        | same transform =>
            simpa only [CurrentOrigin.ofDirect, CurrentOrigin.directCode,
              CurrentOrigin.directResultInterface, input, output] using
              transform runtimeValue native.runtime_eq runtimeReady type_eq
    | nonCanonical shape =>
        exact (shape.notArrow
          { domain := domain
            codomain := codomain.weaken
            equality := type_eq }).elim
  let slot : AllocationSlot frame native runtimeReady :=
    { behavior := output.view
      nativeReady := nativeReady
      normalizes := running.reductions.trans suffix
      memberCell := allocationCapability.memberCell runtimeReady
      functionCell := allocationCapability.functionCell runtimeReady }
  let resumeGenerated : GeneratedResultContext
      (.ofResume
        (slot.behavior.resume
          ((translateType frame.scope frame.image.resultWf).subst
            frame.closing.substitution))) :=
    .ofResume
      (slot.behavior.resume
        ((translateType frame.scope frame.image.resultWf).subst
          frame.closing.substitution))
  { nativeCoherent := nativeCoherent
    slot := slot
    suffix := suffix
    pathLaws := output.accepted.paths
    functionBinding := by
      intro domain codomain type_eq
      simpa only [slot] using functionBinding type_eq
    resumeAdapter :=
      ofGeneratedOrdinary resumeGenerated
        (OperationalStateImage.DirectCodeEnvironment.resultBoundary
          (frame.afterAllocationCode native runtimeReady slot))
        frame.scope frame.image.resultWf saved.resultShape frame.closing
        (storeArguments frame.environment) }

/-- The target suffix corresponding to allocation at the active frame. -/
theorem frame_steps
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    {frame : CapturedFrame sourceStore runtimeBody}
    {native : DirectCodeEnvironment sourceStore runtimeValue}
    {runtimeReady : runtimeValue.IsValue}
    {running : ExecutionRunning (frameBoundClosed frame)
      (directClosed native)
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary native)
      (OperationalStateImage.CapturedFrame.boundBoundary frame)}
    (execution : AllocationExecution frame native runtimeReady running) :
    Exp.Steps
      (frame.compilation.closeFrame.fill
        (running.context.plug (directClosed native)))
      ((execution.slot.behavior.resume
          ((translateType frame.scope frame.image.resultWf).subst
            frame.closing.substitution)).plug
        ((frame.afterAllocationCode native runtimeReady execution.slot).closing.closeExp
          (TermTranslation.elaborate
            (frame.afterAllocationCode native runtimeReady execution.slot).scope
            frame.image.bodyTyping))) := by
  refine (frame_fill_steps frame.compilation.closeFrame execution.suffix).trans ?_
  exact OperationalFrameElimination.CapturedFrame.allocation_suffix_steps
    frame native runtimeReady execution.slot

/-- Recursive environment coherence extends through allocation while
retaining the independently coherent native origin of the stored value. -/
noncomputable def afterCoherent
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    {frame : CapturedFrame sourceStore runtimeBody}
    {native : DirectCodeEnvironment sourceStore runtimeValue}
    {runtimeReady : runtimeValue.IsValue}
    {running : ExecutionRunning (frameBoundClosed frame)
      (directClosed native)
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary native)
      (OperationalStateImage.CapturedFrame.boundBoundary frame)}
    (saved : SuspendedExecution frame parentOrigin parentBoundary)
    (execution : AllocationExecution frame native runtimeReady running) :
    EnvironmentCoherence
      (frame.afterAllocationEnvironment native runtimeReady execution.slot) :=
  saved.coherent.extendGenerated frame.boundTyping native.original
    native.valuation native.admissible (native.valueEvidence runtimeReady)
    native.environment execution.nativeCoherent execution.slot.nativeReady
    runtimeReady native.runtime_eq execution.slot.memberCell
    execution.slot.functionCell execution.slot.behavior
    execution.slot.normalizes execution.pathLaws execution.functionBinding

end AllocationExecution

/-- Restore the parent computation after eliminating an allocated value
through the popped frame. -/
noncomputable def restoreAfterAllocation
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    {frame : CapturedFrame sourceStore runtimeBody}
    {parentOrigin : Exp []}
    {parentBoundary : ResultBoundary.{0}}
    (saved : SuspendedExecution frame parentOrigin parentBoundary)
    (native : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (slot : AllocationSlot frame native runtimeReady)
    (resumeAdapter : ExpectedResultAdapter
      (.ofResume
        (slot.behavior.resume
          ((translateType frame.scope frame.image.resultWf).subst
            frame.closing.substitution)))
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary
        (frame.afterAllocationCode native runtimeReady slot))
      (OperationalStateImage.CapturedFrame.resultBoundary frame)) :
    ExecutionRunning parentOrigin
      (directClosed (frame.afterAllocationCode native runtimeReady slot))
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary
        (frame.afterAllocationCode native runtimeReady slot))
      parentBoundary where
  context := saved.surrounding.compose
    (.ofResume
      (slot.behavior.resume
        ((translateType frame.scope frame.image.resultWf).subst
          frame.closing.substitution)))
  generated := saved.generated.compose
    (.ofResume
      (slot.behavior.resume
        ((translateType frame.scope frame.image.resultWf).subst
          frame.closing.substitution)))
  adapter := saved.adapter.compose resumeAdapter
  reductions := saved.reductions.trans
    (saved.surrounding.steps
      (CapturedFrame.allocation_steps frame native runtimeReady slot))

/-- Image of the allocating state immediately before the CK transition. -/
noncomputable def beforeAllocation
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {runtimeValue : LambdaPFC.Tm current}
    (frame : CapturedFrame sourceStore runtimeBody)
    {parentBoundary : ResultBoundary.{0}}
    (saved : SuspendedExecution frame parentOrigin parentBoundary)
    (tail : ExecutionStack sourceStore runtimeRest parentOrigin
      parentBoundary)
    (native : DirectCodeEnvironment sourceStore runtimeValue)
    (nativeCoherent : EnvironmentCoherence native.environment)
    (running : ExecutionRunning (frameBoundClosed frame)
      (directClosed native)
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary native)
      (OperationalStateImage.CapturedFrame.boundBoundary frame))
    (capability : ActiveResultCapability
      (CurrentOrigin.ofDirect native nativeCoherent) (.cons frame saved tail))
    (functionCapability : ActiveFunctionCapability
      (CurrentOrigin.ofDirect native nativeCoherent) (.cons frame saved tail)
      running capability) :
    StateImage
      (LambdaPFC.State.mk sourceStore (runtimeBody :: runtimeRest)
        runtimeValue) :=
  { focus := directClosed native
    activeOrigin := frameBoundClosed frame
    activeBoundary :=
      OperationalStateImage.CapturedFrame.boundBoundary frame
    current := currentOfDirect native nativeCoherent
    stack := .cons frame saved tail
    running := running
    capability := capability
    functionCapability := functionCapability }

/-- Pop the active frame after physical allocation, weaken every older saved
source frame, and restore the parent computation history. -/
noncomputable def allocate
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {runtimeValue : LambdaPFC.Tm current}
    (frame : CapturedFrame sourceStore runtimeBody)
    {parentBoundary : ResultBoundary.{0}}
    (saved : SuspendedExecution frame parentOrigin parentBoundary)
    (tail : ExecutionStack sourceStore runtimeRest parentOrigin
      parentBoundary)
    (native : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (running : ExecutionRunning (frameBoundClosed frame)
      (directClosed native)
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary native)
      (OperationalStateImage.CapturedFrame.boundBoundary frame))
    (execution : AllocationExecution frame native runtimeReady running)
    (capability : ActiveResultCapability
      (CurrentOrigin.ofDirect native execution.nativeCoherent)
      (.cons frame saved tail)) :
    StateImage
      (LambdaPFC.State.mk (.val sourceStore runtimeValue runtimeReady)
        runtimeRest.weaken runtimeBody) :=
  let code := frame.afterAllocationCode native runtimeReady execution.slot
  let coherent := execution.afterCoherent saved
  let restoredRunning := restoreAfterAllocation saved native runtimeReady
    execution.slot execution.resumeAdapter
  let restoredCapability := capability.popNative runtimeValue runtimeReady
    (CurrentOrigin.ofDirect code coherent) saved.resultShape
  { focus := directClosed code
    activeOrigin := parentOrigin
    activeBoundary := parentBoundary
    current := currentOfDirect code coherent
    stack := tail.nativeWeaken runtimeValue runtimeReady
    running := restoredRunning
    capability := restoredCapability
    functionCapability :=
      ActiveFunctionCapability.ofNonCanonicalInput restoredCapability
        (LambdaPToFCo.OperationalStateImage.NonCanonicalResultShape.weaken
          saved.resultShape) }

/-- One native allocation transition at the exact zipper shape. -/
theorem allocation_source_step
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {runtimeValue : LambdaPFC.Tm current}
    (runtimeReady : runtimeValue.IsValue) :
    LambdaPFC.State.Step
      (LambdaPFC.State.mk sourceStore (runtimeBody :: runtimeRest)
        runtimeValue)
      (LambdaPFC.State.mk (.val sourceStore runtimeValue runtimeReady)
        runtimeRest.weaken runtimeBody) :=
  .allocate runtimeReady

/-- Target suffix corresponding to the single source allocation step.  The
old local computation prefix is not replayed. -/
theorem allocate_target_steps
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {runtimeValue : LambdaPFC.Tm current}
    (frame : CapturedFrame sourceStore runtimeBody)
    {parentBoundary : ResultBoundary.{0}}
    (saved : SuspendedExecution frame parentOrigin parentBoundary)
    (tail : ExecutionStack sourceStore runtimeRest parentOrigin
      parentBoundary)
    (native : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (running : ExecutionRunning (frameBoundClosed frame)
      (directClosed native)
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary native)
      (OperationalStateImage.CapturedFrame.boundBoundary frame))
    (execution : AllocationExecution frame native runtimeReady running)
    (capability : ActiveResultCapability
      (CurrentOrigin.ofDirect native execution.nativeCoherent)
      (.cons frame saved tail))
    (functionCapability : ActiveFunctionCapability
      (CurrentOrigin.ofDirect native execution.nativeCoherent)
      (.cons frame saved tail) running capability) :
    Exp.Steps
      (beforeAllocation frame saved tail native execution.nativeCoherent
        running capability functionCapability).target
      (allocate frame saved tail native runtimeReady running execution
        capability).target := by
  have localSteps := saved.surrounding.steps execution.frame_steps
  have lifted := tail.plug_steps localSteps
  simpa only [beforeAllocation, allocate, StateImage.target,
    ExecutionStack.plug, restoreAfterAllocation,
    ResultContext.compose_plug, ResultContext.ofResume_plug,
    ExecutionStack.plug_nativeWeaken] using lifted

/-! ### Zipper pop for an existing-location return -/

/-- Complete local evidence for returning a resolved location through the
active source frame.  As in allocation, `suffix` begins at the target
endpoint represented by the current source state. -/
structure ReturnExecution
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody)
    (origin : CurrentOrigin sourceStore)
    (sourcePath : LambdaPFC.Path origin.original.arity)
    (location : Fin current)
    (resolved : ResolvedPathView origin sourcePath location)
    (running : ExecutionRunning (frameBoundClosed frame)
      resolved.target.view.argument origin.resultBoundary
      (OperationalStateImage.CapturedFrame.boundBoundary frame)) : Type where
  boundShape : NonCanonicalResultShape frame.image.holeType
  slot : ReturnSlot frame location
  nativeCoherent : EnvironmentCoherence slot.nativeEnvironment
  suffix : Exp.Steps
    (running.context.plug resolved.target.view.argument)
    slot.behavior.argument
  pathLaws : BehaviorPathCoherence frame.scope frame.image.holeWf
    frame.closing slot.behavior (storeArguments frame.environment)
  resumeAdapter : ExpectedResultAdapter
    (.ofResume
      (slot.behavior.resume
        ((translateType frame.scope frame.image.resultWf).subst
          frame.closing.substitution)))
    (OperationalStateImage.DirectCodeEnvironment.resultBoundary
      (frame.afterReturnCode location slot))
    (OperationalStateImage.CapturedFrame.resultBoundary frame)

namespace ReturnExecution

/-- Generated application administration around a ready resolved path
supplies the return suffix once its endpoint is identified with the frame's
adapted binder behavior. -/
noncomputable def ofGenerated
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {frame : CapturedFrame sourceStore runtimeBody}
    {origin : CurrentOrigin sourceStore}
    {sourcePath : LambdaPFC.Path origin.original.arity}
    {location : Fin current}
    {resolved : ResolvedPathView origin sourcePath location}
    {running : ExecutionRunning (frameBoundClosed frame)
      resolved.target.view.argument origin.resultBoundary
      (OperationalStateImage.CapturedFrame.boundBoundary frame)}
    (boundShape : NonCanonicalResultShape frame.image.holeType)
    (slot : ReturnSlot frame location)
    (nativeCoherent : EnvironmentCoherence slot.nativeEnvironment)
    (endpoint_eq :
      (running.generated.normalize resolved.target.view_ready).result =
        slot.behavior.argument)
    (pathLaws : BehaviorPathCoherence frame.scope frame.image.holeWf
      frame.closing slot.behavior (storeArguments frame.environment))
    (resumeAdapter : ExpectedResultAdapter
      (.ofResume
        (slot.behavior.resume
          ((translateType frame.scope frame.image.resultWf).subst
            frame.closing.substitution)))
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary
        (frame.afterReturnCode location slot))
      (OperationalStateImage.CapturedFrame.resultBoundary frame)) :
    ReturnExecution frame origin sourcePath location resolved running where
  boundShape := boundShape
  slot := slot
  nativeCoherent := nativeCoherent
  suffix := by
    simpa only [endpoint_eq] using
      (running.generated.normalize resolved.target.view_ready).reductions
  pathLaws := pathLaws
  resumeAdapter := resumeAdapter

/-- Derive the adapted return behavior, physical binding, native coherence,
path laws, and transparent resume adapter from the resolved-path image and
the active expected-result adapter.  Canonical head capabilities at the
captured hole type remain explicit source/store provenance. -/
noncomputable def ofImage
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {frame : CapturedFrame sourceStore runtimeBody}
    {origin : CurrentOrigin sourceStore}
    {sourcePath : LambdaPFC.Path origin.original.arity}
    {location : Fin current}
    {resolved : ResolvedPathView origin sourcePath location}
    {running : ExecutionRunning (frameBoundClosed frame)
      resolved.target.view.argument origin.resultBoundary
      (OperationalStateImage.CapturedFrame.boundBoundary frame)}
    {parentOrigin : Exp []} {parentBoundary : ResultBoundary.{0}}
    (saved : SuspendedExecution frame parentOrigin parentBoundary)
    (boundShape : NonCanonicalResultShape frame.image.holeType)
    (memberCell : MemberCell frame.image.holeType sourceStore
      frame.image.valuation location)
    (functionCell : FunctionCell frame.image.holeType sourceStore
      frame.image.valuation location) :
    ReturnExecution frame origin sourcePath location resolved running := by
  let input := resolved.resultInterface
  let mapped : ResultInterface
      (OperationalStateImage.CapturedFrame.boundBoundary frame) :=
    running.adapter.map input
  let mappedHole := ResultInterface.castSourceWf frame.scope
    frame.holeWf_eq frame.closing (storeArguments frame.environment) mapped
  let behavior := mappedHole.view
  have suffix : Exp.Steps
      (running.context.plug resolved.target.view.argument)
      behavior.argument := by
    simpa only [input, mapped, ResolvedPathView.resultInterface_argument,
      behavior, mappedHole, ResultInterface.castSourceWf_argument] using
      running.adapter.steps input
  let located := resolved.located
  have binds : LambdaPFC.Store.Binds sourceStore location
      located.runtimeValue := by
    exact Eq.mp
      (congrArg
        (fun index => LambdaPFC.Store.Binds sourceStore index
          located.runtimeValue)
        resolved.location_eq.symm)
      located.binds
  let slot : ReturnSlot frame location :=
    { runtimeValue := located.runtimeValue
      binds := binds
      compiled := located.compiled
      nativeTargetSig := located.nativeTargetSig
      nativeTargetContext := located.nativeTargetContext
      nativeScope := located.nativeScope
      nativeClosing := located.nativeClosing
      nativeEnvironment := located.nativeEnvironment
      behavior := behavior
      memberCell := memberCell
      functionCell := functionCell }
  let nativeCoherent : EnvironmentCoherence located.nativeEnvironment :=
    origin.coherent.lookupNative (typedPathReferent resolved.typing)
  let resume := behavior.resume
    ((translateType frame.scope frame.image.resultWf).subst
      frame.closing.substitution)
  let resumeAdapter : ExpectedResultAdapter
      (.ofResume resume)
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary
        (frame.afterReturnCode location slot))
      (OperationalStateImage.CapturedFrame.resultBoundary frame) :=
    ofGeneratedOrdinary (GeneratedResultContext.ofResume resume)
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary
        (frame.afterReturnCode location slot))
      frame.scope frame.image.resultWf saved.resultShape frame.closing
      (storeArguments frame.environment)
  exact
    { boundShape := boundShape
      slot := slot
      nativeCoherent := nativeCoherent
      suffix := suffix
      pathLaws := mappedHole.accepted.paths
      resumeAdapter := resumeAdapter }

/-- Suffix-only target execution at the popped return frame. -/
theorem frame_steps
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {frame : CapturedFrame sourceStore runtimeBody}
    {origin : CurrentOrigin sourceStore}
    {sourcePath : LambdaPFC.Path origin.original.arity}
    {location : Fin current}
    {resolved : ResolvedPathView origin sourcePath location}
    {running : ExecutionRunning (frameBoundClosed frame)
      resolved.target.view.argument origin.resultBoundary
      (OperationalStateImage.CapturedFrame.boundBoundary frame)}
    (execution : ReturnExecution frame origin sourcePath location resolved
      running) :
    Exp.Steps
      (frame.compilation.closeFrame.fill
        (running.context.plug resolved.target.view.argument))
      ((execution.slot.behavior.resume
          ((translateType frame.scope frame.image.resultWf).subst
            frame.closing.substitution)).plug
        ((frame.afterReturnCode location execution.slot).closing.closeExp
          (TermTranslation.elaborate
            (frame.afterReturnCode location execution.slot).scope
            frame.image.bodyTyping))) := by
  refine (frame_fill_steps frame.compilation.closeFrame execution.suffix).trans ?_
  exact OperationalFrameElimination.CapturedFrame.return_suffix_steps frame
    location execution.slot

/-- The returned lexical interface extends recursive environment coherence,
including coherence of the physical binding's retained native origin. -/
noncomputable def afterCoherent
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {frame : CapturedFrame sourceStore runtimeBody}
    {origin : CurrentOrigin sourceStore}
    {sourcePath : LambdaPFC.Path origin.original.arity}
    {location : Fin current}
    {resolved : ResolvedPathView origin sourcePath location}
    {running : ExecutionRunning (frameBoundClosed frame)
      resolved.target.view.argument origin.resultBoundary
      (OperationalStateImage.CapturedFrame.boundBoundary frame)}
    (saved : SuspendedExecution frame parentOrigin parentBoundary)
    (execution : ReturnExecution frame origin sourcePath location resolved
      running) :
    EnvironmentCoherence
      (frame.afterReturnEnvironment location execution.slot) :=
  saved.coherent.bindLocationGenerated frame.image.holeWf
    execution.boundShape location
    execution.slot.binds execution.slot.compiled
    execution.slot.nativeEnvironment execution.nativeCoherent
    execution.slot.memberCell execution.slot.functionCell
    execution.slot.behavior execution.pathLaws

end ReturnExecution

/-- Restore the parent computation after returning an existing source
location through the popped frame. -/
noncomputable def restoreAfterReturn
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {frame : CapturedFrame sourceStore runtimeBody}
    {parentOrigin : Exp []}
    {parentBoundary : ResultBoundary.{0}}
    (saved : SuspendedExecution frame parentOrigin parentBoundary)
    (location : Fin current)
    (slot : ReturnSlot frame location)
    (boundToBehavior : Exp.Steps (frameBoundClosed frame)
      slot.behavior.argument)
    (resumeAdapter : ExpectedResultAdapter
      (.ofResume
        (slot.behavior.resume
          ((translateType frame.scope frame.image.resultWf).subst
            frame.closing.substitution)))
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary
        (frame.afterReturnCode location slot))
      (OperationalStateImage.CapturedFrame.resultBoundary frame)) :
    ExecutionRunning parentOrigin
      (directClosed (frame.afterReturnCode location slot))
      (OperationalStateImage.DirectCodeEnvironment.resultBoundary
        (frame.afterReturnCode location slot))
      parentBoundary where
  context := saved.surrounding.compose
    (.ofResume
      (slot.behavior.resume
        ((translateType frame.scope frame.image.resultWf).subst
          frame.closing.substitution)))
  generated := saved.generated.compose
    (.ofResume
      (slot.behavior.resume
        ((translateType frame.scope frame.image.resultWf).subst
          frame.closing.substitution)))
  adapter := saved.adapter.compose resumeAdapter
  reductions := saved.reductions.trans
    (saved.surrounding.steps
      ((frame_fill_steps frame.compilation.closeFrame boundToBehavior).trans
        (OperationalFrameElimination.CapturedFrame.return_suffix_steps frame
          location slot)))

/-- Image of the resolved-location state immediately before return. -/
noncomputable def beforeReturn
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    (frame : CapturedFrame sourceStore runtimeBody)
    {parentBoundary : ResultBoundary.{0}}
    (saved : SuspendedExecution frame parentOrigin parentBoundary)
    (tail : ExecutionStack sourceStore runtimeRest parentOrigin
      parentBoundary)
    (origin : CurrentOrigin sourceStore)
    (sourcePath : LambdaPFC.Path origin.original.arity)
    (location : Fin current)
    (resolved : ResolvedPathView origin sourcePath location)
    (running : ExecutionRunning (frameBoundClosed frame)
      resolved.target.view.argument origin.resultBoundary
      (OperationalStateImage.CapturedFrame.boundBoundary frame))
    (capability : ActiveResultCapability origin (.cons frame saved tail))
    (functionCapability : ActiveFunctionCapability origin
      (.cons frame saved tail) running capability) :
    StateImage
      (LambdaPFC.State.mk sourceStore (runtimeBody :: runtimeRest)
        (.path (.var location))) where
  focus := resolved.target.view.argument
  activeOrigin := frameBoundClosed frame
  activeBoundary := OperationalStateImage.CapturedFrame.boundBoundary frame
  current :=
    ⟨origin, @CurrentFocusImage.resolvedPath current sourceStore origin
      sourcePath location resolved⟩
  stack := .cons frame saved tail
  running := running
  capability := capability
  functionCapability := functionCapability

/-- Pop the active frame after an existing-location return. -/
noncomputable def afterReturn
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    (frame : CapturedFrame sourceStore runtimeBody)
    {parentBoundary : ResultBoundary.{0}}
    (saved : SuspendedExecution frame parentOrigin parentBoundary)
    (tail : ExecutionStack sourceStore runtimeRest parentOrigin
      parentBoundary)
    (origin : CurrentOrigin sourceStore)
    (sourcePath : LambdaPFC.Path origin.original.arity)
    (location : Fin current)
    (resolved : ResolvedPathView origin sourcePath location)
    (running : ExecutionRunning (frameBoundClosed frame)
      resolved.target.view.argument origin.resultBoundary
      (OperationalStateImage.CapturedFrame.boundBoundary frame))
    (execution : ReturnExecution frame origin sourcePath location resolved
      running)
    (capability : ActiveResultCapability origin (.cons frame saved tail)) :
    StateImage
      (LambdaPFC.State.mk sourceStore runtimeRest
        (runtimeBody.open location)) :=
  let code := frame.afterReturnCode location execution.slot
  let coherent := execution.afterCoherent saved
  have boundToBehavior : Exp.Steps (frameBoundClosed frame)
      execution.slot.behavior.argument :=
    running.reductions.trans execution.suffix
  let restoredRunning := restoreAfterReturn saved location execution.slot
    boundToBehavior execution.resumeAdapter
  let restoredCapability := capability.pop
    (CurrentOrigin.ofDirect code coherent) saved.resultShape
  { focus := directClosed code
    activeOrigin := parentOrigin
    activeBoundary := parentBoundary
    current := currentOfDirect code coherent
    stack := tail
    running := restoredRunning
    capability := restoredCapability
    functionCapability :=
      ActiveFunctionCapability.ofNonCanonicalInput restoredCapability
        (LambdaPToFCo.OperationalStateImage.NonCanonicalResultShape.weaken
          saved.resultShape) }

/-- One native existing-location return transition. -/
theorem return_source_step
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    (location : Fin current) :
    LambdaPFC.State.Step
      (LambdaPFC.State.mk sourceStore (runtimeBody :: runtimeRest)
        (.path (.var location)))
      (LambdaPFC.State.mk sourceStore runtimeRest
        (runtimeBody.open location)) :=
  .return

/-- Target suffix corresponding to one source return step. -/
theorem return_target_steps
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    (frame : CapturedFrame sourceStore runtimeBody)
    {parentBoundary : ResultBoundary.{0}}
    (saved : SuspendedExecution frame parentOrigin parentBoundary)
    (tail : ExecutionStack sourceStore runtimeRest parentOrigin
      parentBoundary)
    (origin : CurrentOrigin sourceStore)
    (sourcePath : LambdaPFC.Path origin.original.arity)
    (location : Fin current)
    (resolved : ResolvedPathView origin sourcePath location)
    (running : ExecutionRunning (frameBoundClosed frame)
      resolved.target.view.argument origin.resultBoundary
      (OperationalStateImage.CapturedFrame.boundBoundary frame))
    (execution : ReturnExecution frame origin sourcePath location resolved
      running)
    (capability : ActiveResultCapability origin (.cons frame saved tail))
    (functionCapability : ActiveFunctionCapability origin
      (.cons frame saved tail) running capability) :
    Exp.Steps
      (beforeReturn frame saved tail origin sourcePath location resolved
        running capability functionCapability).target
      (afterReturn frame saved tail origin sourcePath location resolved running
        execution capability).target := by
  have localSteps := saved.surrounding.steps execution.frame_steps
  have lifted := tail.plug_steps localSteps
  simpa only [beforeReturn, afterReturn, StateImage.target, ExecutionStack.plug,
    restoreAfterReturn, ResultContext.compose_plug,
    ResultContext.ofResume_plug] using lifted

end StateImage

end OperationalStateImage
end LambdaPToFCo
