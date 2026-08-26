import LambdaPToFCo.OperationalAdmissibility
import LambdaPToFCo.OperationalClosedFrames
import LambdaPToFCo.OperationalResultContext

/-!
# Environment-indexed machine images

This module is the low-level machine-image layer of the exact-member
operational core.  A saved CK frame retains the source environment and target
closing substitution belonging to the lexical context in which its let was
written.
`StoreEnvironment.nativeWeaken` lets that captured view cross allocations
performed while the bound computation runs.

The allocation construction below is intentionally premise-driven.  It
requires the behavioral binder view and the member/function head facts that
the complete state invariant derives for the computed value.  Given those
facts, it performs the real source-environment update and proves the target
administrative reduction under the captured frame.  Its endpoint retains the
view's explicit `Resume`.  Higher modules supply the recursive coherence and
result interfaces that discharge these premises, including structural-arrow
application and general allocation, and then prove unconditional one-step
image preservation and source safety for the executable core.
-/

namespace LambdaPToFCo
namespace OperationalMachineImage

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalBindingView
open OperationalEnvironment
open OperationalStoreEnvironment
open OperationalAdmissibility
open OperationalApplicationSpine
open OperationalApplication
open OperationalResultContext

/-! ## Direct current code and captured frames -/

/-- A current runtime term which is still a direct valuation closure of its
original admissible source code, together with the lexical source/target
environment in which that code is interpreted. -/
structure DirectCodeEnvironment {current : Nat}
    (sourceStore : LambdaPFC.Store current)
    (runtimeTerm : LambdaPFC.Tm current) : Type where
  original : TypedCode
  valuation : SourceValuation original.arity current
  runtime_eq : runtimeTerm = original.term.rename valuation
  admissible : OperationallyAdmissible original.typing
  targetSig : Sig
  targetContext : Ctx targetSig
  scope : Scope original.context targetContext
  closing : ClosingEnv targetSig []
  environment : StoreEnvironment original.context sourceStore valuation
    targetContext scope closing

namespace DirectCodeEnvironment

/-- Forget the environment while retaining the ordinary source `CodeImage`.
-/
def codeImage (code : DirectCodeEnvironment sourceStore runtimeTerm) :
    CodeImage sourceStore runtimeTerm where
  original := code.original
  form := .direct code.valuation code.runtime_eq

/-- Native source value shape recovered from the runtime value constructor;
renaming cannot create an abstraction or pair. -/
noncomputable def sourceReady
    (code : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue) : code.original.term.IsValue :=
  let renamedReady :
      (code.original.term.rename code.valuation).IsValue :=
    code.runtime_eq ▸ runtimeReady
  OperationalValueEvidence.ValueEvidence.isValue_of_rename
    code.original.term code.valuation renamedReady

/-- The richer heap-storable value evidence selected by admissibility. -/
noncomputable def valueEvidence
    (code : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue) :
    ApplicationValueEvidence code.original.typing :=
  code.admissible.valueEvidence (code.sourceReady runtimeReady)

/-- A direct code environment survives a native allocation which is hidden
from its lexical context. -/
noncomputable def nativeWeaken
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeTerm : LambdaPFC.Tm current}
    (code : DirectCodeEnvironment sourceStore runtimeTerm)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    DirectCodeEnvironment (.val sourceStore runtimeValue runtimeReady)
      runtimeTerm.weaken where
  original := code.original
  valuation := code.valuation.weaken
  runtime_eq := by
    calc
      runtimeTerm.weaken =
          (code.original.term.rename code.valuation).weaken :=
        congrArg LambdaPFC.Tm.weaken code.runtime_eq
      _ = code.original.term.rename code.valuation.weaken :=
        SourceValuation.rename_weaken code.original.term code.valuation
  admissible := code.admissible
  targetSig := code.targetSig
  targetContext := code.targetContext
  scope := code.scope
  closing := code.closing
  environment := code.environment.nativeWeaken runtimeValue runtimeReady

end DirectCodeEnvironment

/-- One suspended let body together with the bound computation provenance
and the captured lexical environment needed when the CK machine eventually
returns or allocates into its hole. -/
structure CapturedFrame {current : Nat}
    (sourceStore : LambdaPFC.Store current)
    (runtimeBody : LambdaPFC.Tm (current + 1)) : Type where
  image : FrameImage runtimeBody
  boundTerm : LambdaPFC.Tm image.originalArity
  boundTyping : Fragment.HasType image.context boundTerm image.holeType
  holeWf_eq : image.holeWf = boundTyping.typeWf
  boundAdmissible : OperationallyAdmissible boundTyping
  boundPolicy : LetBoundPolicy boundTyping
  bodyAdmissible : OperationallyAdmissible image.bodyTyping
  targetSig : Sig
  targetContext : Ctx targetSig
  scope : Scope image.context targetContext
  closing : ClosingEnv targetSig []
  environment : StoreEnvironment image.context sourceStore image.valuation
    targetContext scope closing

namespace CapturedFrame

/-- The independently closed target frame owned by a captured source frame.
-/
noncomputable def compilation
    (frame : CapturedFrame sourceStore runtimeBody) :
    FrameImage.Compilation frame.image where
  targetSig := frame.targetSig
  targetContext := frame.targetContext
  scope := frame.scope
  coherent := frame.environment.coherent
  environment := frame.closing

/-- A suspended frame crosses an allocation performed by the computation in
its hole without changing its lexical source context or target closure. -/
noncomputable def nativeWeaken
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    CapturedFrame (.val sourceStore runtimeValue runtimeReady)
      (runtimeBody.rename LambdaPFC.FinFun.weaken.ext) where
  image := frame.image.weaken
  boundTerm := frame.boundTerm
  boundTyping := frame.boundTyping
  holeWf_eq := frame.holeWf_eq
  boundAdmissible := frame.boundAdmissible
  boundPolicy := frame.boundPolicy
  bodyAdmissible := frame.bodyAdmissible
  targetSig := frame.targetSig
  targetContext := frame.targetContext
  scope := frame.scope
  closing := frame.closing
  environment := frame.environment.nativeWeaken runtimeValue runtimeReady

/-- Native-only weakening changes source valuations and runtime indices but
not the independently closed target frame. -/
@[simp] theorem closeFrame_nativeWeaken
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    (frame.nativeWeaken runtimeValue runtimeReady).compilation.closeFrame =
      frame.compilation.closeFrame := by
  rfl

/-- Capture the frame introduced by a source `let_push`.  The frame chooses
the bound derivation's canonical well-formedness proof, making the binder
plan equality explicit by reflexivity. -/
def ofLet
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
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing) :
    CapturedFrame sourceStore (body.rename valuation.ext) where
  image :=
    { originalArity := n
      context := sourceContext
      holeType := boundType
      resultType := resultType
      body := body
      holeWf := boundTyping.typeWf
      resultWf := resultWf
      bodyTyping := bodyTyping
      valuation := valuation
      runtime_eq := rfl }
  boundTerm := bound
  boundTyping := boundTyping
  holeWf_eq := rfl
  boundAdmissible := boundAdmissible
  boundPolicy := boundPolicy
  bodyAdmissible := bodyAdmissible
  targetSig := sig
  targetContext := targetContext
  scope := scope
  closing := closing
  environment := environment

/-- The target representation of `let_push` is a change of decomposition,
not a reduction: the closed let is exactly the captured closed frame filled
with the closed bound computation. -/
theorem letPush_eq
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
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing) :
    closing.closeExp
        (TermTranslation.elaborate scope
          (.let boundTyping resultWf bodyTyping)) =
      ((ofLet boundTyping resultWf bodyTyping boundAdmissible boundPolicy
          bodyAdmissible environment).compilation.closeFrame.fill
        (closing.closeExp
          (TermTranslation.elaborate scope boundTyping))) := by
  rw [OperationalContexts.elaborate_let_eq_fill]
  exact closing.closeExp_fill
    (OperationalContexts.compileFrame scope boundTyping.typeWf resultWf
      bodyTyping)
    (TermTranslation.elaborate scope boundTyping)

end CapturedFrame

/-! ## Heterogeneous captured stacks -/

/-- Every suspended source frame owns its own lexical source environment and
closed target compilation.  Only the current physical store is shared. -/
inductive CapturedCont {current : Nat}
    (sourceStore : LambdaPFC.Store current) :
    LambdaPFC.Tm.Cont current -> Type where
  | nil : CapturedCont sourceStore []
  | cons
      {runtimeBody : LambdaPFC.Tm (current + 1)}
      {runtimeRest : LambdaPFC.Tm.Cont current}
      (head : CapturedFrame sourceStore runtimeBody)
      (tail : CapturedCont sourceStore runtimeRest) :
      CapturedCont sourceStore (runtimeBody :: runtimeRest)

namespace CapturedCont

/-- Assemble the independently closed target frames into one target
continuation. -/
noncomputable def closeCont :
    {runtime : LambdaPFC.Tm.Cont current} ->
    CapturedCont sourceStore runtime -> OperationalContexts.Cont []
  | [], .nil => .halt
  | _ :: _, .cons head tail =>
      .push head.compilation.closeFrame tail.closeCont

/-- Every saved frame crosses a physical allocation while retaining its own
lexical context and target closure. -/
noncomputable def nativeWeaken
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    {runtime : LambdaPFC.Tm.Cont current} ->
    (cont : CapturedCont sourceStore runtime) ->
      CapturedCont (.val sourceStore runtimeValue runtimeReady) runtime.weaken
  | [], .nil => .nil
  | _ :: _, .cons head tail =>
      .cons (head.nativeWeaken runtimeValue runtimeReady)
        (tail.nativeWeaken runtimeValue runtimeReady)

/-- Native weakening is invisible in the homogeneous closed target stack. -/
@[simp] theorem closeCont_nativeWeaken
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtime : LambdaPFC.Tm.Cont current}
    (cont : CapturedCont sourceStore runtime)
    (runtimeValue : LambdaPFC.Tm current)
    (runtimeReady : runtimeValue.IsValue) :
    (cont.nativeWeaken runtimeValue runtimeReady).closeCont = cont.closeCont := by
  induction cont with
  | nil => rfl
  | cons head tail ih =>
      change OperationalContexts.Cont.push
        (head.nativeWeaken runtimeValue runtimeReady).compilation.closeFrame
        ((tail.nativeWeaken runtimeValue runtimeReady).closeCont) =
        OperationalContexts.Cont.push head.compilation.closeFrame
          tail.closeCont
      rw [CapturedFrame.closeFrame_nativeWeaken, ih]

end CapturedCont

/-! ## Accumulated target execution of the head computation -/

/-- Target execution accumulated since the head frame's bound computation
was pushed.  `focus` is the target term corresponding to the current source
focus; `resume` records transparent administration that has not yet
discharged. -/
structure RunningComputation
    (frame : CapturedFrame sourceStore runtimeBody) : Type where
  focus : Exp []
  context : ResultContext []
  generated : GeneratedResultContext context
  reductions : Exp.Steps
    (frame.closing.closeExp
      (TermTranslation.elaborate frame.scope frame.boundTyping))
    (context.plug focus)

namespace RunningComputation

/-- Immediately after `let_push`, the bound computation is the focus and no
administrative context is pending. -/
noncomputable def start (frame : CapturedFrame sourceStore runtimeBody) :
    RunningComputation frame where
  focus := frame.closing.closeExp
    (TermTranslation.elaborate frame.scope frame.boundTyping)
  context := .identity
  generated := .identity
  reductions := .refl

/-- Once the focus is a target value, generated application administration
normalizes to an explicit target value.  Structural casts are allowed to
remain in that endpoint. -/
noncomputable def finish
    (running : RunningComputation frame)
    (focusReady : Exp.IsValue running.focus) :
    ValueNormalization
      (frame.closing.closeExp
        (TermTranslation.elaborate frame.scope frame.boundTyping)) :=
  let normalization := running.generated.normalize focusReady
  { result := normalization.result
    ready := normalization.ready
    reductions := running.reductions.trans normalization.reductions }

end RunningComputation

/-! ## The allocation interface at a saved frame -/

/-- Facts needed when a computed native value is allocated into a saved
frame.  `behavior` belongs to the frame's expected hole type, while native
code provenance remains separately owned by `DirectCodeEnvironment`. -/
structure AllocationSlot
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    (frame : CapturedFrame sourceStore runtimeBody)
    (native : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue) : Type where
  behavior : EliminationView
    ((TermTranslation.compileBinder frame.scope
      frame.boundTyping.typeWf).plan.subst
      frame.closing.substitution)
  nativeReady : (native.valueEvidence runtimeReady).ClosedReady
    native.scope native.closing
  normalizes : Exp.Steps
    (frame.closing.closeExp
      (TermTranslation.elaborate frame.scope frame.boundTyping))
    behavior.argument
  memberCell : MemberCell frame.image.holeType
    (.val sourceStore runtimeValue runtimeReady) frame.image.valuation.weaken 0
  functionCell : FunctionCell frame.image.holeType
    (.val sourceStore runtimeValue runtimeReady) frame.image.valuation.weaken 0

namespace RunningComputation

/-- Turn an accumulated head computation which has reached the expected
behavioral argument into the complete slot premise consumed by allocation. -/
noncomputable def allocationSlot
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    {frame : CapturedFrame sourceStore runtimeBody}
    (running : RunningComputation frame)
    (native : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (behavior : EliminationView
      ((TermTranslation.compileBinder frame.scope
        frame.boundTyping.typeWf).plan.subst frame.closing.substitution))
    (focusReady : Exp.IsValue running.focus)
    (endpoint_eq : (running.finish focusReady).result = behavior.argument)
    (nativeReady : (native.valueEvidence runtimeReady).ClosedReady
      native.scope native.closing)
    (memberCell : MemberCell frame.image.holeType
      (.val sourceStore runtimeValue runtimeReady)
      frame.image.valuation.weaken 0)
    (functionCell : FunctionCell frame.image.holeType
      (.val sourceStore runtimeValue runtimeReady)
      frame.image.valuation.weaken 0) :
    AllocationSlot frame native runtimeReady where
  behavior := behavior
  nativeReady := nativeReady
  normalizes := by
    simpa only [endpoint_eq] using (running.finish focusReady).reductions
  memberCell := memberCell
  functionCell := functionCell

end RunningComputation

namespace CapturedFrame

/-- Extend the captured source environment at the frame's lexical hole while
retaining the computed value's independent native origin environment. -/
noncomputable def afterAllocationEnvironment
    (frame : CapturedFrame sourceStore runtimeBody)
    (native : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (slot : AllocationSlot frame native runtimeReady) :
    StoreEnvironment
      (frame.image.context.snoc frame.image.holeType)
      (.val sourceStore runtimeValue runtimeReady)
      frame.image.valuation.ext
      ((TermTranslation.compileBinder frame.scope
        frame.boundTyping.typeWf).plan.context
        frame.targetContext)
      (TermTranslation.compileBinder frame.scope
        frame.boundTyping.typeWf).extended
      (extendClosing frame.closing
        (TermTranslation.compileBinder frame.scope
          frame.boundTyping.typeWf).plan
        slot.behavior) :=
  .extend frame.environment frame.boundTyping native.original native.valuation
    native.admissible (native.valueEvidence runtimeReady) native.environment
    slot.nativeReady runtimeReady native.runtime_eq slot.memberCell
    slot.functionCell slot.behavior slot.normalizes

/-- The source code/environment image entered by the CK allocation
successor. -/
noncomputable def afterAllocationCode
    (frame : CapturedFrame sourceStore runtimeBody)
    (native : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (slot : AllocationSlot frame native runtimeReady) :
    DirectCodeEnvironment (.val sourceStore runtimeValue runtimeReady)
      runtimeBody where
  original := TypedCode.ofTyping frame.image.bodyTyping
  valuation := frame.image.valuation.ext
  runtime_eq := frame.image.runtime_eq
  admissible := frame.bodyAdmissible
  targetSig :=
    (TermTranslation.compileBinder frame.scope
      frame.boundTyping.typeWf).plan.scope
  targetContext :=
    (TermTranslation.compileBinder frame.scope
      frame.boundTyping.typeWf).plan.context
      frame.targetContext
  scope :=
    (TermTranslation.compileBinder frame.scope
      frame.boundTyping.typeWf).extended
  closing := extendClosing frame.closing
    (TermTranslation.compileBinder frame.scope
      frame.boundTyping.typeWf).plan
    slot.behavior
  environment := frame.afterAllocationEnvironment native runtimeReady slot

end CapturedFrame

/-! ## Target counterpart of the head allocation case -/

/-- Eliminating the computed value under its captured closed frame reaches
the newly closed frame body, modulo exactly the transparent administrative
`Resume` advertised by the behavioral view. -/
theorem CapturedFrame.allocation_steps
    (frame : CapturedFrame sourceStore runtimeBody)
    (native : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (slot : AllocationSlot frame native runtimeReady) :
    Exp.Steps
      (frame.compilation.closeFrame.fill
        (frame.closing.closeExp
          (TermTranslation.elaborate frame.scope frame.boundTyping)))
      ((slot.behavior.resume
          ((translateType frame.scope frame.image.resultWf).subst
            frame.closing.substitution)).plug
        ((frame.afterAllocationCode native runtimeReady slot).closing.closeExp
          (TermTranslation.elaborate
            (frame.afterAllocationCode native runtimeReady slot).scope
            frame.image.bodyTyping))) := by
  have normalization :=
    frame.compilation.closeFrame_fill_steps slot.normalizes
  refine normalization.trans ?_
  change Exp.Steps
    (((TermTranslation.compileBinder frame.scope
        frame.image.holeWf).plan.subst frame.closing.substitution).close
      slot.behavior.argument
      ((translateType frame.scope frame.image.resultWf).subst
        frame.closing.substitution)
      ((TermTranslation.elaborate
        (TermTranslation.compileBinder frame.scope
          frame.image.holeWf).extended
        frame.image.bodyTyping).subst
          ((TermTranslation.compileBinder frame.scope
            frame.image.holeWf).plan.scopeSubst
              frame.closing.substitution))) _
  rw [frame.holeWf_eq]
  simpa only [CapturedFrame.afterAllocationCode,
    OperationalStoreEnvironment.closeExp_extendClosing] using
    (slot.behavior.eliminate
      ((translateType frame.scope frame.image.resultWf).subst
        frame.closing.substitution)
      ((TermTranslation.elaborate
        (TermTranslation.compileBinder frame.scope
          frame.boundTyping.typeWf).extended
        frame.image.bodyTyping).subst
          ((TermTranslation.compileBinder frame.scope
            frame.boundTyping.typeWf).plan.scopeSubst
              frame.closing.substitution)))

/-! ## Stack-level CK transition counterparts -/

/-- `let_push` remains a zero-step decomposition equality underneath every
heterogeneous captured outer stack. -/
theorem CapturedCont.letPush_eq
    {n current : Nat}
    {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {runtimeRest : LambdaPFC.Tm.Cont current}
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
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope closing)
    (rest : CapturedCont sourceStore runtimeRest) :
    rest.closeCont.plug
        (closing.closeExp
          (TermTranslation.elaborate scope
            (.let boundTyping resultWf bodyTyping))) =
      (CapturedCont.cons
        (CapturedFrame.ofLet boundTyping resultWf bodyTyping
          boundAdmissible boundPolicy bodyAdmissible environment) rest).closeCont.plug
        (closing.closeExp
          (TermTranslation.elaborate scope boundTyping)) := by
  change rest.closeCont.plug
      (closing.closeExp
        (TermTranslation.elaborate scope
          (.let boundTyping resultWf bodyTyping))) =
    rest.closeCont.plug
      ((CapturedFrame.ofLet boundTyping resultWf bodyTyping
        boundAdmissible boundPolicy bodyAdmissible environment).compilation.closeFrame.fill
        (closing.closeExp (TermTranslation.elaborate scope boundTyping)))
  exact congrArg rest.closeCont.plug
    (CapturedFrame.letPush_eq boundTyping resultWf bodyTyping
      boundAdmissible boundPolicy bodyAdmissible environment)

/-- The complete target counterpart of CK allocation for a captured head
frame and heterogeneous outer stack.  The successor stack is the actual
source `Cont.weaken`; its closed target representation is unchanged. -/
theorem CapturedCont.allocation_steps
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeRest : LambdaPFC.Tm.Cont current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    {runtimeValue : LambdaPFC.Tm current}
    (rest : CapturedCont sourceStore runtimeRest)
    (frame : CapturedFrame sourceStore runtimeBody)
    (native : DirectCodeEnvironment sourceStore runtimeValue)
    (runtimeReady : runtimeValue.IsValue)
    (slot : AllocationSlot frame native runtimeReady) :
    Exp.Steps
      (rest.closeCont.plug
        (frame.compilation.closeFrame.fill
          (frame.closing.closeExp
            (TermTranslation.elaborate frame.scope frame.boundTyping))))
      ((rest.nativeWeaken runtimeValue runtimeReady).closeCont.plug
        ((slot.behavior.resume
            ((translateType frame.scope frame.image.resultWf).subst
              frame.closing.substitution)).plug
          ((frame.afterAllocationCode native runtimeReady slot).closing.closeExp
            (TermTranslation.elaborate
              (frame.afterAllocationCode native runtimeReady slot).scope
              frame.image.bodyTyping)))) := by
  have reductions := rest.closeCont.plug_steps
    (CapturedFrame.allocation_steps frame native runtimeReady slot)
  simpa only [CapturedCont.closeCont_nativeWeaken] using reductions

/-! ## Existing-location return into a saved frame -/

/-- Physical-cell and adapted-interface data needed when CK returns an
existing location to a saved frame. -/
structure ReturnSlot
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody)
    (location : Fin current) : Type where
  runtimeValue : LambdaPFC.Tm current
  binds : LambdaPFC.Store.Binds sourceStore location runtimeValue
  compiled : CompiledBinding runtimeValue
  nativeTargetSig : Sig
  nativeTargetContext : Ctx nativeTargetSig
  nativeScope : Scope compiled.native.context nativeTargetContext
  nativeClosing : ClosingEnv nativeTargetSig []
  nativeEnvironment : StoreEnvironment compiled.native.context sourceStore
    compiled.nativeValuation nativeTargetContext nativeScope nativeClosing
  behavior : EliminationView
    ((TermTranslation.compileBinder frame.scope frame.image.holeWf).plan.subst
      frame.closing.substitution)
  memberCell : MemberCell frame.image.holeType sourceStore
    frame.image.valuation location
  functionCell : FunctionCell frame.image.holeType sourceStore
    frame.image.valuation location

namespace CapturedFrame

/-- Bind an existing physical location at the captured frame's lexical hole.
No fictitious source path computation is attached to this binder. -/
noncomputable def afterReturnEnvironment
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody)
    (location : Fin current)
    (slot : ReturnSlot frame location) :
    StoreEnvironment
      (frame.image.context.snoc frame.image.holeType)
      sourceStore
      (frame.image.valuation.bind location)
      ((TermTranslation.compileBinder frame.scope frame.image.holeWf).plan.context
        frame.targetContext)
      (TermTranslation.compileBinder frame.scope frame.image.holeWf).extended
      (extendClosing frame.closing
        (TermTranslation.compileBinder frame.scope frame.image.holeWf).plan
        slot.behavior) :=
  .bindLocation frame.environment frame.image.holeWf location slot.binds
    slot.compiled slot.nativeEnvironment slot.memberCell slot.functionCell
    slot.behavior

/-- Direct body image entered by a CK `return` transition. -/
noncomputable def afterReturnCode
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody)
    (location : Fin current)
    (slot : ReturnSlot frame location) :
    DirectCodeEnvironment sourceStore (runtimeBody.open location) where
  original := TypedCode.ofTyping frame.image.bodyTyping
  valuation := frame.image.valuation.bind location
  runtime_eq := by
    calc
      runtimeBody.open location =
          (frame.image.body.rename frame.image.valuation.ext).open location :=
        congrArg (fun term => term.open location) frame.image.runtime_eq
      _ = frame.image.body.rename (frame.image.valuation.bind location) :=
        SourceValuation.rename_ext_openAt frame.image.body
          frame.image.valuation location
  admissible := frame.bodyAdmissible
  targetSig :=
    (TermTranslation.compileBinder frame.scope frame.image.holeWf).plan.scope
  targetContext :=
    (TermTranslation.compileBinder frame.scope frame.image.holeWf).plan.context
      frame.targetContext
  scope :=
    (TermTranslation.compileBinder frame.scope frame.image.holeWf).extended
  closing := extendClosing frame.closing
    (TermTranslation.compileBinder frame.scope frame.image.holeWf).plan
    slot.behavior
  environment := frame.afterReturnEnvironment location slot

/-- Target counterpart of CK `return`: eliminate the returned location's
adapted behavioral argument under the captured frame and retain its honest
administrative resumption. -/
theorem return_steps
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody)
    (location : Fin current)
    (slot : ReturnSlot frame location) :
    Exp.Steps
      (frame.compilation.closeFrame.fill slot.behavior.argument)
      ((slot.behavior.resume
          ((translateType frame.scope frame.image.resultWf).subst
            frame.closing.substitution)).plug
        ((frame.afterReturnCode location slot).closing.closeExp
          (TermTranslation.elaborate
            (frame.afterReturnCode location slot).scope
            frame.image.bodyTyping))) := by
  change Exp.Steps
    (((TermTranslation.compileBinder frame.scope
        frame.image.holeWf).plan.subst frame.closing.substitution).close
      slot.behavior.argument
      ((translateType frame.scope frame.image.resultWf).subst
        frame.closing.substitution)
      ((TermTranslation.elaborate
        (TermTranslation.compileBinder frame.scope
          frame.image.holeWf).extended
        frame.image.bodyTyping).subst
          ((TermTranslation.compileBinder frame.scope
            frame.image.holeWf).plan.scopeSubst
              frame.closing.substitution))) _
  simpa only [CapturedFrame.afterReturnCode,
    OperationalStoreEnvironment.closeExp_extendClosing] using
    (slot.behavior.eliminate
      ((translateType frame.scope frame.image.resultWf).subst
        frame.closing.substitution)
      ((TermTranslation.elaborate
        (TermTranslation.compileBinder frame.scope
          frame.image.holeWf).extended
        frame.image.bodyTyping).subst
          ((TermTranslation.compileBinder frame.scope
            frame.image.holeWf).plan.scopeSubst
              frame.closing.substitution)))

end CapturedFrame

end OperationalMachineImage
end LambdaPToFCo
