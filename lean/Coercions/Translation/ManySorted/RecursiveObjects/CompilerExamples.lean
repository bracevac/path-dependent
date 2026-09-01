import Coercions.Translation.ManySorted.RecursiveObjects.SourceExamples
import Coercions.Translation.ManySorted.RecursiveObjects.ModelExamples
import Coercions.Translation.ManySorted.RecursiveObjects.CompletionExamples
import Coercions.Translation.ManySorted.ModalIntersections.Compiler

/-!
# Recursive-object compiler regressions

These examples cross the cumulative compiler rather than stopping at the
recursive encoding or model checker.  The first literal carries a real
function representation whose annotation refers to the recursive signature.
The second program opens a recursive existential explicitly and consumes the
result through its stable root.  No compiler case inserts an implicit open.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.CompilerExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.Compiler
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.RecursiveObjects
open DOTCaptureToManySortedFC.RecursiveObjects.SourceExamples

namespace Src

abbrev Env := DOTCapture.ModalIntersections.TypingEnv
abbrev Value := DOTCapture.ModalIntersections.Value
abbrev Term := DOTCapture.ModalIntersections.Term
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev ObjectType := DOTCapture.ModalIntersections.ObjectType
abbrev Signature := DOTCaptureToManySortedFC.RecursiveObjects.Source.Signature

end Src

private def success? {alpha : Type} : Except Error alpha -> Option alpha
  | .ok value => some value
  | .error _ => none

/-! ## Positive self-dependent function representation -/

def functionObject : Src.Value [] :=
  .recursiveObject functionSignature.objectType functionPayload

def functionObject? := success?
  (compileValue Context.nil functionObjectTyping)

def functionPrepared? := Encoding.prepare Context.nil.core.layout
  functionSignature functionSignatureValid functionRealization

example : functionPrepared?.isOk = true := by native_decide

def functionPrepared := functionPrepared?.toOption.get (by native_decide)

def functionModel? := Model.check? functionPrepared
  (ambientCompiler Context.nil)

example : functionModel?.isSome = true := by native_decide

def functionModel := functionModel?.get (by native_decide)

def functionPayloadContext :=
  PositiveObjectCompilation.payloadContext Context.nil functionPrepared

def functionPayload? := success?
  (compileValue functionPayloadContext functionPayloadTyping)

example : functionPayload?.isSome = true := by native_decide

/-- Recursive payload annotations are interpreted through the simultaneous
model: the local type member denotes its canonical `recProj` witness. -/
example : (ObjectContract.translateType functionPayloadContext.core.layout
    (.ref (.localTypeMember 20) : Src.Ty [])).isOk = true := by
  native_decide

def functionPayloadCompiled := functionPayload?.get (by native_decide)

def functionFinalized? := PositiveObjectCompilation.compile? Context.nil
  functionPrepared (ambientCompiler Context.nil) functionModel .refl .refl
    functionPayloadCompiled

example : functionFinalized?.isSome = true := by native_decide

example : functionObject?.isSome = true := by native_decide

def functionObjectCompiled := functionObject?.get (by native_decide)

/-- The finished existential artifact is accepted independently in the empty
ambient target context. -/
example : ManySortedFC.Tm.check Core.nil.target functionObjectCompiled.term =
    some functionObjectCompiled.checked :=
  functionObjectCompiled.accepted

example : ManySortedFC.Tm.checkValue functionObjectCompiled.term =
    some functionObjectCompiled.valueChecked :=
  functionObjectCompiled.valueAccepted

/-- Recursive names, the model, capture evidence, adaptation, and packaging
all erase; the emitted runtime value is literally the source lambda. -/
theorem functionObjectExactErasure : functionObjectCompiled.term.erase =
    Core.nil.eraseValue functionObject := by
  native_decide

example : functionObjectCompiled.term.erase =
    (.lam .unit : ManySortedFC.Runtime.Tm 0) := by
  native_decide

/-! ## Nonempty representation capture -/

namespace NonemptyRepresentationCapture

open SourceExamples.ExistentialCaptureModels

def objectValue : Src.Value Scope :=
  .recursiveObject signature.objectType .unit

def objectTyping : DOTCapture.ModalIntersections.Value.HasType environment
    objectValue signature.objectType.formedType :=
  .recursiveObject valid realization .unit .refl .captureEmpty

def compiled? := success? (compileValue
  ModelExamples.ExistentialCaptureModels.context objectTyping)

example : compiled?.isSome = true := by native_decide

def compiled := compiled?.get (by native_decide)

/-- This package is finalized with the checked singleton `C_rep`, rather than
the pure representation capture used by the closed execution example. -/
example : ManySortedFC.Ty.outerCapture
    ModelExamples.ExistentialCaptureModels.checkedModel.realizedRepresentation =
      (.singleton .here : ManySortedFC.Capture
        [ManySortedFC.BinderKind.term]) := by
  native_decide

example : ManySortedFC.Tm.check
    ModelExamples.ExistentialCaptureModels.context.core.target compiled.term =
      some compiled.checked :=
  compiled.accepted

example : compiled.term.erase =
    ModelExamples.ExistentialCaptureModels.context.core.eraseValue objectValue :=
  by native_decide

end NonemptyRepresentationCapture

/-! ## Explicit opening and stable negative use -/

/- The mutually constrained capture model above deliberately hides the fact
that its concrete witnesses are empty once the existential is opened.  Its
abstract `x.C21` therefore cannot be discharged as an ambient capability.
For execution, retain the same recursive type member and the same non-Unit
payload while making the representation capture-free in the exported
signature. -/
def executableFunctionSignature : Src.Signature [] where
  typeDefinitions := functionSignature.typeDefinitions
  captureDeclarations := functionSignature.captureDeclarations
  representation := .capturing .empty
    (.arr (.ref (.localTypeMember 20)) .one)
  outerCapture := .empty

def executableFunctionSignatureValid : executableFunctionSignature.Valid where
  nonempty := by
    simpa [executableFunctionSignature] using functionSignatureValid.nonempty
  typeLabelsNodup := by
    simpa [executableFunctionSignature] using
      functionSignatureValid.typeLabelsNodup
  labelsDisjoint := by
    simpa [executableFunctionSignature] using
      functionSignatureValid.labelsDisjoint
  guarded := by
    simpa [executableFunctionSignature] using functionSignatureValid.guarded
  packageCaptureAmbient := rfl

def executableFunctionRealization : Source.Realization
    DOTCapture.ModalIntersections.Ctx.nil executableFunctionSignature where
  captures := mutuallyConstrainedModel
  captureConstraints := .inter (.member .refl .refl) (.member .refl .refl)
  representationContainment := .refl
  packageContainment := .refl

def executableFunctionObject : Src.ObjectType [] :=
  executableFunctionSignature.objectType

def executableFunctionLiteral : Src.Value [] :=
  .recursiveObject executableFunctionObject functionPayload

def executableFunctionLiteralTyping :
    DOTCapture.ModalIntersections.Value.HasType
      DOTCapture.ModalIntersections.TypingEnv.nil
      executableFunctionLiteral executableFunctionObject.formedType :=
  .recursiveObject executableFunctionSignatureValid
    executableFunctionRealization functionPayloadTyping .refl .refl

abbrev OpenedScope : DOTCapture.ModalIntersections.Sig := [] ▹ .term

def openedObject : Src.ObjectType OpenedScope :=
  executableFunctionObject.weaken (kind := .term)

def openedEnvironment : Src.Env OpenedScope :=
  DOTCapture.ModalIntersections.TypingEnv.nil.extendTerm
    executableFunctionObject.formedType

abbrev ConsumerScope : DOTCapture.ModalIntersections.Sig :=
  OpenedScope ▹ .term

def consumerObject : Src.ObjectType ConsumerScope :=
  openedObject.weaken (kind := .term)

def consumerEnvironment : Src.Env ConsumerScope :=
  openedEnvironment.extendTerm openedObject.formedType

def consumerExposure : DOTCapture.ModalIntersections.ExposesObject
    consumerEnvironment.bindings (.var .here) consumerObject :=
  .variable rfl

def consumerTypeOccurrence :
    consumerObject.interface.HasTypeOccurrence 20 .one .one :=
  .left (.left .here)

def consumerUnitToMember : DOTCapture.ModalIntersections.TypeIncludes
    consumerEnvironment.bindings .one
      (.ref (.typeMember (.var .here) 20)) :=
  .lower (.typeMember consumerExposure consumerTypeOccurrence)

def consumerUnitTyping : DOTCapture.ModalIntersections.Value.HasType
    consumerEnvironment .unit (.ref (.typeMember (.var .here) 20)) :=
  .adapt .unit (.cast consumerUnitToMember)

def payloadConsumerBody : Src.Term ConsumerScope :=
  .app (.select (.var .here) .payload) (.ret .unit)

def payloadConsumerBodyRawTyping :
    DOTCapture.ModalIntersections.Term.HasType consumerEnvironment
      payloadConsumerBody (.union .empty .empty) .one :=
  .app consumerExposure.payload rfl (by trivial) (.ret consumerUnitTyping)

def payloadConsumerBodyTyping :
    DOTCapture.ModalIntersections.Term.HasType consumerEnvironment
      payloadConsumerBody .empty .one :=
  .use payloadConsumerBodyRawTyping
    (.captureUnionElim .captureEmpty .captureEmpty)

def openedConsumer : Src.Value OpenedScope :=
  .objectConsumer openedObject .one payloadConsumerBody

def openedConsumerTyping : DOTCapture.ModalIntersections.Value.HasType
    openedEnvironment openedConsumer
      (.capturing .empty (.objectArrow openedObject .one)) :=
  .objectConsumer payloadConsumerBodyTyping .captureEmpty

def openedArgumentTyping :
    DOTCapture.ModalIntersections.ObjectArgument.HasType openedEnvironment
      (.ret (.var .here)) openedObject
      (DOTCapture.ModalIntersections.LocalModel.atPath (.var .here)) :=
  .stable rfl (DOTCapture.ModalIntersections.ObjectType.Adapts.refl _)
    .refl .refl

def openedBody : Src.Term OpenedScope :=
  .objectApp openedObject (.ret openedConsumer) (.ret (.var .here))

def openedBodyRawTyping : DOTCapture.ModalIntersections.Term.HasType
    openedEnvironment openedBody (.union .empty .empty) .one :=
  .objectApp (.ret openedConsumerTyping) rfl openedArgumentTyping

def openedBodyTyping : DOTCapture.ModalIntersections.Term.HasType
    openedEnvironment openedBody .empty .one :=
  .use openedBodyRawTyping
    (.captureUnionElim .captureEmpty .captureEmpty)

def openedDischarge : DOTCapture.ModalIntersections.CaptureIncludes
    openedEnvironment.bindings .empty
      (.union .empty (.singleton (.var .here))) :=
  .captureEmpty

def openedProgram : Src.Term [] :=
  .objectLet executableFunctionObject .one
    (.ret executableFunctionLiteral) openedBody

def openedProgramRawTyping : DOTCapture.ModalIntersections.Term.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil
    openedProgram (.union .empty .empty) .one :=
  .objectLet (.ret executableFunctionLiteralTyping) openedBodyTyping
    openedDischarge

def openedProgramTyping : DOTCapture.ModalIntersections.Term.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil
    openedProgram .empty .one :=
  .use openedProgramRawTyping
    (.captureUnionElim .captureEmpty .captureEmpty)

def openedProgram? := success?
  (compileTerm Context.nil openedProgramTyping)

example : openedProgram?.isSome = true := by native_decide

def openedProgramCompiled := openedProgram?.get (by native_decide)

example : ManySortedFC.Tm.check Core.nil.target openedProgramCompiled.term =
    some openedProgramCompiled.checked :=
  openedProgramCompiled.accepted

theorem openedProgramExactErasure : openedProgramCompiled.term.erase =
    Core.nil.eraseTerm openedProgram := by
  native_decide

theorem openedProgramErasure : openedProgramCompiled.term.erase =
    (.let' (.lam .unit)
      (.app (.lam (.app (.var 0) .unit)) (.var 0)) :
      ManySortedFC.Runtime.Tm 0) := by
  native_decide

/-- The explicit object open is a real zeta step; the stable negative
consumer and selected recursive payload then each perform a real beta step. -/
theorem openedProgramExecutes : ManySortedFC.Runtime.Steps
    openedProgramCompiled.term.erase .unit := by
  rw [openedProgramErasure]
  exact .tail
    (.tail (.single (.zeta .lam))
    (.beta .lam))
    (.beta .unit)

/-! ## Local advertised capture with a distinct package envelope -/

namespace LocalAdvertisedCaptureApplication

abbrev BaseScope := SourceExamples.ExistentialCaptureModels.Scope

def baseEnvironment := SourceExamples.ExistentialCaptureModels.environment

def envelope := SourceExamples.ExistentialCaptureModels.a

def localSignature := CompletionExamples.RepeatedRecursiveCapture.signature

def localValid := CompletionExamples.RepeatedRecursiveCapture.valid

def localRealization := CompletionExamples.RepeatedRecursiveCapture.realization

def baseContext := CompletionExamples.RepeatedRecursiveCapture.context

def object : Src.ObjectType BaseScope := localSignature.objectType

def literal : Src.Value BaseScope := .recursiveObject object .unit

def literalTyping : DOTCapture.ModalIntersections.Value.HasType baseEnvironment
    literal object.formedType :=
  .recursiveObject localValid localRealization .unit .refl .captureEmpty

abbrev OpenedScope : DOTCapture.ModalIntersections.Sig := BaseScope ▹ .term

def openedObject : Src.ObjectType OpenedScope := object.weaken (kind := .term)

def openedEnvironment : Src.Env OpenedScope :=
  baseEnvironment.extendTerm object.formedType

def exposure : DOTCapture.ModalIntersections.ExposesObject
    openedEnvironment.bindings (.var .here) openedObject :=
  .variable rfl

/-- The extra repeated `D : ∅ .. {a}` declaration is retained after
opening and supplies the ambient discharge used below. -/
def advertisedUpperOccurrence : openedObject.interface.HasCaptureOccurrence
    32 .empty envelope.weaken :=
  .right (.right .here)

def advertisedAtRoot : Src.Capture OpenedScope :=
  .ref (.captureMember (.var .here) 32)

def advertisedToEnvelope : DOTCapture.ModalIntersections.CaptureIncludes
    openedEnvironment.bindings advertisedAtRoot envelope.weaken :=
  .upper (.captureMember exposure advertisedUpperOccurrence)

abbrev ConsumerScope : DOTCapture.ModalIntersections.Sig := OpenedScope ▹ .term

def consumer : Src.Value OpenedScope :=
  .objectConsumer openedObject .one (.ret .unit)

def consumerTyping : DOTCapture.ModalIntersections.Value.HasType
    openedEnvironment consumer
      (.capturing .empty (.objectArrow openedObject .one)) :=
  .objectConsumer (.ret .unit) .captureEmpty

def argumentTyping : DOTCapture.ModalIntersections.ObjectArgument.HasType
    openedEnvironment (.ret (.var .here)) openedObject
      (DOTCapture.ModalIntersections.LocalModel.atPath (.var .here)) :=
  .stable rfl (DOTCapture.ModalIntersections.ObjectType.Adapts.refl _)
    .refl .refl

def application : Src.Term OpenedScope :=
  .objectApp openedObject (.ret consumer) (.ret (.var .here))

/-- Direct negative use is charged to the opened advertised member `x.D`,
not to the ambient package envelope `{a}`. -/
def applicationRawTyping : DOTCapture.ModalIntersections.Term.HasType
    openedEnvironment application (.union .empty advertisedAtRoot) .one :=
  .objectApp (.ret consumerTyping) rfl argumentTyping

def applicationTyping : DOTCapture.ModalIntersections.Term.HasType
    openedEnvironment application envelope.weaken .one :=
  .use applicationRawTyping
    (.captureUnionElim .captureEmpty advertisedToEnvelope)

def discharge : DOTCapture.ModalIntersections.CaptureIncludes
    openedEnvironment.bindings envelope.weaken
      (.union envelope.weaken (.singleton (.var .here))) :=
  .captureUnionLeft

def program : Src.Term BaseScope :=
  .objectLet object .one (.ret literal) application

def programUse : Src.Capture BaseScope :=
  DOTCapture.ModalIntersections.Capture.seq .empty
    (.union envelope envelope)

def programTyping : DOTCapture.ModalIntersections.Term.HasType baseEnvironment
    program programUse .one :=
  .objectLet (.ret literalTyping) applicationTyping discharge

def compiled? := success? (compileTerm baseContext programTyping)

example : compiled?.isSome = true := by native_decide

def compiled := compiled?.get (by native_decide)

example : ManySortedFC.Tm.check baseContext.core.target compiled.term =
    some compiled.checked :=
  compiled.accepted

example : compiled.term.erase = baseContext.core.eraseTerm program := by
  native_decide

end LocalAdvertisedCaptureApplication

/-! ## Syntax-directed negative-use boundary -/

/-- Raw direct negative use.  This term deliberately has no intrinsic typing
derivation: recursive literals are positive and cannot inhabit the
`ObjectArgument.HasType` judgment. -/
def directConsumer : Src.Value [] :=
  .objectConsumer executableFunctionObject .one (.ret .unit)

def directRecursiveUse : Src.Term [] :=
  .objectApp executableFunctionObject (.ret directConsumer)
    (.ret executableFunctionLiteral)

/-- The real source/compiler entrypoint checks raw syntax before demanding a
typing derivation, so the untypable direct use receives the Stage 6
diagnostic. -/
example : compileSourceTerm Context.nil directRecursiveUse none =
    .error (.unsupported .recursiveObjectArgumentRequiresExplicitOpen) := rfl

/-- The same entrypoint accepts an elaborated explicit-open program and
forwards it to the independently checked compiler core. -/
def openedProgramAtBoundary? := compileSourceTerm Context.nil openedProgram
  (some {
    use := .empty
    type := .one
    typing := openedProgramTyping })

example : openedProgramAtBoundary?.isOk = true := by native_decide

def openedProgramAtBoundary :=
  openedProgramAtBoundary?.toOption.get (by native_decide)

example : openedProgramAtBoundary.compiled.term = openedProgramCompiled.term :=
  by native_decide

example : ManySortedFC.Tm.check Core.nil.target
    openedProgramAtBoundary.compiled.term =
      some openedProgramAtBoundary.compiled.checked :=
  openedProgramAtBoundary.compiled.accepted

end DOTCaptureToManySortedFC.RecursiveObjects.CompilerExamples
