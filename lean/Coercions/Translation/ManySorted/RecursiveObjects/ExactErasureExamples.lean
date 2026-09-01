import Coercions.Translation.ManySorted.RecursiveObjects.CompilerExamples
import Coercions.Translation.ManySorted.RecursiveObjects.ExactErasure

/-!
# Exact-erasure boundary regressions

The first regression is a checked counterexample to unrestricted literal
adapter erasure.  The remaining examples exercise the exact recursive-value
and explicit-open lifting results.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.ExactErasureExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.Compiler
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.RecursiveObjects
open DOTCaptureToManySortedFC.RecursiveObjects.ExactErasure
open DOTCaptureToManySortedFC.RecursiveObjects.CompilerExamples

private def success? {alpha error : Type} : Except error alpha -> Option alpha
  | .ok value => some value
  | .error _ => none

/-! ## Unrestricted literal equality is false -/

namespace EtaCounterexample

/-- Even identity component adapters produce the function adapter's runtime
eta wrapper. -/
def adapter : ManySortedFC.Adapter [] :=
  .function (.identity .one) (.identity .one)

def runtimeFunction : ManySortedFC.Runtime.Tm 0 := .lam .unit

/-- The counterexample is itself accepted by the target adapter checker. -/
example : (ManySortedFC.Adapter.check ManySortedFC.Ctx.nil adapter).isSome =
    true := by
  native_decide

example : adapter.erase runtimeFunction =
    .lam (.let' (.app runtimeFunction.weaken (.var 0)) (.var 0)) := rfl

/-- Hence a theorem claiming literal erasure for every accepted structural
adapter would be false. -/
theorem not_literal : adapter.erase runtimeFunction ≠ runtimeFunction := by
  native_decide

/-- The intended general guarantee still holds. -/
theorem administratively_equal : ManySortedFC.Runtime.AdministrativeEq
    (adapter.erase runtimeFunction) runtimeFunction :=
  adapter.erase_admin runtimeFunction .lam

end EtaCounterexample

/-! ## Exact recursive-value lifting -/

def finalizedFunctionObject := functionFinalized?.get (by native_decide)

def exactFunctionPayload : ValueExact functionPayloadCompiled := by
  unfold ValueExact
  native_decide

def exactFunctionObject : ExactCompiledValue Context.nil.core functionObject
    SourceExamples.functionSignature.objectType.formedType :=
  recursiveObjectExactResult finalizedFunctionObject exactFunctionPayload

example : exactFunctionObject.artifact.term.erase =
    Context.nil.core.eraseValue functionObject :=
  exactFunctionObject.exact

/-- This is an exact characterization: recursive finalization is exact iff
the already compiled payload is exact. -/
example : finalizedFunctionObject.result.term.erase =
      Context.nil.core.eraseValue functionObject ↔
    functionPayloadCompiled.term.erase =
      Context.nil.core.eraseValue SourceExamples.functionPayload :=
  by
    simpa [functionObject] using
      finalizedFunctionObject.result_exact_erasure_iff

/-! ## Exact explicit object opening -/

def executablePrepared? := prepareObject? Context.nil.core
  executableFunctionObject

example : executablePrepared?.isSome = true := by native_decide

def executablePrepared := executablePrepared?.get (by native_decide)

def rhsCompiled? := success? (compileTerm Context.nil
  (.ret executableFunctionLiteralTyping))

example : rhsCompiled?.isSome = true := by native_decide

def rhsCompiled := rhsCompiled?.get (by native_decide)

def rhsExact : ExactCompiledTerm Context.nil.core
    (.ret executableFunctionLiteral) .empty executableFunctionObject.formedType
    where
  artifact := rhsCompiled
  exact := by
    unfold TermExact
    native_decide

def bodyContext := Context.nil.extendContractedObject executableFunctionObject
  executablePrepared

def bodyCompiled? := success? (compileTerm bodyContext openedBodyTyping)

example : bodyCompiled?.isSome = true := by native_decide

def bodyCompiled := bodyCompiled?.get (by native_decide)

def bodyExact : ExactCompiledTerm bodyContext.core openedBody .empty .one where
  artifact := bodyCompiled
  exact := by
    unfold TermExact
    native_decide

def resultPrepared : PreparedTerm Context.nil.core (.one : Source.Ty []) where
  targetType := .one
  prepared := rfl

def bodyOuterPrepared : PreparedCapture Context.nil.core
    (.empty : Source.Capture []) where
  targetCapture := .empty
  prepared := rfl

def targetDischarge? := compileIncludes? bodyContext.compiler.leaves
  openedDischarge

example : targetDischarge?.isSome = true := by native_decide

def targetDischarge := targetDischarge?.get (by native_decide)

def rawOpenedExact? := finishObjectLetExact? Context.nil
  executablePrepared.object resultPrepared rhsExact bodyExact
  bodyOuterPrepared openedDischarge targetDischarge.evidence

example : rawOpenedExact?.isSome = true := by native_decide

def rawOpenedExact := rawOpenedExact?.get (by native_decide)

def outerUse : DOTCapture.ModalIntersections.CaptureIncludes
    DOTCapture.ModalIntersections.Ctx.nil
    (DOTCapture.ModalIntersections.Capture.seq .empty
      (.union executableFunctionObject.packageCapture .empty))
    .empty :=
  .captureUnionElim .captureEmpty .captureEmpty

def targetOuterUse? := compileIncludes? Context.nil.compiler.leaves outerUse

example : targetOuterUse?.isSome = true := by native_decide

def targetOuterUse := targetOuterUse?.get (by native_decide)

def openedExact? := finishUseExact? rawOpenedExact outerUse
  targetOuterUse.evidence

example : openedExact?.isSome = true := by native_decide

def openedExact := openedExact?.get (by native_decide)

example : openedExact.artifact.term.erase = Context.nil.core.eraseTerm
    openedProgram :=
  openedExact.exact

/-- The exact compositional path emits the same checked syntax as the main
derivation-directed compiler. -/
example : openedExact.artifact.term = openedProgramCompiled.term := by
  native_decide

end DOTCaptureToManySortedFC.RecursiveObjects.ExactErasureExamples
