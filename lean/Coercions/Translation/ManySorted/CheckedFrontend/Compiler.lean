import Coercions.Translation.ManySorted.CheckedFrontend.Checker
import Coercions.Translation.ManySorted.ModalIntersections.Compiler

/-!
# Checked front-end/compiler pipeline

This is the executable boundary missing from the derivation-directed compiler:
raw syntax is checked first, and only the returned intrinsic derivation is
passed to `ModalIntersections.Compiler.compileTerm`.  The result retains the
standalone target check and the global `AdministrativeEq` guarantee already
carried by `CompiledTerm`.
-/

namespace DOTCaptureToManySortedFC.CheckedFrontend

/-- Pipeline failures preserve whether rejection happened in source checking
or in the existing cumulative compilation/target-checking boundary. -/
inductive PipelineError : Type where
  | frontend (error : Error)
  | compiler
      (error : DOTCaptureToManySortedFC.ModalIntersections.Compiler.Error)

/-- Complete successful output of checked elaboration followed by cumulative
compilation.  `sourceAccepted` ties the synthesized derivation to this exact
raw input rather than leaving `raw` as a phantom index. -/
structure Compiled {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : ManySortedFC.Sig}
    (context :
      DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext.Context
        environment targetScope)
    (raw : RawTerm sourceScope) where
  checked : CheckedTerm environment
  sourceAccepted : checkTerm environment raw = .ok checked
  artifact :
    DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts.CompiledTerm
      context.core checked.term checked.use checked.type

/-- Check annotated source syntax and compile the resulting intrinsic
derivation.  No caller-supplied derivation enters this function. -/
def compile {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : ManySortedFC.Sig}
    (context :
      DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext.Context
        environment targetScope)
    (raw : RawTerm sourceScope) : Except PipelineError (Compiled context raw) :=
  match sourceAccepted : checkTerm environment raw with
  | .error error => .error (.frontend error)
  | .ok checked =>
      match DOTCaptureToManySortedFC.ModalIntersections.Compiler.compileTerm
          context checked.typing with
      | .error error => .error (.compiler error)
      | .ok artifact => .ok { checked, sourceAccepted, artifact }

namespace Compiled

/-- The source half of a successful pipeline result is intrinsically typed. -/
def sourceTyping {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : ManySortedFC.Sig}
    {context :
      DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext.Context
        environment targetScope}
    {raw : RawTerm sourceScope} (compiled : Compiled context raw) :
    DOTCapture.ModalIntersections.Term.HasType environment
      compiled.checked.term compiled.checked.use compiled.checked.type :=
  compiled.checked.typing

/-- The emitted artifact was accepted by the independent target checker. -/
theorem targetAccepted {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : ManySortedFC.Sig}
    {context :
      DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext.Context
        environment targetScope}
    {raw : RawTerm sourceScope} (compiled : Compiled context raw) :
    ManySortedFC.Tm.check context.core.target compiled.artifact.term =
      some compiled.artifact.checked :=
  compiled.artifact.accepted

/-- The checker independently reproduces the prepared target indices. -/
theorem targetSynthesizes {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : ManySortedFC.Sig}
    {context :
      DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext.Context
        environment targetScope}
    {raw : RawTerm sourceScope} (compiled : Compiled context raw) :
    ManySortedFC.Tm.synth context.core.target compiled.artifact.term =
      some (compiled.artifact.targetUse, compiled.artifact.targetType) :=
  compiled.artifact.checkerAccepts

/-- Global compiler correctness remains administrative equality.  In
particular, this statement does not claim literal equality for function or
modal adapters that eta-expand. -/
theorem administrativeErasure {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : ManySortedFC.Sig}
    {context :
      DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext.Context
        environment targetScope}
    {raw : RawTerm sourceScope} (compiled : Compiled context raw) :
    ManySortedFC.Runtime.AdministrativeEq compiled.artifact.term.erase
      (context.core.eraseTerm compiled.checked.term) :=
  compiled.artifact.erasure

end Compiled

end DOTCaptureToManySortedFC.CheckedFrontend
