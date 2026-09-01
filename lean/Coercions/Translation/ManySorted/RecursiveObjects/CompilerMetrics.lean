import Coercions.Translation.ManySorted.RecursiveObjects.Model
import Coercions.Translation.ManySorted.RecursiveObjects.PositiveObjectCompilation
import Coercions.Translation.ManySorted.ModalIntersections.CompilerMetrics

/-!
# Recursive-object compiler metrics

This module keeps two measurements distinct. `recursiveModelStats` recounts
one independently checked recursive model. `ofCompiledObject` combines those
statistics with a value compilation only when both are indices of the same
recursive positive-object finalization artifact. Nested program reports use
the ordinary cumulative compiler metrics; a model reconstructed separately
for such a program must be reported separately as well.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.CompilerMetrics

open DOTCaptureToManySortedFC.RecursiveObjects
open DOTCaptureToManySortedFC.ModalIntersections.Compiler
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence

namespace Src

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev Value := DOTCapture.ModalIntersections.Value
abbrev Term := DOTCapture.ModalIntersections.Term
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture

end Src

namespace Target

abbrev Sig := ManySortedFC.Sig

end Target

/-- Static resources of the recursive model packaged by one source object.
`modelEvidenceNodes` measures proof syntax, whereas the two argument counts
measure the checked vectors supplied to the theory model checker. Runtime
payloads are not model data; their target package sites are counted by the
ordinary compilation report. -/
structure RecursiveModelStats where
  sourceTypeDefinitions : Nat
  sourceCaptureOccurrences : Nat
  checkedTheorySymbols : Nat
  checkedTheoryConstraints : Nat
  modelSymbolArguments : Nat
  modelEvidenceArguments : Nat
  modelEvidenceNodes : Nat
  modelCheckerAccepted : Bool
deriving DecidableEq, Repr

/-- Recount a checked recursive model and independently rerun the target
theory-model checker. -/
def recursiveModelStats {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Source.Signature sourceScope}
    {valid : signature.Valid}
    {realization : Source.Realization environment.bindings signature}
    {prepared : Encoding.Prepared core.layout signature valid realization}
    {ambient : AmbientCompiler core}
    (checked : Model.CheckedModel core prepared ambient) :
    RecursiveModelStats :=
  { sourceTypeDefinitions := signature.typeDefinitions.length
    sourceCaptureOccurrences := signature.captureLabels.length
    checkedTheorySymbols := prepared.object.symbols.length
    checkedTheoryConstraints := prepared.object.relations.length
    modelSymbolArguments :=
      ModalIntersections.CompilerMetrics.symbolArgumentCount
        checked.model.symbols
    modelEvidenceArguments :=
      ModalIntersections.CompilerMetrics.evidenceArgumentCount
        checked.model.evidence
    modelEvidenceNodes :=
      ModalIntersections.CompilerMetrics.evidenceArgumentsNodeCount
        checked.model.evidence
    modelCheckerAccepted :=
      (ManySortedFC.Theory.checkModel core.target prepared.object.theory
        checked.model.symbols checked.model.evidence).isSome }

/-- One provenance-linked audit record for a positive recursive object. The
compiled value and recursive model cannot be supplied independently: both
come from the same `PositiveObjectCompilation.CompiledObject`. -/
structure PositiveObjectReport where
  compilation : ModalIntersections.CompilerMetrics.CompilationReport
  recursiveModel : RecursiveModelStats
deriving DecidableEq, Repr

/-- Audit the compiled value and checked model retained by one recursive
positive-object finalization. -/
def ofCompiledObject {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext.Context
      environment targetScope}
    {signature : Source.Signature sourceScope}
    {valid : signature.Valid}
    {realization : Source.Realization environment.bindings signature}
    {prepared : Encoding.Prepared context.core.layout signature valid realization}
    {ambient : AmbientCompiler context.core}
    {checkedModel : Model.CheckedModel context.core prepared ambient}
    {payload : Src.Value sourceScope} {payloadType : Src.Ty sourceScope}
    {payloadShape : DOTCapture.ModalIntersections.TypeIncludes
      environment.bindings payloadType.stripCapture
        (signature.realizedRepresentation realization.captures).stripCapture}
    {payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings payloadType.outerCapture
        (signature.realizedRepresentation realization.captures).outerCapture}
    {payloadCompiled : CompiledValue
      (PositiveObjectCompilation.payloadContext context prepared).core
        payload payloadType}
    (compiled : PositiveObjectCompilation.CompiledObject context prepared
      ambient checkedModel payloadShape payloadCapture payloadCompiled) :
    PositiveObjectReport :=
  { compilation :=
      ModalIntersections.CompilerMetrics.ofCompiledValue compiled.result
    recursiveModel := recursiveModelStats checkedModel }

end DOTCaptureToManySortedFC.RecursiveObjects.CompilerMetrics
