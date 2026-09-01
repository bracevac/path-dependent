import Coercions.Translation.ManySorted.RecursiveObjects.CompilerExamples
import Coercions.Translation.ManySorted.RecursiveObjects.CompilerMetrics

/-!
# Recursive-object compiler metric regressions

The reports below audit the actual cumulative compiler artifacts.  Their
checker and erasure flags are recomputed by the report functions.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.CompilerMetricsExamples

open DOTCaptureToManySortedFC.RecursiveObjects.CompilerExamples
open DOTCaptureToManySortedFC.RecursiveObjects.CompilerMetrics
open DOTCaptureToManySortedFC.ModalIntersections.Compiler
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext

/-! ## Positive recursive function object -/

def functionFinalized := functionFinalized?.get (by native_decide)

/-- The report consumes the finalization artifact that contains both this
compiled value and this checked model as indices. -/
def functionObjectReport : PositiveObjectReport :=
  ofCompiledObject functionFinalized

example : functionFinalized.result.term = functionObjectCompiled.term := by
  native_decide

example :
    (functionObjectReport.compilation.source.objects,
      functionObjectReport.compilation.source.objectLets,
      functionObjectReport.compilation.source.objectConsumers,
      functionObjectReport.compilation.source.objectApplications) =
      (1, 0, 0, 0) := by
  native_decide

example :
    (functionObjectReport.compilation.target.packages,
      functionObjectReport.compilation.target.opens,
      functionObjectReport.compilation.runtime.lambdas) = (1, 0, 1) := by
  native_decide

/-- The model has one guarded type definition, two recursive capture-member
occurrences, and the generated representation-capture symbol. -/
example :
    (functionObjectReport.recursiveModel.sourceTypeDefinitions,
      functionObjectReport.recursiveModel.sourceCaptureOccurrences,
      functionObjectReport.recursiveModel.checkedTheorySymbols,
      functionObjectReport.recursiveModel.checkedTheoryConstraints) =
      (1, 2, 4, 8) := by
  native_decide
example :
    (functionObjectReport.recursiveModel.modelSymbolArguments,
      functionObjectReport.recursiveModel.modelEvidenceArguments,
      functionObjectReport.recursiveModel.modelEvidenceNodes) =
      (4, 8, 11) := by
  native_decide

example :
    (functionObjectReport.recursiveModel.modelCheckerAccepted,
      functionObjectReport.compilation.checkerAccepted,
      functionObjectReport.compilation.checkerIndicesMatch,
      functionObjectReport.compilation.valueCheckerAccepted,
      functionObjectReport.compilation.literalErasureMatches) =
      (true, true, true, some true, true) := by
  native_decide

/-! ## Explicit open, stable selection, and negative consumption -/

/-- Reconstruct and rerun the independently checked model used by the
executable recursive literal. -/
def openedPrepared? := Encoding.prepare Context.nil.core.layout
  executableFunctionSignature executableFunctionSignatureValid
    executableFunctionRealization

example : openedPrepared?.isOk = true := by native_decide

def openedPrepared := openedPrepared?.toOption.get (by native_decide)

def openedModel? := Model.check? openedPrepared (ambientCompiler Context.nil)

example : openedModel?.isSome = true := by native_decide

def openedModel := openedModel?.get (by native_decide)

/-- Metrics extracted from the actual nested compiled term. -/
def openedProgramCompilation :
    DOTCaptureToManySortedFC.ModalIntersections.CompilerMetrics.CompilationReport :=
  DOTCaptureToManySortedFC.ModalIntersections.CompilerMetrics.ofCompiledTerm
    openedProgramCompiled

/-- Model statistics reconstructed and rechecked from the recursive literal's
source signature. The nested `CompiledTerm` currently retains no pointer to
that internal positive-object finalization, so these statistics are reported
separately rather than combined under a false provenance claim. -/
def openedReconstructedModelStats : RecursiveModelStats :=
  recursiveModelStats openedModel

/-- This one source program contains the recursive literal, its explicit
open, a stable negative consumer, and the object application. -/
example :
    (openedProgramCompilation.source.objects,
      openedProgramCompilation.source.objectLets,
      openedProgramCompilation.source.objectConsumers,
      openedProgramCompilation.source.objectApplications,
      openedProgramCompilation.source.applications,
      openedProgramCompilation.source.selections) =
      (1, 1, 1, 1, 1, 1) := by
  native_decide

/-- The recursive object is packaged and opened exactly once.  Static model
application erases, leaving the source let and the two real applications. -/
example :
    (openedProgramCompilation.target.packages,
      openedProgramCompilation.target.opens,
      openedProgramCompilation.runtime.lets,
      openedProgramCompilation.runtime.lambdas,
      openedProgramCompilation.runtime.applications) =
      (1, 1, 1, 2, 2) := by
  native_decide

/-- The complete emitted artifact contains four appearances of the
four-symbol, eight-constraint recursive object theory. -/
example :
    (openedProgramCompilation.certificate.theorySites,
      openedProgramCompilation.certificate.theorySymbols,
      openedProgramCompilation.certificate.theoryConstraints,
      openedProgramCompilation.certificate.symbolArguments,
      openedProgramCompilation.certificate.evidenceArguments,
      openedProgramCompilation.certificate.evidenceNodes) =
      (4, 16, 32, 8, 16, 65) := by
  native_decide

example :
    (openedReconstructedModelStats.checkedTheorySymbols,
      openedReconstructedModelStats.checkedTheoryConstraints,
      openedReconstructedModelStats.modelSymbolArguments,
      openedReconstructedModelStats.modelEvidenceArguments,
      openedReconstructedModelStats.modelEvidenceNodes) =
      (4, 8, 4, 8, 11) := by
  native_decide

example : openedReconstructedModelStats.modelCheckerAccepted = true := by
  native_decide

example :
    (openedProgramCompilation.checkerAccepted,
      openedProgramCompilation.checkerIndicesMatch,
      openedProgramCompilation.valueCheckerAccepted,
      openedProgramCompilation.literalErasureMatches) =
      (true, true, none, true) := by
  native_decide

end DOTCaptureToManySortedFC.RecursiveObjects.CompilerMetricsExamples
