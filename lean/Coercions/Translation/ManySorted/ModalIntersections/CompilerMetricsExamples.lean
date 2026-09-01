import Coercions.Translation.ManySorted.ModalIntersections.CompilerExamples
import Coercions.Translation.ManySorted.ModalIntersections.CompilerMetrics

/-!
# Cumulative compiler metric regressions

The examples cover each target boundary counted by `TargetStats`, rerun the
standalone checker through `CompilationReport`, and include a malformed
candidate so a report cannot inherit success from a source derivation.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.CompilerMetricsExamples

open DOTCaptureToManySortedFC.ModalIntersections.CompilerExamples
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.CompilerMetrics

def betaReport : CompilationReport := ofCompiledTerm betaCompiled
def zetaReport : CompilationReport := ofCompiledTerm zetaCompiled
def staticReport : CompilationReport := ofCompiledTerm staticCompiled
def openReport : CompilationReport := ofCompiledTerm openCompiled
def modalReport : CompilationReport := ofCompiledTerm modalCompiled
def objectReport : CompilationReport := ofCompiledTerm objectCompiled
def adapterReport : CompilationReport := ofCompiledTerm adapterCompiled
def useReport : CompilationReport := ofCompiledTerm useCompiled
def objectConsumerReport : CompilationReport :=
  ofCompiledValue objectConsumerCompiled
def canonicalObjectApplicationReport : CompilationReport :=
  ofCompiledTerm EmbeddedM11.canonicalCompiled
def openedObjectApplicationReport : CompilationReport :=
  ofCompiledTerm EmbeddedM11.openedCompiled
def mergedCanonicalObjectApplicationReport : CompilationReport :=
  ofCompiledTerm EmbeddedM11.mergedCanonicalCompiled
def mergedOpenedObjectApplicationReport : CompilationReport :=
  ofCompiledTerm EmbeddedM11.mergedOpenedCompiled
def computedOpenedObjectApplicationReport : CompilationReport :=
  ofCompiledTerm EmbeddedM11.computedOpenedCompiled
def capturingObjectApplicationReport : CompilationReport :=
  ofCompiledTerm CapturingObjectApplication.applicationCompiled

/-! The source layer counts explicit returns and values; target and runtime
layers do not. -/

example : betaReport.source.termNodes = 4 := by native_decide
example : betaReport.source.valueNodes = 3 := by native_decide
example : betaReport.source.lambdas = 1 := by native_decide
example : betaReport.source.applications = 1 := by native_decide

example : betaReport.target.termNodes = 4 := by native_decide
example : betaReport.target.lambdas = 1 := by native_decide
example : betaReport.target.applications = 1 := by native_decide
example : betaReport.runtime.nodes = 4 := by native_decide

example : zetaReport.source.lets = 1 := by native_decide
example : zetaReport.target.lets = 1 := by native_decide
example : zetaReport.runtime.lets = 1 := by native_decide

/-! Static, existential, and modal boundaries remain visible in the annotated
target and disappear or become ordinary runtime constructs after erasure. -/

example : staticReport.target.staticLambdas = 1 := by native_decide
example : staticReport.target.staticApplications = 1 := by native_decide
example : staticReport.runtime.nodes = 1 := by native_decide

example : openReport.target.packages = 1 := by native_decide
example : openReport.target.opens = 1 := by native_decide
example : openReport.runtime.lets = 1 := by native_decide

example : modalReport.target.modalLocks = 1 := by native_decide
example : modalReport.target.modalUnlocks = 1 := by native_decide
example : modalReport.runtime.suspensions = 1 := by native_decide
example : modalReport.runtime.forces = 1 := by native_decide

example : objectReport.source.objects = 1 := by native_decide
example : objectReport.target.packages = 1 := by native_decide
example : objectReport.runtime.nodes = 1 := by native_decide

/-! Even the empty user interface carries the generated `C_rep` symbol,
`repExact`, and `repCapture`. These are certificate nodes, not runtime nodes. -/

example : objectReport.certificate.theorySites = 1 := by native_decide
example : objectReport.certificate.theorySymbols = 1 := by native_decide
example : objectReport.certificate.theoryConstraints = 2 := by native_decide
example : objectReport.certificate.symbolArguments = 1 := by native_decide
example : objectReport.certificate.evidenceArguments = 2 := by native_decide
example : objectReport.certificate.evidenceNodes = 5 := by native_decide

/-! The negative consumer reuses the same one-symbol, two-constraint object
contract under static abstraction. No model arguments exist until use. -/

example : objectConsumerReport.source.objectConsumers = 1 := by native_decide
example : objectConsumerReport.target.staticLambdas = 1 := by native_decide
example : objectConsumerReport.target.lambdas = 1 := by native_decide
example : objectConsumerReport.certificate.theorySites = 1 := by
  native_decide
example : objectConsumerReport.certificate.theorySymbols = 1 := by
  native_decide
example : objectConsumerReport.certificate.theoryConstraints = 2 := by
  native_decide
example : objectConsumerReport.certificate.symbolArguments = 0 := by
  native_decide
example : objectConsumerReport.certificate.evidenceArguments = 0 := by
  native_decide
example : objectConsumerReport.checkerAccepted = true := by native_decide
example : objectConsumerReport.valueCheckerAccepted = some true := by
  native_decide
example : objectConsumerReport.literalErasureMatches = true := by
  native_decide

/-! Canonical and stable negative uses apply the model directly. The only
package/open pairs below are the source object lets themselves. -/

example : canonicalObjectApplicationReport.source.objectApplications = 1 := by
  native_decide
example : canonicalObjectApplicationReport.target.applications = 1 := by
  native_decide
example : canonicalObjectApplicationReport.target.staticApplications = 1 := by
  native_decide
example : canonicalObjectApplicationReport.target.packages = 0 := by
  native_decide
example : canonicalObjectApplicationReport.target.opens = 0 := by
  native_decide

example : openedObjectApplicationReport.source.objectApplications = 1 := by
  native_decide
example : openedObjectApplicationReport.source.objectLets = 1 := by
  native_decide
example : openedObjectApplicationReport.target.applications = 1 := by
  native_decide
example : openedObjectApplicationReport.target.staticApplications = 1 := by
  native_decide
example : openedObjectApplicationReport.target.packages = 1 := by
  native_decide
example : openedObjectApplicationReport.target.opens = 1 := by
  native_decide

example : mergedCanonicalObjectApplicationReport.target.packages = 0 := by
  native_decide
example : mergedCanonicalObjectApplicationReport.target.opens = 0 := by
  native_decide
example : mergedCanonicalObjectApplicationReport.target.applications = 1 := by
  native_decide
example : mergedCanonicalObjectApplicationReport.target.staticApplications =
    1 := by
  native_decide

example : mergedOpenedObjectApplicationReport.source.objectLets = 1 := by
  native_decide
example : mergedOpenedObjectApplicationReport.target.packages = 1 := by
  native_decide
example : mergedOpenedObjectApplicationReport.target.opens = 1 := by
  native_decide

example : computedOpenedObjectApplicationReport.source.objectLets = 2 := by
  native_decide
example : computedOpenedObjectApplicationReport.target.packages = 2 := by
  native_decide
example : computedOpenedObjectApplicationReport.target.opens = 2 := by
  native_decide

/-! Contract counts include `C_rep`, `repExact`, `repCapture`, and the
member-model certificates at every theory boundary. -/

example : canonicalObjectApplicationReport.certificate.theorySites = 2 := by
  native_decide
example : canonicalObjectApplicationReport.certificate.theorySymbols = 4 := by
  native_decide
example : canonicalObjectApplicationReport.certificate.theoryConstraints =
    8 := by
  native_decide
example : canonicalObjectApplicationReport.certificate.symbolArguments = 2 := by
  native_decide
example : canonicalObjectApplicationReport.certificate.evidenceArguments =
    4 := by
  native_decide

example : openedObjectApplicationReport.certificate.theorySites = 4 := by
  native_decide
example : openedObjectApplicationReport.certificate.theorySymbols = 14 := by
  native_decide
example : openedObjectApplicationReport.certificate.theoryConstraints = 36 := by
  native_decide
example : openedObjectApplicationReport.certificate.symbolArguments = 7 := by
  native_decide
example : openedObjectApplicationReport.certificate.evidenceArguments = 18 := by
  native_decide

example : mergedCanonicalObjectApplicationReport.certificate.theorySymbols =
    10 := by
  native_decide
example : mergedCanonicalObjectApplicationReport.certificate.theoryConstraints =
    28 := by
  native_decide
example : mergedCanonicalObjectApplicationReport.certificate.symbolArguments =
    5 := by
  native_decide
example : mergedCanonicalObjectApplicationReport.certificate.evidenceArguments =
    14 := by
  native_decide

example : computedOpenedObjectApplicationReport.certificate.theorySites = 6 := by
  native_decide
example : computedOpenedObjectApplicationReport.certificate.theorySymbols =
    24 := by
  native_decide
example : computedOpenedObjectApplicationReport.certificate.theoryConstraints =
    64 := by
  native_decide

example : canonicalObjectApplicationReport.checkerAccepted = true := by
  native_decide
example : canonicalObjectApplicationReport.checkerIndicesMatch = true := by
  native_decide
example : canonicalObjectApplicationReport.literalErasureMatches = true := by
  native_decide
example : openedObjectApplicationReport.checkerAccepted = true := by
  native_decide
example : openedObjectApplicationReport.checkerIndicesMatch = true := by
  native_decide
example : openedObjectApplicationReport.literalErasureMatches = true := by
  native_decide
example : mergedCanonicalObjectApplicationReport.checkerAccepted = true := by
  native_decide
example : mergedCanonicalObjectApplicationReport.literalErasureMatches =
    true := by
  native_decide
example : mergedOpenedObjectApplicationReport.checkerAccepted = true := by
  native_decide
example : mergedOpenedObjectApplicationReport.literalErasureMatches = true := by
  native_decide
example : computedOpenedObjectApplicationReport.checkerAccepted = true := by
  native_decide
example : computedOpenedObjectApplicationReport.literalErasureMatches = true := by
  native_decide

example : capturingObjectApplicationReport.source.objectApplications = 1 := by
  native_decide
example : capturingObjectApplicationReport.target.applications = 1 := by
  native_decide
example : capturingObjectApplicationReport.target.staticApplications = 1 := by
  native_decide
example : capturingObjectApplicationReport.target.packages = 0 := by
  native_decide
example : capturingObjectApplicationReport.target.opens = 0 := by
  native_decide
example : capturingObjectApplicationReport.certificate.theorySymbols = 2 := by
  native_decide
example : capturingObjectApplicationReport.certificate.theoryConstraints =
    4 := by
  native_decide
example : capturingObjectApplicationReport.certificate.symbolArguments = 1 := by
  native_decide
example : capturingObjectApplicationReport.certificate.evidenceArguments = 2 := by
  native_decide
example : capturingObjectApplicationReport.checkerAccepted = true := by
  native_decide
example : capturingObjectApplicationReport.checkerIndicesMatch = true := by
  native_decide
example : capturingObjectApplicationReport.literalErasureMatches = true := by
  native_decide

example : adapterReport.target.adapterSites = 1 := by native_decide
example : adapterReport.target.adapterNodes = 1 := by native_decide
example : adapterReport.runtime.nodes = 1 := by native_decide

example : useReport.target.uses = 1 := by native_decide
example : useReport.runtime.nodes = 1 := by native_decide

/-! Reports rerun checking and compare against independent source erasure. -/

example : betaReport.checkerAccepted = true := by native_decide
example : betaReport.checkerIndicesMatch = true := by native_decide
example : betaReport.valueCheckerAccepted = none := by native_decide
example : betaReport.literalErasureMatches = true := by native_decide

example : openReport.checkerAccepted = true := by native_decide
example : openReport.checkerIndicesMatch = true := by native_decide
example : openReport.literalErasureMatches = true := by native_decide

example : modalReport.checkerAccepted = true := by native_decide
example : modalReport.checkerIndicesMatch = true := by native_decide
example : modalReport.literalErasureMatches = true := by native_decide

def rejectedReport : CompilationReport :=
  reportTerm Core.nil Source.beta Source.closedUse .one
    (.app .unit .unit)

example : rejectedReport.checkerAccepted = false := by native_decide
example : rejectedReport.checkerIndicesMatch = false := by native_decide
example : rejectedReport.literalErasureMatches = false := by native_decide

end DOTCaptureToManySortedFC.ModalIntersections.CompilerMetricsExamples
