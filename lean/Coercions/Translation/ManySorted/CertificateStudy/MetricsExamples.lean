import Coercions.Translation.ManySorted.CertificateStudy.Metrics
import Coercions.Translation.ManySorted.ModalIntersections.AdapterElaborationExamples
import Coercions.Translation.ManySorted.ModalIntersections.CompilerExamples

/-!
# Certificate-study metric regressions

The small examples distinguish a literal compiler artifact from a checked
eta-producing function adapter.  The larger snapshots reuse the cumulative
opened-object programs so certificate growth is measured on actual compiler
output rather than only on synthetic proof trees.
-/

namespace DOTCaptureToManySortedFC.CertificateStudy.MetricsExamples

open DOTCaptureToManySortedFC.CertificateStudy.Metrics
open DOTCaptureToManySortedFC.ModalIntersections.CompilerExamples

def beta : Overhead := overhead betaCompiled.term
def openedObject : Overhead := overhead EmbeddedM11.openedCompiled.term
def computedOpenedObjects : Overhead :=
  overhead EmbeddedM11.computedOpenedCompiled.term

/-! ## A checked eta-producing adapter -/

namespace EtaHeavy

open DOTCaptureToManySortedFC.ModalIntersections.AdapterElaborationExamples

/-- A closed target function at the source endpoint of the compiled function
adapter. -/
def sourceFunction : ManySortedFC.Tm [] :=
  .lam .top .one .empty .unit
    (.captureEmpty (.union .empty (.singleton .here)))

/-- The real structural adapter eta-expands this value during erasure. -/
def adapted : ManySortedFC.Tm [] :=
  .adapt sourceFunction
    (.captured (.inclusionRefl (.capture .empty))
      functionCompiled.adapter)

example : (ManySortedFC.Tm.check .nil adapted).isSome = true := by
  native_decide

def report : Overhead := overhead adapted

example :
    (report.adapterSites, report.adapterNodes,
      report.runtimeNodesWithoutAdapters, report.runtimeNodes,
      report.adapterRuntimeNodeDelta) = (1, 4, 2, 7, 5) := by
  native_decide

/-- The measurement does not silently call eta expansion "erasure equality". -/
example : adapted.erase ≠ eraseWithoutAdapters adapted := by
  native_decide

end EtaHeavy

/-! ## Compiler-corpus snapshots -/

example :
    (beta.annotatedTermNodes, beta.logicalEvidenceNodes, beta.runtimeNodes,
      beta.adapterRuntimeNodeDelta) = (4, 1, 4, 0) := by
  native_decide

example :
    (openedObject.annotatedTermNodes,
      openedObject.logicalEvidenceNodes,
      openedObject.theorySymbols,
      openedObject.theoryConstraints,
      openedObject.modelEvidenceArguments,
      openedObject.runtimeNodes) = (19, 61, 14, 36, 18, 6) := by
  native_decide

example :
    (computedOpenedObjects.annotatedTermNodes,
      computedOpenedObjects.logicalEvidenceNodes,
      computedOpenedObjects.theorySymbols,
      computedOpenedObjects.theoryConstraints,
      computedOpenedObjects.modelEvidenceArguments,
      computedOpenedObjects.runtimeNodes) = (24, 81, 24, 64, 32, 8) := by
  native_decide

/-- Evidence and annotated-syntax percentages are ratios against the actual
runtime term, not percentages of some manually selected source subset. -/
example :
    (openedObject.evidencePerRuntimePercent,
      openedObject.annotatedPerRuntimePercent) = (1016, 316) := by
  native_decide

end DOTCaptureToManySortedFC.CertificateStudy.MetricsExamples
