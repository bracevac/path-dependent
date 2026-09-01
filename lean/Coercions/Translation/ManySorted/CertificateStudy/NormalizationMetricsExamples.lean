import Coercions.Translation.ManySorted.CertificateStudy.NormalizationMetrics
import Coercions.Translation.ManySorted.ModalIntersections.CompilerExamples
import Coercions.Translation.ManySorted.ModalIntersections.EvidenceElaborationExamples

/-!
# Evidence-normalization measurement regressions

The rechecked corpus mixes one real evidence item emitted by the cumulative
compiler's evidence elaborator with synthetic administrative stress trees.
The artifact figures are reported separately as syntax-only opportunities.
-/

namespace DOTCaptureToManySortedFC.CertificateStudy.NormalizationMetricsExamples

open ManySortedFC
open DOTCaptureToManySortedFC.CertificateStudy.NormalizationMetrics

/-! ## One real emitted certificate -/

/-- The cumulative source evidence compiler emits this explicit two-step
subcapture proof from `captureReadOnly` followed by `captureUnionLeft`. -/
def emittedInclusion :=
  DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaborationExamples.compiledStructuralCapture?.get
    (by native_decide)

def emittedMeasurement? : Option RecheckedMeasurement :=
  measureChecked Ctx.nil emittedInclusion.evidence

example : emittedMeasurement?.isSome = true := by native_decide

def emittedMeasurement : RecheckedMeasurement :=
  emittedMeasurement?.get (by native_decide)

example : emittedMeasurement =
    { beforeNodes := 3
      afterNodes := 3
      savedNodes := 0
      beforeDepth := 2
      afterDepth := 2
      savedDepth := 0
      strictlyReduced := false } := by
  native_decide

/-! ## Synthetic administrative stress -/

/-- Each layer adds two canceling symmetries and one reflexive transitivity
link.  All endpoints remain `One`, so every original tree is well checked. -/
def equalityStress : Nat -> Evidence (.equality .type) []
  | 0 => .equalityRefl (.type .one)
  | level + 1 =>
      .equalityTrans
        (.equalitySymm (.equalitySymm (equalityStress level)))
        (.equalityRefl (.type .one))

/-- Each layer embeds a reflexive equality as inclusion and composes it with
the previous reflexive inclusion. -/
def inclusionStress : Nat -> Evidence (.inclusion .type) []
  | 0 => .inclusionRefl (.type .one)
  | level + 1 =>
      .inclusionTrans
        (.equalityToInclusion
          (.equalitySymm
            (.equalitySymm (.equalityRefl (.type .one)))))
        (inclusionStress level)

/-- Repeated pairs of symmetry are administrative at separation relation. -/
def separationStress : Nat -> Evidence .separate []
  | 0 => .separateEmpty .empty
  | level + 1 => .separateSymm (.separateSymm (separationStress level))

def equalityMeasurement? : Option RecheckedMeasurement :=
  measureChecked Ctx.nil (equalityStress 8)

def inclusionMeasurement? : Option RecheckedMeasurement :=
  measureChecked Ctx.nil (inclusionStress 8)

def separationMeasurement? : Option RecheckedMeasurement :=
  measureChecked Ctx.nil (separationStress 8)

example : equalityMeasurement?.isSome = true := by native_decide
example : inclusionMeasurement?.isSome = true := by native_decide
example : separationMeasurement?.isSome = true := by native_decide

def equalityMeasurement : RecheckedMeasurement :=
  equalityMeasurement?.get (by native_decide)

def inclusionMeasurement : RecheckedMeasurement :=
  inclusionMeasurement?.get (by native_decide)

def separationMeasurement : RecheckedMeasurement :=
  separationMeasurement?.get (by native_decide)

def recheckedMeasurements : List RecheckedMeasurement :=
  [emittedMeasurement, equalityMeasurement, inclusionMeasurement,
    separationMeasurement]

def recheckedCorpus : RecheckedCorpus :=
  RecheckedCorpus.ofList recheckedMeasurements

example : equalityMeasurement =
    { beforeNodes := 33
      afterNodes := 1
      savedNodes := 32
      beforeDepth := 25
      afterDepth := 1
      savedDepth := 24
      strictlyReduced := true } := by
  native_decide

example : inclusionMeasurement =
    { beforeNodes := 41
      afterNodes := 1
      savedNodes := 40
      beforeDepth := 12
      afterDepth := 1
      savedDepth := 11
      strictlyReduced := true } := by
  native_decide

example : separationMeasurement =
    { beforeNodes := 17
      afterNodes := 1
      savedNodes := 16
      beforeDepth := 17
      afterDepth := 1
      savedDepth := 16
      strictlyReduced := true } := by
  native_decide

example : recheckedCorpus =
    { certificates := 4
      reducedCertificates := 3
      beforeNodes := 94
      afterNodes := 6
      savedNodes := 88
      beforeMaxDepth := 25
      afterMaxDepth := 2 } := by
  native_decide

/-! ## Whole compiled artifacts: opportunity estimates only -/

def simpleObjectOpportunity : Opportunity :=
  artifactOpportunity
    DOTCaptureToManySortedFC.ModalIntersections.CompilerExamples.objectCompiled.term

def mergedOpenOpportunity : Opportunity :=
  artifactOpportunity
    DOTCaptureToManySortedFC.ModalIntersections.CompilerExamples.EmbeddedM11.mergedOpenedCompiled.term

def compiledArtifactOpportunity : Opportunity :=
  simpleObjectOpportunity.add mergedOpenOpportunity

/-- The opportunity traversal sees exactly the same original evidence-node
total as the existing certificate counter on the simple emitted artifact. -/
example : simpleObjectOpportunity.beforeNodes =
    (DOTCaptureToManySortedFC.ModalIntersections.CompilerMetrics.certificateStats
      DOTCaptureToManySortedFC.ModalIntersections.CompilerExamples.objectCompiled.term).evidenceNodes := by
  native_decide

/-- The same accounting agreement holds for a larger package/open artifact. -/
example : mergedOpenOpportunity.beforeNodes =
    (DOTCaptureToManySortedFC.ModalIntersections.CompilerMetrics.certificateStats
      DOTCaptureToManySortedFC.ModalIntersections.CompilerExamples.EmbeddedM11.mergedOpenedCompiled.term).evidenceNodes := by
  native_decide

/-! These figures remain opportunity estimates: `artifactOpportunity` has not
rebuilt either dependent target term or rerun the standalone term checker. -/

example : simpleObjectOpportunity =
    { certificates := 5
      beforeNodes := 5
      candidateNodes := 5
      beforeMaxDepth := 1
      candidateMaxDepth := 1 } := by
  native_decide

example : mergedOpenOpportunity =
    { certificates := 46
      beforeNodes := 71
      candidateNodes := 67
      beforeMaxDepth := 4
      candidateMaxDepth := 3 } := by
  native_decide

example : compiledArtifactOpportunity =
    { certificates := 51
      beforeNodes := 76
      candidateNodes := 72
      beforeMaxDepth := 4
      candidateMaxDepth := 3 } := by
  native_decide

example : compiledArtifactOpportunity.savedNodes = 4 := by native_decide
example : compiledArtifactOpportunity.savedMaxDepth = 1 := by native_decide

end DOTCaptureToManySortedFC.CertificateStudy.NormalizationMetricsExamples
