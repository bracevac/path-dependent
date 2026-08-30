import Coercions.Translation.ManySorted.BinderOnly.ContextEvidence
import Coercions.Translation.ManySorted.BinderOnly.LayoutExamples

/-!
# Evidence-elaboration regressions

These examples use the canonical context compiler for characteristic bad type
and capture intervals. They connect the source derivations—not merely the
source syntax—to the explicit target evidence variables.
-/

namespace DOTCaptureToManySortedFC.BinderOnly.EvidenceExamples

open LayoutExamples

/-- Compiling the source's explicit lower-then-upper derivation produces the
target's explicit transitivity certificate over the two interval slots. -/
def compiledBadTypeCollapse :=
  compileIncludes (contextBoundCompiler badTypeContext)
    DOTCapture.BinderOnly.BadBoundsExamples.topIncludesBottom

@[simp]
theorem compiled_bad_type_evidence_shape :
    compiledBadTypeCollapse.evidence =
      ManySortedFC.Evidence.inclusionTrans
        (.var .here) (.var (.there .here)) := rfl

def compiled_bad_type_collapse_is_typed :
    ManySortedFC.Evidence.Proves
      (translateContext badTypeContext)
      compiledBadTypeCollapse.evidence
      (.inclusion (.type .top) (.type .bot)) :=
  compiledBadTypeCollapse.typing

/-- Older static slots remain canonical after unrelated source extensions. -/
def badTypeThenTermContext :
    DOTCapture.BinderOnly.Ctx
      (([] ▹ .static .type) ▹ .term) :=
  badTypeContext.extendTerm .one

def olderBadTypeUpper :
    DOTCapture.BinderOnly.HasUpper badTypeThenTermContext
      (.bound (.there .here)) (.type .bot) :=
  .bound (lower := .some (.type .top)) rfl

def olderBadTypeInclusion :
    DOTCapture.BinderOnly.Includes badTypeThenTermContext
      (.type (.ref (.bound (.there .here)))) (.type .bot) :=
  .upper olderBadTypeUpper

def compiledOlderBadTypeUpper :=
  compileIncludes (contextBoundCompiler badTypeThenTermContext)
    olderBadTypeInclusion

@[simp]
theorem compiled_older_bound_is_weakened_exactly_once :
    compiledOlderBadTypeUpper.evidence =
      ManySortedFC.Evidence.var (.there (.there .here)) := rfl

/-! ## Capture intervals use the same compiler -/

def compiledBadCaptureCollapse :=
  compileIncludes (contextBoundCompiler badCaptureContext)
    DOTCapture.BinderOnly.BadBoundsExamples.singletonIncludesEmpty

@[simp]
theorem compiled_bad_capture_evidence_shape :
    compiledBadCaptureCollapse.evidence =
      ManySortedFC.Evidence.inclusionTrans
        (.var .here) (.var (.there .here)) := rfl

def compiled_bad_capture_collapse_is_typed :
    ManySortedFC.Evidence.Proves
      (translateContext badCaptureContext)
      compiledBadCaptureCollapse.evidence
      (.inclusion
        (.capture
          (translateCapture badCaptureContext
            (.singleton
              DOTCapture.BinderOnly.BadBoundsExamples.capability)))
        (.capture .empty)) :=
  compiledBadCaptureCollapse.typing

end DOTCaptureToManySortedFC.BinderOnly.EvidenceExamples
