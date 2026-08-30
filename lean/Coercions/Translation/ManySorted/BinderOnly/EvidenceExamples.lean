import Coercions.Translation.ManySorted.BinderOnly.EvidenceElaboration
import Coercions.Translation.ManySorted.BinderOnly.LayoutExamples

/-!
# Evidence-elaboration regressions

These examples discharge the layout invariant for the characteristic
one-binder bad type interval.  They connect the source derivation—not merely
the source syntax—to the explicit target evidence variables.
-/

namespace DOTCaptureToManySortedFC.BinderOnly.EvidenceExamples

open LayoutExamples

/-- The canonical generated-name layout implements both lookup cases of the
source `Top .. Bottom` interval. -/
def badTypeBoundCompiler : BoundCompiler badTypeContext where
  lower := by
    intro sort reference endpoint bound
    cases reference with
    | bound index =>
        cases index with
        | here =>
            cases bound with
            | bound found =>
                rename_i upper
                change DOTCapture.BinderOnly.Interval.bounds
                    (.some (.type .top)) (.some (.type .bot)) =
                  .bounds (.some endpoint) upper at found
                have pieces :=
                  Eq.mp
                    (DOTCapture.BinderOnly.Interval.bounds.injEq _ _ _ _)
                    found
                have endpointEquality :=
                  Eq.mp
                    (DOTCapture.BinderOnly.Endpoint.some.injEq _ _)
                    pieces.1
                cases endpointEquality
                exact
                  ⟨.var .here,
                    ManySortedTranslation.StaticSlot.proves_between_lower
                      ManySortedFC.Ctx.nil (.type .top) (.type .bot)⟩
        | there older => exact nomatch older
  upper := by
    intro sort reference endpoint bound
    cases reference with
    | bound index =>
        cases index with
        | here =>
            cases bound with
            | bound found =>
                rename_i lower
                change DOTCapture.BinderOnly.Interval.bounds
                    (.some (.type .top)) (.some (.type .bot)) =
                  .bounds lower (.some endpoint) at found
                have pieces :=
                  Eq.mp
                    (DOTCapture.BinderOnly.Interval.bounds.injEq _ _ _ _)
                    found
                have endpointEquality :=
                  Eq.mp
                    (DOTCapture.BinderOnly.Endpoint.some.injEq _ _)
                    pieces.2
                cases endpointEquality
                exact
                  ⟨.var (.there .here),
                    ManySortedTranslation.StaticSlot.proves_between_upper
                      ManySortedFC.Ctx.nil (.type .top) (.type .bot)⟩
        | there older => exact nomatch older

/-- Compiling the source's explicit lower-then-upper derivation produces the
target's explicit transitivity certificate over the two interval slots. -/
def compiledBadTypeCollapse :=
  compileIncludes badTypeBoundCompiler
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

/-! ## Capture intervals use the same compiler -/

/-- The same target slot invariant discharges the lower and upper lookup
rules for the source `{x} .. {}` capture interval. -/
def badCaptureBoundCompiler : BoundCompiler badCaptureContext where
  lower := by
    intro sort reference endpoint bound
    cases reference with
    | bound index =>
        cases index with
        | here =>
            cases bound with
            | bound found =>
                rename_i upper
                change DOTCapture.BinderOnly.Interval.bounds
                    (.some (.capture (.singleton (.var (.there .here)))))
                    (.some (.capture .empty)) =
                  .bounds (.some endpoint) upper at found
                have pieces := Eq.mp
                  (DOTCapture.BinderOnly.Interval.bounds.injEq _ _ _ _) found
                have endpointEquality := Eq.mp
                  (DOTCapture.BinderOnly.Endpoint.some.injEq _ _) pieces.1
                cases endpointEquality
                exact
                  ⟨.var .here,
                    ManySortedTranslation.StaticSlot.proves_between_lower
                      ManySortedFC.StaticExamples.capabilityContext
                      (.capture ManySortedFC.StaticExamples.ambientCapability)
                      (.capture .empty)⟩
        | there older => exact nomatch older
  upper := by
    intro sort reference endpoint bound
    cases reference with
    | bound index =>
        cases index with
        | here =>
            cases bound with
            | bound found =>
                rename_i lower
                change DOTCapture.BinderOnly.Interval.bounds
                    (.some (.capture (.singleton (.var (.there .here)))))
                    (.some (.capture .empty)) =
                  .bounds lower (.some endpoint) at found
                have pieces := Eq.mp
                  (DOTCapture.BinderOnly.Interval.bounds.injEq _ _ _ _) found
                have endpointEquality := Eq.mp
                  (DOTCapture.BinderOnly.Endpoint.some.injEq _ _) pieces.2
                cases endpointEquality
                exact
                  ⟨.var (.there .here),
                    ManySortedTranslation.StaticSlot.proves_between_upper
                      ManySortedFC.StaticExamples.capabilityContext
                      (.capture ManySortedFC.StaticExamples.ambientCapability)
                      (.capture .empty)⟩
        | there older => exact nomatch older

def compiledBadCaptureCollapse :=
  compileIncludes badCaptureBoundCompiler
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
