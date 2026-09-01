import Coercions.Translation.ManySorted.ModalIntersections.ModalProvenance

/-! Focused regressions for proof-relevant modal coordinates and evidence. -/

namespace DOTCaptureToManySortedFC.ModalIntersections.ModalProvenanceExamples

open DOTCaptureToManySortedFC.ModalIntersections

namespace SourceExamples

def modes : Source.ModeContext [.writable, .readOnly] [] :=
  .cons (.cons .nil .empty) .empty

def separation : Source.SeparationContext 2 [] :=
  .cons (.cons .nil .empty) .empty

def requirements : Source.ModalRequirements 2 [.writable, .readOnly] [] :=
  .mk separation modes

/-- Both mode tags retain distinct proof coordinates. -/
example : modeReference
    (context := modes)
    (DOTCapture.ModalIntersections.ModeContext.Occurs.here) =
      ManySortedFC.ConstraintRef.here := rfl

example : modeReference
    (context := modes)
    (DOTCapture.ModalIntersections.ModeContext.Occurs.there
      DOTCapture.ModalIntersections.ModeContext.Occurs.here) =
      ManySortedFC.ConstraintRef.there ManySortedFC.ConstraintRef.here := rfl

/-- The same canonical pair is read directly in newest-to-older order. -/
example : (separationReference
    (context := separation)
    (DOTCapture.ModalIntersections.SeparationContext.Position.Distinct.hereThere
      DOTCapture.ModalIntersections.SeparationContext.Position.here)).orientation =
      SeparationOrientation.forward := rfl

/-- Reversing the source positions records exactly one symmetry step. -/
example : (separationReference
    (context := separation)
    (DOTCapture.ModalIntersections.SeparationContext.Position.Distinct.thereHere
      DOTCapture.ModalIntersections.SeparationContext.Position.here)).orientation =
      SeparationOrientation.reverse := rfl

def satisfaction : DOTCapture.ModalIntersections.Satisfies
    DOTCapture.ModalIntersections.Ctx.nil .nil requirements :=
  .mk
    (fun occurrence =>
      match occurrence with
      | .here => .empty .writable
      | .there .here => .empty .readOnly)
    (fun _ _ distinct =>
      match distinct with
      | .hereThere .here => .empty .empty
      | .thereHere .here => .symm (.empty .empty))

end SourceExamples

def emptyCaptureCompiler : JudgmentCompiler
    DOTCapture.ModalIntersections.Ctx.nil
    DOTCapture.ModalIntersections.ModalAssumptions.nil
    ManySortedFC.Ctx.nil
    (fun _ => (.empty : Target.Capture [])) where
  mode := fun _ =>
    { evidence := .modeEmpty _
      typing := .modeEmpty _ }
  separate := fun _ =>
    { evidence := .separateEmpty .empty
      typing := .separateEmpty .empty }

def compiledSatisfaction : CompiledSatisfaction
    ManySortedFC.Ctx.nil
    (fun _ => (.empty : Target.Capture []))
    SourceExamples.requirements :=
  compileSatisfies emptyCaptureCompiler SourceExamples.satisfaction

/-- Satisfaction emits modes first, then the single canonical unordered
separation pair. -/
example : compiledSatisfaction.evidence =
    ManySortedFC.EvidenceArgs.cons (.modeEmpty .writable)
      (ManySortedFC.EvidenceArgs.cons (.modeEmpty .readOnly)
        (ManySortedFC.EvidenceArgs.cons (.separateEmpty .empty)
          ManySortedFC.EvidenceArgs.nil)) := rfl

noncomputable def firstActive :=
  (ActiveProvenance.nil ManySortedFC.Ctx.nil
    (fun _ => (.empty : Target.Capture []))).push
      SourceExamples.separation SourceExamples.modes

noncomputable def nestedActive :=
  firstActive.push SourceExamples.separation SourceExamples.modes

/-- Duplicate active frames retain distinct target evidence blocks. -/
example : (nestedActive.modeLock
    DOTCapture.ModalIntersections.ModalAssumptions.Lookup.here
    DOTCapture.ModalIntersections.ModeContext.Occurs.here).evidence =
      ManySortedFC.Evidence.var ManySortedFC.BVar.here := rfl

example : (nestedActive.modeLock
    (DOTCapture.ModalIntersections.ModalAssumptions.Lookup.there
      DOTCapture.ModalIntersections.ModalAssumptions.Lookup.here)
    DOTCapture.ModalIntersections.ModeContext.Occurs.here).evidence =
      ManySortedFC.Evidence.var
        (ManySortedFC.BVar.there
          (ManySortedFC.BVar.there
            (ManySortedFC.BVar.there ManySortedFC.BVar.here))) := rfl

/-- Both source orientations select the same pair variable; reverse order
adds exactly one symmetry constructor. -/
example : (firstActive.separateLock
    DOTCapture.ModalIntersections.ModalAssumptions.Lookup.here
    DOTCapture.ModalIntersections.SeparationContext.Position.here
    (DOTCapture.ModalIntersections.SeparationContext.Position.there
      DOTCapture.ModalIntersections.SeparationContext.Position.here)
    (DOTCapture.ModalIntersections.SeparationContext.Position.Distinct.hereThere
      DOTCapture.ModalIntersections.SeparationContext.Position.here)).evidence =
      ManySortedFC.Evidence.var
        (ManySortedFC.BVar.there
          (ManySortedFC.BVar.there ManySortedFC.BVar.here)) := rfl

example : (firstActive.separateLock
    DOTCapture.ModalIntersections.ModalAssumptions.Lookup.here
    (DOTCapture.ModalIntersections.SeparationContext.Position.there
      DOTCapture.ModalIntersections.SeparationContext.Position.here)
    DOTCapture.ModalIntersections.SeparationContext.Position.here
    (DOTCapture.ModalIntersections.SeparationContext.Position.Distinct.thereHere
      DOTCapture.ModalIntersections.SeparationContext.Position.here)).evidence =
      ManySortedFC.Evidence.separateSymm
        (ManySortedFC.Evidence.var
          (ManySortedFC.BVar.there
            (ManySortedFC.BVar.there ManySortedFC.BVar.here))) := rfl

end DOTCaptureToManySortedFC.ModalIntersections.ModalProvenanceExamples
