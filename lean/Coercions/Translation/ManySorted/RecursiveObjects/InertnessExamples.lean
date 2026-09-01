import Coercions.Translation.ManySorted.RecursiveObjects.EncodingExamples
import Coercions.Translation.ManySorted.RecursiveObjects.Inertness

/-! # Exact recursive-member projection regressions -/

namespace DOTCaptureToManySortedFC.RecursiveObjects.InertnessExamples

open DOTCaptureToManySortedFC.RecursiveObjects
open DOTCaptureToManySortedFC.RecursiveObjects.EncodingExamples
open DOTCaptureToManySortedFC.RecursiveObjects.Inertness

noncomputable def projection :=
  structuralTypeProjection ManySortedFC.Ctx.nil prepared

example : SourceExamples.signature.typeLabels.Nodup :=
  projection.sourceLabelsUnique
example : SourceExamples.signature.captureDeclarations.ambientOnly :=
  projection.captureTheoryAcyclic

noncomputable def exactA := projection.exact ⟨0, by decide⟩
noncomputable def exactB := projection.exact ⟨1, by decide⟩

example : Encoding.publicTypeWitness? prepared.object prepared.memberSymbols 1 =
    some (.recProj prepared.bodies ⟨0, by decide⟩) :=
  (projection.publicAligned ⟨0, by decide⟩).aligned

example : Encoding.publicTypeWitness? prepared.object prepared.memberSymbols 2 =
    some (.recProj prepared.bodies ⟨1, by decide⟩) :=
  (projection.publicAligned ⟨1, by decide⟩).aligned

example :
    (ManySortedFC.Evidence.check ManySortedFC.Ctx.nil
      (.unfoldRec prepared.bodies ⟨0, by decide⟩)).map
        ManySortedFC.Evidence.Checked.proposition =
      some (.equality
        (.type (.recProj prepared.bodies ⟨0, by decide⟩))
        (.type (prepared.bodies.unfoldAt ⟨0, by decide⟩))) :=
  exactA.checkerAcceptance

example :
    (ManySortedFC.Evidence.check ManySortedFC.Ctx.nil
      (.unfoldRec prepared.bodies ⟨1, by decide⟩)).map
        ManySortedFC.Evidence.Checked.proposition =
      some (.equality
        (.type (.recProj prepared.bodies ⟨1, by decide⟩))
        (.type (prepared.bodies.unfoldAt ⟨1, by decide⟩))) :=
  exactB.checkerAcceptance

/-! ## Source occurrence coordinates under reversed public order -/

noncomputable def reversedProjection :=
  structuralTypeProjection ManySortedFC.Ctx.nil reversedPrepared

/-- Source slot zero is `B`, even though canonical public order places label
`A` first.  M11 retains that source occurrence's exact interval coordinates,
and the public `B` model witness is recursive slot zero. -/
noncomputable def reversedBAlignment :=
  reversedProjection.sourceOccurrences ⟨0, by decide⟩

example : Encoding.publicTypeWitness? reversedPrepared.object
    reversedPrepared.memberSymbols 2 =
      some (.recProj reversedPrepared.bodies ⟨0, by decide⟩) :=
  reversedBAlignment.publicWitness.aligned

example : Nonempty
    (DOTCaptureToManySortedFC.ModalIntersections.ConstraintRetention.TypeCoordinates
      DOTCaptureToManySortedFC.ModalIntersections.Layout.empty
      reversedPrepared.object.encoding.prepared 2
      { lower := .type SourceExamples.typeB.body
        upper := .type SourceExamples.typeB.body }) :=
  ⟨reversedBAlignment.coordinates⟩

example :
    (DOTCaptureToManySortedFC.Intersections.Encoding.encode
      reversedPrepared.object.encoding.prepared).theory.propositionAt
        reversedBAlignment.coordinates.lower =
      .inclusion reversedBAlignment.coordinates.translated.lower
        (.type (.tvar reversedBAlignment.coordinates.name)) :=
  reversedBAlignment.coordinates.lowerProposition

example :
    (DOTCaptureToManySortedFC.Intersections.Encoding.encode
      reversedPrepared.object.encoding.prepared).theory.propositionAt
        reversedBAlignment.coordinates.upper =
      .inclusion (.type (.tvar reversedBAlignment.coordinates.name))
        reversedBAlignment.coordinates.translated.upper :=
  reversedBAlignment.coordinates.upperProposition

end DOTCaptureToManySortedFC.RecursiveObjects.InertnessExamples
