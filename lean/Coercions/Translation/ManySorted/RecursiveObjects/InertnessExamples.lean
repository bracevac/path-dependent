import Coercions.Translation.ManySorted.RecursiveObjects.ModelExamples
import Coercions.Translation.ManySorted.RecursiveObjects.Inertness

/-! # Exact recursive-member projection regressions -/

namespace DOTCaptureToManySortedFC.RecursiveObjects.InertnessExamples

open DOTCaptureToManySortedFC.RecursiveObjects
open DOTCaptureToManySortedFC.RecursiveObjects.EncodingExamples
open DOTCaptureToManySortedFC.RecursiveObjects.Inertness
open DOTCaptureToManySortedFC.RecursiveObjects.ModelExamples
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext

noncomputable def projection :=
  structuralTypeProjection ManySortedFC.Ctx.nil prepared

example : SourceExamples.signature.typeLabels.Nodup :=
  projection.sourceLabelsUnique
example : forall label,
    Source.captureAmbientOnly (realization.captures.witness label) = true :=
  projection.captureWitnessesAmbient

noncomputable example : SourceExamples.signature.captureDeclarations.Realizes
    DOTCapture.ModalIntersections.Ctx.nil realization.captures :=
  projection.captureTheoryRealized

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

/-! ## Projection through the independently accepted model -/

noncomputable def realizedProjection :=
  realizedTypeProjection Core.nil prepared ambient checkedModel

example : ManySortedFC.Theory.checkModel Core.nil.target
    prepared.object.theory checkedModel.model.symbols
      checkedModel.model.evidence = some checkedModel.model.checked :=
  realizedProjection.standaloneModelAcceptance

/-- The public interpretation used by the accepted model is the exact
recursive projection for source member `A`. -/
noncomputable def realizedA := realizedProjection.members ⟨0, by decide⟩

example : prepared.targetLocalModel.typeMember? 1 =
    some (.recProj prepared.bodies ⟨0, by decide⟩) :=
  realizedA.targetInterpretation

/-- Both retained M11 interval coordinates have ambient certificates in the
accepted model. -/
example : Nonempty (ManySortedFC.Evidence.Proves Core.nil.target
    (checkedModel.model.checked.evidence.lookup
      (memberConstraintRef realizedA.structural.coordinates.lower))
    (ManySortedFC.Proposition.instantiateSymbols
      (prepared.object.theory.propositionAt
        (memberConstraintRef realizedA.structural.coordinates.lower))
      checkedModel.model.checked.symbols)) :=
  ⟨realizedA.modelLower⟩

example : Nonempty (ManySortedFC.Evidence.Proves Core.nil.target
    (checkedModel.model.checked.evidence.lookup
      (memberConstraintRef realizedA.structural.coordinates.upper))
    (ManySortedFC.Proposition.instantiateSymbols
      (prepared.object.theory.propositionAt
        (memberConstraintRef realizedA.structural.coordinates.upper))
      checkedModel.model.checked.symbols)) :=
  ⟨realizedA.modelUpper⟩

/-- Ordinary exact-member inertness is obtained by forgetting the surrounding
capture/model components. -/
noncomputable def ordinaryA := realizedProjection.typeProjection ⟨0, by decide⟩

example : ordinaryA.targetInterpretation = realizedA.targetInterpretation :=
  rfl

example : Nonempty
    (OrdinaryExactTypeMemberInertness (core := Core.nil) prepared
      ⟨0, by decide⟩) :=
  ordinaryExactTypeMemberInertness_is_typeProjection realizedProjection
    ⟨0, by decide⟩

/-! ## Recursive capture theory and non-unit representation -/

def recursiveCaptureModel := recursiveCaptureCheckedModel?.get
  (by native_decide)

noncomputable def recursiveCaptureProjection := realizedTypeProjection
  Core.nil recursiveCapturePrepared ambient recursiveCaptureModel

noncomputable example : recursiveCaptureSignature.captureDeclarations.Realizes
    DOTCapture.ModalIntersections.Ctx.nil
      recursiveCaptureRealization.captures :=
  recursiveCaptureProjection.simultaneousCaptureRealization

example : ManySortedFC.Theory.checkModel Core.nil.target
    recursiveCapturePrepared.object.theory
      recursiveCaptureModel.model.symbols
      recursiveCaptureModel.model.evidence =
        some recursiveCaptureModel.model.checked :=
  recursiveCaptureProjection.standaloneModelAcceptance

noncomputable def dependentRepresentationProjection := realizedTypeProjection
  Core.nil dependentRepresentationPrepared ambient
    dependentRepresentationCheckedModel

example : dependentRepresentationPrepared.targetLocalModel.typeMember? 20 =
    some (.recProj dependentRepresentationPrepared.bodies ⟨0, by decide⟩) :=
  (dependentRepresentationProjection.members
    ⟨0, by decide⟩).targetInterpretation

example : ambient.compile
    dependentRepresentationRealization.representationContainment =
      some dependentRepresentationCheckedModel.containmentEvidence :=
  dependentRepresentationProjection.representationContainmentCompiled

end DOTCaptureToManySortedFC.RecursiveObjects.InertnessExamples
