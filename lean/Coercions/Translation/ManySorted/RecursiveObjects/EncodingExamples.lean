import Coercions.Translation.ManySorted.RecursiveObjects.SourceExamples
import Coercions.Translation.ManySorted.RecursiveObjects.Encoding

/-!
# Source-indexed recursive encoding regressions

These checks isolate the allocation boundary from later package evidence.
Mutually recursive type labels become distinct self slots, capture members
are interpreted by an explicit simultaneous ambient model, and the target
type block is guarded.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.EncodingExamples

open DOTCaptureToManySortedFC.RecursiveObjects
open DOTCaptureToManySortedFC.RecursiveObjects.SourceExamples
open DOTCaptureToManySortedFC.RecursiveObjects.Encoding

def captureModel : Source.AmbientCaptureModel [] where
  witness := fun _ => .empty
  ambient := by intro; rfl

def realization : Source.Realization
    DOTCapture.ModalIntersections.Ctx.nil signature where
  captures := captureModel
  captureConstraints := .member .refl .refl
  representationContainment := .refl
  packageContainment := .refl

def prepared? := Encoding.prepare
  DOTCaptureToManySortedFC.ModalIntersections.Layout.empty signature
    signatureValid realization

example : prepared?.isOk = true := by native_decide

def prepared := prepared?.toOption.get (by native_decide)

example : prepared.bodies.headGuarded = true := prepared.guarded

/-- `A` is slot zero and its body refers to `B`, slot one. -/
example : prepared.bodies.get ⟨0, by decide⟩ =
    (.arr (.tvar (.there .here)) .one :
      ManySortedFC.Ty (ManySortedFC.TypeScope [] 2)) := by
  native_decide

/-- `B` refers back to `A`; its capture member has already become the
ambient empty witness rather than a recursive capture slot. -/
example : prepared.bodies.get ⟨1, by decide⟩ =
    (.capturing .empty (.tvar .here) :
      ManySortedFC.Ty (ManySortedFC.TypeScope [] 2)) := by
  native_decide

example : prepared.memberSymbols =
    (.cons (.type (.recProj prepared.bodies ⟨0, by decide⟩))
      (.cons (.type (.recProj prepared.bodies ⟨1, by decide⟩))
        (.cons (.capture .empty) .nil))) := by
  rfl

/-- The cumulative model has one additional, distinguished `C_rep`; it is not
one recursive slot per intersection component. -/
example : prepared.object.symbols =
    .capture :: prepared.object.memberSymbols := rfl

def recursiveCaptureType : Source.TypeDefinition [] where
  label := 10
  body := .arr .one .one

def recursiveCaptureConstraint : Source.CaptureInterface [] :=
  .member 11 (.ref (.localCaptureMember 11))
    (.readOnly (.ref (.localCaptureMember 11)))

def recursiveCaptureSignature : Source.Signature [] where
  typeDefinitions := [recursiveCaptureType]
  captureDeclarations := recursiveCaptureConstraint
  representation := .one
  outerCapture := .empty

/-- Local capture references are admitted by the cumulative boundary.  A
concrete model must still realize their constraints before packaging. -/
example : Encoding.checkBoundary recursiveCaptureSignature = .ok () := rfl

def recursiveCaptureValid : recursiveCaptureSignature.Valid where
  nonempty := by simp [recursiveCaptureSignature]
  typeLabelsNodup := by
    simp [Source.Signature.typeLabels, Source.TypeDefinitions.labels,
      recursiveCaptureSignature, recursiveCaptureType]
  labelsDisjoint := by
    intro label member
    simp [Source.Signature.typeLabels, Source.TypeDefinitions.labels,
      recursiveCaptureSignature, recursiveCaptureType] at member
    rcases member with rfl
    simp [Source.Signature.captureLabels, Source.CaptureInterface.labels,
      recursiveCaptureSignature, recursiveCaptureConstraint]
  guarded := by
    intro definition member
    simp [recursiveCaptureSignature] at member
    rcases member with rfl
    rfl
  packageCaptureAmbient := rfl

/-- The concrete empty witness is substituted for the self-reference before
either source inclusion is compiled.  No assumption from the target theory
is used to construct these proofs. -/
def recursiveCaptureRealization : Source.Realization
    DOTCapture.ModalIntersections.Ctx.nil recursiveCaptureSignature where
  captures := captureModel
  captureConstraints := .member .refl .captureEmpty
  representationContainment := .refl
  packageContainment := .refl

def recursiveCapturePrepared? := Encoding.prepare
  DOTCaptureToManySortedFC.ModalIntersections.Layout.empty
    recursiveCaptureSignature recursiveCaptureValid
    recursiveCaptureRealization

example : recursiveCapturePrepared?.isOk = true := by native_decide

def recursiveCapturePrepared := recursiveCapturePrepared?.toOption.get
  (by native_decide)

example : recursiveCapturePrepared.memberSymbols =
    (.cons (.type (.recProj recursiveCapturePrepared.bodies
      ⟨0, by decide⟩)) (.cons (.capture .empty) .nil)) := by
  rfl

/-! ## Non-unit representation indexed by the complete model -/

def representationType : Source.TypeDefinition [] where
  label := 20
  body := .one

def representationCapture : Source.CaptureInterface [] :=
  .member 21 .empty .empty

def dependentRepresentationSignature : Source.Signature [] where
  typeDefinitions := [representationType]
  captureDeclarations := representationCapture
  representation := .capturing (.ref (.localCaptureMember 21))
    (.arr (.ref (.localTypeMember 20)) (.ref (.localTypeMember 20)))
  outerCapture := .empty

def dependentRepresentationValid : dependentRepresentationSignature.Valid where
  nonempty := by simp [dependentRepresentationSignature]
  typeLabelsNodup := by
    simp [Source.Signature.typeLabels, Source.TypeDefinitions.labels,
      dependentRepresentationSignature, representationType]
  labelsDisjoint := by
    intro label member
    simp [Source.Signature.typeLabels, Source.TypeDefinitions.labels,
      dependentRepresentationSignature, representationType] at member
    rcases member with rfl
    simp [Source.Signature.captureLabels, Source.CaptureInterface.labels,
      dependentRepresentationSignature, representationCapture]
  guarded := by
    intro definition member
    simp [dependentRepresentationSignature] at member
    rcases member with rfl
    rfl
  packageCaptureAmbient := rfl

def dependentRepresentationRealization : Source.Realization
    DOTCapture.ModalIntersections.Ctx.nil
      dependentRepresentationSignature where
  captures := captureModel
  captureConstraints := .member .refl .refl
  representationContainment := .refl
  packageContainment := .refl

def dependentRepresentationPrepared? := Encoding.prepare
  DOTCaptureToManySortedFC.ModalIntersections.Layout.empty
    dependentRepresentationSignature dependentRepresentationValid
    dependentRepresentationRealization

example : dependentRepresentationPrepared?.isOk = true := by native_decide

def dependentRepresentationPrepared :=
  dependentRepresentationPrepared?.toOption.get (by native_decide)

/-- Both occurrences of the representation's local type member select the
same recursive witness; its local capture member uses the concrete witness. -/
example :
    dependentRepresentationPrepared.object.sourceRepresentationAtNames =
      (.capturing (.cvar (.there .here))
        (.arr (.tvar .here) (.tvar .here)) :
          ManySortedFC.Ty (ManySortedFC.SymbolScope []
            dependentRepresentationPrepared.object.memberSymbols)) := by
  rfl

example : dependentRepresentationPrepared.targetLocalModel.typeMember? 20 =
    some (.recProj dependentRepresentationPrepared.bodies ⟨0, by decide⟩) :=
  by native_decide

example : dependentRepresentationPrepared.targetLocalModel.captureMember? 21 =
    some .empty := by native_decide

/-! ## Canonical public order versus recursive source order -/

def reversedRealization : Source.Realization
    DOTCapture.ModalIntersections.Ctx.nil reversedSignature where
  captures := captureModel
  captureConstraints := .member .refl .refl
  representationContainment := .refl
  packageContainment := .refl

def reversedPrepared? := Encoding.prepare
  DOTCaptureToManySortedFC.ModalIntersections.Layout.empty reversedSignature
    reversedValid reversedRealization

example : reversedPrepared?.isOk = true := by native_decide

def reversedPrepared := reversedPrepared?.toOption.get (by native_decide)

/-- Public labels remain `[A,B,C]`, while their witnesses point to source
slots `[1,0,-]` because the recursive definitions were supplied as `[B,A]`. -/
example : reversedPrepared.memberSymbols =
    (.cons (.type (.recProj reversedPrepared.bodies ⟨1, by decide⟩))
      (.cons (.type (.recProj reversedPrepared.bodies ⟨0, by decide⟩))
        (.cons (.capture .empty) .nil))) := by
  rfl

example : Encoding.publicTypeWitness? reversedPrepared.object
    reversedPrepared.memberSymbols 1 =
      some (.recProj reversedPrepared.bodies ⟨1, by decide⟩) :=
  reversedPrepared.publicWitnessesAligned ⟨1, by decide⟩

example : Encoding.publicTypeWitness? reversedPrepared.object
    reversedPrepared.memberSymbols 2 =
      some (.recProj reversedPrepared.bodies ⟨0, by decide⟩) :=
  reversedPrepared.publicWitnessesAligned ⟨0, by decide⟩

/-! ## Repeated capture occurrences -/

def repeatedRealization : Source.Realization
    DOTCapture.ModalIntersections.Ctx.nil repeatedCaptureSignature where
  captures := captureModel
  captureConstraints := .inter (.member .refl .refl) (.member .refl .refl)
  representationContainment := .refl
  packageContainment := .refl

def repeatedPrepared? := Encoding.prepare
  DOTCaptureToManySortedFC.ModalIntersections.Layout.empty
    repeatedCaptureSignature repeatedCaptureValid repeatedRealization

example : repeatedPrepared?.isOk = true := by native_decide

def repeatedPrepared := repeatedPrepared?.toOption.get (by native_decide)

/-- Two retained capture intervals share one normalized public capture name. -/
example : repeatedPrepared.object.memberSymbols =
    [.type, .type, .capture] := by native_decide

/-! ## Explicit existential capture model

The source equations are prepared only after the complete finite witness
vector has been selected.  Both capture labels therefore become the same
ambient singleton; neither is allocated as a recursive capture slot. -/

namespace ExistentialCaptureModels

def layout :=
  DOTCaptureToManySortedFC.ModalIntersections.Layout.empty.extendPlain

def prepared? := Encoding.prepare layout
  SourceExamples.ExistentialCaptureModels.signature
  SourceExamples.ExistentialCaptureModels.valid
  SourceExamples.ExistentialCaptureModels.realization

example : prepared?.isOk = true := by native_decide

def prepared := prepared?.toOption.get (by native_decide)

example : prepared.bodies = .nil := by native_decide

example : prepared.object.memberSymbols = [.capture, .capture] := by
  native_decide

example : prepared.targetLocalModel.captureMember? 31 =
    some (.singleton .here) := by native_decide

example : prepared.targetLocalModel.captureMember? 32 =
    some (.singleton .here) := by native_decide

/-- The source representation is captured by local `D`; instantiation makes
the distinguished payload capture and the advertised object envelope the
same ambient singleton. -/
example : prepared.object.actualCapture prepared.memberSymbols =
    (.singleton .here : ManySortedFC.Capture
      [ManySortedFC.BinderKind.term]) := by native_decide

example : prepared.object.outerCapture =
    (.singleton .here : ManySortedFC.Capture
      [ManySortedFC.BinderKind.term]) := by native_decide

/-- The capture-only vector contains the two explicitly selected singleton
captures and no artificial recursive type slot. -/
example : prepared.memberSymbols =
    (.cons (.capture (.singleton .here))
      (.cons (.capture (.singleton .here)) .nil)) := by
  native_decide

end ExistentialCaptureModels

end DOTCaptureToManySortedFC.RecursiveObjects.EncodingExamples
