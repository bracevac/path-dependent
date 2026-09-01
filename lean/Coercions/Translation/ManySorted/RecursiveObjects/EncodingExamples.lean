import Coercions.Translation.ManySorted.RecursiveObjects.SourceExamples
import Coercions.Translation.ManySorted.RecursiveObjects.Encoding

/-!
# Source-indexed recursive encoding regressions

These checks isolate the allocation boundary from later package evidence:
mutually recursive source labels become distinct self slots, the acyclic
capture member is interpreted by an explicit ambient witness, and the target
block is guarded.
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

def recursiveCaptureSignature : Source.Signature [] where
  typeDefinitions := [typeA]
  captureDeclarations := recursiveCapture
  representation := .one
  outerCapture := .empty

example : Encoding.checkBoundary recursiveCaptureSignature =
    .error (.recursiveCaptureMember 11) := rfl

/-! ## Canonical public order versus recursive source order -/

def reversedRealization : Source.Realization
    DOTCapture.ModalIntersections.Ctx.nil reversedSignature where
  captures := captureModel
  captureConstraints := .member .refl .refl
  representationContainment := .refl

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

def repeatedPrepared? := Encoding.prepare
  DOTCaptureToManySortedFC.ModalIntersections.Layout.empty
    repeatedCaptureSignature repeatedCaptureValid repeatedRealization

example : repeatedPrepared?.isOk = true := by native_decide

def repeatedPrepared := repeatedPrepared?.toOption.get (by native_decide)

/-- Two retained capture intervals share one normalized public capture name. -/
example : repeatedPrepared.object.memberSymbols =
    [.type, .type, .capture] := by native_decide

end DOTCaptureToManySortedFC.RecursiveObjects.EncodingExamples
