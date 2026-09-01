import Coercions.Translation.ManySorted.RecursiveObjects.Source

/-!
# Recursive-signature source regressions

The positive block contains two mutually recursive type definitions and one
ordinary capture member.  Negative checks isolate the Stage 6A boundary:
naked type aliases are not guarded, local capture recursion is not admitted,
and a type/capture label collision violates formation.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.SourceExamples

open DOTCaptureToManySortedFC.RecursiveObjects.Source

def typeA : TypeDefinition [] where
  label := 1
  body := .arr (.ref (.localTypeMember 2)) .one

def typeB : TypeDefinition [] where
  label := 2
  body := .capturing (.ref (.localCaptureMember 3))
    (.ref (.localTypeMember 1))

def captureC : CaptureInterface [] :=
  .member 3 .empty .empty

def signature : Signature [] where
  typeDefinitions := [typeA, typeB]
  captureDeclarations := captureC
  representation := .one
  outerCapture := .empty

example : typeA.headGuarded = true := rfl
example : typeB.headGuarded = true := rfl
example : signature.typeLabels = [1, 2] := rfl
example : signature.captureLabels = [3] := rfl

def signatureValid : signature.Valid where
  nonempty := by simp [signature]
  typeLabelsNodup := by simp [Signature.typeLabels, signature,
    TypeDefinitions.labels, typeA, typeB]
  labelsDisjoint := by
    intro label member
    simp [Signature.typeLabels, TypeDefinitions.labels, signature, typeA,
      typeB] at member
    rcases member with rfl | rfl
    <;> simp [Signature.captureLabels, CaptureInterface.labels, signature,
      captureC]
  guarded := by
    intro definition member
    simp [signature] at member
    rcases member with rfl | rfl
    <;> rfl
  capturesAmbient := by simp [signature, captureC,
    CaptureInterface.ambientOnly, captureAmbientOnly]
  representationIsUnit := rfl
  outerCaptureAmbient := rfl

def nakedAlias : TypeDefinition [] where
  label := 10
  body := .ref (.localTypeMember 10)

example : nakedAlias.headGuarded = false := rfl

def recursiveCapture : CaptureInterface [] :=
  .member 11 (.ref (.localCaptureMember 11)) .empty

example : ¬ recursiveCapture.ambientOnly := by
  simp [recursiveCapture, CaptureInterface.ambientOnly, captureAmbientOnly]

def colliding : Signature [] where
  typeDefinitions := [typeA]
  captureDeclarations := .member 1 .empty .empty
  representation := .one
  outerCapture := .empty

example : ¬ (forall label, label ∈ colliding.typeLabels ->
    label ∉ colliding.captureLabels) := by
  simp [colliding, Signature.typeLabels, Signature.captureLabels,
    TypeDefinitions.labels, CaptureInterface.labels, typeA]

/-! Repeated capture declarations remain legal M11 conjunctions.  They share
one public label while retaining both pairs of interval obligations. -/

def repeatedCaptureC : CaptureInterface [] :=
  .inter (.member 3 .empty .empty) (.member 3 .empty .empty)

def repeatedCaptureSignature : Signature [] where
  typeDefinitions := [typeA, typeB]
  captureDeclarations := repeatedCaptureC
  representation := .one
  outerCapture := .empty

def repeatedCaptureValid : repeatedCaptureSignature.Valid where
  nonempty := by simp [repeatedCaptureSignature]
  typeLabelsNodup := by simp [Signature.typeLabels,
    repeatedCaptureSignature, TypeDefinitions.labels, typeA, typeB]
  labelsDisjoint := by
    intro label member
    simp [Signature.typeLabels, TypeDefinitions.labels,
      repeatedCaptureSignature, typeA, typeB] at member
    rcases member with rfl | rfl
    <;> simp [Signature.captureLabels, CaptureInterface.labels,
      repeatedCaptureSignature, repeatedCaptureC]
  guarded := by
    intro definition member
    simp [repeatedCaptureSignature] at member
    rcases member with rfl | rfl
    <;> rfl
  capturesAmbient := by simp [repeatedCaptureSignature, repeatedCaptureC,
    CaptureInterface.ambientOnly, captureAmbientOnly]
  representationIsUnit := rfl
  outerCaptureAmbient := rfl

example : repeatedCaptureSignature.captureLabels = [3, 3] := rfl

/-! Source definition order is independent of the canonical public label
order chosen by normalization. -/

def reversedSignature : Signature [] where
  typeDefinitions := [typeB, typeA]
  captureDeclarations := captureC
  representation := .one
  outerCapture := .empty

def reversedValid : reversedSignature.Valid where
  nonempty := by simp [reversedSignature]
  typeLabelsNodup := by simp [Signature.typeLabels, reversedSignature,
    TypeDefinitions.labels, typeA, typeB]
  labelsDisjoint := by
    intro label member
    simp [Signature.typeLabels, TypeDefinitions.labels, reversedSignature,
      typeA, typeB] at member
    rcases member with rfl | rfl
    <;> simp [Signature.captureLabels, CaptureInterface.labels,
      reversedSignature, captureC]
  guarded := by
    intro definition member
    simp [reversedSignature] at member
    rcases member with rfl | rfl
    <;> rfl
  capturesAmbient := by simp [reversedSignature, captureC,
    CaptureInterface.ambientOnly, captureAmbientOnly]
  representationIsUnit := rfl
  outerCaptureAmbient := rfl

end DOTCaptureToManySortedFC.RecursiveObjects.SourceExamples
