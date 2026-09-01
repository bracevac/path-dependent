import Coercions.Translation.ManySorted.RecursiveObjects.Source
import Coercions.DOT.Captures.ModalIntersections.Typing

/-!
# Recursive-signature source regressions

The base block contains two mutually recursive type definitions and one
ordinary capture member.  Negative checks reject naked unguarded aliases and
type/capture label collisions.  The cumulative examples then admit local
capture cycles through an explicit simultaneous concrete model.
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
  packageCaptureAmbient := rfl

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

/-! ## Cumulative source-typing boundary

The representation below is a real function type that refers statically to
both a recursive type member and a locally declared capture member. The two
capture declarations also refer to one another. A simultaneous concrete
model maps both capture names to the ambient empty capture, so every bound and
the representation-containment obligation is checked without assuming the
object theory being constructed. -/

def payloadTypeDefinition : TypeDefinition [] where
  label := 20
  body := .one

def mutuallyConstrainedCaptures : CaptureInterface [] :=
  .inter
    (.member 21 (.ref (.localCaptureMember 22))
      (.ref (.localCaptureMember 22)))
    (.member 22 (.ref (.localCaptureMember 21))
      (.ref (.localCaptureMember 21)))

def functionSignature : Signature [] where
  typeDefinitions := [payloadTypeDefinition]
  captureDeclarations := mutuallyConstrainedCaptures
  representation := .capturing (.ref (.localCaptureMember 21))
    (.arr (.ref (.localTypeMember 20)) .one)
  outerCapture := .empty

def functionSignatureValid : functionSignature.Valid where
  nonempty := by simp [functionSignature]
  typeLabelsNodup := by
    simp [Signature.typeLabels, TypeDefinitions.labels, functionSignature,
      payloadTypeDefinition]
  labelsDisjoint := by
    intro label member
    simp [Signature.typeLabels, TypeDefinitions.labels, functionSignature,
      payloadTypeDefinition] at member
    subst label
    simp [Signature.captureLabels, CaptureInterface.labels,
      functionSignature, mutuallyConstrainedCaptures]
  guarded := by
    intro definition member
    simp [functionSignature] at member
    subst definition
    rfl
  packageCaptureAmbient := rfl

def mutuallyConstrainedModel : AmbientCaptureModel [] where
  witness := fun _ => .empty
  ambient := by intro; rfl

def functionRealization : Realization
    DOTCapture.ModalIntersections.Ctx.nil functionSignature where
  captures := mutuallyConstrainedModel
  captureConstraints := .inter (.member .refl .refl) (.member .refl .refl)
  representationContainment := .refl
  packageContainment := .refl

def functionPayload : DOTCapture.ModalIntersections.Value [] :=
  .lam (.ref (.localTypeMember 20)) .one (.ret .unit)

def functionPayloadTyping : DOTCapture.ModalIntersections.Value.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil functionPayload
      (.capturing .empty (.arr (.ref (.localTypeMember 20)) .one)) :=
  .lam (by trivial) (.ret .unit) .captureEmpty

def functionObjectTyping : DOTCapture.ModalIntersections.Value.HasType
    DOTCapture.ModalIntersections.TypingEnv.nil
      (.recursiveObject functionSignature.objectType functionPayload)
      functionSignature.objectType.formedType :=
  .recursiveObject functionSignatureValid functionRealization
    functionPayloadTyping .refl .refl

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
  packageCaptureAmbient := rfl

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
  packageCaptureAmbient := rfl

/-! ## Explicit existential capture models

Recursive capture declarations constrain a simultaneously chosen vector of
finite ambient captures.  They do not generate a least fixed point.  The
first theory below has the exact equations `C = D` and
`D = {a} ∪ C`; the explicit solution chooses `C = D = {a}`. -/

namespace ExistentialCaptureModels

abbrev Scope : DOTCapture.ModalIntersections.Sig := [] ▹ .term

def boundType : DOTCapture.ModalIntersections.Ty [] :=
  .one

def environment : DOTCapture.ModalIntersections.TypingEnv Scope :=
  DOTCapture.ModalIntersections.TypingEnv.nil.extendTerm boundType

def a : DOTCapture.ModalIntersections.Capture Scope :=
  .singleton (.var .here)

def equations : CaptureInterface Scope :=
  .inter
    (.member 31 (.ref (.localCaptureMember 32))
      (.ref (.localCaptureMember 32)))
    (.member 32
      (.union a (.ref (.localCaptureMember 31)))
      (.union a (.ref (.localCaptureMember 31))))

def signature : Signature Scope where
  typeDefinitions := []
  captureDeclarations := equations
  representation := .capturing
    (.ref (.localCaptureMember 32)) .one
  outerCapture := a

def valid : signature.Valid where
  nonempty := by
    right
    simp [Signature.captureLabels, CaptureInterface.labels, signature,
      equations]
  typeLabelsNodup := by
    simp [Signature.typeLabels, TypeDefinitions.labels, signature]
  labelsDisjoint := by
    intro label member
    simp [Signature.typeLabels, TypeDefinitions.labels, signature] at member
  guarded := by
    intro definition member
    simp [signature] at member
  packageCaptureAmbient := rfl

/-- The finite witness vector selected externally for the two equations. -/
def singletonModel : AmbientCaptureModel Scope where
  witness := fun _ => a
  ambient := by intro; rfl

/-- After simultaneous substitution, `C = D` is reflexive and
`D = {a} ∪ C` is witnessed in both directions by the ordinary union rules. -/
def constraints : equations.Realizes environment.bindings singletonModel :=
  .inter
    (.member .refl .refl)
    (.member (.captureUnionElim .refl .refl) .captureUnionLeft)

def realization : Realization environment.bindings signature where
  captures := singletonModel
  captureConstraints := constraints
  representationContainment := .refl
  packageContainment := .refl

example : signature.typeDefinitions = [] := rfl
example : signature.captureLabels = [31, 32] := rfl
example : singletonModel.witness 31 = a := rfl
example : singletonModel.witness 32 = a := rfl

/-! The self equation `C = C` has several finite solutions.  Both choices
below satisfy the same declaration, demonstrating model selection rather
than generative fixed-point semantics. -/

def selfEquation : CaptureInterface Scope :=
  .member 41 (.ref (.localCaptureMember 41))
    (.ref (.localCaptureMember 41))

def emptyModel : AmbientCaptureModel Scope where
  witness := fun _ => .empty
  ambient := by intro; rfl

def selfEmptySolution : selfEquation.Realizes environment.bindings emptyModel :=
  .member .refl .refl

def selfSingletonSolution :
    selfEquation.Realizes environment.bindings singletonModel :=
  .member .refl .refl

example : emptyModel.witness 41 ≠ singletonModel.witness 41 := by
  simp [emptyModel, singletonModel, a]

end ExistentialCaptureModels

end DOTCaptureToManySortedFC.RecursiveObjects.SourceExamples
