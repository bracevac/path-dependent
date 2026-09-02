import Coercions.DOT.Captures.Intersections.GeneralExpression.Typing
import Coercions.DOT.Captures.ModalIntersections.ContextEmbedding
import Coercions.DOT.Captures.ModalIntersections.StaticJudgments

/-!
# Captured-intersection judgment embedding

The all-term embedding of captured intersections preserves the complete
static judgment layer.  Raw interval occurrences, stable opening, object
exposure, independently selected bounds, and both source inclusion judgments
map to the corresponding cumulative proofs without allocating new member
identities or changing endpoint provenance.
-/

namespace DOTCapture.ModalIntersections.Embedding.CapturedIntersections

open DOTCapture.ModalIntersections

/-! ## Raw interface occurrences -/

/-- A retained type-member occurrence remains the same branch of the embedded
raw intersection tree. -/
def hasTypeOccurrence {scope : Nat}
    {sourceInterface : DOTCapture.Intersections.Source.Interface scope}
    {label : DOTCapture.Intersections.Source.Label}
    {lower upper : DOTCapture.Intersections.Source.Ty scope}
    (occurrence : sourceInterface.HasTypeOccurrence label lower upper) :
    (interface sourceInterface).HasTypeOccurrence label
      (type lower) (type upper) :=
  match occurrence with
  | .here => .here
  | .left nested => .left (hasTypeOccurrence nested)
  | .right nested => .right (hasTypeOccurrence nested)

/-- Capture-member counterpart of `hasTypeOccurrence`. -/
def hasCaptureOccurrence {scope : Nat}
    {sourceInterface : DOTCapture.Intersections.Source.Interface scope}
    {label : DOTCapture.Intersections.Source.Label}
    {lower upper : DOTCapture.Intersections.Source.Capture scope}
    (occurrence : sourceInterface.HasCaptureOccurrence label lower upper) :
    (interface sourceInterface).HasCaptureOccurrence label
      (capture lower) (capture upper) :=
  match occurrence with
  | .here => .here
  | .left nested => .left (hasCaptureOccurrence nested)
  | .right nested => .right (hasCaptureOccurrence nested)

/-! ## Stable opening commutes with embedding -/

@[simp]
def capture_openAt {scope : Nat}
    (receiver : DOTCapture.Intersections.Source.Path scope)
    (sourceCapture : DOTCapture.Intersections.Source.Capture scope) :
    capture (DOTCapture.Intersections.Source.Capture.openAt
      receiver sourceCapture) =
      (capture sourceCapture).openAt (path receiver) :=
  match sourceCapture with
  | .empty => rfl
  | .union left right => by
      change
        Capture.union
            (capture (DOTCapture.Intersections.Source.Capture.openAt
              receiver left))
            (capture (DOTCapture.Intersections.Source.Capture.openAt
              receiver right)) =
          Capture.union
            ((capture left).openAt (path receiver))
            ((capture right).openAt (path receiver))
      rw [capture_openAt receiver left, capture_openAt receiver right]
  | .singleton _ => rfl
  | .ref reference => by
      cases reference <;> change _ = _ <;> rfl

@[simp]
def type_openAt {scope : Nat}
    (receiver : DOTCapture.Intersections.Source.Path scope)
    (sourceType : DOTCapture.Intersections.Source.Ty scope) :
    type (DOTCapture.Intersections.Source.Ty.openAt receiver sourceType) =
      (type sourceType).openAt (path receiver) :=
  match sourceType with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by
      cases reference <;> change _ = _ <;> rfl
  | .arr domain codomain => by
      change
        Ty.arr
            (type (DOTCapture.Intersections.Source.Ty.openAt receiver domain))
            (type (DOTCapture.Intersections.Source.Ty.openAt
              receiver codomain)) =
          Ty.arr ((type domain).openAt (path receiver))
            ((type codomain).openAt (path receiver))
      rw [type_openAt receiver domain, type_openAt receiver codomain]
  | .capturing captures shape => by
      change
        Ty.capturing
            (capture (DOTCapture.Intersections.Source.Capture.openAt
              receiver captures))
            (type (DOTCapture.Intersections.Source.Ty.openAt receiver shape)) =
          Ty.capturing ((capture captures).openAt (path receiver))
            ((type shape).openAt (path receiver))
      rw [capture_openAt receiver captures, type_openAt receiver shape]
  | .object _ => by
      change _ = _
      rfl

@[simp]
theorem staticRef_expression {scope : Nat}
    {sort : DOTCapture.Intersections.Source.StaticSort}
    (reference : DOTCapture.Intersections.Source.StaticRef sort scope) :
    staticExpr reference.expression = (staticRef reference).expression := by
  cases reference <;> rfl

@[simp]
theorem type_stripCapture {scope : Nat}
    (sourceType : DOTCapture.Intersections.Source.Ty scope) :
    type sourceType.stripCapture = (type sourceType).stripCapture := by
  cases sourceType <;> rfl

@[simp]
theorem type_outerCapture {scope : Nat}
    (sourceType : DOTCapture.Intersections.Source.Ty scope) :
    capture sourceType.outerCapture = (type sourceType).outerCapture := by
  cases sourceType <;> rfl

@[simp]
theorem objectType_interface {scope : Nat}
    (sourceObject : DOTCapture.Intersections.Source.ObjectType scope) :
    interface sourceObject.interface = (objectType sourceObject).interface := by
  cases sourceObject
  rfl

@[simp]
theorem objectType_representation {scope : Nat}
    (sourceObject : DOTCapture.Intersections.Source.ObjectType scope) :
    type sourceObject.representation =
      (objectType sourceObject).representation := by
  cases sourceObject
  rfl

@[simp]
theorem objectType_outerCapture {scope : Nat}
    (sourceObject : DOTCapture.Intersections.Source.ObjectType scope) :
    capture sourceObject.outerCapture =
      (objectType sourceObject).outerCapture := by
  cases sourceObject
  rfl

/-! ## Stable exposure and selected bounds -/

/-- Context lookup and capture stripping preserve stable object exposure. -/
def exposesObject {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {receiver : DOTCapture.Intersections.Source.Path scope}
    {sourceObject : DOTCapture.Intersections.Source.ObjectType scope}
    (exposes : DOTCapture.Intersections.Source.ExposesObject sourceContext
      receiver sourceObject) :
    DOTCapture.ModalIntersections.ExposesObject (context sourceContext)
      (path receiver) (objectType sourceObject) :=
  match exposes with
  | @DOTCapture.Intersections.Source.ExposesObject.variable _ _ name _ found => by
      apply DOTCapture.ModalIntersections.ExposesObject.variable
      rw [← context_lookup sourceContext name]
      rw [← type_stripCapture]
      exact congrArg type found

/-- Every selected lower-bound proof embeds with its exact raw occurrence. -/
def hasLower {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sort : DOTCapture.Intersections.Source.StaticSort}
    {reference : DOTCapture.Intersections.Source.StaticRef sort scope}
    {endpoint : DOTCapture.Intersections.Source.StaticExpr sort scope}
    (bound : DOTCapture.Intersections.Source.HasLower sourceContext
      reference endpoint) :
    DOTCapture.ModalIntersections.HasLower (context sourceContext)
      (staticRef reference) (staticExpr endpoint) :=
  match bound with
  | .typeMember exposes occurrence => by
      have embeddedOccurrence := hasTypeOccurrence occurrence
      rw [objectType_interface] at embeddedOccurrence
      simpa only [staticRef, staticExpr, type_openAt] using
        DOTCapture.ModalIntersections.HasLower.typeMember
          (exposesObject exposes) embeddedOccurrence
  | .captureMember exposes occurrence => by
      have embeddedOccurrence := hasCaptureOccurrence occurrence
      rw [objectType_interface] at embeddedOccurrence
      simpa only [staticRef, staticExpr, capture_openAt] using
        DOTCapture.ModalIntersections.HasLower.captureMember
          (exposesObject exposes) embeddedOccurrence

/-- Every selected upper-bound proof embeds with its exact raw occurrence. -/
def hasUpper {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sort : DOTCapture.Intersections.Source.StaticSort}
    {reference : DOTCapture.Intersections.Source.StaticRef sort scope}
    {endpoint : DOTCapture.Intersections.Source.StaticExpr sort scope}
    (bound : DOTCapture.Intersections.Source.HasUpper sourceContext
      reference endpoint) :
    DOTCapture.ModalIntersections.HasUpper (context sourceContext)
      (staticRef reference) (staticExpr endpoint) :=
  match bound with
  | .typeMember exposes occurrence => by
      have embeddedOccurrence := hasTypeOccurrence occurrence
      rw [objectType_interface] at embeddedOccurrence
      simpa only [staticRef, staticExpr, type_openAt] using
        DOTCapture.ModalIntersections.HasUpper.typeMember
          (exposesObject exposes) embeddedOccurrence
  | .captureMember exposes occurrence => by
      have embeddedOccurrence := hasCaptureOccurrence occurrence
      rw [objectType_interface] at embeddedOccurrence
      simpa only [staticRef, staticExpr, capture_openAt] using
        DOTCapture.ModalIntersections.HasUpper.captureMember
          (exposesObject exposes) embeddedOccurrence

/-! ## Inclusion judgments -/

/-- The original captured-intersection inclusion judgment is a literal
subsystem of cumulative sorted inclusion. -/
def includes {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sort : DOTCapture.Intersections.Source.StaticSort}
    {lower upper : DOTCapture.Intersections.Source.StaticExpr sort scope}
    (proof : DOTCapture.Intersections.Source.Includes sourceContext
      lower upper) :
    DOTCapture.ModalIntersections.Includes (context sourceContext)
      (staticExpr lower) (staticExpr upper) :=
  match proof with
  | .refl => .refl
  | .trans first second => .trans (includes first) (includes second)
  | .lower bound => by
      simpa only [staticRef_expression] using
        DOTCapture.ModalIntersections.Includes.lower (hasLower bound)
  | .upper bound => by
      simpa only [staticRef_expression] using
        DOTCapture.ModalIntersections.Includes.upper (hasUpper bound)
  | .typeTop => .typeTop
  | .typeBottom => .typeBottom
  | .typeCapturing captures shape =>
      .typeCapturing (includes captures) (includes shape)
  | .captureEmpty => .captureEmpty
  | .captureUnionLeft => .captureUnionLeft
  | .captureUnionRight => .captureUnionRight
  | .captureUnionElim fromLeft fromRight =>
      .captureUnionElim (includes fromLeft) (includes fromRight)

/-- The general-expression extension also embeds, including its stable
payload-root contraction rule. -/
def generalIncludes {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sort : DOTCapture.Intersections.Source.StaticSort}
    {lower upper : DOTCapture.Intersections.Source.StaticExpr sort scope}
    (proof : DOTCapture.Intersections.GeneralExpression.Includes sourceContext
      lower upper) :
    DOTCapture.ModalIntersections.Includes (context sourceContext)
      (staticExpr lower) (staticExpr upper) :=
  match proof with
  | .source sourceProof => includes sourceProof
  | .trans first second =>
      .trans (generalIncludes first) (generalIncludes second)
  | .typeCapturing captures shape =>
      .typeCapturing (generalIncludes captures) (generalIncludes shape)
  | .captureUnionElim fromLeft fromRight =>
      .captureUnionElim (generalIncludes fromLeft)
        (generalIncludes fromRight)
  | .payloadRoot exposes => by
      simpa only [staticExpr, capture,
        DOTCapture.Intersections.GeneralExpression.ObjectType.representationAt,
        DOTCapture.ModalIntersections.ObjectType.representationAt,
        objectType_representation, type_openAt, type_outerCapture] using
        DOTCapture.ModalIntersections.Includes.payloadRoot
          (exposesObject exposes)

end DOTCapture.ModalIntersections.Embedding.CapturedIntersections
