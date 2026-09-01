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

/-! The historical captured-intersection source now shares the cumulative
three-sort signature syntax.  Type and capture expressions embed into the
ordinary two-sort judgment, while classifier expressions embed into the
separate classifier judgment. -/

def EmbeddedStaticRef (scope : Nat) :
    DOTCapture.Intersections.Source.StaticSort -> Type
  | .type => DOTCapture.ModalIntersections.StaticRef .type (termScope scope)
  | .capture =>
      DOTCapture.ModalIntersections.StaticRef .capture (termScope scope)
  | .classifier =>
      DOTCapture.ModalIntersections.ClassifierRef (termScope scope)

def staticRef {scope : Nat} :
    {sort : DOTCapture.Intersections.Source.StaticSort} ->
      DOTCapture.Intersections.Source.StaticRef sort scope ->
        EmbeddedStaticRef scope sort
  | .type, reference => typeRef reference
  | .capture, reference => captureRef reference
  | .classifier, reference => classifierRef reference

def EmbeddedStaticExpr (scope : Nat) :
    DOTCapture.Intersections.Source.StaticSort -> Type
  | .type => DOTCapture.ModalIntersections.StaticExpr .type (termScope scope)
  | .capture =>
      DOTCapture.ModalIntersections.StaticExpr .capture (termScope scope)
  | .classifier =>
      DOTCapture.ModalIntersections.ClassifierExpr (termScope scope)

def staticExpr {scope : Nat} :
    {sort : DOTCapture.Intersections.Source.StaticSort} ->
      DOTCapture.Intersections.Source.StaticExpr sort scope ->
        EmbeddedStaticExpr scope sort
  | .type, .type sourceType => .type (type sourceType)
  | .capture, .capture sourceCapture => .capture (capture sourceCapture)
  | .classifier, .classifier sourceClassifier => classifier sourceClassifier

def embeddedReferenceExpression {scope : Nat} :
    {sort : DOTCapture.Intersections.Source.StaticSort} ->
      EmbeddedStaticRef scope sort -> EmbeddedStaticExpr scope sort
  | .type, reference => reference.expression
  | .capture, reference => reference.expression
  | .classifier, reference => .ref reference

def EmbeddedIncludes {scope : Nat}
    (sourceContext : DOTCapture.Intersections.Source.Ctx scope) :
    {sort : DOTCapture.Intersections.Source.StaticSort} ->
      DOTCapture.Intersections.Source.StaticExpr sort scope ->
      DOTCapture.Intersections.Source.StaticExpr sort scope -> Type
  | .type, lower, upper =>
      DOTCapture.ModalIntersections.Includes (context sourceContext)
        (staticExpr lower) (staticExpr upper)
  | .capture, lower, upper =>
      DOTCapture.ModalIntersections.Includes (context sourceContext)
        (staticExpr lower) (staticExpr upper)
  | .classifier, lower, upper =>
      DOTCapture.ModalIntersections.ClassifierIncludes (context sourceContext)
        (staticExpr lower) (staticExpr upper)

def EmbeddedHasLower {scope : Nat}
    (sourceContext : DOTCapture.Intersections.Source.Ctx scope) :
    {sort : DOTCapture.Intersections.Source.StaticSort} ->
      DOTCapture.Intersections.Source.StaticRef sort scope ->
      DOTCapture.Intersections.Source.StaticExpr sort scope -> Type
  | .type, reference, endpoint =>
      DOTCapture.ModalIntersections.HasLower (context sourceContext)
        (staticRef reference) (staticExpr endpoint)
  | .capture, reference, endpoint =>
      DOTCapture.ModalIntersections.HasLower (context sourceContext)
        (staticRef reference) (staticExpr endpoint)
  | .classifier, _, _ => Empty

def EmbeddedHasUpper {scope : Nat}
    (sourceContext : DOTCapture.Intersections.Source.Ctx scope) :
    {sort : DOTCapture.Intersections.Source.StaticSort} ->
      DOTCapture.Intersections.Source.StaticRef sort scope ->
      DOTCapture.Intersections.Source.StaticExpr sort scope -> Type
  | .type, reference, endpoint =>
      DOTCapture.ModalIntersections.HasUpper (context sourceContext)
        (staticRef reference) (staticExpr endpoint)
  | .capture, reference, endpoint =>
      DOTCapture.ModalIntersections.HasUpper (context sourceContext)
        (staticRef reference) (staticExpr endpoint)
  | .classifier, _, _ => Empty

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

/-- Classifier-member counterpart of `hasTypeOccurrence`. -/
def hasClassifierOccurrence {scope : Nat}
    {sourceInterface : DOTCapture.Intersections.Source.Interface scope}
    {label : DOTCapture.Intersections.Source.Label}
    {lower upper : DOTCapture.Intersections.Source.ClassifierExpr scope}
    (occurrence :
      DOTCapture.Intersections.GeneralExpression.Interface.HasClassifierOccurrence
        sourceInterface label lower upper) :
    (interface sourceInterface).HasClassifierOccurrence label
      (classifier lower) (classifier upper) :=
  match occurrence with
  | .here => .here
  | .left nested => .left (hasClassifierOccurrence nested)
  | .right nested => .right (hasClassifierOccurrence nested)

/-- One retained classifier-disjointness constraint embeds at the same raw
intersection-tree position. -/
def hasClassifierDisjointOccurrence {scope : Nat}
    {sourceInterface : DOTCapture.Intersections.Source.Interface scope}
    {left right : DOTCapture.Intersections.Source.ClassifierExpr scope}
    (occurrence :
      DOTCapture.Intersections.GeneralExpression.Interface.HasClassifierDisjointOccurrence
        sourceInterface left right) :
    (interface sourceInterface).HasClassifierDisjointOccurrence
      (classifier left) (classifier right) :=
  match occurrence with
  | .here => .here
  | .left nested => .left (hasClassifierDisjointOccurrence nested)
  | .right nested => .right (hasClassifierDisjointOccurrence nested)

/-- One retained capture-kind constraint embeds at the same raw
intersection-tree position. -/
def hasCaptureKindOccurrence {scope : Nat}
    {sourceInterface : DOTCapture.Intersections.Source.Interface scope}
    {sourceCapture : DOTCapture.Intersections.Source.Capture scope}
    {sourceClassifier : DOTCapture.Intersections.Source.ClassifierExpr scope}
    (occurrence :
      DOTCapture.Intersections.GeneralExpression.Interface.HasCaptureKindOccurrence
        sourceInterface sourceCapture sourceClassifier) :
    (interface sourceInterface).HasCaptureKindOccurrence
      (capture sourceCapture) (classifier sourceClassifier) :=
  match occurrence with
  | .here => .here
  | .left nested => .left (hasCaptureKindOccurrence nested)
  | .right nested => .right (hasCaptureKindOccurrence nested)

/-! ## Stable opening commutes with embedding -/

@[simp]
def classifier_openAt {scope : Nat}
    (receiver : DOTCapture.Intersections.Source.Path scope)
    (sourceClassifier : DOTCapture.Intersections.Source.ClassifierExpr scope) :
    classifier (DOTCapture.Intersections.Source.ClassifierExpr.openAt
      receiver sourceClassifier) =
      (classifier sourceClassifier).openAt (path receiver) :=
  match sourceClassifier with
  | .ground _ => rfl
  | .ref reference => by cases reference <;> rfl

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
  | .project sourceCapture sourceClassifier => by
      change
        Capture.project
            (capture (DOTCapture.Intersections.Source.Capture.openAt
              receiver sourceCapture))
            (classifier
              (DOTCapture.Intersections.Source.ClassifierExpr.openAt
                receiver sourceClassifier)) =
          Capture.project ((capture sourceCapture).openAt (path receiver))
            ((classifier sourceClassifier).openAt (path receiver))
      rw [capture_openAt receiver sourceCapture,
        classifier_openAt receiver sourceClassifier]
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
    staticExpr reference.expression =
      embeddedReferenceExpression (staticRef reference) := by
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
    EmbeddedHasLower sourceContext reference endpoint :=
  match bound with
  | .typeMember exposes occurrence => by
      have embeddedOccurrence := hasTypeOccurrence occurrence
      rw [objectType_interface] at embeddedOccurrence
      simpa only [EmbeddedHasLower, staticRef, staticExpr, type_openAt] using
        DOTCapture.ModalIntersections.HasLower.typeMember
          (exposesObject exposes) embeddedOccurrence
  | .captureMember exposes occurrence => by
      have embeddedOccurrence := hasCaptureOccurrence occurrence
      rw [objectType_interface] at embeddedOccurrence
      simpa only [EmbeddedHasLower, staticRef, staticExpr,
        capture_openAt] using
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
    EmbeddedHasUpper sourceContext reference endpoint :=
  match bound with
  | .typeMember exposes occurrence => by
      have embeddedOccurrence := hasTypeOccurrence occurrence
      rw [objectType_interface] at embeddedOccurrence
      simpa only [EmbeddedHasUpper, staticRef, staticExpr, type_openAt] using
        DOTCapture.ModalIntersections.HasUpper.typeMember
          (exposesObject exposes) embeddedOccurrence
  | .captureMember exposes occurrence => by
      have embeddedOccurrence := hasCaptureOccurrence occurrence
      rw [objectType_interface] at embeddedOccurrence
      simpa only [EmbeddedHasUpper, staticRef, staticExpr,
        capture_openAt] using
        DOTCapture.ModalIntersections.HasUpper.captureMember
          (exposesObject exposes) embeddedOccurrence

/-! ## Inclusion judgments -/

private def embeddedIncludesRefl {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sort : DOTCapture.Intersections.Source.StaticSort}
    (expression : DOTCapture.Intersections.Source.StaticExpr sort scope) :
    EmbeddedIncludes sourceContext expression expression :=
  match expression with
  | .type _ => DOTCapture.ModalIntersections.Includes.refl
  | .capture _ => DOTCapture.ModalIntersections.Includes.refl
  | .classifier _ => DOTCapture.ModalIntersections.ClassifierIncludes.refl

private def embeddedIncludesTrans {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sort : DOTCapture.Intersections.Source.StaticSort}
    {source middle target :
      DOTCapture.Intersections.Source.StaticExpr sort scope}
    (first : EmbeddedIncludes sourceContext source middle)
    (second : EmbeddedIncludes sourceContext middle target) :
    EmbeddedIncludes sourceContext source target :=
  match source, middle, target with
  | .type _, .type _, .type _ =>
      DOTCapture.ModalIntersections.Includes.trans first second
  | .capture _, .capture _, .capture _ =>
      DOTCapture.ModalIntersections.Includes.trans first second
  | .classifier _, .classifier _, .classifier _ =>
      DOTCapture.ModalIntersections.ClassifierIncludes.trans first second

/-- The original captured-intersection inclusion judgment is a literal
subsystem of cumulative sorted inclusion. -/
def includes {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sort : DOTCapture.Intersections.Source.StaticSort}
    {lower upper : DOTCapture.Intersections.Source.StaticExpr sort scope}
    (proof : DOTCapture.Intersections.Source.Includes sourceContext
      lower upper) :
    EmbeddedIncludes sourceContext lower upper :=
  match proof with
  | .refl => embeddedIncludesRefl _
  | .trans first second =>
      embeddedIncludesTrans (includes first) (includes second)
  | .lower bound => by
      cases bound with
      | typeMember exposes occurrence =>
          simpa only [EmbeddedIncludes, staticRef_expression] using
            DOTCapture.ModalIntersections.Includes.lower
              (hasLower (.typeMember exposes occurrence))
      | captureMember exposes occurrence =>
          simpa only [EmbeddedIncludes, staticRef_expression] using
            DOTCapture.ModalIntersections.Includes.lower
              (hasLower (.captureMember exposes occurrence))
  | .upper bound => by
      cases bound with
      | typeMember exposes occurrence =>
          simpa only [EmbeddedIncludes, staticRef_expression] using
            DOTCapture.ModalIntersections.Includes.upper
              (hasUpper (.typeMember exposes occurrence))
      | captureMember exposes occurrence =>
          simpa only [EmbeddedIncludes, staticRef_expression] using
            DOTCapture.ModalIntersections.Includes.upper
              (hasUpper (.captureMember exposes occurrence))
  | .typeTop => DOTCapture.ModalIntersections.Includes.typeTop
  | .typeBottom => DOTCapture.ModalIntersections.Includes.typeBottom
  | .typeCapturing captures shape =>
      DOTCapture.ModalIntersections.Includes.typeCapturing
        (includes captures) (includes shape)
  | .captureEmpty => DOTCapture.ModalIntersections.Includes.captureEmpty
  | .captureUnionLeft =>
      DOTCapture.ModalIntersections.Includes.captureUnionLeft
  | .captureUnionRight =>
      DOTCapture.ModalIntersections.Includes.captureUnionRight
  | .captureUnionElim fromLeft fromRight =>
      DOTCapture.ModalIntersections.Includes.captureUnionElim
        (includes fromLeft) (includes fromRight)

/-- The general-expression extension also embeds, including its stable
payload-root contraction rule. -/
def generalIncludes {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sort : DOTCapture.Intersections.Source.StaticSort}
    {lower upper : DOTCapture.Intersections.Source.StaticExpr sort scope}
    (proof : DOTCapture.Intersections.GeneralExpression.Includes sourceContext
      lower upper) :
    EmbeddedIncludes sourceContext lower upper :=
  match proof with
  | .source sourceProof => includes sourceProof
  | .trans first second =>
      embeddedIncludesTrans (generalIncludes first) (generalIncludes second)
  | .typeCapturing captures shape =>
      DOTCapture.ModalIntersections.Includes.typeCapturing
        (generalIncludes captures) (generalIncludes shape)
  | .captureUnionElim fromLeft fromRight =>
      DOTCapture.ModalIntersections.Includes.captureUnionElim
        (generalIncludes fromLeft)
        (generalIncludes fromRight)
  | .captureProjectSource =>
      DOTCapture.ModalIntersections.Includes.captureProjectSource
  | .payloadRoot exposes => by
      simpa only [EmbeddedIncludes, staticExpr, capture,
        DOTCapture.Intersections.GeneralExpression.ObjectType.representationAt,
        DOTCapture.ModalIntersections.ObjectType.representationAt,
        objectType_representation, type_openAt, type_outerCapture] using
        DOTCapture.ModalIntersections.Includes.payloadRoot
          (exposesObject exposes)

/-! ## Classifier and mixed static judgments -/

/-- Ground and stable-path classifier-disjointness embeds without changing
the selected object-theory occurrence. -/
def classifiersDisjoint {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {left right : DOTCapture.Intersections.Source.ClassifierExpr scope}
    (proof :
      DOTCapture.Intersections.GeneralExpression.ClassifiersDisjoint
        sourceContext left right) :
    DOTCapture.ModalIntersections.ClassifiersDisjoint
      (context sourceContext) (classifier left) (classifier right) :=
  match proof with
  | .ground disjoint => .ground disjoint
  | .member exposes occurrence => by
      have embeddedOccurrence := hasClassifierDisjointOccurrence occurrence
      rw [objectType_interface] at embeddedOccurrence
      simpa only [classifier_openAt] using
        DOTCapture.ModalIntersections.ClassifiersDisjoint.member
          (exposesObject exposes) embeddedOccurrence
  | .symm inner => .symm (classifiersDisjoint inner)

/-- Classifier inclusion embeds through the cumulative classifier judgment.
The old source has no implicit exclusion rule: every constructor remains
proof-relevant. -/
def classifierIncludes {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {lower upper : DOTCapture.Intersections.Source.ClassifierExpr scope}
    (proof : DOTCapture.Intersections.GeneralExpression.ClassifierIncludes
      sourceContext lower upper) :
    DOTCapture.ModalIntersections.ClassifierIncludes (context sourceContext)
      (classifier lower) (classifier upper) :=
  match proof with
  | .refl => .refl
  | .trans first second =>
      .trans (classifierIncludes first) (classifierIncludes second)
  | .ground included => .ground included
  | .lower exposes occurrence => by
      have embeddedOccurrence := hasClassifierOccurrence occurrence
      rw [objectType_interface] at embeddedOccurrence
      rw [classifier_openAt]
      exact DOTCapture.ModalIntersections.ClassifierIncludes.lower
        (exposesObject exposes) embeddedOccurrence
  | .upper exposes occurrence => by
      have embeddedOccurrence := hasClassifierOccurrence occurrence
      rw [objectType_interface] at embeddedOccurrence
      rw [classifier_openAt]
      exact DOTCapture.ModalIntersections.ClassifierIncludes.upper
        (exposesObject exposes) embeddedOccurrence

/-- Capture-kind membership embeds compositionally, including project and
the exact stable object-theory constraint used by a member proof. -/
def captureHasKind {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sourceCapture : DOTCapture.Intersections.Source.Capture scope}
    {sourceClassifier : DOTCapture.Intersections.Source.ClassifierExpr scope}
    (proof : DOTCapture.Intersections.GeneralExpression.CaptureHasKind
      sourceContext sourceCapture sourceClassifier) :
    DOTCapture.ModalIntersections.CaptureHasKind (context sourceContext)
      (capture sourceCapture) (classifier sourceClassifier) :=
  match proof with
  | .empty => .empty
  | .union left right =>
      .union (captureHasKind left) (captureHasKind right)
  | .project => .project
  | .member exposes occurrence => by
      have embeddedOccurrence := hasCaptureKindOccurrence occurrence
      rw [objectType_interface] at embeddedOccurrence
      simpa only [capture_openAt, classifier_openAt] using
        DOTCapture.ModalIntersections.CaptureHasKind.member
          (exposesObject exposes) embeddedOccurrence
  | .widen membership included =>
      .widen (captureHasKind membership) (classifierIncludes included)

end DOTCapture.ModalIntersections.Embedding.CapturedIntersections
