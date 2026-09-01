import Coercions.DOT.Captures.Intersections.GeneralExpression.Typing
import Coercions.DOT.Captures.ModalIntersections.CapturedJudgmentEmbedding
import Coercions.DOT.Captures.ModalIntersections.Typing

/-!
# Typing conservativity for captured intersections

The M11 captured-intersection language occupies the all-term fragment of the
cumulative modal language.  This file records the pointwise embedding of its
models and object-theory judgments, then lifts complete computational typing
derivations into a typing environment with no active modal assumptions.
-/

namespace DOTCapture.ModalIntersections.Embedding.CapturedIntersections

open DOTCapture.ModalIntersections

namespace Old

abbrev Model :=
  DOTCapture.Intersections.GeneralExpression.LocalModel.Model
abbrev Mapping :=
  DOTCapture.Intersections.GeneralExpression.LocalModel.Mapping

end Old

/-! ## Environments and structural operations -/

/-- Captured-intersection contexts have no active modal assumptions. -/
def typingEnvironment {scope : Nat}
    (sourceContext : DOTCapture.Intersections.Source.Ctx scope) :
    TypingEnv (termScope scope) :=
  ⟨context sourceContext, .nil⟩

@[simp]
theorem typingEnvironment_bindings {scope : Nat}
    (sourceContext : DOTCapture.Intersections.Source.Ctx scope) :
    (typingEnvironment sourceContext).bindings = context sourceContext :=
  rfl

@[simp]
theorem typingEnvironment_locks {scope : Nat}
    (sourceContext : DOTCapture.Intersections.Source.Ctx scope) :
    (typingEnvironment sourceContext).locks = ModalAssumptions.nil :=
  rfl

@[simp]
theorem typingEnvironment_extendTerm {scope : Nat}
    (sourceContext : DOTCapture.Intersections.Source.Ctx scope)
    (sourceType : DOTCapture.Intersections.Source.Ty scope) :
    typingEnvironment (sourceContext.extendTerm sourceType) =
      (typingEnvironment sourceContext).extendTerm (type sourceType) :=
  rfl

@[simp]
theorem objectType_formedType {scope : Nat}
    (sourceObject : DOTCapture.Intersections.Source.ObjectType scope) :
    type sourceObject.formedType = (objectType sourceObject).formedType := by
  cases sourceObject
  rfl

@[simp]
theorem generalObjectType_formedType {scope : Nat}
    (sourceObject : DOTCapture.Intersections.Source.ObjectType scope) :
    type
        (DOTCapture.Intersections.GeneralExpression.ObjectType.formedType
          sourceObject) =
      (objectType sourceObject).formedType := by
  cases sourceObject
  rfl

/-- The historical captured-intersection object embeds as an ordinary
object, whose existential package and advertised representation use the same
ambient capture annotation. -/
@[simp]
theorem objectType_packageCapture {scope : Nat}
    (sourceObject : DOTCapture.Intersections.Source.ObjectType scope) :
    capture sourceObject.outerCapture =
      (objectType sourceObject).packageCapture := by
  cases sourceObject
  rfl

/-- Embedded M11 object types inhabit the ordinary (non-contracted)
constructor of the cumulative language. -/
@[simp]
theorem objectType_eq_mk {scope : Nat}
    (sourceObject : DOTCapture.Intersections.Source.ObjectType scope) :
    objectType sourceObject =
      .mk (interface sourceObject.interface)
        (type sourceObject.representation)
        (capture sourceObject.outerCapture) := by
  cases sourceObject
  rfl

/-- Realizing the advertised capture of an embedded historical object is an
identity: its sole capture annotation is ambient, not a local member
contract. -/
@[simp]
theorem objectType_realizedOuterCapture {scope : Nat}
    (sourceObject : DOTCapture.Intersections.Source.ObjectType scope)
    (model : LocalModel.Model (termScope scope)) :
    (objectType sourceObject).realizedOuterCapture model =
      (objectType sourceObject).outerCapture := by
  cases sourceObject
  rfl

/-- Structural mappings likewise leave the ambient advertised capture of an
embedded ordinary object unchanged. -/
@[simp]
theorem objectType_mappedOuterCapture {scope : Nat}
    (sourceObject : DOTCapture.Intersections.Source.ObjectType scope)
    (mapping : LocalModel.Mapping (termScope scope)) :
    (objectType sourceObject).mappedOuterCapture mapping =
      (objectType sourceObject).outerCapture := by
  cases sourceObject
  rfl

@[simp]
theorem capture_seq {scope : Nat}
    (first second : DOTCapture.Intersections.Source.Capture scope) :
    capture (DOTCapture.Intersections.Source.Capture.seq first second) =
      (capture first).seq (capture second) := by
  cases first <;> rfl

/-- M11's ordinary-binding side condition is unchanged by embedding. -/
theorem plain {scope : Nat}
    {sourceType : DOTCapture.Intersections.Source.Ty scope}
    (proof : DOTCapture.Intersections.GeneralExpression.Plain sourceType) :
    Plain (type sourceType) := by
  unfold DOTCapture.Intersections.GeneralExpression.Plain at proof
  unfold Plain
  rw [← type_stripCapture]
  generalize sourceType.stripCapture = stripped at proof ⊢
  cases stripped <;> exact proof

/-! ## Local models and simultaneous realization -/

/-- Translate every witness in an M11 local model pointwise. -/
def localModel {scope : Nat} (model : Old.Model scope) :
    LocalModel.Model (termScope scope) where
  typeMember := fun label => type (model.typeMember label)
  captureMember := fun label => capture (model.captureMember label)
  classifierMember := fun label => classifier (model.classifierMember label)

/-- Translate every symbolic image in an M11 theory mapping pointwise. -/
def localMapping {scope : Nat} (mapping : Old.Mapping scope) :
    LocalModel.Mapping (termScope scope) where
  typeMember := fun label => type (mapping.typeMember label)
  captureMember := fun label => capture (mapping.captureMember label)
  classifierMember := fun label => classifier (mapping.classifierMember label)

@[simp]
theorem localModel_atPath {scope : Nat}
    (receiver : DOTCapture.Intersections.Source.Path scope) :
    localModel
        (DOTCapture.Intersections.GeneralExpression.LocalModel.atPath
          receiver) =
      LocalModel.atPath (path receiver) := by
  rfl

@[simp]
theorem sourceClassifier_realizeLocals_atPath {scope : Nat}
    (receiver : DOTCapture.Intersections.Source.Path scope)
    (sourceClassifier : DOTCapture.Intersections.Source.ClassifierExpr scope) :
    DOTCapture.Intersections.GeneralExpression.ClassifierExpr.realizeLocals
        (DOTCapture.Intersections.GeneralExpression.LocalModel.atPath receiver)
        sourceClassifier =
      DOTCapture.Intersections.Source.ClassifierExpr.openAt receiver
        sourceClassifier := by
  cases sourceClassifier with
  | ground _ => rfl
  | ref reference => cases reference <;> rfl

@[simp]
def classifier_realizeLocals {scope : Nat} (model : Old.Model scope)
    (sourceClassifier : DOTCapture.Intersections.Source.ClassifierExpr scope) :
    classifier
        (DOTCapture.Intersections.GeneralExpression.ClassifierExpr.realizeLocals
          model sourceClassifier) =
      (classifier sourceClassifier).realizeLocals (localModel model) :=
  match sourceClassifier with
  | .ground _ => rfl
  | .ref reference => by cases reference <;> rfl

mutual

@[simp]
def capture_realizeLocals {scope : Nat} (model : Old.Model scope)
    (sourceCapture : DOTCapture.Intersections.Source.Capture scope) :
    capture
        (DOTCapture.Intersections.GeneralExpression.Capture.realizeLocals
          model sourceCapture) =
      (capture sourceCapture).realizeLocals (localModel model) :=
  match sourceCapture with
  | .empty => rfl
  | .union left right => by
      simp only [DOTCapture.Intersections.GeneralExpression.Capture.realizeLocals,
        capture, Capture.realizeLocals, capture_realizeLocals model left,
        capture_realizeLocals model right]
  | .project sourceCapture sourceClassifier => by
      simp only [DOTCapture.Intersections.GeneralExpression.Capture.realizeLocals,
        capture, Capture.realizeLocals,
        capture_realizeLocals model sourceCapture,
        classifier_realizeLocals model sourceClassifier]
  | .singleton _ => rfl
  | .ref reference => by cases reference <;> rfl

@[simp]
def type_realizeLocals {scope : Nat} (model : Old.Model scope)
    (sourceType : DOTCapture.Intersections.Source.Ty scope) :
    type
        (DOTCapture.Intersections.GeneralExpression.Ty.realizeLocals
          model sourceType) =
      (type sourceType).realizeLocals (localModel model) :=
  match sourceType with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by cases reference <;> rfl
  | .arr domain codomain => by
      simp only [DOTCapture.Intersections.GeneralExpression.Ty.realizeLocals,
        type, Ty.realizeLocals, type_realizeLocals model domain,
        type_realizeLocals model codomain]
  | .capturing captures shape => by
      simp only [DOTCapture.Intersections.GeneralExpression.Ty.realizeLocals,
        type, Ty.realizeLocals, capture_realizeLocals model captures,
        type_realizeLocals model shape]
  | .object _ => rfl

end

@[simp]
theorem localMapping_mapType {scope : Nat} (mapping : Old.Mapping scope)
    (sourceType : DOTCapture.Intersections.Source.Ty scope) :
    type (mapping.mapType sourceType) =
      (localMapping mapping).mapType (type sourceType) :=
  type_realizeLocals mapping.asModel sourceType

@[simp]
theorem localMapping_mapCapture {scope : Nat} (mapping : Old.Mapping scope)
    (sourceCapture : DOTCapture.Intersections.Source.Capture scope) :
    capture (mapping.mapCapture sourceCapture) =
      (localMapping mapping).mapCapture (capture sourceCapture) :=
  capture_realizeLocals mapping.asModel sourceCapture

@[simp]
theorem localMapping_mapClassifier {scope : Nat} (mapping : Old.Mapping scope)
    (sourceClassifier : DOTCapture.Intersections.Source.ClassifierExpr scope) :
    classifier (mapping.mapClassifier sourceClassifier) =
      (localMapping mapping).mapClassifier (classifier sourceClassifier) :=
  classifier_realizeLocals mapping.asModel sourceClassifier

@[simp]
theorem localMapping_apply {scope : Nat} (mapping : Old.Mapping scope)
    (model : Old.Model scope) :
    localModel (mapping.apply model) =
      (localMapping mapping).apply (localModel model) := by
  unfold localModel localMapping
    DOTCapture.Intersections.GeneralExpression.LocalModel.Mapping.apply
    LocalModel.Mapping.apply
  congr
  · funext label
    exact type_realizeLocals model (mapping.typeMember label)
  · funext label
    exact capture_realizeLocals model (mapping.captureMember label)
  · funext label
    exact classifier_realizeLocals model (mapping.classifierMember label)

@[simp]
theorem objectType_realizedRepresentation {scope : Nat}
    (sourceObject : DOTCapture.Intersections.Source.ObjectType scope)
    (model : Old.Model scope) :
    type (DOTCapture.Intersections.GeneralExpression.ObjectType.realizedRepresentation
        sourceObject model) =
      ObjectType.realizedRepresentation (objectType sourceObject)
        (localModel model) := by
  cases sourceObject
  exact type_realizeLocals model _

/-! ## Object-theory judgments -/

/-- The historical local theory now has a classifier sort, while the
cumulative calculus intentionally keeps classifier inclusion in its own
judgment family. -/
def EmbeddedLocalTheoryIncludes {scope : Nat}
    (sourceContext : DOTCapture.Intersections.Source.Ctx scope)
    (available : DOTCapture.Intersections.Source.Interface scope) :
    {sort : DOTCapture.Intersections.Source.StaticSort} ->
      DOTCapture.Intersections.Source.StaticExpr sort scope ->
      DOTCapture.Intersections.Source.StaticExpr sort scope -> Type
  | .type, lower, upper =>
      LocalTheory.Includes (context sourceContext) (interface available)
        (staticExpr lower) (staticExpr upper)
  | .capture, lower, upper =>
      LocalTheory.Includes (context sourceContext) (interface available)
        (staticExpr lower) (staticExpr upper)
  | .classifier, lower, upper =>
      LocalTheory.ClassifierIncludes (context sourceContext)
        (interface available) (staticExpr lower) (staticExpr upper)

private def embeddedLocalTheoryAmbient {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {available : DOTCapture.Intersections.Source.Interface scope}
    {sort : DOTCapture.Intersections.Source.StaticSort}
    {lower upper : DOTCapture.Intersections.Source.StaticExpr sort scope}
    (proof : EmbeddedIncludes sourceContext lower upper) :
    EmbeddedLocalTheoryIncludes sourceContext available lower upper :=
  match lower, upper with
  | .type _, .type _ => LocalTheory.Includes.ambient proof
  | .capture _, .capture _ => LocalTheory.Includes.ambient proof
  | .classifier _, .classifier _ =>
      LocalTheory.ClassifierIncludes.ambient proof

private def embeddedLocalTheoryTrans {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {available : DOTCapture.Intersections.Source.Interface scope}
    {sort : DOTCapture.Intersections.Source.StaticSort}
    {lower middle upper :
      DOTCapture.Intersections.Source.StaticExpr sort scope}
    (first : EmbeddedLocalTheoryIncludes sourceContext available lower middle)
    (second : EmbeddedLocalTheoryIncludes sourceContext available middle upper) :
    EmbeddedLocalTheoryIncludes sourceContext available lower upper :=
  match lower, middle, upper with
  | .type _, .type _, .type _ => LocalTheory.Includes.trans first second
  | .capture _, .capture _, .capture _ =>
      LocalTheory.Includes.trans first second
  | .classifier _, .classifier _, .classifier _ =>
      LocalTheory.ClassifierIncludes.trans first second

/-- Symbolic local-theory inclusion preserves every exact occurrence. -/
def localTheoryIncludes {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {available : DOTCapture.Intersections.Source.Interface scope}
    {sort : DOTCapture.Intersections.Source.StaticSort}
    {lower upper : DOTCapture.Intersections.Source.StaticExpr sort scope}
    (proof :
      DOTCapture.Intersections.GeneralExpression.LocalTheory.Includes
        sourceContext available lower upper) :
    EmbeddedLocalTheoryIncludes sourceContext available lower upper :=
  match proof with
  | .ambient ambient => embeddedLocalTheoryAmbient (generalIncludes ambient)
  | .typeLower occurrence => LocalTheory.Includes.typeLower
      (hasTypeOccurrence occurrence)
  | .typeUpper occurrence => LocalTheory.Includes.typeUpper
      (hasTypeOccurrence occurrence)
  | .captureLower occurrence => LocalTheory.Includes.captureLower
      (hasCaptureOccurrence occurrence)
  | .captureUpper occurrence => LocalTheory.Includes.captureUpper
      (hasCaptureOccurrence occurrence)
  | .trans first second =>
      embeddedLocalTheoryTrans (localTheoryIncludes first)
        (localTheoryIncludes second)

/-- Embed classifier inclusion under an opened raw object theory. -/
def localTheoryClassifierIncludes {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {available : DOTCapture.Intersections.Source.Interface scope}
    {lower upper : DOTCapture.Intersections.Source.ClassifierExpr scope}
    (proof :
      DOTCapture.Intersections.GeneralExpression.LocalTheory.ClassifierIncludes
        sourceContext available lower upper) :
    LocalTheory.ClassifierIncludes (context sourceContext)
      (interface available) (classifier lower) (classifier upper) :=
  match proof with
  | .ambient ambient => .ambient (classifierIncludes ambient)
  | .lower occurrence => .lower (hasClassifierOccurrence occurrence)
  | .upper occurrence => .upper (hasClassifierOccurrence occurrence)
  | .trans first second =>
      .trans (localTheoryClassifierIncludes first)
        (localTheoryClassifierIncludes second)

/-- Embed classifier disjointness under an opened raw object theory. -/
def localTheoryClassifiersDisjoint {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {available : DOTCapture.Intersections.Source.Interface scope}
    {left right : DOTCapture.Intersections.Source.ClassifierExpr scope}
    (proof :
      DOTCapture.Intersections.GeneralExpression.LocalTheory.ClassifiersDisjoint
        sourceContext available left right) :
    LocalTheory.ClassifiersDisjoint (context sourceContext)
      (interface available) (classifier left) (classifier right) :=
  match proof with
  | .ambient ambient => .ambient (classifiersDisjoint ambient)
  | .assumption occurrence =>
      .assumption (hasClassifierDisjointOccurrence occurrence)
  | .symm inner => .symm (localTheoryClassifiersDisjoint inner)

/-- Embed capture-kind membership under an opened raw object theory. -/
def localTheoryCaptureHasKind {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {available : DOTCapture.Intersections.Source.Interface scope}
    {sourceCapture : DOTCapture.Intersections.Source.Capture scope}
    {sourceClassifier : DOTCapture.Intersections.Source.ClassifierExpr scope}
    (proof :
      DOTCapture.Intersections.GeneralExpression.LocalTheory.CaptureHasKind
        sourceContext available sourceCapture sourceClassifier) :
    LocalTheory.CaptureHasKind (context sourceContext) (interface available)
      (capture sourceCapture) (classifier sourceClassifier) :=
  match proof with
  | .ambient ambient => .ambient (captureHasKind ambient)
  | .assumption occurrence => .assumption (hasCaptureKindOccurrence occurrence)
  | .widen membership included =>
      .widen (localTheoryCaptureHasKind membership)
        (localTheoryClassifierIncludes included)

/-- A positive M11 realization remains a positive cumulative realization. -/
def interfaceRealizes {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {model : Old.Model scope}
    {sourceInterface : DOTCapture.Intersections.Source.Interface scope}
    (proof : DOTCapture.Intersections.GeneralExpression.Interface.Realizes
      sourceContext model sourceInterface) :
    Interface.Realizes (context sourceContext) (localModel model)
      (interface sourceInterface) :=
  match proof with
  | .empty => .empty
  | .typeMember lowerProof upperProof =>
      .typeMember
        (by simpa only [EmbeddedIncludes, staticExpr, localModel,
            type_realizeLocals] using
          generalIncludes lowerProof)
        (by simpa only [EmbeddedIncludes, staticExpr, localModel,
            type_realizeLocals] using
          generalIncludes upperProof)
  | .captureMember lowerProof upperProof =>
      .captureMember
        (by simpa only [EmbeddedIncludes, staticExpr, localModel,
            capture_realizeLocals] using
          generalIncludes lowerProof)
        (by simpa only [EmbeddedIncludes, staticExpr, localModel,
            capture_realizeLocals] using
          generalIncludes upperProof)
  | .classifierMember lowerProof upperProof =>
      .classifierMember
        (by simpa only [localModel, classifier_realizeLocals] using
          classifierIncludes lowerProof)
        (by simpa only [localModel, classifier_realizeLocals] using
          classifierIncludes upperProof)
  | .classifierDisjoint disjoint =>
      .classifierDisjoint
        (by simpa only [localModel, classifier_realizeLocals] using
          classifiersDisjoint disjoint)
  | .captureHasKind membership =>
      .captureHasKind
        (by simpa only [localModel, capture_realizeLocals,
            classifier_realizeLocals] using
          captureHasKind membership)
  | .inter left right =>
      .inter (interfaceRealizes left) (interfaceRealizes right)

/-- Every symbolic cross-shape proof embeds constructor for constructor. -/
def interfaceDerives {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {available expected : DOTCapture.Intersections.Source.Interface scope}
    {mapping : Old.Mapping scope}
    (proof : DOTCapture.Intersections.GeneralExpression.Interface.Derives
      sourceContext available mapping expected) :
    Interface.Derives (context sourceContext) (interface available)
      (localMapping mapping) (interface expected) :=
  match proof with
  | .empty => .empty
  | .typeMember lowerProof upperProof =>
      .typeMember
        (by simpa only [EmbeddedLocalTheoryIncludes, staticExpr, localMapping,
            localMapping_mapType] using
          localTheoryIncludes lowerProof)
        (by simpa only [EmbeddedLocalTheoryIncludes, staticExpr, localMapping,
            localMapping_mapType] using
          localTheoryIncludes upperProof)
  | .captureMember lowerProof upperProof =>
      .captureMember
        (by simpa only [EmbeddedLocalTheoryIncludes, staticExpr, localMapping,
            localMapping_mapCapture] using
          localTheoryIncludes lowerProof)
        (by simpa only [EmbeddedLocalTheoryIncludes, staticExpr, localMapping,
            localMapping_mapCapture] using
          localTheoryIncludes upperProof)
  | .classifierMember lowerProof upperProof =>
      .classifierMember
        (by simpa only [localMapping,
            localMapping_mapClassifier] using
          localTheoryClassifierIncludes lowerProof)
        (by simpa only [localMapping,
            localMapping_mapClassifier] using
          localTheoryClassifierIncludes upperProof)
  | .classifierDisjoint disjoint =>
      .classifierDisjoint
        (by simpa only [localMapping,
            localMapping_mapClassifier] using
          localTheoryClassifiersDisjoint disjoint)
  | .captureHasKind membership =>
      .captureHasKind
        (by simpa only [localMapping, localMapping_mapCapture,
            localMapping_mapClassifier] using
          localTheoryCaptureHasKind membership)
  | .inter left right =>
      .inter (interfaceDerives left) (interfaceDerives right)

/-- A complete positive M11 object model embeds pointwise. -/
def objectRealization {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sourceObject : DOTCapture.Intersections.Source.ObjectType scope}
    (realization :
      DOTCapture.Intersections.GeneralExpression.ObjectType.Realization
        sourceContext sourceObject) :
    ObjectType.Realization (context sourceContext)
      (objectType sourceObject) where
  model := localModel realization.model
  constraints := by
    simpa only [objectType_interface] using
      interfaceRealizes realization.constraints

@[simp]
theorem objectRealization_model {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sourceObject : DOTCapture.Intersections.Source.ObjectType scope}
    (realization :
      DOTCapture.Intersections.GeneralExpression.ObjectType.Realization
        sourceContext sourceObject) :
    (objectRealization realization).model = localModel realization.model :=
  rfl

/-! ## Stable realizations and cross-shape views -/

/-- Opening a stable path realizes every occurrence in its exposed raw
interface.  This is the source-side certificate needed to specialize an M11
representation adaptation at a stable negative argument. -/
def interfaceRealizesAtPath {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {receiver : DOTCapture.Intersections.Source.Path scope}
    {sourceObject : DOTCapture.Intersections.Source.ObjectType scope}
    (exposes : DOTCapture.Intersections.Source.ExposesObject sourceContext
      receiver sourceObject) :
    (sourceInterface : DOTCapture.Intersections.Source.Interface scope) ->
    (typeInObject : forall {label lower upper},
      sourceInterface.HasTypeOccurrence label lower upper ->
        sourceObject.interface.HasTypeOccurrence label lower upper) ->
    (captureInObject : forall {label lower upper},
      sourceInterface.HasCaptureOccurrence label lower upper ->
        sourceObject.interface.HasCaptureOccurrence label lower upper) ->
    (classifierInObject : forall {label lower upper},
      DOTCapture.Intersections.GeneralExpression.Interface.HasClassifierOccurrence
          sourceInterface label lower upper ->
        DOTCapture.Intersections.GeneralExpression.Interface.HasClassifierOccurrence
          sourceObject.interface label lower upper) ->
    (disjointInObject : forall {left right},
      DOTCapture.Intersections.GeneralExpression.Interface.HasClassifierDisjointOccurrence
          sourceInterface left right ->
        DOTCapture.Intersections.GeneralExpression.Interface.HasClassifierDisjointOccurrence
          sourceObject.interface left right) ->
    (captureKindInObject : forall {sourceCapture sourceClassifier},
      DOTCapture.Intersections.GeneralExpression.Interface.HasCaptureKindOccurrence
          sourceInterface sourceCapture sourceClassifier ->
        DOTCapture.Intersections.GeneralExpression.Interface.HasCaptureKindOccurrence
          sourceObject.interface sourceCapture sourceClassifier) ->
      DOTCapture.Intersections.GeneralExpression.Interface.Realizes
        sourceContext
        (DOTCapture.Intersections.GeneralExpression.LocalModel.atPath receiver)
        sourceInterface
  | .empty, _, _, _, _, _ => .empty
  | .typeMember _ _ _, typeInObject, _, _, _, _ =>
      .typeMember
        (by simpa using
          (DOTCapture.Intersections.GeneralExpression.Includes.source
            (DOTCapture.Intersections.Source.Includes.lower
              (DOTCapture.Intersections.Source.HasLower.typeMember exposes
                (typeInObject
                  DOTCapture.Intersections.Source.Interface.HasTypeOccurrence.here)))))
        (by simpa using
          (DOTCapture.Intersections.GeneralExpression.Includes.source
            (DOTCapture.Intersections.Source.Includes.upper
              (DOTCapture.Intersections.Source.HasUpper.typeMember exposes
                (typeInObject
                  DOTCapture.Intersections.Source.Interface.HasTypeOccurrence.here)))))
  | .captureMember _ _ _, _, captureInObject, _, _, _ =>
      .captureMember
        (by simpa using
          (DOTCapture.Intersections.GeneralExpression.Includes.source
            (DOTCapture.Intersections.Source.Includes.lower
              (DOTCapture.Intersections.Source.HasLower.captureMember exposes
                (captureInObject
                  DOTCapture.Intersections.Source.Interface.HasCaptureOccurrence.here)))))
        (by simpa using
          (DOTCapture.Intersections.GeneralExpression.Includes.source
            (DOTCapture.Intersections.Source.Includes.upper
              (DOTCapture.Intersections.Source.HasUpper.captureMember exposes
                (captureInObject
                  DOTCapture.Intersections.Source.Interface.HasCaptureOccurrence.here)))))
  | .classifierMember _ _ _, _, _, classifierInObject, _, _ =>
      .classifierMember
        (by simpa using
          (DOTCapture.Intersections.GeneralExpression.ClassifierIncludes.lower
            exposes
            (classifierInObject
              DOTCapture.Intersections.GeneralExpression.Interface.HasClassifierOccurrence.here)))
        (by simpa using
          (DOTCapture.Intersections.GeneralExpression.ClassifierIncludes.upper
            exposes
            (classifierInObject
              DOTCapture.Intersections.GeneralExpression.Interface.HasClassifierOccurrence.here)))
  | .classifierDisjoint _ _, _, _, _, disjointInObject, _ =>
      .classifierDisjoint
        (DOTCapture.Intersections.GeneralExpression.ClassifiersDisjoint.member
          exposes
          (disjointInObject
            DOTCapture.Intersections.GeneralExpression.Interface.HasClassifierDisjointOccurrence.here))
  | .captureHasKind _ _, _, _, _, _, captureKindInObject =>
      .captureHasKind
        (by simpa only [
            DOTCapture.Intersections.GeneralExpression.Capture.realizeLocals_atPath,
            sourceClassifier_realizeLocals_atPath] using
          (DOTCapture.Intersections.GeneralExpression.CaptureHasKind.member
            exposes
            (captureKindInObject
              DOTCapture.Intersections.GeneralExpression.Interface.HasCaptureKindOccurrence.here)))
  | .inter left right, typeInObject, captureInObject, classifierInObject,
      disjointInObject, captureKindInObject =>
      .inter
        (interfaceRealizesAtPath exposes left
          (fun occurrence => typeInObject (.left occurrence))
          (fun occurrence => captureInObject (.left occurrence))
          (fun occurrence => classifierInObject (.left occurrence))
          (fun occurrence => disjointInObject (.left occurrence))
          (fun occurrence => captureKindInObject (.left occurrence)))
        (interfaceRealizesAtPath exposes right
          (fun occurrence => typeInObject (.right occurrence))
          (fun occurrence => captureInObject (.right occurrence))
          (fun occurrence => classifierInObject (.right occurrence))
          (fun occurrence => disjointInObject (.right occurrence))
          (fun occurrence => captureKindInObject (.right occurrence)))

/-- The positive-style source realization exposed by an object variable. -/
def objectRealizationAtVariable {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    (name : DOTCapture.Acyclic.Var scope)
    (sourceObject : DOTCapture.Intersections.Source.ObjectType scope)
    (canonical : sourceContext.lookup name =
      DOTCapture.Intersections.GeneralExpression.ObjectType.formedType
        sourceObject) :
    DOTCapture.Intersections.GeneralExpression.ObjectType.Realization
      sourceContext sourceObject := by
  let exposes : DOTCapture.Intersections.Source.ExposesObject sourceContext
      (.var name) sourceObject := .variable (by
        rw [canonical]
        cases sourceObject
        rfl)
  exact
    { model :=
        DOTCapture.Intersections.GeneralExpression.LocalModel.atPath (.var name)
      constraints := interfaceRealizesAtPath exposes sourceObject.interface
        (fun occurrence => occurrence) (fun occurrence => occurrence)
        (fun occurrence => occurrence) (fun occurrence => occurrence)
        (fun occurrence => occurrence) }

/-- The structural portion of an M11 cross-shape view embeds without
quantifying over models from the larger cumulative syntax. -/
def objectAdapts {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {available expected : DOTCapture.Intersections.Source.ObjectType scope}
    (adaptation :
      DOTCapture.Intersections.GeneralExpression.ObjectType.Adapts
        sourceContext available expected) :
    ObjectType.Adapts (context sourceContext) (objectType available)
      (objectType expected) where
  mapping := localMapping adaptation.mapping
  theory := by
    simpa only [objectType_interface] using
      interfaceDerives adaptation.theory
  outerCapture := by
    simpa only [EmbeddedIncludes, staticExpr, objectType_outerCapture,
      objectType_mappedOuterCapture] using
      (LocalTheory.Includes.ambient
        (generalIncludes adaptation.outerCapture))
  packageCapture := by
    have translated := generalIncludes adaptation.outerCapture
    simp only [EmbeddedIncludes, staticExpr] at translated
    rw [objectType_packageCapture available,
      objectType_packageCapture expected] at translated
    exact translated

@[simp]
theorem objectAdapts_mapping {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {available expected : DOTCapture.Intersections.Source.ObjectType scope}
    (adaptation :
      DOTCapture.Intersections.GeneralExpression.ObjectType.Adapts
        sourceContext available expected) :
    (objectAdapts adaptation).mapping = localMapping adaptation.mapping :=
  rfl

/-- Specialize an old representation adaptation at an old model, then embed
the resulting proof.  This avoids the invalid claim that every enriched
cumulative model reflects into M11 syntax. -/
def objectAdaptationRepresentation {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {available expected : DOTCapture.Intersections.Source.ObjectType scope}
    (adaptation :
      DOTCapture.Intersections.GeneralExpression.ObjectType.Adapts
        sourceContext available expected)
    (model : Old.Model scope)
    (realization :
      DOTCapture.Intersections.GeneralExpression.Interface.Realizes
        sourceContext model available.interface) :
    TypeIncludes (context sourceContext)
      (ObjectType.realizedRepresentation (objectType available)
        (localModel model))
      (ObjectType.realizedRepresentation (objectType expected)
        ((objectAdapts adaptation).mapping.apply (localModel model))) := by
  simpa only [EmbeddedIncludes, staticExpr,
    objectType_realizedRepresentation,
    objectAdapts_mapping, localMapping_apply] using
      generalIncludes (adaptation.representation model realization)

/-- The exact cumulative model produced by an embedded M11 negative
argument.  The index is not existentially forgotten: native dependent object
application can inspect the corresponding model in its result type. -/
def objectArgumentModel {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sourceArgument : DOTCapture.Intersections.GeneralExpression.Term scope}
    {expected : DOTCapture.Intersections.Source.ObjectType scope}
    (typing :
      DOTCapture.Intersections.GeneralExpression.ObjectArgument.HasType
        sourceContext sourceArgument expected) :
    LocalModel.Model (termScope scope) :=
  match typing with
  | .literal realization _ _ _ _ adaptation _ =>
      (objectAdapts adaptation).mapping.apply
        (localModel realization.model)
  | @DOTCapture.Intersections.GeneralExpression.ObjectArgument.HasType.stable
      _ _ name _ _ _ adaptation _ =>
      (objectAdapts adaptation).mapping.apply
        (LocalModel.atPath (.var (embedVar name)))

/-! ## Complete computational typing conservativity -/

mutual

/-- Every M11 value derivation embeds at the same type in an environment with
an empty modal-assumption stack. -/
def valueTyping {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sourceValue : DOTCapture.Intersections.GeneralExpression.Value scope}
    {sourceType : DOTCapture.Intersections.Source.Ty scope}
    (typing : DOTCapture.Intersections.GeneralExpression.Value.HasType
      sourceContext sourceValue sourceType) :
    Value.HasType (typingEnvironment sourceContext) (value sourceValue)
      (type sourceType) :=
  match typing with
  | .var => by
      simpa only [value, typingEnvironment, context_lookup] using
        (Value.HasType.declaredVar
          (environment := typingEnvironment sourceContext))
  | .unit => .unit
  | @DOTCapture.Intersections.GeneralExpression.Value.HasType.lam _ _ domain
      codomain body bodyUse closure domainPlain bodyTyping captures => by
      have embeddedBody : Term.HasType
          ((typingEnvironment sourceContext).extendTerm (type domain))
          (term body) (capture bodyUse)
          ((type codomain).weaken (kind := .term)) := by
        simpa only [typingEnvironment_extendTerm, type_rename,
          embedRename_succ, Ty.weaken] using termTyping bodyTyping
      have embeddedCaptures : CaptureIncludes
          ((typingEnvironment sourceContext).extendTerm (type domain)).bindings
          (capture bodyUse)
          (.union ((capture closure).weaken (kind := .term))
            (.singleton (.var .here))) := by
        simpa only [EmbeddedIncludes, typingEnvironment_extendTerm, staticExpr,
          capture_rename, embedRename_succ, Capture.weaken, capture, path,
          embedVar] using generalIncludes captures
      simpa only [value, type] using
        (Value.HasType.lam (plain domainPlain) embeddedBody
          embeddedCaptures)
  | @DOTCapture.Intersections.GeneralExpression.Value.HasType.objectConsumer
      _ _ parameter result body bodyUse closure bodyTyping captures => by
      have embeddedBody : Term.HasType
          ((typingEnvironment sourceContext).extendTerm
            (objectType parameter).formedType)
          (term body) (capture bodyUse)
          ((type result).weaken (kind := .term)) := by
        simpa only [typingEnvironment_extendTerm,
          generalObjectType_formedType,
          type_rename, embedRename_succ, Ty.weaken] using
            termTyping bodyTyping
      have embeddedCaptures : CaptureIncludes
          ((typingEnvironment sourceContext).extendTerm
            (objectType parameter).formedType).bindings
          (capture bodyUse)
          (.union ((capture closure).weaken (kind := .term))
            (.singleton (.var .here))) := by
        simpa only [typingEnvironment_extendTerm,
          generalObjectType_formedType,
          context_extendTerm, EmbeddedIncludes, staticExpr, capture_rename,
          embedRename_succ,
          Capture.weaken, capture, path, embedVar] using
            generalIncludes captures
      simpa only [value, type, generalObjectType_formedType] using
        (Value.HasType.legacyObjectConsumer embeddedBody embeddedCaptures)
  | @DOTCapture.Intersections.GeneralExpression.Value.HasType.embeddedObjectConsumer
      _ _ parameter result body bodyUse closure bodyTyping captures => by
      have embeddedBody : Term.HasType
          ((typingEnvironment sourceContext).extendTerm
            (objectType parameter).formedType)
          (term body) (capture bodyUse)
          ((type result).weaken (kind := .term)) := by
        simpa only [typingEnvironment_extendTerm,
          generalObjectType_formedType,
          type_rename, embedRename_succ, Ty.weaken] using
            termTyping bodyTyping
      have embeddedCaptures : CaptureIncludes
          ((typingEnvironment sourceContext).extendTerm
            (objectType parameter).formedType).bindings
          (capture bodyUse)
          (.union ((capture closure).weaken (kind := .term))
            (.singleton (.var .here))) := by
        simpa only [typingEnvironment_extendTerm,
          generalObjectType_formedType,
          context_extendTerm, EmbeddedIncludes, staticExpr, capture_rename,
          embedRename_succ,
          Capture.weaken, capture, path, embedVar] using
            generalIncludes captures
      simpa only [value, type, generalObjectType_formedType] using
        (Value.HasType.embeddedObjectConsumer embeddedBody embeddedCaptures)
  | @DOTCapture.Intersections.GeneralExpression.Value.HasType.object _ _
      (.mk sourceInterface sourceRepresentation sourceOuterCapture)
      payload payloadType realization payloadTyping payloadShape
      payloadCapture objectCapture => by
      let sourceObject : DOTCapture.Intersections.Source.ObjectType scope :=
        .mk sourceInterface sourceRepresentation sourceOuterCapture
      have embeddedShape : TypeIncludes (context sourceContext)
          (type payloadType).stripCapture
          (ObjectType.realizedRepresentation (objectType sourceObject)
            (localModel realization.model)).stripCapture := by
        simpa only [EmbeddedIncludes, staticExpr, type_stripCapture,
          objectType_realizedRepresentation] using
            generalIncludes payloadShape
      have embeddedPayloadCapture : CaptureIncludes (context sourceContext)
          (type payloadType).outerCapture
          (ObjectType.realizedRepresentation (objectType sourceObject)
            (localModel realization.model)).outerCapture := by
        simpa only [EmbeddedIncludes, staticExpr, type_outerCapture,
          objectType_realizedRepresentation] using
            generalIncludes payloadCapture
      have embeddedObjectCapture : CaptureIncludes (context sourceContext)
          (ObjectType.realizedRepresentation (objectType sourceObject)
            (localModel realization.model)).outerCapture
          (objectType sourceObject).outerCapture := by
        have translated := generalIncludes objectCapture
        simp only [EmbeddedIncludes, staticExpr] at translated
        rw [type_outerCapture, objectType_realizedRepresentation,
          objectType_outerCapture] at translated
        exact translated
      simpa only [value, generalObjectType_formedType,
        typingEnvironment_bindings, objectType_eq_mk,
        objectRealization_model] using
        (Value.HasType.object (environment := typingEnvironment sourceContext)
          (interface := interface sourceObject.interface)
          (representation := type sourceObject.representation)
          (outerCapture := capture sourceObject.outerCapture)
          (objectRealization realization)
          (payloadType := type payloadType)
          (valueTyping payloadTyping) embeddedShape embeddedPayloadCapture
          embeddedObjectCapture)
  | .adapt inner inclusion =>
      .adapt (valueTyping inner) (.cast (generalIncludes inclusion))

/-- Canonical and stable M11 negative arguments retain their direct negative
interpretation; no package/open redex is inserted. -/
def objectArgumentTyping {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sourceArgument : DOTCapture.Intersections.GeneralExpression.Term scope}
    {expected : DOTCapture.Intersections.Source.ObjectType scope}
    (typing :
      DOTCapture.Intersections.GeneralExpression.ObjectArgument.HasType
      sourceContext sourceArgument expected) :
    ObjectArgument.HasType (typingEnvironment sourceContext)
      (term sourceArgument) (objectType expected)
      (objectArgumentModel typing) :=
  match typing with
  | @DOTCapture.Intersections.GeneralExpression.ObjectArgument.HasType.literal
      _ _ (.mk availableInterface availableRepresentation availableOuterCapture)
      (.mk expectedInterface expectedRepresentation expectedOuterCapture)
      payload payloadType realization payloadTyping
      payloadShape payloadCapture objectCapture adaptation expectedCapture => by
      let available : DOTCapture.Intersections.Source.ObjectType scope :=
        .mk availableInterface availableRepresentation availableOuterCapture
      let expected : DOTCapture.Intersections.Source.ObjectType scope :=
        .mk expectedInterface expectedRepresentation expectedOuterCapture
      have embeddedShape : TypeIncludes (context sourceContext)
          (type payloadType).stripCapture
          (ObjectType.realizedRepresentation (objectType available)
            (localModel realization.model)).stripCapture := by
        simpa only [EmbeddedIncludes, staticExpr, type_stripCapture,
          objectType_realizedRepresentation] using
            generalIncludes payloadShape
      have embeddedPayloadCapture : CaptureIncludes (context sourceContext)
          (type payloadType).outerCapture
          (ObjectType.realizedRepresentation (objectType available)
            (localModel realization.model)).outerCapture := by
        simpa only [EmbeddedIncludes, staticExpr, type_outerCapture,
          objectType_realizedRepresentation] using
            generalIncludes payloadCapture
      have embeddedObjectCapture : CaptureIncludes (context sourceContext)
          (ObjectType.realizedRepresentation (objectType available)
            (localModel realization.model)).outerCapture
          (objectType available).outerCapture := by
        have translated := generalIncludes objectCapture
        simp only [EmbeddedIncludes, staticExpr] at translated
        rw [type_outerCapture, objectType_realizedRepresentation,
          objectType_outerCapture] at translated
        exact translated
      have embeddedExpectedCapture : CaptureIncludes (context sourceContext)
          (ObjectType.realizedRepresentation (objectType expected)
            ((objectAdapts adaptation).mapping.apply
              (localModel realization.model))).outerCapture
          (objectType expected).outerCapture := by
        have translated := generalIncludes expectedCapture
        simp only [EmbeddedIncludes, staticExpr] at translated
        rw [type_outerCapture, objectType_realizedRepresentation,
          localMapping_apply, objectType_outerCapture] at translated
        simpa only [objectAdapts_mapping] using translated
      simpa only [term, value, objectArgumentModel] using
        (ObjectArgument.HasType.literal
          (environment := typingEnvironment sourceContext)
          (interface := interface available.interface)
          (representationType := type available.representation)
          (outerCapture := capture available.outerCapture)
          (expected := objectType expected)
          (expectedInterface := interface expected.interface)
          (expectedRepresentation := type expected.representation)
          (expectedOuterCapture := capture expected.outerCapture)
          (payload := value payload) (payloadType := type payloadType)
          (objectType_eq_mk expected)
          (objectRealization realization) (valueTyping payloadTyping)
          embeddedShape embeddedPayloadCapture embeddedObjectCapture
          (objectAdapts adaptation)
          (objectAdaptationRepresentation adaptation realization.model
            realization.constraints)
          embeddedExpectedCapture)
  | @DOTCapture.Intersections.GeneralExpression.ObjectArgument.HasType.stable
      _ sourceContext name available expected canonical adaptation
      expectedCapture => by
      let realization := objectRealizationAtVariable name available canonical
      have representation := objectAdaptationRepresentation adaptation
        realization.model realization.constraints
      have embeddedCanonical :
          (typingEnvironment sourceContext).bindings.lookupTerm
              (embedVar name) =
            (objectType available).formedType := by
        rw [typingEnvironment_bindings, ← context_lookup sourceContext name,
          canonical, generalObjectType_formedType]
      have embeddedRepresentation : TypeIncludes (context sourceContext)
          (ObjectType.realizedRepresentation (objectType available)
            (LocalModel.atPath (.var (embedVar name))))
          (ObjectType.realizedRepresentation (objectType expected)
            ((objectAdapts adaptation).mapping.apply
              (LocalModel.atPath (.var (embedVar name))))) := by
        simpa only [realization, objectRealizationAtVariable,
          localModel_atPath] using representation
      have embeddedExpectedCapture : CaptureIncludes (context sourceContext)
          (ObjectType.realizedRepresentation (objectType expected)
            ((objectAdapts adaptation).mapping.apply
              (LocalModel.atPath (.var (embedVar name))))).outerCapture
          (objectType expected).outerCapture := by
        have translated := generalIncludes expectedCapture
        simp only [EmbeddedIncludes, staticExpr] at translated
        rw [type_outerCapture, objectType_realizedRepresentation,
          localMapping_apply, localModel_atPath,
          objectType_outerCapture] at translated
        simpa only [objectAdapts_mapping, path] using translated
      have embeddedRealizedExpectedCapture : CaptureIncludes
          (context sourceContext)
          (ObjectType.realizedRepresentation (objectType expected)
            ((objectAdapts adaptation).mapping.apply
              (LocalModel.atPath (.var (embedVar name))))).outerCapture
          ((objectType expected).realizedOuterCapture
            ((objectAdapts adaptation).mapping.apply
              (LocalModel.atPath (.var (embedVar name))))) := by
        simpa only [objectType_realizedOuterCapture] using
          embeddedExpectedCapture
      simpa only [term, value, typingEnvironment, context_lookup,
        generalObjectType_formedType, objectType_realizedRepresentation,
        objectType_realizedOuterCapture,
        objectAdapts_mapping, localMapping_apply, localModel_atPath,
        EmbeddedIncludes, staticExpr, objectArgumentModel] using
        (ObjectArgument.HasType.stable
          (environment := typingEnvironment sourceContext)
          (name := embedVar name) (available := objectType available)
          (expected := objectType expected)
          embeddedCanonical (objectAdapts adaptation)
          embeddedRepresentation embeddedRealizedExpectedCapture)

/-- Every M11 negative-function derivation embeds without changing its
administrative computation spine. -/
def objectFunctionTyping {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sourceFunction : DOTCapture.Intersections.GeneralExpression.Term scope}
    {sourceUse : DOTCapture.Intersections.Source.Capture scope}
    {parameter : DOTCapture.Intersections.Source.ObjectType scope}
    {result : DOTCapture.Intersections.Source.Ty scope}
    {closure : DOTCapture.Intersections.Source.Capture scope}
    (typing : DOTCapture.Intersections.GeneralExpression.ObjectFunction.HasType
      sourceContext sourceFunction sourceUse parameter result closure) :
    ObjectFunction.HasType (typingEnvironment sourceContext)
      (term sourceFunction) (capture sourceUse) (objectType parameter)
      (type result) (capture closure) :=
  match typing with
  | @DOTCapture.Intersections.GeneralExpression.ObjectFunction.HasType.returned
      _ _ parameter result body bodyUse closure bodyTyping captures => by
      have embeddedBody : Term.HasType
          ((typingEnvironment sourceContext).extendTerm
            (objectType parameter).formedType)
          (term body) (capture bodyUse)
          ((type result).weaken (kind := .term)) := by
        simpa only [typingEnvironment_extendTerm,
          generalObjectType_formedType, type_rename, embedRename_succ,
          Ty.weaken] using termTyping bodyTyping
      have embeddedCaptures : CaptureIncludes
          ((typingEnvironment sourceContext).extendTerm
            (objectType parameter).formedType).bindings
          (capture bodyUse)
          (.union ((capture closure).weaken (kind := .term))
            (.singleton (.var .here))) := by
        simpa only [typingEnvironment_extendTerm, context_extendTerm,
          generalObjectType_formedType, EmbeddedIncludes, staticExpr,
          capture_rename,
          embedRename_succ, Capture.weaken, capture, path, embedVar] using
            generalIncludes captures
      simpa only [term, value, capture] using
        (ObjectFunction.HasType.returned embeddedBody embeddedCaptures)
  | @DOTCapture.Intersections.GeneralExpression.ObjectFunction.HasType.embeddedReturned
      _ _ parameter result body bodyUse closure bodyTyping captures => by
      have embeddedBody : Term.HasType
          ((typingEnvironment sourceContext).extendTerm
            (objectType parameter).formedType)
          (term body) (capture bodyUse)
          ((type result).weaken (kind := .term)) := by
        simpa only [typingEnvironment_extendTerm,
          generalObjectType_formedType, type_rename, embedRename_succ,
          Ty.weaken] using termTyping bodyTyping
      have embeddedCaptures : CaptureIncludes
          ((typingEnvironment sourceContext).extendTerm
            (objectType parameter).formedType).bindings
          (capture bodyUse)
          (.union ((capture closure).weaken (kind := .term))
            (.singleton (.var .here))) := by
        simpa only [typingEnvironment_extendTerm, context_extendTerm,
          generalObjectType_formedType, EmbeddedIncludes, staticExpr,
          capture_rename,
          embedRename_succ, Capture.weaken, capture, path, embedVar] using
            generalIncludes captures
      simpa only [term, value, generalObjectType_formedType, capture] using
        (ObjectFunction.HasType.embeddedReturned embeddedBody embeddedCaptures)
  | @DOTCapture.Intersections.GeneralExpression.ObjectFunction.HasType.letPlain
      _ _ parameter result bound closure rhs body rhsUse bodyUse
      bodyOuterUse boundPlain rhsTyping bodyTyping discharge => by
      have embeddedBody : ObjectFunction.HasType
          ((typingEnvironment sourceContext).extendTerm (type bound))
          (term body) (capture bodyUse)
          ((objectType parameter).weaken (kind := .term))
          ((type result).weaken (kind := .term))
          ((capture closure).weaken (kind := .term)) := by
        simpa only [typingEnvironment_extendTerm, objectType_rename,
          type_rename, capture_rename, embedRename_succ, ObjectType.weaken,
          Ty.weaken, Capture.weaken] using
            objectFunctionTyping bodyTyping
      have embeddedDischarge : CaptureIncludes
          ((typingEnvironment sourceContext).extendTerm (type bound)).bindings
          (capture bodyUse)
          ((capture bodyOuterUse).weaken (kind := .term)) := by
        simpa only [typingEnvironment_extendTerm, context_extendTerm,
          EmbeddedIncludes, staticExpr, capture_rename, embedRename_succ,
          Capture.weaken] using
            generalIncludes discharge
      simpa only [term, type, capture, generalObjectType_formedType] using
        (ObjectFunction.HasType.letPlain (plain boundPlain)
          (termTyping rhsTyping) embeddedBody embeddedDischarge)
  | .use functionTyping inclusion =>
      .use (objectFunctionTyping functionTyping) (generalIncludes inclusion)

/-- Every M11 computation derivation embeds with identical source syntax,
use index, and result type. -/
def termTyping {scope : Nat}
    {sourceContext : DOTCapture.Intersections.Source.Ctx scope}
    {sourceTerm : DOTCapture.Intersections.GeneralExpression.Term scope}
    {sourceUse : DOTCapture.Intersections.Source.Capture scope}
    {sourceType : DOTCapture.Intersections.Source.Ty scope}
    (typing : DOTCapture.Intersections.GeneralExpression.Term.HasType
      sourceContext sourceTerm sourceUse sourceType) :
    Term.HasType (typingEnvironment sourceContext) (term sourceTerm)
      (capture sourceUse) (type sourceType) :=
  match typing with
  | .ret sourceValueTyping => .ret (valueTyping sourceValueTyping)
  | .select exposes => by
      simpa only [term, valueLabel,
        DOTCapture.Intersections.GeneralExpression.ObjectType.representationAt,
        ObjectType.representationAt, objectType_representation,
        type_openAt] using
        (Term.HasType.select (exposesObject exposes))
  | .app functionTyping functionShape domainPlain argumentTyping => by
      simpa only [term, capture_seq, type_stripCapture, type_outerCapture,
        type, capture, EmbeddedIncludes, staticExpr] using
        (Term.HasType.app (termTyping functionTyping)
          (by simpa only [type_stripCapture, type] using
            congrArg type functionShape)
          (plain domainPlain)
          (termTyping argumentTyping))
  | .objectApp functionTyping argumentTyping => by
      simpa only [term, capture_seq, objectType_outerCapture,
        objectType_realizedOuterCapture, capture] using
        (Term.HasType.legacyObjectApp (objectFunctionTyping functionTyping)
          (objectArgumentTyping argumentTyping))
  | .embeddedObjectApp functionTyping argumentTyping => by
      simpa only [term, capture_seq, objectType_outerCapture,
        objectType_realizedOuterCapture, capture] using
        (Term.HasType.embeddedObjectApp
          (objectFunctionTyping functionTyping)
          (objectArgumentTyping argumentTyping))
  | @DOTCapture.Intersections.GeneralExpression.Term.HasType.letPlain _ _
      result bound rhs body rhsUse bodyUse bodyOuterUse boundPlain rhsTyping
      bodyTyping discharge => by
      have embeddedBody : Term.HasType
          ((typingEnvironment sourceContext).extendTerm (type bound))
          (term body) (capture bodyUse)
          ((type result).weaken (kind := .term)) := by
        simpa only [typingEnvironment_extendTerm, type_rename,
          embedRename_succ, Ty.weaken] using termTyping bodyTyping
      have embeddedDischarge : CaptureIncludes
          ((typingEnvironment sourceContext).extendTerm (type bound)).bindings
          (capture bodyUse)
          ((capture bodyOuterUse).weaken (kind := .term)) := by
        simpa only [typingEnvironment_extendTerm, context_extendTerm,
          EmbeddedIncludes, staticExpr, capture_rename, embedRename_succ,
          Capture.weaken] using
            generalIncludes discharge
      simpa only [term, capture] using
        (Term.HasType.letPlain (plain boundPlain) (termTyping rhsTyping)
          embeddedBody embeddedDischarge)
  | @DOTCapture.Intersections.GeneralExpression.Term.HasType.objectLet _ _
      sourceObject result rhs rhsUse body bodyUse bodyOuterUse rhsTyping
      bodyTyping discharge => by
      have embeddedRhs : Term.HasType (typingEnvironment sourceContext)
          (term rhs) (capture rhsUse) (objectType sourceObject).formedType := by
        simpa only [generalObjectType_formedType] using termTyping rhsTyping
      have embeddedBody : Term.HasType
          ((typingEnvironment sourceContext).extendTerm
            (objectType sourceObject).formedType)
          (term body) (capture bodyUse)
          ((type result).weaken (kind := .term)) := by
        simpa only [typingEnvironment_extendTerm,
          generalObjectType_formedType, type_rename, embedRename_succ,
          Ty.weaken] using termTyping bodyTyping
      have embeddedDischarge : CaptureIncludes
          ((typingEnvironment sourceContext).extendTerm
            (objectType sourceObject).formedType).bindings
          (capture bodyUse)
          (.union ((capture bodyOuterUse).weaken (kind := .term))
            (.singleton (.var .here))) := by
        simpa only [typingEnvironment_extendTerm, context_extendTerm,
          generalObjectType_formedType, EmbeddedIncludes, staticExpr,
          capture_rename,
          embedRename_succ, Capture.weaken, capture, path, embedVar] using
            generalIncludes discharge
      simpa only [term, capture_seq, objectType_packageCapture, capture] using
        (Term.HasType.objectLet embeddedRhs embeddedBody embeddedDischarge)
  | @DOTCapture.Intersections.GeneralExpression.Term.HasType.embeddedObjectLet
      _ _ sourceObject result rhs rhsUse body bodyUse bodyOuterUse rhsTyping
      bodyTyping discharge => by
      have embeddedRhs : Term.HasType (typingEnvironment sourceContext)
          (term rhs) (capture rhsUse) (objectType sourceObject).formedType := by
        simpa only [generalObjectType_formedType] using termTyping rhsTyping
      have embeddedBody : Term.HasType
          ((typingEnvironment sourceContext).extendTerm
            (objectType sourceObject).formedType)
          (term body) (capture bodyUse)
          ((type result).weaken (kind := .term)) := by
        simpa only [typingEnvironment_extendTerm,
          generalObjectType_formedType, type_rename, embedRename_succ,
          Ty.weaken] using termTyping bodyTyping
      have embeddedDischarge : CaptureIncludes
          ((typingEnvironment sourceContext).extendTerm
            (objectType sourceObject).formedType).bindings
          (capture bodyUse)
          (.union ((capture bodyOuterUse).weaken (kind := .term))
            (.singleton (.var .here))) := by
        simpa only [typingEnvironment_extendTerm, context_extendTerm,
          generalObjectType_formedType, EmbeddedIncludes, staticExpr,
          capture_rename,
          embedRename_succ, Capture.weaken, capture, path, embedVar] using
            generalIncludes discharge
      simpa only [term, capture_seq, objectType_packageCapture, capture] using
        (Term.HasType.embeddedObjectLet embeddedRhs embeddedBody
          embeddedDischarge)
  | .use inner inclusion =>
      .use (termTyping inner) (generalIncludes inclusion)

end

end DOTCapture.ModalIntersections.Embedding.CapturedIntersections
