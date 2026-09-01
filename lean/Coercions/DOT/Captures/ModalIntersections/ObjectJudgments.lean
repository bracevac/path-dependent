import Coercions.DOT.Captures.ModalIntersections.StaticJudgments

/-!
# Object-model judgments for modal captured intersections

Object interfaces are interpreted by one shared type or capture witness per
label.  Repeated declarations retain independent interval proofs.  A
`LocalModel.Mapping` describes a checked negative view without allocating new
member identities.
-/

namespace DOTCapture.ModalIntersections

namespace LocalModel

/-- A sort-correct witness for every possible local member label.  Only
labels occurring in an interface are constrained by `Interface.Realizes`. -/
structure Model (scope : Sig) where
  typeMember : Label -> Ty scope
  captureMember : Label -> Capture scope
  classifierMember : Label -> ClassifierExpr scope :=
    fun _ => .ground ManySortedFC.Classifier.Kind.empty

/-- A symbolic interpretation of destination labels in the local theory of
an available object. -/
structure Mapping (scope : Sig) where
  typeMember : Label -> Ty scope
  captureMember : Label -> Capture scope
  classifierMember : Label -> ClassifierExpr scope :=
    fun _ => .ground ManySortedFC.Classifier.Kind.empty

namespace Model

def rename {source target : Sig} (model : Model source)
    (rho : Rename source target) : Model target where
  typeMember := fun label => (model.typeMember label).rename rho
  captureMember := fun label => (model.captureMember label).rename rho
  classifierMember := fun label => (model.classifierMember label).rename rho

def weaken {scope : Sig} {kind : BinderKind} (model : Model scope) :
    Model (scope ▹ kind) :=
  model.rename DOTCapture.BinderOnly.Rename.succ

end Model

/-- The local model exposed by a stable object root. -/
def atPath {scope : Sig} (receiver : Path scope) : Model scope where
  typeMember := fun label => .ref (.typeMember receiver label)
  captureMember := fun label => .ref (.captureMember receiver label)
  classifierMember := fun label => .ref (.member receiver label)

@[simp]
theorem atPath_weaken {scope : Sig} {kind : BinderKind}
    (receiver : Path scope) :
    (atPath receiver).weaken (kind := kind) = atPath receiver.weaken := by
  rfl

end LocalModel

/-! ## Realization of local references -/

def ClassifierExpr.realizeLocals {scope : Sig}
    (model : LocalModel.Model scope) :
    ClassifierExpr scope -> ClassifierExpr scope
  | .ground kind => .ground kind
  | .ref (.localMember label) => model.classifierMember label
  | .ref reference => .ref reference

def Capture.realizeLocals {scope : Sig} (model : LocalModel.Model scope) :
    Capture scope -> Capture scope
  | .empty => .empty
  | .union left right =>
      .union (left.realizeLocals model) (right.realizeLocals model)
  | .project inner classifier =>
      .project (inner.realizeLocals model) (classifier.realizeLocals model)
  | .readOnly capture => .readOnly (capture.realizeLocals model)
  | .singleton path => .singleton path
  | .ref (.localCaptureMember label) => model.captureMember label
  | .ref reference => .ref reference

def SeparationContext.realizeLocals {scope : Sig} {count : Nat}
    (model : LocalModel.Model scope) :
    SeparationContext count scope -> SeparationContext count scope
  | .nil => .nil
  | .cons rest capture =>
      .cons (rest.realizeLocals model) (capture.realizeLocals model)

def ModeContext.realizeLocals {scope : Sig} {modes : List CaptureMode}
    (model : LocalModel.Model scope) :
    ModeContext modes scope -> ModeContext modes scope
  | .nil => .nil
  | .cons rest capture =>
      .cons (rest.realizeLocals model) (capture.realizeLocals model)

def ModalRequirements.realizeLocals {scope : Sig}
    {separationCount : Nat} {modes : List CaptureMode}
    (model : LocalModel.Model scope) :
    ModalRequirements separationCount modes scope ->
      ModalRequirements separationCount modes scope
  | .mk separation mode =>
      .mk (separation.realizeLocals model) (mode.realizeLocals model)

mutual

/-- Replace references to the interface currently being realized.  A nested
object or negative object arrow starts a fresh local-member namespace and is
therefore left intact. -/
def Ty.realizeLocals {scope : Sig} (model : LocalModel.Model scope) :
    Ty scope -> Ty scope
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .ref (.localTypeMember label) => model.typeMember label
  | .ref reference => .ref reference
  | .arr domain codomain =>
      .arr (domain.realizeLocals model) (codomain.realizeLocals model)
  | .objectArrow parameter resultTemplate =>
      .objectArrow parameter resultTemplate
  | .capturing captures shape =>
      .capturing (captures.realizeLocals model) (shape.realizeLocals model)
  | @Ty.forallI _ sort interval body =>
      .forallI (interval.realizeLocals model)
        (body.realizeLocals (model.weaken (kind := .static sort)))
  | @Ty.existsI _ sort interval body =>
      .existsI (interval.realizeLocals model)
        (body.realizeLocals (model.weaken (kind := .static sort)))
  | .modal requirements body =>
      .modal (requirements.realizeLocals model) (body.realizeLocals model)
  | .object object => .object object

def StaticExpr.realizeLocals {scope : Sig} {sort : StaticSort}
    (model : LocalModel.Model scope) : StaticExpr sort scope ->
      StaticExpr sort scope
  | .type type => .type (type.realizeLocals model)
  | .capture capture => .capture (capture.realizeLocals model)

def Endpoint.realizeLocals {scope : Sig} {sort : StaticSort}
    (model : LocalModel.Model scope) : Endpoint sort scope ->
      Endpoint sort scope
  | .none => .none
  | .some expression => .some (expression.realizeLocals model)

def Interval.realizeLocals {scope : Sig} {sort : StaticSort}
    (model : LocalModel.Model scope) : Interval sort scope ->
      Interval sort scope
  | .bounds lower upper =>
      .bounds (lower.realizeLocals model) (upper.realizeLocals model)

end

/-! ## Stable-path realization -/

@[simp]
theorem ClassifierExpr.realizeLocals_atPath {scope : Sig}
    (receiver : Path scope) (classifier : ClassifierExpr scope) :
    classifier.realizeLocals (LocalModel.atPath receiver) =
      classifier.openAt receiver := by
  cases classifier with
  | ground kind => rfl
  | ref reference => cases reference <;> rfl

@[simp]
theorem Capture.realizeLocals_atPath {scope : Sig}
    (receiver : Path scope) (capture : Capture scope) :
    capture.realizeLocals (LocalModel.atPath receiver) =
      capture.openAt receiver := by
  induction capture with
  | empty => rfl
  | union left right leftIH rightIH =>
      simp only [Capture.realizeLocals, Capture.openAt, leftIH, rightIH]
  | project inner classifier induction =>
      simp only [Capture.realizeLocals, Capture.openAt, induction,
        ClassifierExpr.realizeLocals_atPath]
  | readOnly capture induction =>
      simp only [Capture.realizeLocals, Capture.openAt, induction]
  | singleton path => rfl
  | ref reference => cases reference <;> rfl

@[simp]
theorem SeparationContext.realizeLocals_atPath {scope : Sig} {count : Nat}
    (receiver : Path scope) (context : SeparationContext count scope) :
    context.realizeLocals (LocalModel.atPath receiver) =
      context.openAt receiver := by
  induction context with
  | nil => rfl
  | cons rest capture induction =>
      simp only [SeparationContext.realizeLocals,
        SeparationContext.openAt, induction, Capture.realizeLocals_atPath]

@[simp]
theorem ModeContext.realizeLocals_atPath {scope : Sig}
    {modes : List CaptureMode} (receiver : Path scope)
    (context : ModeContext modes scope) :
    context.realizeLocals (LocalModel.atPath receiver) =
      context.openAt receiver := by
  induction context with
  | nil => rfl
  | cons rest capture induction =>
      simp only [ModeContext.realizeLocals, ModeContext.openAt, induction,
        Capture.realizeLocals_atPath]

@[simp]
theorem ModalRequirements.realizeLocals_atPath {scope : Sig}
    {separationCount : Nat} {modes : List CaptureMode}
    (receiver : Path scope)
    (requirements : ModalRequirements separationCount modes scope) :
    requirements.realizeLocals (LocalModel.atPath receiver) =
      requirements.openAt receiver := by
  cases requirements
  simp only [ModalRequirements.realizeLocals, ModalRequirements.openAt,
    SeparationContext.realizeLocals_atPath,
    ModeContext.realizeLocals_atPath]

mutual

@[simp]
theorem Ty.realizeLocals_atPath {scope : Sig} (receiver : Path scope) :
    (type : Ty scope) ->
      type.realizeLocals (LocalModel.atPath receiver) =
        type.openAt receiver
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by cases reference <;> rfl
  | .arr domain codomain => by
      simp only [Ty.realizeLocals, Ty.openAt,
        Ty.realizeLocals_atPath receiver domain,
        Ty.realizeLocals_atPath receiver codomain]
  | .objectArrow parameter resultTemplate => rfl
  | .capturing captures shape => by
      simp only [Ty.realizeLocals, Ty.openAt,
        Capture.realizeLocals_atPath receiver captures,
        Ty.realizeLocals_atPath receiver shape]
  | @Ty.forallI _ sort interval body => by
      simp only [Ty.realizeLocals, Ty.openAt,
        Interval.realizeLocals_atPath receiver interval,
        LocalModel.atPath_weaken,
        Ty.realizeLocals_atPath (receiver.weaken (kind := .static sort)) body]
  | @Ty.existsI _ sort interval body => by
      simp only [Ty.realizeLocals, Ty.openAt,
        Interval.realizeLocals_atPath receiver interval,
        LocalModel.atPath_weaken,
        Ty.realizeLocals_atPath (receiver.weaken (kind := .static sort)) body]
  | .modal requirements body => by
      simp only [Ty.realizeLocals, Ty.openAt,
        ModalRequirements.realizeLocals_atPath receiver requirements,
        Ty.realizeLocals_atPath receiver body]
  | .object object => rfl

@[simp]
theorem StaticExpr.realizeLocals_atPath {scope : Sig}
    {sort : StaticSort} (receiver : Path scope) :
    (expression : StaticExpr sort scope) ->
      expression.realizeLocals (LocalModel.atPath receiver) =
        expression.openAt receiver
  | .type type => by
      simp only [StaticExpr.realizeLocals, StaticExpr.openAt,
        Ty.realizeLocals_atPath receiver type]
  | .capture capture => by
      simp only [StaticExpr.realizeLocals, StaticExpr.openAt,
        Capture.realizeLocals_atPath receiver capture]

@[simp]
theorem Endpoint.realizeLocals_atPath {scope : Sig} {sort : StaticSort}
    (receiver : Path scope) : (endpoint : Endpoint sort scope) ->
    endpoint.realizeLocals (LocalModel.atPath receiver) =
      endpoint.openAt receiver
  | .none => rfl
  | .some expression => by
      simp only [Endpoint.realizeLocals, Endpoint.openAt,
        StaticExpr.realizeLocals_atPath receiver expression]

@[simp]
theorem Interval.realizeLocals_atPath {scope : Sig} {sort : StaticSort}
    (receiver : Path scope) : (interval : Interval sort scope) ->
    interval.realizeLocals (LocalModel.atPath receiver) =
      interval.openAt receiver
  | .bounds lower upper => by
      simp only [Interval.realizeLocals, Interval.openAt,
        Endpoint.realizeLocals_atPath receiver lower,
        Endpoint.realizeLocals_atPath receiver upper]
end

namespace LocalModel.Mapping

/-- Regard a symbolic mapping as a simultaneous local substitution. -/
def asModel {scope : Sig} (mapping : LocalModel.Mapping scope) :
    LocalModel.Model scope where
  typeMember := mapping.typeMember
  captureMember := mapping.captureMember
  classifierMember := mapping.classifierMember

def mapType {scope : Sig} (mapping : LocalModel.Mapping scope)
    (type : Ty scope) : Ty scope :=
  type.realizeLocals mapping.asModel

def mapCapture {scope : Sig} (mapping : LocalModel.Mapping scope)
    (capture : Capture scope) : Capture scope :=
  capture.realizeLocals mapping.asModel

def mapClassifier {scope : Sig} (mapping : LocalModel.Mapping scope)
    (classifier : ClassifierExpr scope) : ClassifierExpr scope :=
  classifier.realizeLocals mapping.asModel

/-- Interpret a symbolic mapping in an available ambient model. -/
def apply {scope : Sig} (mapping : LocalModel.Mapping scope)
    (model : LocalModel.Model scope) : LocalModel.Model scope where
  typeMember := fun label =>
    (mapping.typeMember label).realizeLocals model
  captureMember := fun label =>
    (mapping.captureMember label).realizeLocals model
  classifierMember := fun label =>
    (mapping.classifierMember label).realizeLocals model

/-- Map each destination label to the same local member. -/
def identity {scope : Sig} : LocalModel.Mapping scope where
  typeMember := fun label => .ref (.localTypeMember label)
  captureMember := fun label => .ref (.localCaptureMember label)
  classifierMember := fun label => .ref (.localMember label)

@[simp]
theorem apply_identity {scope : Sig} (model : LocalModel.Model scope) :
    apply (identity (scope := scope)) model = model := by
  cases model
  rfl

@[simp]
theorem identity_asModel_weaken {scope : Sig} {kind : BinderKind} :
    (identity (scope := scope)).asModel.weaken (kind := kind) =
      (identity (scope := scope ▹ kind)).asModel := by
  rfl

private theorem realizeClassifierIdentity {scope : Sig}
    (classifier : ClassifierExpr scope) :
    classifier.realizeLocals (identity (scope := scope)).asModel =
      classifier := by
  cases classifier with
  | ground kind => rfl
  | ref reference => cases reference <;> rfl

private theorem realizeCaptureIdentity {scope : Sig}
    (capture : Capture scope) :
    capture.realizeLocals (identity (scope := scope)).asModel = capture := by
  induction capture with
  | empty => rfl
  | union left right leftIH rightIH =>
      simp only [Capture.realizeLocals, leftIH, rightIH]
  | project inner classifier induction =>
      simp only [Capture.realizeLocals, induction,
        realizeClassifierIdentity classifier]
  | readOnly capture induction =>
      simp only [Capture.realizeLocals, induction]
  | singleton path => rfl
  | ref reference => cases reference <;> rfl

@[simp]
theorem mapClassifier_identity {scope : Sig}
    (classifier : ClassifierExpr scope) :
    mapClassifier (identity (scope := scope)) classifier = classifier :=
  realizeClassifierIdentity classifier

@[simp]
theorem mapCapture_identity {scope : Sig} (capture : Capture scope) :
    mapCapture (identity (scope := scope)) capture = capture :=
  realizeCaptureIdentity capture

@[simp]
theorem mapSeparation_identity {scope : Sig} {count : Nat}
    (context : SeparationContext count scope) :
    context.realizeLocals (identity (scope := scope)).asModel = context := by
  induction context with
  | nil => rfl
  | cons rest capture induction =>
      simp only [SeparationContext.realizeLocals, induction,
        realizeCaptureIdentity]

@[simp]
theorem mapModeContext_identity {scope : Sig} {modes : List CaptureMode}
    (context : ModeContext modes scope) :
    context.realizeLocals (identity (scope := scope)).asModel = context := by
  induction context with
  | nil => rfl
  | cons rest capture induction =>
      simp only [ModeContext.realizeLocals, induction,
        realizeCaptureIdentity]

@[simp]
theorem mapRequirements_identity {scope : Sig} {separationCount : Nat}
    {modes : List CaptureMode}
    (requirements : ModalRequirements separationCount modes scope) :
    requirements.realizeLocals (identity (scope := scope)).asModel =
      requirements := by
  cases requirements
  simp only [ModalRequirements.realizeLocals, mapSeparation_identity,
    mapModeContext_identity]

mutual

@[simp]
theorem realizeTypeIdentity {scope : Sig} : (type : Ty scope) ->
    type.realizeLocals (identity (scope := scope)).asModel = type
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by cases reference <;> rfl
  | .arr domain codomain => by
      simp only [Ty.realizeLocals, realizeTypeIdentity domain,
        realizeTypeIdentity codomain]
  | .objectArrow parameter resultTemplate => rfl
  | .capturing captures shape => by
      simp only [Ty.realizeLocals, realizeCaptureIdentity,
        realizeTypeIdentity shape]
  | @Ty.forallI _ sort interval body => by
      simp only [Ty.realizeLocals, realizeIntervalIdentity,
        identity_asModel_weaken, realizeTypeIdentity body]
  | @Ty.existsI _ sort interval body => by
      simp only [Ty.realizeLocals, realizeIntervalIdentity,
        identity_asModel_weaken, realizeTypeIdentity body]
  | .modal requirements body => by
      simp only [Ty.realizeLocals, mapRequirements_identity,
        realizeTypeIdentity body]
  | .object object => rfl

@[simp]
theorem realizeStaticExprIdentity {scope : Sig} {sort : StaticSort}
    : (expression : StaticExpr sort scope) ->
    expression.realizeLocals (identity (scope := scope)).asModel =
      expression
  | .type type => by
      simp only [StaticExpr.realizeLocals, realizeTypeIdentity]
  | .capture capture => by
      simp only [StaticExpr.realizeLocals, realizeCaptureIdentity]

@[simp]
theorem realizeEndpointIdentity {scope : Sig} {sort : StaticSort}
    : (endpoint : Endpoint sort scope) ->
    endpoint.realizeLocals (identity (scope := scope)).asModel = endpoint
  | .none => rfl
  | .some expression => by
      simp only [Endpoint.realizeLocals,
        realizeStaticExprIdentity]

@[simp]
theorem realizeIntervalIdentity {scope : Sig} {sort : StaticSort}
    : (interval : Interval sort scope) ->
    interval.realizeLocals (identity (scope := scope)).asModel = interval
  | .bounds lower upper => by
      simp only [Interval.realizeLocals,
        realizeEndpointIdentity]
end

@[simp]
theorem mapType_identity {scope : Sig} (type : Ty scope) :
    mapType (identity (scope := scope)) type = type :=
  realizeTypeIdentity type

end LocalModel.Mapping

namespace ObjectType

/-- Representation type under one ambient positive realization. -/
def realizedRepresentation {scope : Sig} (object : ObjectType scope)
    (model : LocalModel.Model scope) : Ty scope :=
  object.representation.realizeLocals model

/-- Capture charged by direct negative use under one model.  Historical
ordinary objects carry an ambient outer capture and remain definitionally
unchanged.  Contracted objects may advertise a local member, which is
resolved only after their model has been selected or opened. -/
def realizedOuterCapture {scope : Sig} (object : ObjectType scope)
    (model : LocalModel.Model scope) : Capture scope :=
  match object with
  | .mk _ _ outerCapture => outerCapture
  | .mkContracted _ _ outerCapture _ => outerCapture.realizeLocals model

/-- Advertised capture of a projected signature.  Historical `.mk` objects
store an ambient capture and therefore ignore the local-member mapping;
contracted objects interpret their advertised capture through it. -/
def mappedOuterCapture {scope : Sig} (object : ObjectType scope)
    (mapping : LocalModel.Mapping scope) : Capture scope :=
  match object with
  | .mk _ _ outerCapture => outerCapture
  | .mkContracted _ _ outerCapture _ => mapping.mapCapture outerCapture

@[simp]
theorem realizedRepresentation_atPath {scope : Sig}
    (object : ObjectType scope) (receiver : Path scope) :
    realizedRepresentation object (LocalModel.atPath receiver) =
      object.representationAt receiver := by
  simp only [realizedRepresentation, representationAt,
    Ty.realizeLocals_atPath]

end ObjectType

/-! ## Symbolic inclusion under an available interface -/

inductive LocalTheory.Includes {scope : Sig} (context : Ctx scope)
    (available : Interface scope) :
    {sort : StaticSort} -> StaticExpr sort scope -> StaticExpr sort scope ->
      Type where
  | ambient {sort : StaticSort} {lower upper : StaticExpr sort scope}
      (proof : DOTCapture.ModalIntersections.Includes context lower upper) :
      LocalTheory.Includes context available lower upper
  | typeLower {label : Label} {lower upper : Ty scope}
      (occurrence : available.HasTypeOccurrence label lower upper) :
      LocalTheory.Includes context available (.type lower)
        (.type (.ref (.localTypeMember label)))
  | typeUpper {label : Label} {lower upper : Ty scope}
      (occurrence : available.HasTypeOccurrence label lower upper) :
      LocalTheory.Includes context available
        (.type (.ref (.localTypeMember label))) (.type upper)
  | captureLower {label : Label} {lower upper : Capture scope}
      (occurrence : available.HasCaptureOccurrence label lower upper) :
      LocalTheory.Includes context available (.capture lower)
        (.capture (.ref (.localCaptureMember label)))
  | captureUpper {label : Label} {lower upper : Capture scope}
      (occurrence : available.HasCaptureOccurrence label lower upper) :
      LocalTheory.Includes context available
        (.capture (.ref (.localCaptureMember label))) (.capture upper)
  | trans {sort : StaticSort} {lower middle upper : StaticExpr sort scope}
      (first : LocalTheory.Includes context available lower middle)
      (second : LocalTheory.Includes context available middle upper) :
      LocalTheory.Includes context available lower upper

namespace LocalTheory.Includes

def refl {scope : Sig} {context : Ctx scope}
    {available : Interface scope} {sort : StaticSort}
    {expression : StaticExpr sort scope} :
    LocalTheory.Includes context available expression expression :=
  .ambient .refl

end LocalTheory.Includes

/-- Classifier inclusion using either ambient evidence or one of the raw
classifier-member interval assumptions exposed by the available object. -/
inductive LocalTheory.ClassifierIncludes {scope : Sig}
    (context : Ctx scope) (available : Interface scope) :
    ClassifierExpr scope → ClassifierExpr scope → Type where
  | ambient {lower upper : ClassifierExpr scope}
      (proof : DOTCapture.ModalIntersections.ClassifierIncludes context
        lower upper) :
      LocalTheory.ClassifierIncludes context available lower upper
  | lower {label : Label} {lower upper : ClassifierExpr scope}
      (occurrence : available.HasClassifierOccurrence label lower upper) :
      LocalTheory.ClassifierIncludes context available lower
        (.ref (.localMember label))
  | upper {label : Label} {lower upper : ClassifierExpr scope}
      (occurrence : available.HasClassifierOccurrence label lower upper) :
      LocalTheory.ClassifierIncludes context available
        (.ref (.localMember label)) upper
  | trans {lower middle upper : ClassifierExpr scope}
      (first : LocalTheory.ClassifierIncludes context available lower middle)
      (second : LocalTheory.ClassifierIncludes context available middle upper) :
      LocalTheory.ClassifierIncludes context available lower upper

namespace LocalTheory.ClassifierIncludes

def refl {scope : Sig} {context : Ctx scope}
    {available : Interface scope} {classifier : ClassifierExpr scope} :
    LocalTheory.ClassifierIncludes context available classifier classifier :=
  .ambient .refl

end LocalTheory.ClassifierIncludes

/-- Classifier disjointness available either ambiently or as an explicit raw
constraint of the opened object theory. -/
inductive LocalTheory.ClassifiersDisjoint {scope : Sig}
    (context : Ctx scope) (available : Interface scope) :
    ClassifierExpr scope → ClassifierExpr scope → Type where
  | ambient {left right : ClassifierExpr scope}
      (proof : DOTCapture.ModalIntersections.ClassifiersDisjoint context
        left right) :
      LocalTheory.ClassifiersDisjoint context available left right
  | assumption {left right : ClassifierExpr scope}
      (occurrence : available.HasClassifierDisjointOccurrence left right) :
      LocalTheory.ClassifiersDisjoint context available left right
  | symm {left right : ClassifierExpr scope}
      (proof : LocalTheory.ClassifiersDisjoint context available left right) :
      LocalTheory.ClassifiersDisjoint context available right left

/-- Capture membership in a classifier, with explicit object-theory
constraints available after a stable open. -/
inductive LocalTheory.CaptureHasKind {scope : Sig}
    (context : Ctx scope) (available : Interface scope) :
    Capture scope → ClassifierExpr scope → Type where
  | ambient {capture : Capture scope} {classifier : ClassifierExpr scope}
      (proof : DOTCapture.ModalIntersections.CaptureHasKind context capture
        classifier) :
      LocalTheory.CaptureHasKind context available capture classifier
  | assumption {capture : Capture scope} {classifier : ClassifierExpr scope}
      (occurrence : available.HasCaptureKindOccurrence capture classifier) :
      LocalTheory.CaptureHasKind context available capture classifier
  | widen {capture : Capture scope} {lower upper : ClassifierExpr scope}
      (membership : LocalTheory.CaptureHasKind context available capture lower)
      (included : LocalTheory.ClassifierIncludes context available lower upper) :
      LocalTheory.CaptureHasKind context available capture upper

/-! ## Positive realizations and negative interface views -/

namespace Interface

/-- Every raw occurrence is checked against the shared witness for its
label. -/
inductive Realizes {scope : Sig} (context : Ctx scope)
    (model : LocalModel.Model scope) : Interface scope -> Type where
  | empty : Realizes context model .empty
  | typeMember {label : Label} {lower upper : Ty scope}
      (lowerProof : TypeIncludes context (lower.realizeLocals model)
        (model.typeMember label))
      (upperProof : TypeIncludes context (model.typeMember label)
        (upper.realizeLocals model)) :
      Realizes context model (.typeMember label lower upper)
  | captureMember {label : Label} {lower upper : Capture scope}
      (lowerProof : CaptureIncludes context (lower.realizeLocals model)
        (model.captureMember label))
      (upperProof : CaptureIncludes context (model.captureMember label)
        (upper.realizeLocals model)) :
      Realizes context model (.captureMember label lower upper)
  | classifierMember {label : Label}
      {lower upper : ClassifierExpr scope}
      (lowerProof : ClassifierIncludes context
        (lower.realizeLocals model) (model.classifierMember label))
      (upperProof : ClassifierIncludes context
        (model.classifierMember label) (upper.realizeLocals model)) :
      Realizes context model (.classifierMember label lower upper)
  | classifierDisjoint {left right : ClassifierExpr scope}
      (proof : ClassifiersDisjoint context
        (left.realizeLocals model) (right.realizeLocals model)) :
      Realizes context model (.classifierDisjoint left right)
  | captureHasKind {capture : Capture scope}
      {classifier : ClassifierExpr scope}
      (proof : CaptureHasKind context (capture.realizeLocals model)
        (classifier.realizeLocals model)) :
      Realizes context model (.captureHasKind capture classifier)
  | inter {left right : Interface scope}
      (leftProof : Realizes context model left)
      (rightProof : Realizes context model right) :
      Realizes context model (.inter left right)

/-- A model realizes an intersection exactly when it realizes both component
theories. `Nonempty` hides the proof-relevant realization certificates in this
semantic conjunction statement. -/
theorem realizesInterNonemptyIff {scope : Sig} {context : Ctx scope}
    {model : LocalModel.Model scope} {left right : Interface scope} :
    Nonempty (Realizes context model (.inter left right)) ↔
      Nonempty (Realizes context model left) ∧
        Nonempty (Realizes context model right) := by
  constructor
  · rintro ⟨realization⟩
    cases realization with
    | inter leftProof rightProof => exact ⟨⟨leftProof⟩, ⟨rightProof⟩⟩
  · rintro ⟨⟨leftProof⟩, ⟨rightProof⟩⟩
    exact ⟨.inter leftProof rightProof⟩

/-- Prove every destination occurrence from the raw local theory of the
available interface after symbolic substitution. -/
inductive Derives {scope : Sig} (context : Ctx scope)
    (available : Interface scope) (mapping : LocalModel.Mapping scope) :
    Interface scope -> Type where
  | empty : Derives context available mapping .empty
  | typeMember {label : Label} {lower upper : Ty scope}
      (lowerProof : LocalTheory.Includes context available
        (.type (mapping.mapType lower)) (.type (mapping.typeMember label)))
      (upperProof : LocalTheory.Includes context available
        (.type (mapping.typeMember label)) (.type (mapping.mapType upper))) :
      Derives context available mapping (.typeMember label lower upper)
  | captureMember {label : Label} {lower upper : Capture scope}
      (lowerProof : LocalTheory.Includes context available
        (.capture (mapping.mapCapture lower))
        (.capture (mapping.captureMember label)))
      (upperProof : LocalTheory.Includes context available
        (.capture (mapping.captureMember label))
        (.capture (mapping.mapCapture upper))) :
      Derives context available mapping (.captureMember label lower upper)
  | classifierMember {label : Label}
      {lower upper : ClassifierExpr scope}
      (lowerProof : LocalTheory.ClassifierIncludes context available
        (mapping.mapClassifier lower) (mapping.classifierMember label))
      (upperProof : LocalTheory.ClassifierIncludes context available
        (mapping.classifierMember label) (mapping.mapClassifier upper)) :
      Derives context available mapping
        (.classifierMember label lower upper)
  | classifierDisjoint {left right : ClassifierExpr scope}
      (proof : LocalTheory.ClassifiersDisjoint context available
        (mapping.mapClassifier left) (mapping.mapClassifier right)) :
      Derives context available mapping (.classifierDisjoint left right)
  | captureHasKind {capture : Capture scope}
      {classifier : ClassifierExpr scope}
      (proof : LocalTheory.CaptureHasKind context available
        (mapping.mapCapture capture) (mapping.mapClassifier classifier)) :
      Derives context available mapping (.captureHasKind capture classifier)
  | inter {left right : Interface scope}
      (leftProof : Derives context available mapping left)
      (rightProof : Derives context available mapping right) :
      Derives context available mapping (.inter left right)

end Interface

namespace ObjectType

/-- A complete positive model of an object interface. -/
structure Realization {scope : Sig} (context : Ctx scope)
    (object : ObjectType scope) where
  model : LocalModel.Model scope
  constraints : Interface.Realizes context model object.interface

/-- A checked cross-shape view from an available object to the signature
expected by a negative consumer. -/
structure Adapts {scope : Sig} (context : Ctx scope)
    (available expected : ObjectType scope) where
  mapping : LocalModel.Mapping scope
  theory : Interface.Derives context available.interface mapping
    expected.interface
  /-- Advertised captures live in the available object's local theory.  The
  expected endpoint is interpreted by the same checked member mapping used
  for the rest of the projected signature. -/
  outerCapture : LocalTheory.Includes context available.interface
    (.capture available.outerCapture)
    (.capture (expected.mappedOuterCapture mapping))
  packageCapture : CaptureIncludes context available.packageCapture
    expected.packageCapture

namespace Adapts

private def identityTheoryWithin {scope : Sig} {context : Ctx scope}
    (available current : Interface scope)
    (typeInAvailable : forall {label lower upper},
      current.HasTypeOccurrence label lower upper ->
        available.HasTypeOccurrence label lower upper)
    (captureInAvailable : forall {label lower upper},
      current.HasCaptureOccurrence label lower upper ->
        available.HasCaptureOccurrence label lower upper)
    (classifierInAvailable : forall {label lower upper},
      current.HasClassifierOccurrence label lower upper ->
        available.HasClassifierOccurrence label lower upper)
    (disjointInAvailable : forall {left right},
      current.HasClassifierDisjointOccurrence left right ->
        available.HasClassifierDisjointOccurrence left right)
    (captureKindInAvailable : forall {capture classifier},
      current.HasCaptureKindOccurrence capture classifier ->
        available.HasCaptureKindOccurrence capture classifier) :
    Interface.Derives context available LocalModel.Mapping.identity current := by
  cases current with
  | empty => exact .empty
  | typeMember label lower upper =>
      exact .typeMember
        (by simpa using (LocalTheory.Includes.typeLower
          (typeInAvailable Interface.HasTypeOccurrence.here)))
        (by simpa using (LocalTheory.Includes.typeUpper
          (typeInAvailable Interface.HasTypeOccurrence.here)))
  | captureMember label lower upper =>
      exact .captureMember
        (by simpa using (LocalTheory.Includes.captureLower
          (captureInAvailable Interface.HasCaptureOccurrence.here)))
        (by simpa using (LocalTheory.Includes.captureUpper
          (captureInAvailable Interface.HasCaptureOccurrence.here)))
  | classifierMember label lower upper =>
      exact .classifierMember
        (by simpa using (LocalTheory.ClassifierIncludes.lower
          (classifierInAvailable Interface.HasClassifierOccurrence.here)))
        (by simpa using (LocalTheory.ClassifierIncludes.upper
          (classifierInAvailable Interface.HasClassifierOccurrence.here)))
  | classifierDisjoint left right =>
      exact .classifierDisjoint
        (by simpa using (LocalTheory.ClassifiersDisjoint.assumption
          (disjointInAvailable
            Interface.HasClassifierDisjointOccurrence.here)))
  | captureHasKind capture classifier =>
      exact .captureHasKind
        (by simpa using (LocalTheory.CaptureHasKind.assumption
          (captureKindInAvailable Interface.HasCaptureKindOccurrence.here)))
  | inter left right =>
      exact .inter
        (identityTheoryWithin available left
          (fun occurrence => typeInAvailable (.left occurrence))
          (fun occurrence => captureInAvailable (.left occurrence))
          (fun occurrence => classifierInAvailable (.left occurrence))
          (fun occurrence => disjointInAvailable (.left occurrence))
          (fun occurrence => captureKindInAvailable (.left occurrence)))
        (identityTheoryWithin available right
          (fun occurrence => typeInAvailable (.right occurrence))
          (fun occurrence => captureInAvailable (.right occurrence))
          (fun occurrence => classifierInAvailable (.right occurrence))
          (fun occurrence => disjointInAvailable (.right occurrence))
          (fun occurrence => captureKindInAvailable (.right occurrence)))

/-- The symbolic identity derivation retains every raw occurrence. -/
def identityTheory {scope : Sig} {context : Ctx scope}
    (interface : Interface scope) :
    Interface.Derives context interface LocalModel.Mapping.identity
      interface :=
  identityTheoryWithin interface interface (fun occurrence => occurrence)
    (fun occurrence => occurrence) (fun occurrence => occurrence)
    (fun occurrence => occurrence) (fun occurrence => occurrence)

def project {scope : Sig} {context : Ctx scope}
    {available expected : ObjectType scope}
    (adaptation : ObjectType.Adapts context available expected)
    (model : LocalModel.Model scope) : LocalModel.Model scope :=
  adaptation.mapping.apply model

/-- Every object interface is a view of itself. -/
def refl {scope : Sig} {context : Ctx scope} (object : ObjectType scope) :
    ObjectType.Adapts context object object where
  mapping := LocalModel.Mapping.identity
  theory := identityTheory object.interface
  outerCapture := by
    cases object <;>
      simp [ObjectType.mappedOuterCapture,
        LocalModel.Mapping.mapCapture_identity]
      <;> exact .ambient .refl
  packageCapture := .refl

end Adapts

end ObjectType

end DOTCapture.ModalIntersections
