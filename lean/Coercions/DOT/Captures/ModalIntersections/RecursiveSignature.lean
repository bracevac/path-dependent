import Coercions.DOT.Captures.ModalIntersections.ObjectJudgments

/-!
# Guarded recursive signatures for cumulative objects

This source layer describes simultaneous exact type-member definitions and
ambient realizations of the capture members in the same object signature.  It
contains no target syntax or compilation functions.  Recursive type bodies
and runtime representation types may mention the signature's local members;
capture names are resolved by an explicit ambient model before representation
capture obligations are checked.

The completed object still has the ordinary cumulative `ObjectType` view.
Consequently, once a recursively constructed object is opened, the existing
stable-path, selection, object-consumer, and object-application judgments can
use it without a second object calculus.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev Label := DOTCapture.ModalIntersections.Label
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev StaticRef := DOTCapture.ModalIntersections.StaticRef
abbrev Interface := DOTCapture.ModalIntersections.Interface
abbrev ObjectType := DOTCapture.ModalIntersections.ObjectType
abbrev Ctx := DOTCapture.ModalIntersections.Ctx

/-! ## Exact recursive type definitions -/

/-- One exact recursive type-member definition. Local type and capture
references in `body` refer to the object signature containing the complete
definition block. -/
structure TypeDefinition (scope : Sig) where
  label : Label
  body : Ty scope
deriving DecidableEq

namespace TypeDefinition

/-- The exact interval exported by one recursive definition. -/
def interface {scope : Sig} (definition : TypeDefinition scope) :
    Interface scope :=
  .typeMember definition.label definition.body definition.body

/-- Reject a naked recursive alias. Every proper type constructor guards
recursive occurrences below it. -/
def headGuarded {scope : Sig} (definition : TypeDefinition scope) : Bool :=
  match definition.body with
  | .ref (.localTypeMember _) => false
  | _ => true

end TypeDefinition

namespace TypeDefinitions

/-- Source-order labels, independently of the canonical order chosen by
interface normalization. -/
def labels {scope : Sig} (definitions : List (TypeDefinition scope)) :
    List Label :=
  definitions.map TypeDefinition.label

/-- Conjoin exact definitions into one raw cumulative interface. -/
def interface {scope : Sig} : List (TypeDefinition scope) -> Interface scope
  | [] => .empty
  | definition :: remaining =>
      .inter definition.interface (interface remaining)

/-- Every recursive definition satisfies the source head guard. -/
def allHeadGuarded {scope : Sig}
    (definitions : List (TypeDefinition scope)) : Prop :=
  forall definition, definition ∈ definitions ->
    definition.headGuarded = true

end TypeDefinitions

/-! ## Simultaneously realized capture-member declarations -/

/-- A classifier filter is ambient when it is ground or selected from an
already stable outer root.  A local classifier member would add a recursive
classifier equation, which is deliberately outside Stage 6/7. -/
def classifierAmbientOnly {scope : Sig} :
    DOTCapture.ModalIntersections.ClassifierExpr scope -> Bool
  | .ground _ => true
  | .ref (.member _ _) => true
  | .ref (.localMember _) => false

/-- Capture expressions that do not refer to the signature currently being
constructed. Stable selections from already opened ambient roots remain
admissible. -/
def captureAmbientOnly {scope : Sig} : Capture scope -> Bool
  | .empty => true
  | .union left right =>
      captureAmbientOnly left && captureAmbientOnly right
  | .project capture classifier =>
      captureAmbientOnly capture && classifierAmbientOnly classifier
  | .readOnly capture => captureAmbientOnly capture
  | .singleton _ => true
  | .ref (.localCaptureMember _) => false
  | .ref _ => true

/-- A capture-only raw signature. Keeping this separate makes a cross-sort
same-label collision explicit without admitting recursive capture witnesses. -/
inductive CaptureInterface : Sig -> Type where
  | empty {scope : Sig} : CaptureInterface scope
  | member {scope : Sig} (label : Label)
      (lower upper : Capture scope) : CaptureInterface scope
  | inter {scope : Sig} (left right : CaptureInterface scope) :
      CaptureInterface scope
deriving DecidableEq

namespace CaptureInterface

def toInterface {scope : Sig} : CaptureInterface scope -> Interface scope
  | .empty => .empty
  | .member label lower upper => .captureMember label lower upper
  | .inter left right => .inter left.toInterface right.toInterface

def labels {scope : Sig} : CaptureInterface scope -> List Label
  | .empty => []
  | .member label _ _ => [label]
  | .inter left right => left.labels ++ right.labels

/-- Legacy Stage 6A predicate requiring raw capture bounds themselves to be
ambient. The cumulative recursive signature no longer requires this:
declarations may refer to one another and are checked after simultaneous
realization by `Realizes`. -/
def ambientOnly {scope : Sig} : CaptureInterface scope -> Prop
  | .empty => True
  | .member _ lower upper =>
      captureAmbientOnly lower = true ∧ captureAmbientOnly upper = true
  | .inter left right => left.ambientOnly ∧ right.ambientOnly

/-- Report the first capture declaration that tries to use the recursive
capture-member namespace. -/
def firstRecursiveMember? {scope : Sig} :
    CaptureInterface scope -> Option Label
  | .empty => none
  | .member label lower upper =>
      if captureAmbientOnly lower && captureAmbientOnly upper then none
      else some label
  | .inter left right =>
      match left.firstRecursiveMember? with
      | some label => some label
      | none => right.firstRecursiveMember?

end CaptureInterface

/-! ## Explicit ambient capture realizations -/

/-- Concrete ambient witnesses for capture members. -/
structure AmbientCaptureModel (scope : Sig) where
  witness : Label -> Capture scope
  ambient : forall label, captureAmbientOnly (witness label) = true

namespace AmbientCaptureModel

/-- Simultaneous substitution used for recursive type bodies and
representation types. Type members remain recursive local slots; capture
members become the checked ambient witnesses. -/
def asLocalModel {scope : Sig} (model : AmbientCaptureModel scope) :
    DOTCapture.ModalIntersections.LocalModel.Model scope where
  typeMember := fun label => .ref (.localTypeMember label)
  captureMember := model.witness
  classifierMember := fun label => .ref (.localMember label)

@[simp]
theorem asLocalModel_classifierMember {scope : Sig}
    (model : AmbientCaptureModel scope) (label : Label) :
    model.asLocalModel.classifierMember label = .ref (.localMember label) := rfl

end AmbientCaptureModel

namespace CaptureInterface

/-- Every capture interval is realized without assuming the theory being
constructed. Bounds may mention other local capture members; the complete
concrete model is substituted simultaneously before either inclusion is
proved. Exact type witnesses are supplied separately by guarded recursive
projections in the target. -/
inductive Realizes {scope : Sig} (context : Ctx scope)
    (model : AmbientCaptureModel scope) : CaptureInterface scope -> Type where
  | empty : Realizes context model .empty
  | member {label : Label} {lower upper : Capture scope}
      (lowerProof : DOTCapture.ModalIntersections.CaptureIncludes context
        (lower.realizeLocals model.asLocalModel) (model.witness label))
      (upperProof : DOTCapture.ModalIntersections.CaptureIncludes context
        (model.witness label) (upper.realizeLocals model.asLocalModel)) :
      Realizes context model (.member label lower upper)
  | inter {left right : CaptureInterface scope}
      (leftProof : Realizes context model left)
      (rightProof : Realizes context model right) :
      Realizes context model (.inter left right)

end CaptureInterface

/-! ## Complete recursive signature -/

/-- A recursively realized static signature and its one runtime
representation. The representation may refer statically to local type and
capture members; it does not introduce a runtime self binding. -/
structure Signature (scope : Sig) where
  typeDefinitions : List (TypeDefinition scope)
  captureDeclarations : CaptureInterface scope
  representation : Ty scope
  /-- Capture advertised by the opened representation contract. It may refer
  to a recursive capture member; its concrete witness is selected together
  with the rest of the simultaneous model. -/
  outerCapture : Capture scope
  /-- Ambient envelope carried by the positive existential package. Ordinary
  signatures default to the advertised capture; recursive-local advertised
  captures provide a separate ambient envelope. -/
  packageCapture : Capture scope := outerCapture
deriving DecidableEq

namespace Signature

def interface {scope : Sig} (signature : Signature scope) : Interface scope :=
  .inter (TypeDefinitions.interface signature.typeDefinitions)
    signature.captureDeclarations.toInterface

def objectType {scope : Sig} (signature : Signature scope) : ObjectType scope :=
  .mkContracted signature.interface signature.representation
    signature.outerCapture signature.packageCapture

def typeLabels {scope : Sig} (signature : Signature scope) : List Label :=
  TypeDefinitions.labels signature.typeDefinitions

def captureLabels {scope : Sig} (signature : Signature scope) : List Label :=
  signature.captureDeclarations.labels

/-- Resolve the complete concrete capture-member model in a representation
while retaining its recursive local type slots. -/
def realizedRepresentation {scope : Sig} (signature : Signature scope)
    (model : AmbientCaptureModel scope) : Ty scope :=
  signature.representation.realizeLocals model.asLocalModel

/-- Concrete advertised capture selected by the simultaneous model. -/
def realizedOuterCapture {scope : Sig} (signature : Signature scope)
    (model : AmbientCaptureModel scope) : Capture scope :=
  signature.outerCapture.realizeLocals model.asLocalModel

end Signature

/-- Formation conditions for the recursive layer. A signature contains at
least one static member of either sort. Runtime representations may depend
statically on the complete recursive type block and the simultaneously
realized capture members. -/
structure Signature.Valid {scope : Sig} (signature : Signature scope) : Prop where
  nonempty : signature.typeDefinitions ≠ [] ∨ signature.captureLabels ≠ []
  typeLabelsNodup : signature.typeLabels.Nodup
  labelsDisjoint : forall label, label ∈ signature.typeLabels ->
    label ∉ signature.captureLabels
  guarded : TypeDefinitions.allHeadGuarded signature.typeDefinitions
  packageCaptureAmbient : captureAmbientOnly signature.packageCapture = true

/-- Ambient obligations for one recursive signature. Representation capture
containment is stated after substituting the explicit capture model, so a
representation may advertise a local capture member without manufacturing a
subcapture fact from that reference. -/
structure Realization {scope : Sig} (context : Ctx scope)
    (signature : Signature scope) where
  captures : AmbientCaptureModel scope
  captureConstraints :
    signature.captureDeclarations.Realizes context captures
  representationContainment :
    DOTCapture.ModalIntersections.CaptureIncludes context
      (signature.realizedRepresentation captures).outerCapture
      (signature.realizedOuterCapture captures)
  /-- Independent proof used by positive package formation. The internal
  `repCapture` proposition above and this ambient envelope check are kept
  distinct even when their endpoints happen to coincide. -/
  packageContainment :
    DOTCapture.ModalIntersections.CaptureIncludes context
      (signature.realizedRepresentation captures).outerCapture
      signature.packageCapture

end DOTCaptureToManySortedFC.RecursiveObjects.Source

/-! A source-facing name that does not mention the translation namespace.
The historical namespace above remains the compatibility surface used by the
already completed Stage 6A files. -/

namespace DOTCapture.ModalIntersections.RecursiveSignature

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev Ctx := DOTCapture.ModalIntersections.Ctx
abbrev TypeDefinition :=
  DOTCaptureToManySortedFC.RecursiveObjects.Source.TypeDefinition
abbrev CaptureInterface :=
  DOTCaptureToManySortedFC.RecursiveObjects.Source.CaptureInterface
abbrev AmbientCaptureModel :=
  DOTCaptureToManySortedFC.RecursiveObjects.Source.AmbientCaptureModel
abbrev Signature := DOTCaptureToManySortedFC.RecursiveObjects.Source.Signature
abbrev Realization {scope : Sig} (context : Ctx scope)
    (signature : Signature scope) :=
  DOTCaptureToManySortedFC.RecursiveObjects.Source.Realization context
    signature

end DOTCapture.ModalIntersections.RecursiveSignature
