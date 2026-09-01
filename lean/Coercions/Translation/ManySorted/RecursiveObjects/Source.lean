import Coercions.DOT.Captures.ModalIntersections.ObjectJudgments

/-!
# Guarded recursive type-member signatures

This is the source boundary for the cumulative recursive-object case study.
It deliberately adds recursion only for type-member definitions.  Capture
members remain ordinary, ambiently realized interval declarations; in
particular, their endpoints cannot refer to the local capture-member
namespace.  Runtime representations are likewise independent of the local
member namespace in this first recursive slice.

A recursive type definition uses the existing local-member references in its
body.  Thus `A = local B -> Unit` is the syntax-level counterpart of the DOT
definition `self.A = self.B -> Unit`.  All definitions are allocated
simultaneously by the cumulative M11 normalizer before their bodies are
translated.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects

namespace Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev Label := DOTCapture.ModalIntersections.Label
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev StaticRef := DOTCapture.ModalIntersections.StaticRef
abbrev Interface := DOTCapture.ModalIntersections.Interface
abbrev ObjectType := DOTCapture.ModalIntersections.ObjectType
abbrev Ctx := DOTCapture.ModalIntersections.Ctx

/-! ## Exact recursive type definitions -/

/-- One exact recursive type-member definition.  Local type and capture
references in `body` refer to the one object signature containing the whole
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

/-- Head guardedness rejects exactly a naked reference to a recursive local
type member.  Every proper type constructor guards recursive occurrences
below it.  Ambient lexical and stable-path selections are not recursive
heads. -/
def headGuarded {scope : Sig} (definition : TypeDefinition scope) : Bool :=
  match definition.body with
  | .ref (.localTypeMember _) => false
  | _ => true

end TypeDefinition

namespace TypeDefinitions

/-- Source-order labels, used to state uniqueness independently of the
canonical label order chosen later by interface normalization. -/
def labels {scope : Sig} (definitions : List (TypeDefinition scope)) :
    List Label :=
  definitions.map TypeDefinition.label

/-- Conjoin a list of exact definitions into one raw interface. -/
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

/-! ## Acyclic capture-member declarations -/

/-- Capture expressions admitted as model-independent endpoints in Stage 6A.
Selected members of already stable ambient roots remain admissible.  Only a
reference to the signature currently being constructed is rejected. -/
def captureAmbientOnly {scope : Sig} : Capture scope -> Bool
  | .empty => true
  | .union left right =>
      captureAmbientOnly left && captureAmbientOnly right
  | .readOnly capture => captureAmbientOnly capture
  | .singleton _ => true
  | .ref (.localCaptureMember _) => false
  | .ref _ => true

/-- A capture-only raw signature.  A separate datatype makes a cross-sort
same-label collision visible when it is combined with the recursive type
definitions, without admitting hidden type declarations in this component. -/
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

/-- Stage 6A has no recursive capture witnesses.  Both endpoints of every
capture occurrence are formed entirely in the ambient source context. -/
def ambientOnly {scope : Sig} : CaptureInterface scope -> Prop
  | .empty => True
  | .member _ lower upper =>
      captureAmbientOnly lower = true ∧ captureAmbientOnly upper = true
  | .inter left right => left.ambientOnly ∧ right.ambientOnly

/-- Report the first declaration whose bounds try to use the recursive
capture-member namespace.  The executable compiler uses this check before
ordinary interface preparation, so the Stage 6A boundary is not hidden behind
an unrelated local-member lookup error. -/
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

/-- Concrete witnesses for capture members.  Every witness is formed in the
ambient source context: a recursive type body may mention `self.C`, but the
model supplied for `C` may not mention the local capture namespace again. -/
structure AmbientCaptureModel (scope : Sig) where
  witness : Label -> Capture scope
  ambient : forall label, captureAmbientOnly (witness label) = true

namespace AmbientCaptureModel

/-- Simultaneous local substitution used only while translating recursive
type bodies.  Type members remain local references and become recursive
self slots in the target; capture members are replaced by the explicit
ambient witnesses above. -/
def asLocalModel {scope : Sig} (model : AmbientCaptureModel scope) :
    DOTCapture.ModalIntersections.LocalModel.Model scope where
  typeMember := fun label => .ref (.localTypeMember label)
  captureMember := model.witness

end AmbientCaptureModel

namespace CaptureInterface

/-- Every capture interval is realized ambiently.  Unlike an ordinary object
realization, this judgment has no type-witness field: exact type witnesses are
the recursive projections allocated by the target encoding. -/
inductive Realizes {scope : Sig} (context : Ctx scope)
    (model : AmbientCaptureModel scope) : CaptureInterface scope -> Type where
  | empty : Realizes context model .empty
  | member {label : Label} {lower upper : Capture scope}
      (lowerProof : DOTCapture.ModalIntersections.CaptureIncludes context lower
        (model.witness label))
      (upperProof : DOTCapture.ModalIntersections.CaptureIncludes context
        (model.witness label) upper) :
      Realizes context model (.member label lower upper)
  | inter {left right : CaptureInterface scope}
      (leftProof : Realizes context model left)
      (rightProof : Realizes context model right) :
      Realizes context model (.inter left right)

end CaptureInterface

/-! ## Complete recursive-signature case-study input -/

/-- One recursively realized static signature and one nonrecursive runtime
representation.  The ordinary cumulative object type obtained from
`objectType` remains the public source view used after the object is opened. -/
structure Signature (scope : Sig) where
  typeDefinitions : List (TypeDefinition scope)
  captureDeclarations : CaptureInterface scope
  representation : Ty scope
  outerCapture : Capture scope
deriving DecidableEq

namespace Signature

def interface {scope : Sig} (signature : Signature scope) : Interface scope :=
  .inter (TypeDefinitions.interface signature.typeDefinitions)
    signature.captureDeclarations.toInterface

def objectType {scope : Sig} (signature : Signature scope) : ObjectType scope :=
  .mk signature.interface signature.representation signature.outerCapture

def typeLabels {scope : Sig} (signature : Signature scope) : List Label :=
  TypeDefinitions.labels signature.typeDefinitions

def captureLabels {scope : Sig} (signature : Signature scope) : List Label :=
  signature.captureDeclarations.labels

end Signature

/-- Formation conditions specific to the Stage 6A recursive layer.  Ordinary
well-formedness and realization of the resulting cumulative object are kept
as separate derivations, as in the existing source calculus.

The first case study keeps the runtime representation at `Unit`.  Recursive
runtime records or self-dependent payload representations are a separate
extension from recursive static member identity. -/
structure Signature.Valid {scope : Sig} (signature : Signature scope) : Prop where
  nonempty : signature.typeDefinitions ≠ []
  typeLabelsNodup : signature.typeLabels.Nodup
  labelsDisjoint : forall label, label ∈ signature.typeLabels ->
    label ∉ signature.captureLabels
  guarded : TypeDefinitions.allHeadGuarded signature.typeDefinitions
  capturesAmbient : signature.captureDeclarations.ambientOnly
  representationIsUnit : signature.representation = .one
  outerCaptureAmbient : captureAmbientOnly signature.outerCapture = true

/-- The derivation-directed inputs needed to construct a closed recursive
object package.  The representation is `Unit`, hence its actual outer capture
is empty; containment in the advertised object capture is still supplied as
an ordinary source proof and later checked in the ambient target context. -/
structure Realization {scope : Sig} (context : Ctx scope)
    (signature : Signature scope) where
  captures : AmbientCaptureModel scope
  captureConstraints :
    signature.captureDeclarations.Realizes context captures
  representationContainment :
    DOTCapture.ModalIntersections.CaptureIncludes context .empty
      signature.outerCapture

end Source

end DOTCaptureToManySortedFC.RecursiveObjects
