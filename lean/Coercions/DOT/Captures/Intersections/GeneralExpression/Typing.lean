import Coercions.DOT.Captures.Intersections.GeneralExpression.Embedding
import Coercions.DOT.Captures.Intersections.SourceTyping
import Coercions.DOT.Captures.Acyclic.GeneralExpression.Typing

/-!
# Typing for cumulative intersection general expressions

The judgments in this file remain entirely in the source language.  A
positive object derivation carries an explicit interpretation of its labeled
local members and proofs of every retained interval.  Negative use carries a
proof-relevant projection from the available interpretation to the one
expected by the consumer; this is the source analogue of a cross-shape theory
map, without exposing target names or evidence syntax.
-/

namespace DOTCapture.Intersections.GeneralExpression

abbrev Ctx := DOTCapture.Intersections.Source.Ctx

namespace LocalModel

/-- A sort-correct ambient witness for every possible local member label.
Only labels occurring in an interface are constrained by `Interface.Realizes`.
-/
structure Model (scope : Scope) where
  typeMember : Source.Label -> Ty scope
  captureMember : Source.Label -> Capture scope

/-- A source-syntactic description of a model projection.  Each destination
member is described by an expression over the local members of the available
object; applying the mapping performs local-member realization. -/
structure Mapping (scope : Scope) where
  typeMember : Source.Label -> Ty scope
  captureMember : Source.Label -> Capture scope

/-- The ambient local model exposed by one stable object root. -/
def atPath {scope : Scope} (receiver : Path scope) : Model scope where
  typeMember := fun label => .ref (.typeMember receiver label)
  captureMember := fun label => .ref (.captureMember receiver label)

end LocalModel

mutual

/-- Replace references to the interface currently being realized by the
chosen ambient witnesses. Stable path selections are left unchanged. -/
def Capture.realizeLocals {scope : Scope} (model : LocalModel.Model scope) :
    Capture scope -> Capture scope
  | .empty => .empty
  | .union left right =>
      .union (Capture.realizeLocals model left)
        (Capture.realizeLocals model right)
  | .singleton path => .singleton path
  | .ref (.localCaptureMember label) => model.captureMember label
  | .ref (.captureMember receiver label) =>
      .ref (.captureMember receiver label)

/-- Realize local type and capture references in one source type. Nested
objects delimit their own local-member namespace and are therefore retained.
-/
def Ty.realizeLocals {scope : Scope} (model : LocalModel.Model scope) :
    Ty scope -> Ty scope
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .ref (.localTypeMember label) => model.typeMember label
  | .ref (.typeMember receiver label) => .ref (.typeMember receiver label)
  | .arr domain codomain =>
      .arr (Ty.realizeLocals model domain) (Ty.realizeLocals model codomain)
  | .capturing captures shape =>
      .capturing (Capture.realizeLocals model captures)
        (Ty.realizeLocals model shape)
  | .object object => .object object

end

mutual

@[simp]
theorem Capture.realizeLocals_atPath {scope : Scope} (receiver : Path scope)
    (capture : Capture scope) :
    Capture.realizeLocals (LocalModel.atPath receiver) capture =
      Source.Capture.openAt receiver capture := by
  cases capture with
  | empty => rfl
  | union left right =>
      simp [Capture.realizeLocals, Source.Capture.openAt,
        Capture.realizeLocals_atPath receiver left,
        Capture.realizeLocals_atPath receiver right]
  | singleton path => rfl
  | ref reference => cases reference <;> rfl

@[simp]
theorem Ty.realizeLocals_atPath {scope : Scope} (receiver : Path scope)
    (type : Ty scope) :
    Ty.realizeLocals (LocalModel.atPath receiver) type =
      Source.Ty.openAt receiver type := by
  cases type with
  | top => rfl
  | bot => rfl
  | one => rfl
  | ref reference => cases reference <;> rfl
  | arr domain codomain =>
      simp [Ty.realizeLocals, Source.Ty.openAt,
        Ty.realizeLocals_atPath receiver domain,
        Ty.realizeLocals_atPath receiver codomain]
  | capturing captures shape =>
      simp [Ty.realizeLocals, Source.Ty.openAt,
        Capture.realizeLocals_atPath receiver captures,
        Ty.realizeLocals_atPath receiver shape]
  | object object => rfl

end

namespace LocalModel.Mapping

/-- Regard a syntactic mapping as a simultaneous substitution for local
member references.  Unlike `apply`, the images remain expressions over the
available object's local theory. -/
def asModel {scope : Scope} (mapping : LocalModel.Mapping scope) :
    LocalModel.Model scope where
  typeMember := mapping.typeMember
  captureMember := mapping.captureMember

/-- Substitute the expected interface's local type members by their symbolic
images in the available interface. -/
def mapType {scope : Scope} (mapping : LocalModel.Mapping scope)
    (type : Ty scope) : Ty scope :=
  Ty.realizeLocals mapping.asModel type

/-- Substitute the expected interface's local capture members by their
symbolic images in the available interface. -/
def mapCapture {scope : Scope} (mapping : LocalModel.Mapping scope)
    (capture : Capture scope) : Capture scope :=
  Capture.realizeLocals mapping.asModel capture

/-- Interpret a syntactic model mapping in one available ambient model. -/
def apply {scope : Scope} (mapping : LocalModel.Mapping scope)
    (model : LocalModel.Model scope) : LocalModel.Model scope where
  typeMember := fun label =>
    Ty.realizeLocals model (mapping.typeMember label)
  captureMember := fun label =>
    Capture.realizeLocals model (mapping.captureMember label)

/-- The syntactic identity mapping names each same-labeled local member. -/
def identity {scope : Scope} : LocalModel.Mapping scope where
  typeMember := fun label => .ref (.localTypeMember label)
  captureMember := fun label => .ref (.localCaptureMember label)

@[simp]
theorem apply_identity {scope : Scope} (model : LocalModel.Model scope) :
    apply (identity (scope := scope)) model = model := by
  cases model
  rfl

mutual

@[simp]
theorem mapCapture_identity {scope : Scope} (capture : Capture scope) :
    mapCapture (identity (scope := scope)) capture = capture := by
  cases capture with
  | empty => rfl
  | union left right =>
      change
        Source.Capture.union (mapCapture (identity (scope := scope)) left)
            (mapCapture (identity (scope := scope)) right) =
          Source.Capture.union left right
      rw [mapCapture_identity left, mapCapture_identity right]
  | singleton path => rfl
  | ref reference => cases reference <;> rfl

@[simp]
theorem mapType_identity {scope : Scope} (type : Ty scope) :
    mapType (identity (scope := scope)) type = type := by
  cases type with
  | top => rfl
  | bot => rfl
  | one => rfl
  | ref reference => cases reference <;> rfl
  | arr domain codomain =>
      change
        Source.Ty.arr (mapType (identity (scope := scope)) domain)
            (mapType (identity (scope := scope)) codomain) =
          Source.Ty.arr domain codomain
      rw [mapType_identity domain, mapType_identity codomain]
  | capturing captures shape =>
      change
        Source.Ty.capturing
            (mapCapture (identity (scope := scope)) captures)
            (mapType (identity (scope := scope)) shape) =
          Source.Ty.capturing captures shape
      rw [mapCapture_identity captures, mapType_identity shape]
  | object object => rfl

end

end LocalModel.Mapping


namespace ObjectType

/-- Runtime representation type after an object has acquired a stable root. -/
def representationAt {scope : Scope} (object : ObjectType scope)
    (receiver : Path scope) : Ty scope :=
  Source.Ty.openAt receiver object.representation

/-- Ambient representation type chosen by one positive realization. -/
def realizedRepresentation {scope : Scope} (object : ObjectType scope)
    (model : LocalModel.Model scope) : Ty scope :=
  Ty.realizeLocals model object.representation

@[simp]
theorem realizedRepresentation_atPath {scope : Scope}
    (object : ObjectType scope) (receiver : Path scope) :
    realizedRepresentation object (LocalModel.atPath receiver) =
      representationAt object receiver := by
  simp [realizedRepresentation, representationAt]

end ObjectType

/-! ## Logical inclusion used by general-expression typing -/

/-- Source inclusion extended with the one negative-use rule that contracts a
stable object root to the retained capture of its opened representation. -/
inductive Includes {scope : Scope} (context : Ctx scope) :
    {sort : StaticSort} -> StaticExpr sort scope -> StaticExpr sort scope ->
      Type where
  | source {sort : StaticSort} {first second : StaticExpr sort scope}
      (proof : Source.Includes context first second) :
      Includes context first second
  | trans {sort : StaticSort} {first middle last : StaticExpr sort scope}
      (left : Includes context first middle)
      (right : Includes context middle last) : Includes context first last
  | typeCapturing {sourceCaptures targetCaptures : Capture scope}
      {sourceShape targetShape : Ty scope}
      (captures : Includes context (.capture sourceCaptures)
        (.capture targetCaptures))
      (shape : Includes context (.type sourceShape) (.type targetShape)) :
      Includes context (.type (.capturing sourceCaptures sourceShape))
        (.type (.capturing targetCaptures targetShape))
  | captureUnionElim {left right target : Capture scope}
      (fromLeft : Includes context (.capture left) (.capture target))
      (fromRight : Includes context (.capture right) (.capture target)) :
      Includes context (.capture (.union left right)) (.capture target)
  | payloadRoot {receiver : Path scope} {object : ObjectType scope}
      (exposes : Source.ExposesObject context receiver object) :
      Includes context (.capture (.singleton receiver))
        (.capture (ObjectType.representationAt object receiver).outerCapture)

abbrev TypeIncludes {scope : Scope} (context : Ctx scope)
    (source target : Ty scope) : Type :=
  Includes context (.type source) (.type target)

abbrev CaptureIncludes {scope : Scope} (context : Ctx scope)
    (source target : Capture scope) : Type :=
  Includes context (.capture source) (.capture target)

/-- Ordinary binders exclude exactly the object shape exposed by stable
selection.  Like M10, one outer capture annotation is ignored. -/
def Plain {scope : Scope} (type : Ty scope) : Prop :=
  match type.stripCapture with
  | .object _ => False
  | _ => True

namespace Includes

def refl {scope : Scope} {context : Ctx scope} {sort : StaticSort}
    {expression : StaticExpr sort scope} :
    Includes context expression expression :=
  .source .refl

def typeTop {scope : Scope} {context : Ctx scope} {type : Ty scope} :
    TypeIncludes context type .top :=
  .source .typeTop

def typeBottom {scope : Scope} {context : Ctx scope} {type : Ty scope} :
    TypeIncludes context .bot type :=
  .source .typeBottom

def captureEmpty {scope : Scope} {context : Ctx scope}
    {captures : Capture scope} : CaptureIncludes context .empty captures :=
  .source .captureEmpty

def captureUnionLeft {scope : Scope} {context : Ctx scope}
    {left right : Capture scope} :
    CaptureIncludes context left (.union left right) :=
  .source .captureUnionLeft

def captureUnionRight {scope : Scope} {context : Ctx scope}
    {left right : Capture scope} :
    CaptureIncludes context right (.union left right) :=
  .source .captureUnionRight

end Includes

/-! ## Symbolic proofs under an available local theory -/

/-- Inclusion in the local theory generated by an available object
interface.  Exact occurrence constructors retain duplicate interval
assumptions; no satisfiability premise is imposed. -/
inductive LocalTheory.Includes {scope : Scope} (context : Ctx scope)
    (available : Interface scope) :
    {sort : StaticSort} -> StaticExpr sort scope -> StaticExpr sort scope ->
      Type where
  | ambient {sort : StaticSort} {lower upper : StaticExpr sort scope}
      (proof : DOTCapture.Intersections.GeneralExpression.Includes context
        lower upper) :
      LocalTheory.Includes context available lower upper
  | typeLower {label : Source.Label} {lower upper : Ty scope}
      (occurrence : available.HasTypeOccurrence label lower upper) :
      LocalTheory.Includes context available (.type lower)
        (.type (.ref (.localTypeMember label)))
  | typeUpper {label : Source.Label} {lower upper : Ty scope}
      (occurrence : available.HasTypeOccurrence label lower upper) :
      LocalTheory.Includes context available
        (.type (.ref (.localTypeMember label))) (.type upper)
  | captureLower {label : Source.Label} {lower upper : Capture scope}
      (occurrence : available.HasCaptureOccurrence label lower upper) :
      LocalTheory.Includes context available (.capture lower)
        (.capture (.ref (.localCaptureMember label)))
  | captureUpper {label : Source.Label} {lower upper : Capture scope}
      (occurrence : available.HasCaptureOccurrence label lower upper) :
      LocalTheory.Includes context available
        (.capture (.ref (.localCaptureMember label))) (.capture upper)
  | trans {sort : StaticSort} {lower middle upper : StaticExpr sort scope}
      (first : LocalTheory.Includes context available lower middle)
      (second : LocalTheory.Includes context available middle upper) :
      LocalTheory.Includes context available lower upper

namespace LocalTheory.Includes

def refl {scope : Scope} {context : Ctx scope}
    {available : Interface scope} {sort : StaticSort}
    {expression : StaticExpr sort scope} :
    LocalTheory.Includes context available expression expression :=
  .ambient .refl

end LocalTheory.Includes

/-! ## Positive realizations and cross-shape negative projections -/

namespace Interface

/-- Every retained occurrence is checked independently against one shared
witness per label. Repeated declarations consequently retain repeated proof
fields while sharing their interpreted member. -/
inductive Realizes {scope : Scope} (context : Ctx scope)
    (model : LocalModel.Model scope) : Interface scope -> Type where
  | empty : Realizes context model .empty
  | typeMember {label : Source.Label} {lower upper : Ty scope}
      (lowerProof : TypeIncludes context (Ty.realizeLocals model lower)
        (model.typeMember label))
      (upperProof : TypeIncludes context (model.typeMember label)
        (Ty.realizeLocals model upper)) :
      Realizes context model (.typeMember label lower upper)
  | captureMember {label : Source.Label} {lower upper : Capture scope}
      (lowerProof : CaptureIncludes context (Capture.realizeLocals model lower)
        (model.captureMember label))
      (upperProof : CaptureIncludes context (model.captureMember label)
        (Capture.realizeLocals model upper)) :
      Realizes context model (.captureMember label lower upper)
  | inter {left right : Interface scope}
      (leftProof : Realizes context model left)
      (rightProof : Realizes context model right) :
      Realizes context model (.inter left right)

/-- A proof-relevant interpretation of every constraint in `expected` under
the raw interval assumptions of `available`.  Every expected occurrence has
its own pair of derivations even when labels share one mapped member image. -/
inductive Derives {scope : Scope} (context : Ctx scope)
    (available : Interface scope) (mapping : LocalModel.Mapping scope) :
    Interface scope -> Type where
  | empty : Derives context available mapping .empty
  | typeMember {label : Source.Label} {lower upper : Ty scope}
      (lowerProof : LocalTheory.Includes context available
        (.type (mapping.mapType lower)) (.type (mapping.typeMember label)))
      (upperProof : LocalTheory.Includes context available
        (.type (mapping.typeMember label)) (.type (mapping.mapType upper))) :
      Derives context available mapping (.typeMember label lower upper)
  | captureMember {label : Source.Label} {lower upper : Capture scope}
      (lowerProof : LocalTheory.Includes context available
        (.capture (mapping.mapCapture lower))
        (.capture (mapping.captureMember label)))
      (upperProof : LocalTheory.Includes context available
        (.capture (mapping.captureMember label))
        (.capture (mapping.mapCapture upper))) :
      Derives context available mapping (.captureMember label lower upper)
  | inter {left right : Interface scope}
      (leftProof : Derives context available mapping left)
      (rightProof : Derives context available mapping right) :
      Derives context available mapping (.inter left right)

end Interface

namespace ObjectType

/-- A complete positive model of an object's source interface. -/
structure Realization {scope : Scope} (context : Ctx scope)
    (object : ObjectType scope) where
  model : LocalModel.Model scope
  constraints : Interface.Realizes context model object.interface

/-- Proof-relevant projection from an available object signature to the view
expected by a negative consumer.  The model transformation is source syntax,
so target compilation can reify it as a theory map rather than inspecting an
arbitrary meta-level function. -/
structure Adapts {scope : Scope} (context : Ctx scope)
    (available expected : ObjectType scope) where
  mapping : LocalModel.Mapping scope
  theory : Interface.Derives context available.interface mapping
    expected.interface
  constraints : forall (model : LocalModel.Model scope),
    Interface.Realizes context model available.interface ->
      Interface.Realizes context (mapping.apply model) expected.interface
  representation : forall (model : LocalModel.Model scope),
    Interface.Realizes context model available.interface ->
      TypeIncludes context
        (ObjectType.realizedRepresentation available model)
        (ObjectType.realizedRepresentation expected (mapping.apply model))
  outerCapture : CaptureIncludes context available.outerCapture
    expected.outerCapture

namespace Adapts

/-- The identity view retains each raw occurrence as its own target-theory
assumption while mapping every member label to the same local member. -/
private def identityTheoryWithin {scope : Scope} {context : Ctx scope}
    (available current : Interface scope)
    (typeInAvailable : forall {label lower upper},
      current.HasTypeOccurrence label lower upper ->
        available.HasTypeOccurrence label lower upper)
    (captureInAvailable : forall {label lower upper},
      current.HasCaptureOccurrence label lower upper ->
        available.HasCaptureOccurrence label lower upper) :
    Interface.Derives context available LocalModel.Mapping.identity current := by
  cases current with
  | empty => exact .empty
  | typeMember label lower upper =>
      exact .typeMember
        (by simpa using (LocalTheory.Includes.typeLower
          (typeInAvailable Source.Interface.HasTypeOccurrence.here)))
        (by simpa using (LocalTheory.Includes.typeUpper
          (typeInAvailable Source.Interface.HasTypeOccurrence.here)))
  | captureMember label lower upper =>
      exact .captureMember
        (by simpa using (LocalTheory.Includes.captureLower
          (captureInAvailable Source.Interface.HasCaptureOccurrence.here)))
        (by simpa using (LocalTheory.Includes.captureUpper
          (captureInAvailable Source.Interface.HasCaptureOccurrence.here)))
  | inter left right =>
      exact .inter
        (identityTheoryWithin available left
          (fun occurrence => typeInAvailable (.left occurrence))
          (fun occurrence => captureInAvailable (.left occurrence)))
        (identityTheoryWithin available right
          (fun occurrence => typeInAvailable (.right occurrence))
          (fun occurrence => captureInAvailable (.right occurrence)))

/-- The symbolic identity certificate for a complete interface. -/
def identityTheory {scope : Scope} {context : Ctx scope}
    (interface : Interface scope) :
    Interface.Derives context interface LocalModel.Mapping.identity
      interface :=
  identityTheoryWithin interface interface (fun occurrence => occurrence)
    (fun occurrence => occurrence)

/-- The semantic projection induced by a source-syntactic mapping. -/
def project {scope : Scope} {context : Ctx scope}
    {available expected : ObjectType scope}
    (adaptation : ObjectType.Adapts context available expected)
    (model : LocalModel.Model scope) : LocalModel.Model scope :=
  adaptation.mapping.apply model

/-- Every object interface is a view of itself. -/
def refl {scope : Scope} {context : Ctx scope} (object : ObjectType scope) :
    ObjectType.Adapts context object object where
  mapping := LocalModel.Mapping.identity
  theory := identityTheory object.interface
  constraints := fun _ proof => proof
  representation := fun _ _ => .refl
  outerCapture := .refl

end Adapts

end ObjectType

/-! ## Computational typing -/

mutual

/-- Typing of cumulative values. -/
inductive Value.HasType : {scope : Scope} -> Ctx scope ->
    Value scope -> Ty scope -> Type where
  | var {scope : Scope} {context : Ctx scope} {name : Var scope} :
      Value.HasType context (.var name) (context.lookup name)
  | unit {scope : Scope} {context : Ctx scope} :
      Value.HasType context .unit .one
  | lam {scope : Scope} {context : Ctx scope}
      {domain codomain : Ty scope} {body : Term (scope + 1)}
      {bodyUse : Capture (scope + 1)} {closure : Capture scope}
      (domainPlain : Plain domain)
      (bodyTyping : Term.HasType (context.extendTerm domain) body
        bodyUse (codomain.rename DOTCapture.Acyclic.Rename.succ))
      (captures : CaptureIncludes (context.extendTerm domain) bodyUse
        (.union (closure.rename DOTCapture.Acyclic.Rename.succ)
          (.singleton (.var .here)))) :
      Value.HasType context (.lam domain codomain body)
        (.capturing closure (.arr domain codomain))
  | objectConsumer {scope : Scope} {context : Ctx scope}
      {parameter : ObjectType scope} {result : Ty scope}
      {body : Term (scope + 1)} {bodyUse : Capture (scope + 1)}
      {closure : Capture scope}
      (bodyTyping : Term.HasType (context.extendTerm parameter.formedType)
        body bodyUse (result.rename DOTCapture.Acyclic.Rename.succ))
      (captures : CaptureIncludes
        (context.extendTerm parameter.formedType) bodyUse
        (.union (closure.rename DOTCapture.Acyclic.Rename.succ)
          (.singleton (.var .here)))) :
      Value.HasType context (.objectConsumer parameter result body)
        (.capturing closure (.arr parameter.formedType result))
  /-- Legacy negative introduction retained by the structural M10 embedding.
The native M11 syntax uses `objectConsumer`. -/
  | embeddedObjectConsumer {scope : Scope} {context : Ctx scope}
      {parameter : ObjectType scope} {result : Ty scope}
      {body : Term (scope + 1)} {bodyUse : Capture (scope + 1)}
      {closure : Capture scope}
      (bodyTyping : Term.HasType (context.extendTerm parameter.formedType)
        body bodyUse (result.rename DOTCapture.Acyclic.Rename.succ))
      (captures : CaptureIncludes
        (context.extendTerm parameter.formedType) bodyUse
        (.union (closure.rename DOTCapture.Acyclic.Rename.succ)
          (.singleton (.var .here)))) :
      Value.HasType context (.lam parameter.formedType result body)
        (.capturing closure (.arr parameter.formedType result))
  | object {scope : Scope} {context : Ctx scope}
      {object : ObjectType scope} {payload : Value scope}
      {payloadType : Ty scope}
      (realization : ObjectType.Realization context object)
      (payloadTyping : Value.HasType context payload payloadType)
      (payloadShape : TypeIncludes context payloadType.stripCapture
        (ObjectType.realizedRepresentation object
          realization.model).stripCapture)
      (payloadCapture : CaptureIncludes context payloadType.outerCapture
        (ObjectType.realizedRepresentation object
          realization.model).outerCapture)
      (objectCapture : CaptureIncludes context
        (ObjectType.realizedRepresentation object
          realization.model).outerCapture object.outerCapture) :
      Value.HasType context (.object object payload) object.formedType
  | adapt {scope : Scope} {context : Ctx scope} {value : Value scope}
      {source target : Ty scope}
      (valueTyping : Value.HasType context value source)
      (inclusion : TypeIncludes context source target) :
      Value.HasType context value target

/-- Canonical or stable negative object arguments. -/
inductive ObjectArgument.HasType : {scope : Scope} -> Ctx scope ->
    Term scope -> ObjectType scope -> Type where
  | literal {scope : Scope} {context : Ctx scope}
      {available expected : ObjectType scope} {payload : Value scope}
      {payloadType : Ty scope}
      (realization : ObjectType.Realization context available)
      (payloadTyping : Value.HasType context payload payloadType)
      (payloadShape : TypeIncludes context payloadType.stripCapture
        (ObjectType.realizedRepresentation available
          realization.model).stripCapture)
      (payloadCapture : CaptureIncludes context payloadType.outerCapture
        (ObjectType.realizedRepresentation available
          realization.model).outerCapture)
      (objectCapture : CaptureIncludes context
        (ObjectType.realizedRepresentation available
          realization.model).outerCapture available.outerCapture)
      (adaptation : ObjectType.Adapts context available expected)
      (expectedCapture : CaptureIncludes context
        (ObjectType.realizedRepresentation expected
          (adaptation.mapping.apply realization.model)).outerCapture
        expected.outerCapture) :
      ObjectArgument.HasType context (.ret (.object available payload)) expected
  | stable {scope : Scope} {context : Ctx scope} {name : Var scope}
      {available expected : ObjectType scope}
      (canonical : context.lookup name = available.formedType)
      (adaptation : ObjectType.Adapts context available expected)
      (expectedCapture : CaptureIncludes context
        (ObjectType.realizedRepresentation expected
          (adaptation.mapping.apply (LocalModel.atPath (.var name)))).outerCapture
        expected.outerCapture) :
      ObjectArgument.HasType context (.ret (.var name)) expected

/-- A computation known to produce a negative object consumer. -/
inductive ObjectFunction.HasType : {scope : Scope} -> Ctx scope ->
    Term scope -> Capture scope -> ObjectType scope -> Ty scope ->
      Capture scope -> Type where
  | returned {scope : Scope} {context : Ctx scope}
      {parameter : ObjectType scope} {result : Ty scope}
      {body : Term (scope + 1)} {bodyUse : Capture (scope + 1)}
      {closure : Capture scope}
      (bodyTyping : Term.HasType (context.extendTerm parameter.formedType)
        body bodyUse (result.rename DOTCapture.Acyclic.Rename.succ))
      (captures : CaptureIncludes
        (context.extendTerm parameter.formedType) bodyUse
        (.union (closure.rename DOTCapture.Acyclic.Rename.succ)
          (.singleton (.var .here)))) :
      ObjectFunction.HasType context
        (.ret (.objectConsumer parameter result body)) .empty
        parameter result closure
  | embeddedReturned {scope : Scope} {context : Ctx scope}
      {parameter : ObjectType scope} {result : Ty scope}
      {body : Term (scope + 1)} {bodyUse : Capture (scope + 1)}
      {closure : Capture scope}
      (bodyTyping : Term.HasType (context.extendTerm parameter.formedType)
        body bodyUse (result.rename DOTCapture.Acyclic.Rename.succ))
      (captures : CaptureIncludes
        (context.extendTerm parameter.formedType) bodyUse
        (.union (closure.rename DOTCapture.Acyclic.Rename.succ)
          (.singleton (.var .here)))) :
      ObjectFunction.HasType context
        (.ret (.lam parameter.formedType result body)) .empty
        parameter result closure
  | letPlain {scope : Scope} {context : Ctx scope}
      {parameter : ObjectType scope} {result bound : Ty scope}
      {closure : Capture scope} {rhs : Term scope}
      {body : Term (scope + 1)} {rhsUse : Capture scope}
      {bodyUse : Capture (scope + 1)} {bodyOuterUse : Capture scope}
      (boundPlain : Plain bound)
      (rhsTyping : Term.HasType context rhs rhsUse bound)
      (bodyTyping : ObjectFunction.HasType (context.extendTerm bound) body
        bodyUse (parameter.rename DOTCapture.Acyclic.Rename.succ)
        (result.rename DOTCapture.Acyclic.Rename.succ)
        (closure.rename DOTCapture.Acyclic.Rename.succ))
      (discharge : CaptureIncludes (context.extendTerm bound) bodyUse
        (bodyOuterUse.rename DOTCapture.Acyclic.Rename.succ)) :
      ObjectFunction.HasType context
        (.let' (.capturing closure (.arr parameter.formedType result)) rhs body)
        (.union rhsUse bodyOuterUse) parameter result closure
  | use {scope : Scope} {context : Ctx scope} {function : Term scope}
      {sourceUse targetUse : Capture scope} {parameter : ObjectType scope}
      {result : Ty scope} {closure : Capture scope}
      (functionTyping : ObjectFunction.HasType context function sourceUse
        parameter result closure)
      (inclusion : CaptureIncludes context sourceUse targetUse) :
      ObjectFunction.HasType context function targetUse parameter result closure

/-- Typing of cumulative computations. -/
inductive Term.HasType : {scope : Scope} -> Ctx scope -> Term scope ->
    Capture scope -> Ty scope -> Type where
  | ret {scope : Scope} {context : Ctx scope} {value : Value scope}
      {type : Ty scope} (valueTyping : Value.HasType context value type) :
      Term.HasType context (.ret value) .empty type
  | select {scope : Scope} {context : Ctx scope}
      {receiver : Path scope} {object : ObjectType scope}
      (exposes : Source.ExposesObject context receiver object) :
      Term.HasType context (.select receiver .payload) (.singleton receiver)
        (ObjectType.representationAt object receiver)
  | app {scope : Scope} {context : Ctx scope}
      {function argument : Term scope}
      {functionUse argumentUse : Capture scope}
      {functionType domain codomain : Ty scope}
      (functionTyping : Term.HasType context function functionUse functionType)
      (functionShape : functionType.stripCapture = .arr domain codomain)
      (domainPlain : Plain domain)
      (argumentTyping : Term.HasType context argument argumentUse domain) :
      Term.HasType context (.app function argument)
        (Source.Capture.seq functionUse
          (Source.Capture.seq argumentUse
            (.union functionType.outerCapture domain.outerCapture))) codomain
  | objectApp {scope : Scope} {context : Ctx scope}
      {parameter : ObjectType scope} {function argument : Term scope}
      {functionUse closure : Capture scope} {result : Ty scope}
      (functionTyping : ObjectFunction.HasType context function functionUse
        parameter result closure)
      (argumentTyping : ObjectArgument.HasType context argument parameter) :
      Term.HasType context (.objectApp parameter function argument)
        (Source.Capture.seq functionUse
          (.union closure parameter.outerCapture)) result
  /-- Legacy surface application used only by the structural M10 embedding. -/
  | embeddedObjectApp {scope : Scope} {context : Ctx scope}
      {parameter : ObjectType scope} {function argument : Term scope}
      {functionUse closure : Capture scope} {result : Ty scope}
      (functionTyping : ObjectFunction.HasType context function functionUse
        parameter result closure)
      (argumentTyping : ObjectArgument.HasType context argument parameter) :
      Term.HasType context (.app function argument)
        (Source.Capture.seq functionUse
          (.union closure parameter.outerCapture)) result
  | letPlain {scope : Scope} {context : Ctx scope}
      {result bound : Ty scope} {rhs : Term scope}
      {body : Term (scope + 1)} {rhsUse : Capture scope}
      {bodyUse : Capture (scope + 1)} {bodyOuterUse : Capture scope}
      (boundPlain : Plain bound)
      (rhsTyping : Term.HasType context rhs rhsUse bound)
      (bodyTyping : Term.HasType (context.extendTerm bound) body
        bodyUse (result.rename DOTCapture.Acyclic.Rename.succ))
      (discharge : CaptureIncludes (context.extendTerm bound) bodyUse
        (bodyOuterUse.rename DOTCapture.Acyclic.Rename.succ)) :
      Term.HasType context (.let' result rhs body)
        (.union rhsUse bodyOuterUse) result
  | objectLet {scope : Scope} {context : Ctx scope}
      {object : ObjectType scope} {result : Ty scope}
      {rhs : Term scope} {rhsUse : Capture scope}
      {body : Term (scope + 1)} {bodyUse : Capture (scope + 1)}
      {bodyOuterUse : Capture scope}
      (rhsTyping : Term.HasType context rhs rhsUse object.formedType)
      (bodyTyping : Term.HasType (context.extendTerm object.formedType) body
        bodyUse (result.rename DOTCapture.Acyclic.Rename.succ))
      (discharge : CaptureIncludes (context.extendTerm object.formedType)
        bodyUse (.union
          (bodyOuterUse.rename DOTCapture.Acyclic.Rename.succ)
          (.singleton (.var .here)))) :
      Term.HasType context (.objectLet object result rhs body)
        (Source.Capture.seq rhsUse
          (.union object.outerCapture bodyOuterUse)) result
  /-- Legacy source let used by the structural M10 embedding. -/
  | embeddedObjectLet {scope : Scope} {context : Ctx scope}
      {object : ObjectType scope} {result : Ty scope}
      {rhs : Term scope} {rhsUse : Capture scope}
      {body : Term (scope + 1)} {bodyUse : Capture (scope + 1)}
      {bodyOuterUse : Capture scope}
      (rhsTyping : Term.HasType context rhs rhsUse object.formedType)
      (bodyTyping : Term.HasType (context.extendTerm object.formedType) body
        bodyUse (result.rename DOTCapture.Acyclic.Rename.succ))
      (discharge : CaptureIncludes (context.extendTerm object.formedType)
        bodyUse (.union
          (bodyOuterUse.rename DOTCapture.Acyclic.Rename.succ)
          (.singleton (.var .here)))) :
      Term.HasType context (.let' result rhs body)
        (Source.Capture.seq rhsUse
          (.union object.outerCapture bodyOuterUse)) result
  | use {scope : Scope} {context : Ctx scope} {term : Term scope}
      {sourceUse targetUse : Capture scope} {type : Ty scope}
      (termTyping : Term.HasType context term sourceUse type)
      (inclusion : CaptureIncludes context sourceUse targetUse) :
      Term.HasType context term targetUse type

end

namespace ObjectArgument.HasType

/-- Reconstruct the ordinary positive-object typing premise used by a
canonical literal argument. -/
def literalValueTyping {scope : Scope} {context : Ctx scope}
    {available : ObjectType scope} {payload : Value scope}
    {payloadType : Ty scope}
    (realization : ObjectType.Realization context available)
    (payloadTyping : Value.HasType context payload payloadType)
    (payloadShape : TypeIncludes context payloadType.stripCapture
      (ObjectType.realizedRepresentation available
        realization.model).stripCapture)
    (payloadCapture : CaptureIncludes context payloadType.outerCapture
      (ObjectType.realizedRepresentation available
        realization.model).outerCapture)
    (objectCapture : CaptureIncludes context
      (ObjectType.realizedRepresentation available
        realization.model).outerCapture available.outerCapture) :
    Value.HasType context (.object available payload) available.formedType :=
  .object realization payloadTyping payloadShape payloadCapture objectCapture

end ObjectArgument.HasType

namespace Source.ExposesObject

/-- A stable selection may contract its receiver root to the capture retained
by the opened representation. -/
def payload {scope : Scope} {context : Ctx scope}
    {receiver : Path scope} {object : ObjectType scope}
    (exposes : Source.ExposesObject context receiver object) :
    Term.HasType context (.select receiver .payload)
      (ObjectType.representationAt object receiver).outerCapture
      (ObjectType.representationAt object receiver) :=
  .use (.select exposes) (.payloadRoot exposes)

end Source.ExposesObject

end DOTCapture.Intersections.GeneralExpression
