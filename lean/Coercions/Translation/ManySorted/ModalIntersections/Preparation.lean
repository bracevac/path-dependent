import Coercions.Translation.ManySorted.ModalIntersections.Layout
import Coercions.Translation.ManySorted.Intersections.ObjectPreparation
import Coercions.Translation.ManySorted.Acyclic.NegativeObjectInterface

/-!
# Preparation for cumulative modal intersections

Object members are allocated before any bound is translated.  Lexical
intervals use the same one-name true-interval layout as the binder-only
compiler, while object interfaces reuse the target-only intersection
encoding.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.Preparation

namespace Source

abbrev StaticSort := DOTCapture.ModalIntersections.StaticSort
abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev BVar := DOTCapture.ModalIntersections.BVar
abbrev Path := DOTCapture.ModalIntersections.Path
abbrev StaticRef := DOTCapture.ModalIntersections.StaticRef
abbrev CaptureMode := DOTCapture.ModalIntersections.CaptureMode
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev SeparationContext := DOTCapture.ModalIntersections.SeparationContext
abbrev ModeContext := DOTCapture.ModalIntersections.ModeContext
abbrev ModalRequirements := DOTCapture.ModalIntersections.ModalRequirements
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr
abbrev Interval := DOTCapture.ModalIntersections.Interval
abbrev Interface := DOTCapture.ModalIntersections.Interface
abbrev ObjectType := DOTCapture.ModalIntersections.ObjectType
abbrev MemberExpr := DOTCapture.ModalIntersections.Interface.Expr
abbrev MemberEntry := DOTCapture.Intersections.Entry
abbrev MemberSignature := DOTCapture.Intersections.Signature
abbrev MemberInterval := DOTCapture.Intersections.Interval
abbrev SortConflict := DOTCapture.Intersections.SortConflict

end Source

namespace Target

open ManySortedFC

abbrev StaticSort := ManySortedFC.StaticSort
abbrev CaptureMode := ManySortedFC.CaptureMode
abbrev Relation := ManySortedFC.Relation
abbrev Sig := ManySortedFC.Sig
abbrev BVar := ManySortedFC.BVar
abbrev Rename := ManySortedFC.Rename
abbrev Capture := ManySortedFC.Capture
abbrev SeparationContext := ManySortedFC.SeparationContext
abbrev ModeContext := ManySortedFC.ModeContext
abbrev ModalContext := ManySortedFC.ModalContext
abbrev Ty := ManySortedFC.Ty
abbrev StaticExpr := ManySortedFC.StaticExpr
abbrev Theory := ManySortedFC.Theory
abbrev SymbolScope := ManySortedFC.SymbolScope
abbrev StaticScope := ManySortedFC.StaticScope

end Target

open DOTCaptureToManySortedFC.Intersections.Encoding

/-- Preparation failures retain lookup and sort information.  Object nodes
inside a member bound, representation, or dependent result template are an
explicit boundary rather than an accidental partial match. -/
inductive Error : Type where
  | sortConflict (conflict : Source.SortConflict)
  | unknownPathMember (label : Nat)
  | unknownLocalMember (label : Nat)
  | memberSortMismatch (label : Nat)
      (expected actual : Target.StaticSort)
  | nestedObjectBound
  | nestedObjectArrowBound
  | allocationMismatch (label : Nat)
deriving DecidableEq, Repr

/-- Pointwise mode translation, kept public for modal provenance. -/
def translateMode : Source.CaptureMode -> Target.CaptureMode
  | .writable => .writable
  | .readOnly => .readOnly

/-- Intrinsic target index of a source mode list. -/
def translateModes : List Source.CaptureMode -> List Target.CaptureMode
  | [] => []
  | mode :: modes => translateMode mode :: translateModes modes

namespace MemberNames

def find? {scope : Target.Sig} : List (MemberName scope) -> Nat ->
    Option (MemberName scope)
  | [], _ => none
  | member :: remaining, label =>
      if member.label = label then some member else find? remaining label

end MemberNames

namespace Allocation

/-- Canonical target member sorts in normalized label order. -/
def symbols {scope : Source.Sig} :
    List (Source.MemberEntry (Source.MemberExpr scope)) ->
      List Target.StaticSort
  | [] => []
  | .type _ _ :: remaining => .type :: symbols remaining
  | .capture _ _ :: remaining => .capture :: symbols remaining

/-- Allocate every member name before translating the first bound. -/
def members (targetScope : Target.Sig) {sourceScope : Source.Sig} :
    (entries : List (Source.MemberEntry (Source.MemberExpr sourceScope))) ->
      List (MemberName (Target.SymbolScope targetScope (symbols entries)))
  | [] => []
  | .type label _ :: remaining =>
      .type label .here ::
        (members targetScope remaining).map fun member =>
          member.rename ManySortedFC.Rename.succ
  | .capture label _ :: remaining =>
      .capture label .here ::
        (members targetScope remaining).map fun member =>
          member.rename ManySortedFC.Rename.succ

end Allocation

namespace Compile

def expectType {scope : Target.Sig} (label : Nat) :
    MemberName scope -> Except Error
      (Target.BVar scope (.symbol .type))
  | .type _ name => .ok name
  | .capture _ _ =>
      .error (.memberSortMismatch label .type .capture)

def expectCapture {scope : Target.Sig} (label : Nat) :
    MemberName scope -> Except Error
      (Target.BVar scope (.symbol .capture))
  | .capture _ name => .ok name
  | .type _ _ =>
      .error (.memberSortMismatch label .capture .type)

def pathMember {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (path : Source.Path sourceScope) (label : Nat) :
    Except Error (MemberName targetScope) :=
  match layout.member? path label with
  | some member => .ok member
  | none => .error (.unknownPathMember label)

def localMember {scope : Target.Sig}
    (members : List (MemberName scope)) (label : Nat) :
    Except Error (MemberName scope) :=
  match MemberNames.find? members label with
  | some member => .ok member
  | none => .error (.unknownLocalMember label)

/-- Object preparation resolves local references through its freshly
allocated member-name list.  Ambient compilation instead resolves them
through the layout's expression-valued recursive-member model.  Keeping the
two cases explicit prevents a nested object interface from accidentally
capturing an outer recursive namespace. -/
inductive LocalResolution (scope : Target.Sig) where
  | allocated (members : List (MemberName scope))
  | interpreted (model : TargetLocalModel scope)

namespace LocalResolution

def rename {first second : Target.Sig}
    (resolution : LocalResolution first) (rho : Target.Rename first second) :
    LocalResolution second :=
  match resolution with
  | .allocated members =>
      .allocated (members.map fun member => member.rename rho)
  | .interpreted model => .interpreted (model.rename rho)

def typeExpression {scope : Target.Sig}
    (resolution : LocalResolution scope) (label : Nat) :
    Except Error (Target.Ty scope) :=
  match resolution with
  | .allocated members => do
      pure (.tvar (← expectType label (← localMember members label)))
  | .interpreted model =>
      match model.typeMember? label with
      | some type => .ok type
      | none => .error (.unknownLocalMember label)

def captureExpression {scope : Target.Sig}
    (resolution : LocalResolution scope) (label : Nat) :
    Except Error (Target.Capture scope) :=
  match resolution with
  | .allocated members => do
      pure (.cvar (← expectCapture label (← localMember members label)))
  | .interpreted model =>
      match model.captureMember? label with
      | some capture => .ok capture
      | none => .error (.unknownLocalMember label)

end LocalResolution

def typeReference {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (locals : LocalResolution targetScope) :
    Source.StaticRef .type sourceScope ->
      Except Error (Target.Ty targetScope)
  | .bound name => .ok (.tvar (layout.staticSlot name).name)
  | .typeMember path label => do
      pure (.tvar (← expectType label (← pathMember layout path label)))
  | .localTypeMember label => locals.typeExpression label

def captureReference {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (locals : LocalResolution targetScope) :
    Source.StaticRef .capture sourceScope ->
      Except Error (Target.Capture targetScope)
  | .bound name => .ok (.cvar (layout.staticSlot name).name)
  | .captureMember path label => do
      pure (.cvar (← expectCapture label (← pathMember layout path label)))
  | .localCaptureMember label => locals.captureExpression label

def captureCore {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (locals : LocalResolution targetScope) :
    Source.Capture sourceScope -> Except Error (Target.Capture targetScope)
  | .empty => .ok .empty
  | .union left right => do
      pure (.union (← captureCore layout locals left)
        (← captureCore layout locals right))
  | .readOnly capture => do
      pure (.readOnly (← captureCore layout locals capture))
  | .singleton (.var sourceVar) =>
      .ok (.singleton (layout.termVar sourceVar))
  | .ref reference => do
      captureReference layout locals reference

def separationContextCore {count : Nat}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (locals : LocalResolution targetScope) :
    Source.SeparationContext count sourceScope ->
      Except Error (Target.SeparationContext count targetScope)
  | .nil => .ok .nil
  | .cons rest capture => do
      pure (.cons (← separationContextCore layout locals rest)
        (← captureCore layout locals capture))

def modeContextCore {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (locals : LocalResolution targetScope) :
    Source.ModeContext modes sourceScope ->
      Except Error (Target.ModeContext (translateModes modes) targetScope)
  | .nil => .ok .nil
  | .cons rest capture => do
      pure (.cons (← modeContextCore layout locals rest)
        (← captureCore layout locals capture))

def requirementsCore {count : Nat}
    {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (locals : LocalResolution targetScope) :
    Source.ModalRequirements count modes sourceScope ->
      Except Error
        (Target.ModalContext count (translateModes modes) targetScope)
  | .mk separation mode => do
      pure (.mk (← separationContextCore layout locals separation)
        (← modeContextCore layout locals mode))

mutual

def typeCore {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (locals : LocalResolution targetScope) :
    Source.Ty sourceScope -> Except Error (Target.Ty targetScope)
  | .top => .ok .top
  | .bot => .ok .bot
  | .one => .ok .one
  | .ref reference => typeReference layout locals reference
  | .arr domain codomain => do
      pure (.arr (← typeCore layout locals domain)
        (← typeCore layout locals codomain))
  | .objectArrow _ _ => .error .nestedObjectArrowBound
  | .capturing captures shape => do
      pure (.capturing (← captureCore layout locals captures)
        (← typeCore layout locals shape))
  | .forallI interval body => do
      let theory ← intervalCore layout locals interval
      let bodyLocals := locals.rename (Layout.staticRename targetScope interval)
      let targetBody ← typeCore (layout.extendStatic interval) bodyLocals body
      pure (.forallT theory targetBody)
  | .existsI interval body => do
      let theory ← intervalCore layout locals interval
      let bodyLocals := locals.rename (Layout.staticRename targetScope interval)
      let targetBody ← typeCore (layout.extendStatic interval) bodyLocals body
      pure (.existsT theory targetBody)
  | .modal requirements body => do
      pure (.modal (← requirementsCore layout locals requirements)
        (← typeCore layout locals body))
  | .object _ => .error .nestedObjectBound

def staticExpressionCore {sort : Source.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (locals : LocalResolution targetScope) :
    Source.StaticExpr sort sourceScope ->
      Except Error (Target.StaticExpr (translateSort sort) targetScope)
  | .type type => (typeCore layout locals type).map .type
  | .capture capture => (captureCore layout locals capture).map .capture

def intervalCore {sort : Source.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (locals : LocalResolution targetScope)
    (interval : Source.Interval sort sourceScope) :
    Except Error
      (Target.Theory targetScope [translateSort sort]
        (intervalRelations interval)) :=
  match interval with
  | .bounds .none .none =>
      .ok (ManySortedFC.Interval.unconstrained (translateSort sort))
  | .bounds (.some lower) .none => do
      pure (ManySortedFC.Interval.lowerBounded
        (← staticExpressionCore layout locals lower))
  | .bounds .none (.some upper) => do
      pure (ManySortedFC.Interval.upperBounded
        (← staticExpressionCore layout locals upper))
  | .bounds (.some lower) (.some upper) => do
      pure (ManySortedFC.Interval.between
        (← staticExpressionCore layout locals lower)
        (← staticExpressionCore layout locals upper))

end

/-! Member-aware APIs used by object preparation. -/

def translateCapture {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.Capture sourceScope) :
    Except Error (Target.Capture targetScope) :=
  captureCore layout (.allocated members) source

def translateSeparationContext {count : Nat}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.SeparationContext count sourceScope) :
    Except Error (Target.SeparationContext count targetScope) :=
  separationContextCore layout (.allocated members) source

def translateModeContext {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.ModeContext modes sourceScope) :
    Except Error (Target.ModeContext (translateModes modes) targetScope) :=
  modeContextCore layout (.allocated members) source

def translateRequirements {count : Nat}
    {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.ModalRequirements count modes sourceScope) :
    Except Error
      (Target.ModalContext count (translateModes modes) targetScope) :=
  requirementsCore layout (.allocated members) source

def translateType {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.Ty sourceScope) : Except Error (Target.Ty targetScope) :=
  typeCore layout (.allocated members) source

def translateStaticExpr {sort : Source.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.StaticExpr sort sourceScope) :
    Except Error (Target.StaticExpr (translateSort sort) targetScope) :=
  staticExpressionCore layout (.allocated members) source

def translateInterval {sort : Source.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.Interval sort sourceScope) :
    Except Error
      (Target.Theory targetScope [translateSort sort]
        (intervalRelations source)) :=
  intervalCore layout (.allocated members) source

private def translateTypeMemberIntervals {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    List (Source.MemberInterval
      (Source.MemberExpr sourceScope (.type))) ->
      Except Error
        (List (Source.MemberInterval (Target.StaticExpr .type targetScope)))
  | [] => .ok []
  | interval :: remaining => do
      let lower ← staticExpressionCore layout (.allocated members)
        interval.lower
      let upper ← staticExpressionCore layout (.allocated members)
        interval.upper
      pure (⟨lower, upper⟩ ::
        (← translateTypeMemberIntervals layout members remaining))

private def translateCaptureMemberIntervals {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    List (Source.MemberInterval
      (Source.MemberExpr sourceScope (.capture))) ->
      Except Error
        (List (Source.MemberInterval (Target.StaticExpr .capture targetScope)))
  | [] => .ok []
  | interval :: remaining => do
      let lower ← staticExpressionCore layout (.allocated members)
        interval.lower
      let upper ← staticExpressionCore layout (.allocated members)
        interval.upper
      pure (⟨lower, upper⟩ ::
        (← translateCaptureMemberIntervals layout members remaining))

/-- Translate one normalization-layer member expression while preserving its
isomorphic type/capture sort tag. -/
def translateMemberExpr {sort : DOTCapture.Intersections.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.MemberExpr sourceScope sort -> Except Error
      (Target.StaticExpr
        (DOTCaptureToManySortedFC.Intersections.Encoding.targetSort sort)
        targetScope) :=
  match sort with
  | .type => fun expression => translateStaticExpr layout members expression
  | .capture => fun expression => translateStaticExpr layout members expression

/-- Translate a homogeneous block of retained member intervals.  This public,
sort-indexed wrapper is the metatheoretic boundary used to relate raw source
occurrences to the exact normalized target theory; the implementation still
shares the two specialized recursive workers above. -/
def translateMemberIntervals {sort : DOTCapture.Intersections.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    List (Source.MemberInterval (Source.MemberExpr sourceScope sort)) ->
      Except Error (List (Source.MemberInterval
        (Target.StaticExpr
          (DOTCaptureToManySortedFC.Intersections.Encoding.targetSort sort)
          targetScope))) :=
  match sort with
  | .type => translateTypeMemberIntervals layout members
  | .capture => translateCaptureMemberIntervals layout members

@[simp]
theorem translateMemberIntervals_nil
    {sort : DOTCapture.Intersections.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    translateMemberIntervals (sort := sort) layout members [] = .ok [] := by
  cases sort <;> rfl

@[simp]
theorem translateMemberIntervals_cons
    {sort : DOTCapture.Intersections.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (interval : Source.MemberInterval
      (Source.MemberExpr sourceScope sort))
    (remaining : List (Source.MemberInterval
      (Source.MemberExpr sourceScope sort))) :
    translateMemberIntervals layout members (interval :: remaining) = (do
      let lower ← translateMemberExpr layout members interval.lower
      let upper ← translateMemberExpr layout members interval.upper
      let tail ← translateMemberIntervals layout members remaining
      pure (⟨lower, upper⟩ :: tail)) := by
  cases sort with
  | type => rfl
  | capture => rfl

def entries {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (allMembers : List (MemberName targetScope)) :
    List (Source.MemberEntry (Source.MemberExpr sourceScope)) ->
    List (MemberName targetScope) ->
      Except Error (List (PreparedEntry targetScope))
  | [], [] => .ok []
  | .type label sourceIntervals :: remaining,
      .type allocatedLabel name :: allocatedRemaining => do
      if _labelsMatch : label = allocatedLabel then
        pure (.type label name
          (← translateMemberIntervals layout allMembers sourceIntervals) ::
          (← entries layout allMembers remaining allocatedRemaining))
      else
        .error (.allocationMismatch label)
  | .capture label sourceIntervals :: remaining,
      .capture allocatedLabel name :: allocatedRemaining => do
      if _labelsMatch : label = allocatedLabel then
        pure (.capture label name
          (← translateMemberIntervals layout allMembers sourceIntervals) ::
          (← entries layout allMembers remaining allocatedRemaining))
      else
        .error (.allocationMismatch label)
  | entry :: _, _ => .error (.allocationMismatch entry.label)
  | [], _ :: _ => .error (.allocationMismatch 0)

end Compile

/-- Prepare one normalized interface signature in a complete names-only
scope. -/
def prepare {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (signature : Source.MemberSignature (Source.MemberExpr sourceScope)) :
    Except Error (PreparedSignature targetScope) := do
  let symbols := Allocation.symbols signature.entries
  let allocated := Allocation.members targetScope signature.entries
  let namesLayout := layout.renameTarget
    (ManySortedFC.Rename.weakenSymbols symbols)
  let preparedEntries ← Compile.entries namesLayout allocated
    signature.entries allocated
  pure { symbols := symbols, entries := preparedEntries }

/-- Normalize by label, reject cross-sort collisions, then prepare all
retained occurrences. -/
def collectAndPrepare {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Source.Interface sourceScope) :
    Except Error (PreparedSignature targetScope) := do
  let signature ← interface.collect.mapError Error.sortConflict
  prepare layout signature

/-- Reuse the target-only prepared-object carrier from the M11 compiler. -/
abbrev PreparedObject (scope : Target.Sig) :=
  DOTCaptureToManySortedFC.Intersections.ObjectPreparation.PreparedObject scope

namespace PreparedObject

/-- The complete positive target type, including the object's ambient
capture. -/
def targetType {scope : Target.Sig} (object : PreparedObject scope) :
    Target.Ty scope :=
  DOTCaptureToManySortedFC.Intersections.ObjectInterface.objectType
    object.encoding.theory object.representation object.outerCapture

/-- Opening a prepared object contributes exactly one runtime payload. -/
theorem one_payload {scope : Target.Sig} (object : PreparedObject scope) :
    (ManySortedFC.PayloadScope scope object.encoding.symbols
      object.encoding.relations).termCount = scope.termCount + 1 :=
  DOTCaptureToManySortedFC.Intersections.ObjectInterface.payload_term_count
    _ _

end PreparedObject

/-- Prepare a cumulative positive object.  Interface bounds and the runtime
representation use the deliberately non-object-recursive member translator. -/
def prepareObject {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.ObjectType sourceScope) :
    Except Error (PreparedObject targetScope) := do
  let prepared ← collectAndPrepare layout source.interface
  let encoding := encode prepared
  let namesLayout := layout.renameTarget
    (ManySortedFC.Rename.weakenSymbols encoding.symbols)
  let representationAtNames ← Compile.translateType namesLayout
    encoding.prepared.members source.representation
  let representation := representationAtNames.rename
    (ManySortedFC.Rename.weakenMany
      (ManySortedFC.SymbolScope targetScope encoding.symbols)
      (ManySortedFC.evidenceKinds encoding.relations))
  let outerCapture ← Compile.captureCore layout
    (.interpreted layout.localModel) source.packageCapture
  pure { encoding, representation, outerCapture }

/-- A negative object type additionally carries its dependent result in the
same opened names-first theory as the parameter representation. -/
structure PreparedObjectArrow (scope : Target.Sig) where
  object : PreparedObject scope
  result : Target.Ty
    (Target.StaticScope scope object.encoding.symbols
      object.encoding.relations)

namespace PreparedObjectArrow

def targetType {scope : Target.Sig} (prepared : PreparedObjectArrow scope)
    (outerClosure : Target.Capture scope) : Target.Ty scope :=
  DOTCaptureToManySortedFC.Acyclic.NegativeObjectInterface.consumerType
    prepared.object.encoding.theory prepared.object.representation
    prepared.result outerClosure
    (outerClosure.rename
      (ManySortedFC.Rename.weakenStatic prepared.object.encoding.symbols
        prepared.object.encoding.relations))

end PreparedObjectArrow

/-- Prepare the parameter theory and translate local-member references in a
dependent negative result before evidence binders are installed. -/
def prepareObjectArrow {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (parameter : Source.ObjectType sourceScope)
    (resultTemplate : Source.Ty sourceScope) :
    Except Error (PreparedObjectArrow targetScope) := do
  let object ← prepareObject layout parameter
  let namesLayout := layout.renameTarget
    (ManySortedFC.Rename.weakenSymbols object.encoding.symbols)
  let resultAtNames ← Compile.translateType namesLayout
    object.encoding.prepared.members resultTemplate
  let result := resultAtNames.rename
    (ManySortedFC.Rename.weakenMany
      (ManySortedFC.SymbolScope targetScope object.encoding.symbols)
      (ManySortedFC.evidenceKinds object.encoding.relations))
  pure { object, result }

/-! ## Ambient cumulative translation -/

def translateCapture {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.Capture sourceScope) :
    Except Error (Target.Capture targetScope) :=
  Compile.captureCore layout (.interpreted layout.localModel) source

/-- A total capture interpretation for proof-only compiler bookkeeping.
Malformed member selections fall back to the empty target capture; every
prepared compiler input recovers its exact successful translation below. -/
def totalCapture {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) :
    Source.Capture sourceScope -> Target.Capture targetScope
  | .empty => .empty
  | .union left right =>
      .union (totalCapture layout left) (totalCapture layout right)
  | .readOnly capture => .readOnly (totalCapture layout capture)
  | .singleton (.var sourceVar) => .singleton (layout.termVar sourceVar)
  | .ref (.bound sourceVar) => .cvar (layout.staticSlot sourceVar).name
  | .ref (.captureMember path label) =>
      match layout.member? path label with
      | some (.capture _ targetVar) => .cvar targetVar
      | _ => .empty
  | .ref (.localCaptureMember label) =>
      (layout.localModel.captureMember? label).getD .empty

/-- Successful partial capture preparation agrees with the total map. -/
theorem totalCapture_of_prepared {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (sourceCapture : Source.Capture sourceScope)
    (targetCapture : Target.Capture targetScope)
    (prepared : translateCapture layout sourceCapture = .ok targetCapture) :
    totalCapture layout sourceCapture = targetCapture := by
  induction sourceCapture generalizing targetCapture with
  | empty => simpa [translateCapture,
      Compile.captureCore, totalCapture] using prepared
  | union left right leftInduction rightInduction =>
      cases leftPrepared : Compile.captureCore layout
          (.interpreted layout.localModel) left with
      | error error =>
          unfold translateCapture Compile.captureCore at prepared
          rw [leftPrepared] at prepared
          cases prepared
      | ok targetLeft =>
          cases rightPrepared : Compile.captureCore layout
              (.interpreted layout.localModel) right with
          | error error =>
              unfold translateCapture Compile.captureCore at prepared
              rw [leftPrepared, rightPrepared] at prepared
              cases prepared
          | ok targetRight =>
              unfold translateCapture Compile.captureCore at prepared
              rw [leftPrepared, rightPrepared] at prepared
              cases prepared
              have leftEquality : totalCapture layout left = targetLeft :=
                leftInduction targetLeft (by
                  simpa [translateCapture] using
                    leftPrepared)
              have rightEquality : totalCapture layout right = targetRight :=
                rightInduction targetRight (by
                  simpa [translateCapture] using
                    rightPrepared)
              simp [totalCapture, leftEquality, rightEquality]
  | readOnly capture induction =>
      cases innerPrepared : Compile.captureCore layout
          (.interpreted layout.localModel) capture with
      | error error =>
          unfold translateCapture Compile.captureCore at prepared
          rw [innerPrepared] at prepared
          cases prepared
      | ok targetInner =>
          unfold translateCapture Compile.captureCore at prepared
          rw [innerPrepared] at prepared
          cases prepared
          simp only [totalCapture]
          rw [induction targetInner]
          simpa [translateCapture] using
            innerPrepared
  | singleton path =>
      cases path
      simpa [translateCapture,
        Compile.captureCore, totalCapture] using prepared
  | ref reference =>
      cases reference with
      | bound sourceVar =>
          unfold translateCapture
            Compile.captureCore Compile.captureReference at prepared
          cases prepared
          rfl
      | captureMember path label =>
          cases found : layout.member? path label with
          | none =>
              unfold translateCapture
                Compile.captureCore Compile.captureReference
                Compile.pathMember at prepared
              simp [found] at prepared
              cases prepared
          | some member =>
              cases member with
              | type memberLabel memberName =>
                  unfold translateCapture
                    Compile.captureCore Compile.captureReference
                    Compile.pathMember Compile.expectCapture at prepared
                  simp [found] at prepared
                  cases prepared
              | capture memberLabel memberName =>
                  unfold translateCapture
                    Compile.captureCore Compile.captureReference
                    Compile.pathMember Compile.expectCapture at prepared
                  simp [found] at prepared
                  cases prepared
                  simp [totalCapture, found]
      | localCaptureMember label =>
          cases found : layout.localModel.captureMember? label with
          | none =>
              simp only [translateCapture, Compile.captureCore,
                Compile.captureReference,
                Compile.LocalResolution.captureExpression] at prepared
              rw [found] at prepared
              cases prepared
          | some targetCapture =>
              simp only [translateCapture, Compile.captureCore,
                Compile.captureReference,
                Compile.LocalResolution.captureExpression] at prepared
              rw [found] at prepared
              cases prepared
              simp [totalCapture, found]

def translateSeparationContext {count : Nat}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.SeparationContext count sourceScope) :
    Except Error (Target.SeparationContext count targetScope) :=
  Compile.separationContextCore layout (.interpreted layout.localModel) source

def translateModeContext {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.ModeContext modes sourceScope) :
    Except Error (Target.ModeContext (translateModes modes) targetScope) :=
  Compile.modeContextCore layout (.interpreted layout.localModel) source

def translateRequirements {count : Nat}
    {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.ModalRequirements count modes sourceScope) :
    Except Error
      (Target.ModalContext count (translateModes modes) targetScope) :=
  Compile.requirementsCore layout (.interpreted layout.localModel) source

/-- Total separation-context translation induced pointwise by `totalCapture`. -/
def totalSeparationContext {count : Nat} {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope) :
    Source.SeparationContext count sourceScope ->
      Target.SeparationContext count targetScope
  | .nil => .nil
  | .cons rest capture =>
      .cons (totalSeparationContext layout rest) (totalCapture layout capture)

/-- Total mode-context translation induced pointwise by `totalCapture`. -/
def totalModeContext {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) :
    Source.ModeContext modes sourceScope ->
      Target.ModeContext (translateModes modes) targetScope
  | .nil => .nil
  | .cons rest capture =>
      .cons (totalModeContext layout rest) (totalCapture layout capture)

/-- Total modal-interface translation used by coherent context construction. -/
def totalRequirements {count : Nat} {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) :
    Source.ModalRequirements count modes sourceScope ->
      Target.ModalContext count (translateModes modes) targetScope
  | .mk separation mode =>
      .mk (totalSeparationContext layout separation)
        (totalModeContext layout mode)

theorem totalSeparationContext_of_prepared {count : Nat}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.SeparationContext count sourceScope)
    (target : Target.SeparationContext count targetScope)
    (prepared : translateSeparationContext layout source = .ok target) :
    totalSeparationContext layout source = target := by
  induction source with
  | nil =>
      simpa [translateSeparationContext,
        Compile.separationContextCore, totalSeparationContext] using prepared
  | cons rest capture induction =>
      cases restPrepared : Compile.separationContextCore layout
          (.interpreted layout.localModel) rest with
      | error error =>
          unfold translateSeparationContext Compile.separationContextCore at prepared
          rw [restPrepared] at prepared
          cases prepared
      | ok targetRest =>
          cases capturePrepared : Compile.captureCore layout
              (.interpreted layout.localModel) capture with
          | error error =>
              unfold translateSeparationContext
                Compile.separationContextCore at prepared
              rw [restPrepared, capturePrepared] at prepared
              cases prepared
          | ok targetCapture =>
              unfold translateSeparationContext
                Compile.separationContextCore at prepared
              rw [restPrepared, capturePrepared] at prepared
              cases prepared
              have restEquality := induction layout targetRest (by
                  simpa [translateSeparationContext] using restPrepared)
              have captureEquality := totalCapture_of_prepared layout capture
                targetCapture (by
                  simpa [translateCapture] using
                    capturePrepared)
              simp [totalSeparationContext, restEquality, captureEquality]

theorem totalModeContext_of_prepared {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.ModeContext modes sourceScope)
    (target : Target.ModeContext (translateModes modes) targetScope)
    (prepared : translateModeContext layout source = .ok target) :
    totalModeContext layout source = target := by
  induction source with
  | nil =>
      simpa [translateModeContext,
        Compile.modeContextCore, totalModeContext] using prepared
  | cons rest capture induction =>
      cases restPrepared : Compile.modeContextCore layout
          (.interpreted layout.localModel) rest with
      | error error =>
          unfold translateModeContext Compile.modeContextCore at prepared
          rw [restPrepared] at prepared
          cases prepared
      | ok targetRest =>
          cases capturePrepared : Compile.captureCore layout
              (.interpreted layout.localModel) capture with
          | error error =>
              unfold translateModeContext Compile.modeContextCore at prepared
              rw [restPrepared, capturePrepared] at prepared
              cases prepared
          | ok targetCapture =>
              unfold translateModeContext Compile.modeContextCore at prepared
              rw [restPrepared, capturePrepared] at prepared
              cases prepared
              have restEquality := induction layout targetRest (by
                  simpa [translateModeContext]
                    using restPrepared)
              have captureEquality := totalCapture_of_prepared layout capture
                targetCapture (by
                  simpa [translateCapture] using
                    capturePrepared)
              simp [totalModeContext, restEquality, captureEquality]

/-- Successful partial modal preparation is exactly the canonical total
translation used by `CompilerContext.Ready.push`. -/
theorem totalRequirements_of_prepared {count : Nat}
    {modes : List Source.CaptureMode} {sourceScope : Source.Sig}
    {targetScope : Target.Sig} (layout : Layout sourceScope targetScope)
    (source : Source.ModalRequirements count modes sourceScope)
    (target : Target.ModalContext count (translateModes modes) targetScope)
    (prepared : translateRequirements layout source = .ok target) :
    totalRequirements layout source = target := by
  cases source with
  | mk separation mode =>
      unfold translateRequirements at prepared
      simp only [Compile.requirementsCore] at prepared
      cases separationPrepared :
          Compile.separationContextCore layout
            (.interpreted layout.localModel) separation with
      | error error =>
          rw [separationPrepared] at prepared
          cases prepared
      | ok targetSeparation =>
          cases modePrepared : Compile.modeContextCore layout
              (.interpreted layout.localModel) mode with
          | error error =>
              rw [separationPrepared, modePrepared] at prepared
              cases prepared
          | ok targetMode =>
              rw [separationPrepared, modePrepared] at prepared
              cases prepared
              have separationEquality :=
                totalSeparationContext_of_prepared layout separation
                  targetSeparation (by
                    simpa [translateSeparationContext] using
                        separationPrepared)
              have modeEquality := totalModeContext_of_prepared layout mode
                targetMode (by
                  simpa [translateModeContext]
                    using modePrepared)
              simp [totalRequirements, separationEquality, modeEquality]

mutual

/-- Translate ambient cumulative types.  Positive object nodes invoke full
preparation.  A captured native object arrow is translated directly to the
negative consumer encoding, avoiding a positive package/open detour. -/
def translateType {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) :
    Source.Ty sourceScope -> Except Error (Target.Ty targetScope)
  | .top => .ok .top
  | .bot => .ok .bot
  | .one => .ok .one
  | .ref reference =>
      Compile.typeReference layout (.interpreted layout.localModel) reference
  | .arr domain codomain => do
      pure (.arr (← translateType layout domain)
        (← translateType layout codomain))
  | .objectArrow parameter resultTemplate => do
      let prepared ← prepareObjectArrow layout parameter resultTemplate
      pure (prepared.targetType .empty)
  | .capturing captures (.objectArrow parameter resultTemplate) => do
      let closure ← translateCapture layout captures
      let prepared ← prepareObjectArrow layout parameter resultTemplate
      pure (prepared.targetType closure)
  | .capturing captures shape => do
      pure (.capturing (← translateCapture layout captures)
        (← translateType layout shape))
  | .forallI interval body => do
      let theory ← translateInterval layout interval
      let targetBody ← translateType (layout.extendStatic interval) body
      pure (.forallT theory targetBody)
  | .existsI interval body => do
      let theory ← translateInterval layout interval
      let targetBody ← translateType (layout.extendStatic interval) body
      pure (.existsT theory targetBody)
  | .modal requirements body => do
      pure (.modal (← translateRequirements layout requirements)
        (← translateType layout body))
  | .object object => do
      let prepared ← prepareObject layout object
      pure
        (DOTCaptureToManySortedFC.Intersections.ObjectInterface.existentialShape
          prepared.encoding.theory prepared.representation)

/-- Translate an ambient expression of either static sort. -/
def translateStaticExpr {sort : Source.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) :
    Source.StaticExpr sort sourceScope ->
      Except Error (Target.StaticExpr (translateSort sort) targetScope)
  | .type type => (translateType layout type).map .type
  | .capture capture => (translateCapture layout capture).map .capture

/-- Compile an independently optional true interval into a one-symbol target
theory with exactly the evidence binders described by its endpoint shape. -/
def translateInterval {sort : Source.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.Interval sort sourceScope) :
    Except Error
      (Target.Theory targetScope [translateSort sort]
        (intervalRelations source)) :=
  match source with
  | .bounds .none .none =>
      .ok (ManySortedFC.Interval.unconstrained (translateSort sort))
  | .bounds (.some lower) .none => do
      pure (ManySortedFC.Interval.lowerBounded
        (← translateStaticExpr layout lower))
  | .bounds .none (.some upper) => do
      pure (ManySortedFC.Interval.upperBounded
        (← translateStaticExpr layout upper))
  | .bounds (.some lower) (.some upper) => do
      pure (ManySortedFC.Interval.between
        (← translateStaticExpr layout lower)
        (← translateStaticExpr layout upper))

end

/-- Preparation-level name for the canonical newest lexical slot. -/
def newestStaticSlot (targetScope : Target.Sig) {sourceScope : Source.Sig}
    {sort : Source.StaticSort} (interval : Source.Interval sort sourceScope) :
    ManySortedTranslation.StaticSlot
      (Target.StaticScope targetScope [translateSort sort]
        (intervalRelations interval)) (translateSort sort) :=
  Layout.newestStaticSlot targetScope interval

def emptyLayout : Layout [] [] := Layout.empty

end DOTCaptureToManySortedFC.ModalIntersections.Preparation
