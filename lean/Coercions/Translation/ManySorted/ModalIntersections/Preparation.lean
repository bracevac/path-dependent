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

private def expectType {scope : Target.Sig} (label : Nat) :
    MemberName scope -> Except Error
      (Target.BVar scope (.symbol .type))
  | .type _ name => .ok name
  | .capture _ _ =>
      .error (.memberSortMismatch label .type .capture)

private def expectCapture {scope : Target.Sig} (label : Nat) :
    MemberName scope -> Except Error
      (Target.BVar scope (.symbol .capture))
  | .capture _ name => .ok name
  | .type _ _ =>
      .error (.memberSortMismatch label .capture .type)

private def pathMember {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (path : Source.Path sourceScope) (label : Nat) :
    Except Error (MemberName targetScope) :=
  match layout.member? path label with
  | some member => .ok member
  | none => .error (.unknownPathMember label)

private def localMember {scope : Target.Sig}
    (members : List (MemberName scope)) (label : Nat) :
    Except Error (MemberName scope) :=
  match MemberNames.find? members label with
  | some member => .ok member
  | none => .error (.unknownLocalMember label)

private def typeReference {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.StaticRef .type sourceScope ->
      Except Error (Target.BVar targetScope (.symbol .type))
  | .bound name => .ok (layout.staticSlot name).name
  | .typeMember path label => do
      expectType label (← pathMember layout path label)
  | .localTypeMember label => do
      expectType label (← localMember members label)

private def captureReference {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.StaticRef .capture sourceScope ->
      Except Error (Target.BVar targetScope (.symbol .capture))
  | .bound name => .ok (layout.staticSlot name).name
  | .captureMember path label => do
      expectCapture label (← pathMember layout path label)
  | .localCaptureMember label => do
      expectCapture label (← localMember members label)

private def captureCore {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.Capture sourceScope -> Except Error (Target.Capture targetScope)
  | .empty => .ok .empty
  | .union left right => do
      pure (.union (← captureCore layout members left)
        (← captureCore layout members right))
  | .readOnly capture => do
      pure (.readOnly (← captureCore layout members capture))
  | .singleton (.var sourceVar) =>
      .ok (.singleton (layout.termVar sourceVar))
  | .ref reference => do
      pure (.cvar (← captureReference layout members reference))

private def separationContextCore {count : Nat}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.SeparationContext count sourceScope ->
      Except Error (Target.SeparationContext count targetScope)
  | .nil => .ok .nil
  | .cons rest capture => do
      pure (.cons (← separationContextCore layout members rest)
        (← captureCore layout members capture))

private def modeContextCore {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.ModeContext modes sourceScope ->
      Except Error (Target.ModeContext (translateModes modes) targetScope)
  | .nil => .ok .nil
  | .cons rest capture => do
      pure (.cons (← modeContextCore layout members rest)
        (← captureCore layout members capture))

private def requirementsCore {count : Nat}
    {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.ModalRequirements count modes sourceScope ->
      Except Error
        (Target.ModalContext count (translateModes modes) targetScope)
  | .mk separation mode => do
      pure (.mk (← separationContextCore layout members separation)
        (← modeContextCore layout members mode))

private def renameMembers {first second : Target.Sig}
    (members : List (MemberName first)) (rho : Target.Rename first second) :
    List (MemberName second) :=
  members.map fun member => member.rename rho

mutual

private def typeCore {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.Ty sourceScope -> Except Error (Target.Ty targetScope)
  | .top => .ok .top
  | .bot => .ok .bot
  | .one => .ok .one
  | .ref reference => do
      pure (.tvar (← typeReference layout members reference))
  | .arr domain codomain => do
      pure (.arr (← typeCore layout members domain)
        (← typeCore layout members codomain))
  | .objectArrow _ _ => .error .nestedObjectArrowBound
  | .capturing captures shape => do
      pure (.capturing (← captureCore layout members captures)
        (← typeCore layout members shape))
  | .forallI interval body => do
      let theory ← intervalCore layout members interval
      let bodyMembers := renameMembers members
        (Layout.staticRename targetScope interval)
      let targetBody ← typeCore (layout.extendStatic interval) bodyMembers body
      pure (.forallT theory targetBody)
  | .existsI interval body => do
      let theory ← intervalCore layout members interval
      let bodyMembers := renameMembers members
        (Layout.staticRename targetScope interval)
      let targetBody ← typeCore (layout.extendStatic interval) bodyMembers body
      pure (.existsT theory targetBody)
  | .modal requirements body => do
      pure (.modal (← requirementsCore layout members requirements)
        (← typeCore layout members body))
  | .object _ => .error .nestedObjectBound

private def staticExpressionCore {sort : Source.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.StaticExpr sort sourceScope ->
      Except Error (Target.StaticExpr (translateSort sort) targetScope)
  | .type type => (typeCore layout members type).map .type
  | .capture capture => (captureCore layout members capture).map .capture

private def intervalCore {sort : Source.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (interval : Source.Interval sort sourceScope) :
    Except Error
      (Target.Theory targetScope [translateSort sort]
        (intervalRelations interval)) :=
  match interval with
  | .bounds .none .none =>
      .ok (ManySortedFC.Interval.unconstrained (translateSort sort))
  | .bounds (.some lower) .none => do
      pure (ManySortedFC.Interval.lowerBounded
        (← staticExpressionCore layout members lower))
  | .bounds .none (.some upper) => do
      pure (ManySortedFC.Interval.upperBounded
        (← staticExpressionCore layout members upper))
  | .bounds (.some lower) (.some upper) => do
      pure (ManySortedFC.Interval.between
        (← staticExpressionCore layout members lower)
        (← staticExpressionCore layout members upper))

end

/-! Member-aware APIs used by object preparation. -/

def translateCapture {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.Capture sourceScope) :
    Except Error (Target.Capture targetScope) :=
  captureCore layout members source

def translateSeparationContext {count : Nat}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.SeparationContext count sourceScope) :
    Except Error (Target.SeparationContext count targetScope) :=
  separationContextCore layout members source

def translateModeContext {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.ModeContext modes sourceScope) :
    Except Error (Target.ModeContext (translateModes modes) targetScope) :=
  modeContextCore layout members source

def translateRequirements {count : Nat}
    {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.ModalRequirements count modes sourceScope) :
    Except Error
      (Target.ModalContext count (translateModes modes) targetScope) :=
  requirementsCore layout members source

def translateType {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.Ty sourceScope) : Except Error (Target.Ty targetScope) :=
  typeCore layout members source

def translateStaticExpr {sort : Source.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.StaticExpr sort sourceScope) :
    Except Error (Target.StaticExpr (translateSort sort) targetScope) :=
  staticExpressionCore layout members source

def translateInterval {sort : Source.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.Interval sort sourceScope) :
    Except Error
      (Target.Theory targetScope [translateSort sort]
        (intervalRelations source)) :=
  intervalCore layout members source

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
      let lower ← staticExpressionCore layout members interval.lower
      let upper ← staticExpressionCore layout members interval.upper
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
      let lower ← staticExpressionCore layout members interval.lower
      let upper ← staticExpressionCore layout members interval.upper
      pure (⟨lower, upper⟩ ::
        (← translateCaptureMemberIntervals layout members remaining))

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
          (← translateTypeMemberIntervals layout allMembers sourceIntervals) ::
          (← entries layout allMembers remaining allocatedRemaining))
      else
        .error (.allocationMismatch label)
  | .capture label sourceIntervals :: remaining,
      .capture allocatedLabel name :: allocatedRemaining => do
      if _labelsMatch : label = allocatedLabel then
        pure (.capture label name
          (← translateCaptureMemberIntervals layout allMembers sourceIntervals) ::
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
  let .mk interface sourceRepresentation sourceOuterCapture := source
  let prepared ← collectAndPrepare layout interface
  let encoding := encode prepared
  let namesLayout := layout.renameTarget
    (ManySortedFC.Rename.weakenSymbols encoding.symbols)
  let representationAtNames ← Compile.translateType namesLayout
    encoding.prepared.members sourceRepresentation
  let representation := representationAtNames.rename
    (ManySortedFC.Rename.weakenMany
      (ManySortedFC.SymbolScope targetScope encoding.symbols)
      (ManySortedFC.evidenceKinds encoding.relations))
  let outerCapture ← Compile.translateCapture layout [] sourceOuterCapture
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
  Compile.translateCapture layout [] source

def translateSeparationContext {count : Nat}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.SeparationContext count sourceScope) :
    Except Error (Target.SeparationContext count targetScope) :=
  Compile.translateSeparationContext layout [] source

def translateModeContext {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.ModeContext modes sourceScope) :
    Except Error (Target.ModeContext (translateModes modes) targetScope) :=
  Compile.translateModeContext layout [] source

def translateRequirements {count : Nat}
    {modes : List Source.CaptureMode}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.ModalRequirements count modes sourceScope) :
    Except Error
      (Target.ModalContext count (translateModes modes) targetScope) :=
  Compile.translateRequirements layout [] source

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
  | .ref reference => Compile.translateType layout [] (.ref reference)
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
