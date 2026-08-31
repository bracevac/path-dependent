import Coercions.DOT.Captures.Intersections.SourceSyntax
import Coercions.Translation.ManySorted.Intersections.Encoding

/-!
# Two-phase preparation of captured intersection signatures

Preparation first allocates one target name for every normalized label.  Only
then are interval bounds translated in the complete names-only scope.  Local
references can therefore point forward, backward, or mutually across the
canonical member order.
-/

namespace DOTCaptureToManySortedFC.Intersections.Preparation

namespace Source

open DOTCapture.Intersections

abbrev Scope := DOTCapture.Intersections.Source.Scope
abbrev Var := DOTCapture.Intersections.Source.Var
abbrev Path := DOTCapture.Intersections.Source.Path
abbrev StaticSort := DOTCapture.Intersections.Source.StaticSort
abbrev StaticRef := DOTCapture.Intersections.Source.StaticRef
abbrev Capture := DOTCapture.Intersections.Source.Capture
abbrev Ty := DOTCapture.Intersections.Source.Ty
abbrev StaticExpr := DOTCapture.Intersections.Source.StaticExpr
abbrev Interface := DOTCapture.Intersections.Source.Interface
abbrev Expr := DOTCapture.Intersections.Source.Interface.Expr
abbrev Entry := DOTCapture.Intersections.Entry
abbrev Signature := DOTCapture.Intersections.Signature
abbrev Interval := DOTCapture.Intersections.Interval
abbrev SortConflict := DOTCapture.Intersections.SortConflict

end Source

namespace Target

open ManySortedFC

abbrev Sig := ManySortedFC.Sig
abbrev BVar := ManySortedFC.BVar
abbrev Rename := ManySortedFC.Rename
abbrev StaticExpr := ManySortedFC.StaticExpr
abbrev Capture := ManySortedFC.Capture
abbrev Ty := ManySortedFC.Ty
abbrev SymbolScope := ManySortedFC.SymbolScope

end Target

open Encoding

/-- Existing stable roots in the ambient target context.  A lookup returns
the actual target member name, not an arbitrary expression, so identity is
preserved structurally. -/
structure OuterLayout (sourceScope : Source.Scope) (targetScope : Target.Sig)
    where
  termVar : Source.Var sourceScope -> Target.BVar targetScope .term
  member? : Source.Path sourceScope -> Nat ->
    Option (MemberName targetScope)

/-- Failures after label/sort normalization. -/
inductive Error : Type where
  | sortConflict (conflict : Source.SortConflict)
  | unknownPathMember (label : Nat)
  | unknownLocalMember (label : Nat)
  | memberSortMismatch (label : Nat)
      (expected actual : ManySortedFC.StaticSort)
  | nestedObjectBound
  | allocationMismatch (label : Nat)
deriving DecidableEq, Repr

namespace MemberNames

/-- Untyped label lookup is intentional: callers can distinguish a missing
member from a present member at the wrong sort. -/
def find? {scope : Target.Sig} : List (MemberName scope) -> Nat ->
    Option (MemberName scope)
  | [], _ => none
  | member :: remaining, label =>
      if member.label = label then some member else find? remaining label

end MemberNames

namespace Allocation

/-- Canonical target sorts in the same label order as normalized entries. -/
def symbols {scope : Source.Scope} :
    List (Source.Entry (Source.Expr scope)) -> List ManySortedFC.StaticSort
  | [] => []
  | .type _ _ :: remaining => .type :: symbols remaining
  | .capture _ _ :: remaining => .capture :: symbols remaining

/-- Allocate all member names before translating any interval endpoint.  The
head normalized entry is the newest target symbol. -/
def members (targetScope : Target.Sig) {sourceScope : Source.Scope} :
    (entries : List (Source.Entry (Source.Expr sourceScope))) ->
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

private def weakenOuter {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (symbols : List ManySortedFC.StaticSort) :
    OuterLayout sourceScope (Target.SymbolScope targetScope symbols) where
  termVar := fun sourceVar =>
    (ManySortedFC.Rename.weakenSymbols symbols).var (layout.termVar sourceVar)
  member? := fun path label =>
    (layout.member? path label).map fun member =>
      member.rename (ManySortedFC.Rename.weakenSymbols symbols)

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

private def pathMember {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
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

private def typeReference {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.StaticRef .type sourceScope ->
      Except Error (Target.BVar targetScope (.symbol .type))
  | .typeMember path label => do
      expectType label (← pathMember layout path label)
  | .localTypeMember label => do
      expectType label (← localMember members label)

private def captureReference {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.StaticRef .capture sourceScope ->
      Except Error (Target.BVar targetScope (.symbol .capture))
  | .captureMember path label => do
      expectCapture label (← pathMember layout path label)
  | .localCaptureMember label => do
      expectCapture label (← localMember members label)

mutual

private def capture {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.Capture sourceScope -> Except Error (Target.Capture targetScope)
  | .empty => .ok .empty
  | .union left right => do
      pure (.union (← capture layout members left)
        (← capture layout members right))
  | .singleton (.var sourceVar) =>
      .ok (.singleton (layout.termVar sourceVar))
  | .ref reference => do
      pure (.cvar (← captureReference layout members reference))

private def type {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.Ty sourceScope -> Except Error (Target.Ty targetScope)
  | .top => .ok .top
  | .bot => .ok .bot
  | .one => .ok .one
  | .ref reference => do
      pure (.tvar (← typeReference layout members reference))
  | .arr domain codomain => do
      pure (.arr (← type layout members domain)
        (← type layout members codomain))
  | .capturing captures shape => do
      pure (.capturing (← capture layout members captures)
        (← type layout members shape))
  | .object _ => .error .nestedObjectBound

end

private def expression {sort : Source.StaticSort}
    {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.StaticExpr sort sourceScope ->
      Except Error (ManySortedFC.StaticExpr (targetSort sort) targetScope) := by
  intro source
  cases source with
  | type value => exact (type layout members value).map .type
  | capture value => exact (capture layout members value).map .capture

private def interval {sort : Source.StaticSort}
    {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.Interval (Source.Expr sourceScope sort)) :
    Except Error
      (Source.Interval
        (ManySortedFC.StaticExpr (targetSort sort) targetScope)) := do
  pure
    { lower := ← expression layout members source.lower
      upper := ← expression layout members source.upper }

private def intervals {sort : Source.StaticSort}
    {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    List (Source.Interval (Source.Expr sourceScope sort)) ->
      Except Error
        (List (Source.Interval
          (ManySortedFC.StaticExpr (targetSort sort) targetScope)))
  | [] => .ok []
  | current :: remaining => do
      pure ((← interval layout members current) ::
        (← intervals layout members remaining))

private def entries {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (allMembers : List (MemberName targetScope)) :
    List (Source.Entry (Source.Expr sourceScope)) ->
    List (MemberName targetScope) ->
      Except Error (List (PreparedEntry targetScope))
  | [], [] => .ok []
  | .type label sourceIntervals :: remaining,
      .type allocatedLabel name :: allocatedRemaining => do
      if _labelsMatch : label = allocatedLabel then
        pure (.type label name
          (← intervals layout allMembers sourceIntervals) ::
          (← entries layout allMembers remaining allocatedRemaining))
      else
        .error (.allocationMismatch label)
  | .capture label sourceIntervals :: remaining,
      .capture allocatedLabel name :: allocatedRemaining => do
      if _labelsMatch : label = allocatedLabel then
        pure (.capture label name
          (← intervals layout allMembers sourceIntervals) ::
          (← entries layout allMembers remaining allocatedRemaining))
      else
        .error (.allocationMismatch label)
  | entry :: _, _ => .error (.allocationMismatch entry.label)
  | [], _ :: _ => .error (.allocationMismatch 0)

end Compile

/-- Prepare one already-normalized source signature.  Allocation is completed
before `Compile.entries` traverses a single bound. -/
def prepare {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (signature : Source.Signature (Source.Expr sourceScope)) :
    Except Error (PreparedSignature targetScope) := do
  let symbols := Allocation.symbols signature.entries
  let allocated := Allocation.members targetScope signature.entries
  let namesLayout := Compile.weakenOuter layout symbols
  let preparedEntries ← Compile.entries namesLayout allocated
    signature.entries allocated
  pure { symbols := symbols, entries := preparedEntries }

/-- Collect by label, reject a sort conflict, allocate every surviving name,
then translate all bounds. -/
def collectAndPrepare {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (interface : Source.Interface sourceScope) :
    Except Error (PreparedSignature targetScope) := do
  let signature ← interface.collect.mapError Error.sortConflict
  prepare layout signature

/-- The closed source has no ambient term paths or member roots. -/
def emptyLayout (targetScope : Target.Sig) : OuterLayout 0 targetScope where
  termVar := fun sourceVar => nomatch sourceVar
  member? := fun path => nomatch path

end DOTCaptureToManySortedFC.Intersections.Preparation
