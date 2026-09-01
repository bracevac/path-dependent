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
  | .classifier _ _ :: remaining => .classifier :: symbols remaining

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
  | .classifier label _ :: remaining =>
      .classifier label .here ::
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

/-- Weaken an ambient source/target layout below a complete local symbol
allocation.  Preparation exposes this operation so its occurrence theorem
can state endpoint translation in the exact names-only scope it uses. -/
def weakenLayout {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (symbols : List ManySortedFC.StaticSort) :
    OuterLayout sourceScope (Target.SymbolScope targetScope symbols) :=
  weakenOuter layout symbols

private def expectType {scope : Target.Sig} (label : Nat) :
    MemberName scope -> Except Error
      (Target.BVar scope (.symbol .type))
  | .type _ name => .ok name
  | .capture _ _ =>
      .error (.memberSortMismatch label .type .capture)
  | .classifier _ _ =>
      .error (.memberSortMismatch label .type .classifier)

private def expectCapture {scope : Target.Sig} (label : Nat) :
    MemberName scope -> Except Error
      (Target.BVar scope (.symbol .capture))
  | .capture _ name => .ok name
  | .type _ _ =>
      .error (.memberSortMismatch label .capture .type)
  | .classifier _ _ =>
      .error (.memberSortMismatch label .capture .classifier)

private def expectClassifier {scope : Target.Sig} (label : Nat) :
    MemberName scope -> Except Error
      (Target.BVar scope (.symbol .classifier))
  | .classifier _ name => .ok name
  | .type _ _ =>
      .error (.memberSortMismatch label .classifier .type)
  | .capture _ _ =>
      .error (.memberSortMismatch label .classifier .capture)

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

private def classifierReference {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    Source.StaticRef .classifier sourceScope ->
      Except Error (Target.BVar targetScope (.symbol .classifier))
  | .classifierMember path label => do
      expectClassifier label (← pathMember layout path label)
  | .localClassifierMember label => do
      expectClassifier label (← localMember members label)

private def classifier {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    DOTCapture.Intersections.Source.ClassifierExpr sourceScope ->
      Except Error (ManySortedFC.ClassifierExpr targetScope)
  | .ground kind => .ok (.ground kind)
  | .ref reference => do
      pure (.var (← classifierReference layout members reference))

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
  | .project inner filter => do
      pure (.project (← capture layout members inner)
        (← classifier layout members filter))
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
  | classifier value =>
      exact (classifier layout members value).map .classifier

/-- Sort-preserving wrapper for translating either kind of static bound. -/
def translateStaticExpr {sort : Source.StaticSort}
    {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.StaticExpr sort sourceScope) :
    Except Error
      (ManySortedFC.StaticExpr (targetSort sort) targetScope) :=
  expression layout members source

/-! The public wrappers below expose the two computations that preparation
uses for one retained interval and for an interval list.  They are kept
separate from the bound-translation API because their result retains the
source interval boundary needed by the occurrence-retention metatheory. -/

/-- Translate both endpoints of one retained source interval. -/
def translateInterval {sort : Source.StaticSort}
    {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.Interval (Source.Expr sourceScope sort)) :
    Except Error
      (Source.Interval
        (ManySortedFC.StaticExpr (targetSort sort) targetScope)) := do
  pure
    { lower := ← translateStaticExpr layout members source.lower
      upper := ← translateStaticExpr layout members source.upper }

/-- Translate an interval list without changing its order or cardinality. -/
def translateIntervals {sort : Source.StaticSort}
    {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    List (Source.Interval (Source.Expr sourceScope sort)) ->
      Except Error
        (List (Source.Interval
          (ManySortedFC.StaticExpr (targetSort sort) targetScope)))
  | [] => .ok []
  | current :: remaining => do
      pure ((← translateInterval layout members current) ::
        (← translateIntervals layout members remaining))

def translateConstraint {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    DOTCapture.Intersections.Constraint (Source.Expr sourceScope) ->
      Except Error (PreparedConstraint targetScope)
  | .classifierDisjoint left right => do
      let .classifier targetLeft ←
        translateStaticExpr layout members left
      let .classifier targetRight ←
        translateStaticExpr layout members right
      pure (.classifierDisjoint targetLeft targetRight)
  | .captureHasKind sourceCapture sourceClassifier => do
      let .capture targetCapture ←
        translateStaticExpr layout members sourceCapture
      let .classifier targetClassifier ←
        translateStaticExpr layout members sourceClassifier
      pure (.captureHasKind targetCapture targetClassifier)

def translateConstraints {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope)) :
    List (DOTCapture.Intersections.Constraint (Source.Expr sourceScope)) ->
      Except Error (List (PreparedConstraint targetScope))
  | [] => .ok []
  | constraint :: remaining => do
      pure ((← translateConstraint layout members constraint) ::
        (← translateConstraints layout members remaining))

def entries {sourceScope : Source.Scope}
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
          (← translateIntervals layout allMembers sourceIntervals) ::
          (← entries layout allMembers remaining allocatedRemaining))
      else
        .error (.allocationMismatch label)
  | .capture label sourceIntervals :: remaining,
      .capture allocatedLabel name :: allocatedRemaining => do
      if _labelsMatch : label = allocatedLabel then
        pure (.capture label name
          (← translateIntervals layout allMembers sourceIntervals) ::
          (← entries layout allMembers remaining allocatedRemaining))
      else
        .error (.allocationMismatch label)
  | .classifier label sourceIntervals :: remaining,
      .classifier allocatedLabel name :: allocatedRemaining => do
      if _labelsMatch : label = allocatedLabel then
        pure (.classifier label name
          (← translateIntervals layout allMembers sourceIntervals) ::
          (← entries layout allMembers remaining allocatedRemaining))
      else
        .error (.allocationMismatch label)
  | entry :: _, _ => .error (.allocationMismatch entry.label)
  | [], _ :: _ => .error (.allocationMismatch 0)

/-! ## Public bound-translation boundary -/

/-- Translate one capture bound after the complete local member allocation is
available. -/
def translateCapture {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.Capture sourceScope) :
    Except Error (Target.Capture targetScope) :=
  capture layout members source

/-- Translate one type bound after the complete local member allocation is
available.  Local references may point anywhere in `members`. -/
def translateType {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope))
    (source : Source.Ty sourceScope) : Except Error (Target.Ty targetScope) :=
  type layout members source

end Compile

/-- Prepare one already-normalized source signature.  Allocation is completed
before `Compile.entries` traverses a single bound. -/
def prepare {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (signature : Source.Signature (Source.Expr sourceScope)) :
    Except Error (PreparedSignature targetScope) := do
  let symbols := Allocation.symbols signature.entries
  let allocated := Allocation.members targetScope signature.entries
  let namesLayout := Compile.weakenLayout layout symbols
  let preparedEntries ← Compile.entries namesLayout allocated
    signature.entries allocated
  let preparedConstraints ← Compile.translateConstraints namesLayout
    allocated signature.constraints
  pure
    { symbols := symbols
      entries := preparedEntries
      constraints := preparedConstraints }

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
