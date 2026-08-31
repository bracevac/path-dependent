import Coercions.DOT.Captures.Intersections.Signature
import Coercions.ManySortedFC.TheoryMapChecker

/-!
# Names-first encoding of prepared intersection signatures

This module is the target half of M11's two-phase interface translation.
`PreparedSignature` already contains every allocated member name and every
translated bound in the complete symbol scope.  `encode` only emits the two
primitive inclusion propositions for each retained interval occurrence.

No endpoint is combined, and no name is allocated while propositions are
emitted.
-/

namespace DOTCaptureToManySortedFC.Intersections.Encoding

namespace Source

abbrev StaticSort := DOTCapture.Intersections.StaticSort
abbrev Interval := DOTCapture.Intersections.Interval

end Source

namespace Target

open ManySortedFC

abbrev Sig := ManySortedFC.Sig
abbrev StaticSort := ManySortedFC.StaticSort
abbrev Relation := ManySortedFC.Relation
abbrev BVar := ManySortedFC.BVar
abbrev StaticExpr := ManySortedFC.StaticExpr
abbrev Proposition := ManySortedFC.Proposition
abbrev Theory := ManySortedFC.Theory
abbrev SymbolScope := ManySortedFC.SymbolScope
abbrev StaticScope := ManySortedFC.StaticScope
abbrev Rename := ManySortedFC.Rename

end Target

/-- Translate the source sort tag to the identically separated target sort. -/
def targetSort : Source.StaticSort -> Target.StaticSort
  | .type => .type
  | .capture => .capture

/-- A member name allocated in the complete names-only block. -/
inductive MemberName (scope : Target.Sig) where
  | type (label : Nat)
      (name : Target.BVar scope (.symbol .type)) : MemberName scope
  | capture (label : Nat)
      (name : Target.BVar scope (.symbol .capture)) : MemberName scope
deriving DecidableEq

namespace MemberName

def label {scope : Target.Sig} : MemberName scope -> Nat
  | .type label _ => label
  | .capture label _ => label

def sort {scope : Target.Sig} : MemberName scope -> Target.StaticSort
  | .type _ _ => .type
  | .capture _ _ => .capture

def rename {source target : Target.Sig} (member : MemberName source)
    (rho : Target.Rename source target) : MemberName target :=
  match member with
  | .type label name => .type label (rho.var name)
  | .capture label name => .capture label (rho.var name)

@[simp]
theorem rename_label {source target : Target.Sig}
    (member : MemberName source) (rho : Target.Rename source target) :
    (member.rename rho).label = member.label := by
  cases member <;> rfl

@[simp]
theorem rename_sort {source target : Target.Sig}
    (member : MemberName source) (rho : Target.Rename source target) :
    (member.rename rho).sort = member.sort := by
  cases member <;> rfl

end MemberName

/-- A normalized entry after its shared name has been allocated and every
bound has been translated into the complete symbol scope. -/
inductive PreparedEntry (scope : Target.Sig) where
  | type (label : Nat) (name : Target.BVar scope (.symbol .type))
      (intervals : List (Source.Interval (Target.StaticExpr .type scope))) :
      PreparedEntry scope
  | capture (label : Nat) (name : Target.BVar scope (.symbol .capture))
      (intervals : List (Source.Interval (Target.StaticExpr .capture scope))) :
      PreparedEntry scope
deriving DecidableEq

namespace PreparedEntry

def label {scope : Target.Sig} : PreparedEntry scope -> Nat
  | .type label _ _ => label
  | .capture label _ _ => label

def sort {scope : Target.Sig} : PreparedEntry scope -> Target.StaticSort
  | .type _ _ _ => .type
  | .capture _ _ _ => .capture

def member {scope : Target.Sig} : PreparedEntry scope -> MemberName scope
  | .type label name _ => .type label name
  | .capture label name _ => .capture label name

/-- Two directed propositions are retained for every interval occurrence. -/
def relations {scope : Target.Sig} : PreparedEntry scope -> List Target.Relation
  | .type _ _ intervals =>
      intervals.flatMap fun _ => [.inclusion .type, .inclusion .type]
  | .capture _ _ intervals =>
      intervals.flatMap fun _ => [.inclusion .capture, .inclusion .capture]

@[simp]
theorem member_label {scope : Target.Sig} (entry : PreparedEntry scope) :
    entry.member.label = entry.label := by
  cases entry <;> rfl

@[simp]
theorem member_sort {scope : Target.Sig} (entry : PreparedEntry scope) :
    entry.member.sort = entry.sort := by
  cases entry <;> rfl

end PreparedEntry

/-- All names are fixed before `entries` is constructed.  In particular,
every entry bound lives in the same complete symbol scope and may mention any
other member name regardless of entry order. -/
structure PreparedSignature (scope : Target.Sig) where
  symbols : List Target.StaticSort
  entries : List (PreparedEntry (Target.SymbolScope scope symbols))
deriving DecidableEq

namespace PreparedSignature

def relations {scope : Target.Sig} (prepared : PreparedSignature scope) :
    List Target.Relation :=
  prepared.entries.flatMap PreparedEntry.relations

def members {scope : Target.Sig} (prepared : PreparedSignature scope) :
    List (MemberName (Target.SymbolScope scope prepared.symbols)) :=
  prepared.entries.map PreparedEntry.member

end PreparedSignature

/-! ## Emitting a target theory after allocation -/

private def appendTheory {scope : Target.Sig}
    {symbols : List Target.StaticSort}
    {leftRelations rightRelations : List Target.Relation}
    (left : Target.Theory scope symbols leftRelations)
    (right : Target.Theory scope symbols rightRelations) :
    Target.Theory scope symbols (leftRelations ++ rightRelations) :=
  match left with
  | .nil => right
  | .cons proposition rest =>
      .cons proposition (appendTheory rest right)

private def typeIntervalsTheory {scope : Target.Sig}
    {symbols : List Target.StaticSort}
    (name : Target.BVar (Target.SymbolScope scope symbols) (.symbol .type)) :
    (intervals : List (Source.Interval
      (Target.StaticExpr .type (Target.SymbolScope scope symbols)))) ->
      Target.Theory scope symbols
        (intervals.flatMap fun _ =>
          [.inclusion .type, .inclusion .type])
  | [] => .nil
  | interval :: remaining =>
      .cons (.inclusion interval.lower (.type (.tvar name)))
        (.cons (.inclusion (.type (.tvar name)) interval.upper)
          (typeIntervalsTheory name remaining))

private def captureIntervalsTheory {scope : Target.Sig}
    {symbols : List Target.StaticSort}
    (name : Target.BVar (Target.SymbolScope scope symbols)
      (.symbol .capture)) :
    (intervals : List (Source.Interval
      (Target.StaticExpr .capture (Target.SymbolScope scope symbols)))) ->
      Target.Theory scope symbols
        (intervals.flatMap fun _ =>
          [.inclusion .capture, .inclusion .capture])
  | [] => .nil
  | interval :: remaining =>
      .cons (.inclusion interval.lower (.capture (.cvar name)))
        (.cons (.inclusion (.capture (.cvar name)) interval.upper)
          (captureIntervalsTheory name remaining))

private def entryTheory {scope : Target.Sig}
    {symbols : List Target.StaticSort}
    (entry : PreparedEntry (Target.SymbolScope scope symbols)) :
    Target.Theory scope symbols entry.relations :=
  match entry with
  | .type _ name intervals => typeIntervalsTheory name intervals
  | .capture _ name intervals => captureIntervalsTheory name intervals

private def entriesTheory {scope : Target.Sig}
    {symbols : List Target.StaticSort} :
    (entries : List (PreparedEntry (Target.SymbolScope scope symbols))) ->
      Target.Theory scope symbols
        (entries.flatMap PreparedEntry.relations)
  | [] => .nil
  | entry :: remaining =>
      appendTheory (entryTheory entry) (entriesTheory remaining)

/-- A generated names-first target theory together with the allocation table
from which it was produced. -/
structure Encoding (scope : Target.Sig) where
  prepared : PreparedSignature scope
  theory : Target.Theory scope prepared.symbols prepared.relations
deriving DecidableEq

/-- Emit all propositions without allocating or inspecting another name. -/
def encode {scope : Target.Sig} (prepared : PreparedSignature scope) :
    Encoding scope where
  prepared := prepared
  theory := entriesTheory prepared.entries

namespace Encoding

def symbols {scope : Target.Sig} (encoding : Encoding scope) :
    List Target.StaticSort :=
  encoding.prepared.symbols

def relations {scope : Target.Sig} (encoding : Encoding scope) :
    List Target.Relation :=
  encoding.prepared.relations

/-- The same member coordinates after every generated evidence binder has
been opened. -/
def openedMembers {scope : Target.Sig} (encoding : Encoding scope) :
    List (MemberName
      (Target.StaticScope scope encoding.symbols encoding.relations)) :=
  encoding.prepared.members.map fun member =>
    member.rename
      (ManySortedFC.Rename.weakenMany
        (Target.SymbolScope scope encoding.symbols)
        (ManySortedFC.evidenceKinds encoding.relations))

end Encoding

end DOTCaptureToManySortedFC.Intersections.Encoding
