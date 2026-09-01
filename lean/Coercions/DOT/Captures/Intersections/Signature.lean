import Coercions.DOT.Captures.Acyclic.Syntax

/-!
# Normalized many-sorted member signatures

This module is the source-independent collection layer for type, capture, and
classifier member intersections. A signature has at most one entry for each
natural-number label. Every interval occurrence contributing to that label is
kept in the entry; merge never invents a combined endpoint.

The bound-expression family is abstract. Instantiating its three sorts with a
captured-DOT source language is a later layer.
-/

namespace DOTCapture.Intersections

/-- Static sorts admitted by normalized object-member signatures.  This is
deliberately independent of the older acyclic source's two-sort tag: the
cumulative language adds classifier members without retrofitting classifier
quantifiers into the historical source calculi. -/
inductive StaticSort : Type where
  | type
  | capture
  | classifier
deriving DecidableEq, Repr

universe u

/-- One independently retained lower/upper interval occurrence. -/
structure Interval (Expr : Type u) where
  lower : Expr
  upper : Expr
deriving DecidableEq

/-- A sort-tagged interval occurrence, useful for statements that quantify
over every constraint in a heterogeneous signature. -/
inductive Occurrence (Expr : StaticSort -> Type u) where
  | type (label : Nat) (interval : Interval (Expr .type))
  | capture (label : Nat) (interval : Interval (Expr .capture))
  | classifier (label : Nat) (interval : Interval (Expr .classifier))

namespace Occurrence

def label {Expr : StaticSort -> Type u} : Occurrence Expr -> Nat
  | .type label _ => label
  | .capture label _ => label
  | .classifier label _ => label

def sort {Expr : StaticSort -> Type u} : Occurrence Expr -> StaticSort
  | .type _ _ => .type
  | .capture _ _ => .capture
  | .classifier _ _ => .classifier

end Occurrence

/-- One allocated member identity.  Its constructor fixes the sort of every
interval stored under the label. -/
inductive Entry (Expr : StaticSort -> Type u) where
  | type (label : Nat) (intervals : List (Interval (Expr .type)))
  | capture (label : Nat) (intervals : List (Interval (Expr .capture)))
  | classifier (label : Nat)
      (intervals : List (Interval (Expr .classifier)))

namespace Entry

def label {Expr : StaticSort -> Type u} : Entry Expr -> Nat
  | .type label _ => label
  | .capture label _ => label
  | .classifier label _ => label

def sort {Expr : StaticSort -> Type u} : Entry Expr -> StaticSort
  | .type _ _ => .type
  | .capture _ _ => .capture
  | .classifier _ _ => .classifier

def occurrenceCount {Expr : StaticSort -> Type u} : Entry Expr -> Nat
  | .type _ intervals => intervals.length
  | .capture _ intervals => intervals.length
  | .classifier _ intervals => intervals.length

def IsNonempty {Expr : StaticSort -> Type u} : Entry Expr -> Prop
  | .type _ intervals => intervals ≠ []
  | .capture _ intervals => intervals ≠ []
  | .classifier _ intervals => intervals ≠ []

/-- Flatten one homogeneous entry into heterogeneous occurrences. -/
def occurrences {Expr : StaticSort -> Type u} : Entry Expr -> List (Occurrence Expr)
  | .type label intervals => intervals.map (Occurrence.type label)
  | .capture label intervals => intervals.map (Occurrence.capture label)
  | .classifier label intervals =>
      intervals.map (Occurrence.classifier label)

@[simp]
theorem occurrences_type {Expr : StaticSort -> Type u} (label : Nat)
    (intervals : List (Interval (Expr .type))) :
    (Entry.type label intervals).occurrences =
      intervals.map (Occurrence.type label) := rfl

@[simp]
theorem occurrences_capture {Expr : StaticSort -> Type u} (label : Nat)
    (intervals : List (Interval (Expr .capture))) :
    (Entry.capture label intervals).occurrences =
      intervals.map (Occurrence.capture label) := rfl

@[simp]
theorem occurrences_classifier {Expr : StaticSort -> Type u} (label : Nat)
    (intervals : List (Interval (Expr .classifier))) :
    (Entry.classifier label intervals).occurrences =
      intervals.map (Occurrence.classifier label) := rfl

@[simp]
theorem occurrence_label {Expr : StaticSort -> Type u}
    (entry : Entry Expr) (occurrence : Occurrence Expr)
    (membership : occurrence ∈ entry.occurrences) :
    occurrence.label = entry.label := by
  cases entry with
  | type label intervals =>
      obtain ⟨interval, _, rfl⟩ := List.mem_map.mp membership
      rfl
  | capture label intervals =>
      obtain ⟨interval, _, rfl⟩ := List.mem_map.mp membership
      rfl
  | classifier label intervals =>
      obtain ⟨interval, _, rfl⟩ := List.mem_map.mp membership
      rfl

@[simp]
theorem occurrence_sort {Expr : StaticSort -> Type u}
    (entry : Entry Expr) (occurrence : Occurrence Expr)
    (membership : occurrence ∈ entry.occurrences) :
    occurrence.sort = entry.sort := by
  cases entry with
  | type label intervals =>
      obtain ⟨interval, _, rfl⟩ := List.mem_map.mp membership
      rfl
  | capture label intervals =>
      obtain ⟨interval, _, rfl⟩ := List.mem_map.mp membership
      rfl
  | classifier label intervals =>
      obtain ⟨interval, _, rfl⟩ := List.mem_map.mp membership
      rfl

end Entry

/-- Cross-sort propositions contributed by a raw object interface.  They are
kept in source order and translated only after the complete member-name block
has been allocated. -/
inductive Constraint (Expr : StaticSort -> Type u) where
  | classifierDisjoint
      (left right : Expr .classifier) : Constraint Expr
  | captureHasKind
      (capture : Expr .capture) (classifier : Expr .classifier) :
      Constraint Expr

/-- A finite normalized-signature candidate.  Executable constructors are
proof-free; `Signature.Normalized` records their canonical invariant. -/
structure Signature (Expr : StaticSort -> Type u) where
  entries : List (Entry Expr)
  constraints : List (Constraint Expr) := []

/-- A same-label merge cannot identify members of different sorts. -/
structure SortConflict where
  label : Nat
  existing : StaticSort
  incoming : StaticSort
deriving DecidableEq, Repr

namespace Signature

def empty {Expr : StaticSort -> Type u} : Signature Expr := ⟨[], []⟩

def singletonType {Expr : StaticSort -> Type u} (label : Nat)
    (lower upper : Expr .type) : Signature Expr :=
  ⟨[.type label [⟨lower, upper⟩]], []⟩

def singletonCapture {Expr : StaticSort -> Type u} (label : Nat)
    (lower upper : Expr .capture) : Signature Expr :=
  ⟨[.capture label [⟨lower, upper⟩]], []⟩

def singletonClassifier {Expr : StaticSort -> Type u} (label : Nat)
    (lower upper : Expr .classifier) : Signature Expr :=
  ⟨[.classifier label [⟨lower, upper⟩]], []⟩

def singletonConstraint {Expr : StaticSort -> Type u}
    (constraint : Constraint Expr) : Signature Expr :=
  ⟨[], [constraint]⟩

def labels {Expr : StaticSort -> Type u} (signature : Signature Expr) :
    List Nat :=
  signature.entries.map Entry.label

def occurrenceCount {Expr : StaticSort -> Type u}
    (signature : Signature Expr) : Nat :=
  signature.entries.foldl
    (fun count entry => count + entry.occurrenceCount) 0

/-- All constraints in allocation order. -/
def occurrences {Expr : StaticSort -> Type u}
    (signature : Signature Expr) : List (Occurrence Expr) :=
  signature.entries.flatMap Entry.occurrences

/-- All retained constraints for one label, across the (unique, when
normalized) entry at that label. -/
def constraintsAt {Expr : StaticSort -> Type u}
    (signature : Signature Expr) (label : Nat) : List (Occurrence Expr) :=
  signature.occurrences.filter fun occurrence => occurrence.label == label

/-- Lookup by member identity.  Canonical signatures are sorted, but lookup
is intentionally total on arbitrary candidates. -/
def lookupEntries {Expr : StaticSort -> Type u} :
    List (Entry Expr) -> Nat -> Option (Entry Expr)
  | [], _ => none
  | entry :: remaining, label =>
      if entry.label = label then some entry
      else lookupEntries remaining label

def lookup {Expr : StaticSort -> Type u} (signature : Signature Expr)
    (label : Nat) : Option (Entry Expr) :=
  lookupEntries signature.entries label

/-- Strict allocation order. -/
def Before {Expr : StaticSort -> Type u} (left right : Entry Expr) : Prop :=
  left.label < right.label

/-- Exactly one nonempty entry per label, in increasing allocation order. -/
structure Normalized {Expr : StaticSort -> Type u}
    (signature : Signature Expr) : Prop where
  sorted : signature.entries.Pairwise Before
  nonempty : ∀ entry ∈ signature.entries, entry.IsNonempty

/-- Combine two entries already known by the caller to have the same label.
The existing entry owns the allocation coordinate and its occurrences remain
before the incoming occurrences. -/
def combineSameLabel? {Expr : StaticSort -> Type u} :
    Entry Expr -> Entry Expr -> Except SortConflict (Entry Expr)
  | .type label existing, .type _ incoming =>
      .ok (.type label (existing ++ incoming))
  | .capture label existing, .capture _ incoming =>
      .ok (.capture label (existing ++ incoming))
  | .classifier label existing, .classifier _ incoming =>
      .ok (.classifier label (existing ++ incoming))
  | .type label _, .capture _ _ =>
      .error ⟨label, .type, .capture⟩
  | .type label _, .classifier _ _ =>
      .error ⟨label, .type, .classifier⟩
  | .capture label _, .type _ _ =>
      .error ⟨label, .capture, .type⟩
  | .capture label _, .classifier _ _ =>
      .error ⟨label, .capture, .classifier⟩
  | .classifier label _, .type _ _ =>
      .error ⟨label, .classifier, .type⟩
  | .classifier label _, .capture _ _ =>
      .error ⟨label, .classifier, .capture⟩

/-- Insert one entry into an ordered signature candidate.  Equal labels share
their existing identity precisely when their sorts agree. -/
def insertEntry? {Expr : StaticSort -> Type u} (incoming : Entry Expr) :
    List (Entry Expr) -> Except SortConflict (List (Entry Expr))
  | [] => .ok [incoming]
  | current :: remaining =>
      if incoming.label < current.label then
        .ok (incoming :: current :: remaining)
      else if incoming.label = current.label then
        match combineSameLabel? current incoming with
        | .error conflict => .error conflict
        | .ok combined => .ok (combined :: remaining)
      else
        match insertEntry? incoming remaining with
        | .error conflict => .error conflict
        | .ok inserted => .ok (current :: inserted)

/-- Fold every incoming entry into an accumulated canonical signature. -/
def mergeEntries? {Expr : StaticSort -> Type u} :
    List (Entry Expr) -> List (Entry Expr) ->
      Except SortConflict (List (Entry Expr))
  | accumulated, [] => .ok accumulated
  | accumulated, entry :: remaining =>
      match insertEntry? entry accumulated with
      | .error conflict => .error conflict
      | .ok inserted => mergeEntries? inserted remaining

/-- Executable many-sorted signature merge. -/
def merge? {Expr : StaticSort -> Type u}
    (left right : Signature Expr) : Except SortConflict (Signature Expr) :=
  match mergeEntries? left.entries right.entries with
  | .error conflict => .error conflict
  | .ok entries => .ok ⟨entries, left.constraints ++ right.constraints⟩

@[simp]
theorem merge?_empty_right {Expr : StaticSort -> Type u}
    (signature : Signature Expr) :
    merge? signature empty = .ok signature := by
  cases signature
  simp [merge?, empty, mergeEntries?]

end Signature

end DOTCapture.Intersections
