import Coercions.DOT.Intersections.Source.Syntax

/-!
# Normalized member signatures

Signature collection is deliberately separate from target allocation.  A
signature entry represents one member identity (one label), while its list of
intervals records every constraint-bearing view of that identity.  Canonical
signatures order entries by label and contain no empty interval lists.
-/

namespace DotFCI.Source

open DotFC

/-- One lower/upper constraint occurrence contributed by a member view. -/
structure Interval (scope : Sig) where
  lower : Ty scope
  upper : Ty scope
deriving DecidableEq

namespace Interval

/-- Rename both bounds of an interval. -/
def rename {source target : Sig} (interval : Interval source)
    (rho : Rename source target) : Interval target where
  lower := interval.lower.rename rho
  upper := interval.upper.rename rho

@[simp]
theorem rename_id {scope : Sig} (interval : Interval scope) :
    interval.rename Rename.id = interval := by
  cases interval
  simp [rename]

@[simp]
theorem rename_comp {first second third : Sig}
    (interval : Interval first) (firstRename : Rename first second)
    (secondRename : Rename second third) :
    (interval.rename firstRename).rename secondRename =
      interval.rename (firstRename.comp secondRename) := by
  cases interval
  simp [rename, Ty.rename_comp]

end Interval

/-- All accumulated interval constraints for one unique member label. -/
structure SignatureEntry (scope : Sig) where
  label : Name
  intervals : List (Interval scope)
deriving DecidableEq

namespace SignatureEntry

/-- Rename every constraint while retaining the member label. -/
def rename {source target : Sig} (entry : SignatureEntry source)
    (rho : Rename source target) : SignatureEntry target where
  label := entry.label
  intervals := entry.intervals.map fun interval => interval.rename rho

/-- The contribution of one entry at a queried label. -/
def constraintsAt {scope : Sig} (entry : SignatureEntry scope)
    (label : Name) : List (Interval scope) :=
  if entry.label = label then entry.intervals else []

@[simp]
theorem rename_label {source target : Sig} (entry : SignatureEntry source)
    (rho : Rename source target) :
    (entry.rename rho).label = entry.label := rfl

@[simp]
theorem rename_intervals {source target : Sig}
    (entry : SignatureEntry source) (rho : Rename source target) :
    (entry.rename rho).intervals =
      entry.intervals.map fun interval => interval.rename rho := rfl

@[simp]
theorem rename_id {scope : Sig} (entry : SignatureEntry scope) :
    entry.rename Rename.id = entry := by
  cases entry with
  | mk label intervals =>
      simp [rename]

@[simp]
theorem rename_comp {first second third : Sig}
    (entry : SignatureEntry first) (firstRename : Rename first second)
    (secondRename : Rename second third) :
    (entry.rename firstRename).rename secondRename =
      entry.rename (firstRename.comp secondRename) := by
  cases entry with
  | mk label intervals =>
      simp [rename, Interval.rename_comp, List.map_map,
        Function.comp_def]

end SignatureEntry

/-- A finite member signature.  The executable constructors below produce
entries in strictly increasing label order; `Normalized` exposes that
invariant to proofs without storing proof fields in executable data. -/
structure Signature (scope : Sig) where
  entries : List (SignatureEntry scope)
deriving DecidableEq

namespace Signature

/-- Strict label ordering used by canonical signatures. -/
def Before {scope : Sig} (left right : SignatureEntry scope) : Prop :=
  left.label < right.label

/-- Canonical signature invariant: labels are sorted and every label has at
least one interval occurrence. -/
structure Normalized {scope : Sig} (signature : Signature scope) : Prop where
  sorted : signature.entries.Pairwise Before
  nonempty : ∀ entry ∈ signature.entries, entry.intervals ≠ []

/-- The empty member signature. -/
def empty {scope : Sig} : Signature scope := ⟨[]⟩

/-- A one-label, one-interval member signature. -/
def singleton {scope : Sig} (label : Name) (lower upper : Ty scope) :
    Signature scope :=
  ⟨[⟨label, [⟨lower, upper⟩]⟩]⟩

/-- Rename every interval bound in a signature. -/
def rename {source target : Sig} (signature : Signature source)
    (rho : Rename source target) : Signature target :=
  ⟨signature.entries.map fun entry => entry.rename rho⟩

/-- Labels in their allocation order. -/
def labels {scope : Sig} (signature : Signature scope) : List Name :=
  signature.entries.map SignatureEntry.label

/-- Constraint lookup on an entry list. -/
@[simp]
def constraintsAtEntries {scope : Sig} :
    List (SignatureEntry scope) → Name → List (Interval scope)
  | [], _ => []
  | entry :: remaining, label =>
      entry.constraintsAt label ++ constraintsAtEntries remaining label

/-- All interval occurrences associated with one label.  On normalized
signatures at most one entry contributes, but this definition is total and
also useful while proving normalization. -/
def constraintsAt {scope : Sig} (signature : Signature scope)
    (label : Name) : List (Interval scope) :=
  constraintsAtEntries signature.entries label

/-- Total number of interval occurrences across the signature. -/
def intervalCount {scope : Sig} (signature : Signature scope) : Nat :=
  signature.entries.foldl
    (fun count entry => count + entry.intervals.length) 0

/-- Insert one nonempty entry into an ordered unique entry list.  Equal
labels retain the existing identity and append the new interval constraints. -/
def insertEntry {scope : Sig} (entry : SignatureEntry scope) :
    List (SignatureEntry scope) → List (SignatureEntry scope)
  | [] => [entry]
  | current :: remaining =>
      if entry.label < current.label then
        entry :: current :: remaining
      else if entry.label = current.label then
        ⟨current.label, current.intervals ++ entry.intervals⟩ :: remaining
      else
        current :: insertEntry entry remaining

/-- Merge a list of entries into an already accumulated signature. -/
def mergeEntries {scope : Sig} :
    List (SignatureEntry scope) → List (SignatureEntry scope) →
      List (SignatureEntry scope)
  | accumulated, [] => accumulated
  | accumulated, entry :: remaining =>
      mergeEntries (insertEntry entry accumulated) remaining

/-- Canonical signature merge.  Overlapping labels share one entry and
accumulate all interval occurrences. -/
def merge {scope : Sig} (left right : Signature scope) : Signature scope :=
  ⟨mergeEntries left.entries right.entries⟩

/-- Extensional signature equivalence preserves the multiplicity of every
constraint occurrence while allowing their order to differ. -/
def Equiv {scope : Sig} (left right : Signature scope) : Prop :=
  ∀ label, (left.constraintsAt label).Perm (right.constraintsAt label)

infix:50 " ≈ₛ " => Equiv

@[simp]
theorem empty_entries {scope : Sig} :
    (empty : Signature scope).entries = [] := rfl

@[simp]
theorem singleton_entries {scope : Sig} (label : Name)
    (lower upper : Ty scope) :
    (singleton label lower upper).entries =
      [⟨label, [⟨lower, upper⟩]⟩] := rfl

@[simp]
theorem rename_entries {source target : Sig} (signature : Signature source)
    (rho : Rename source target) :
    (signature.rename rho).entries =
      signature.entries.map fun entry => entry.rename rho := rfl

@[simp]
theorem rename_id {scope : Sig} (signature : Signature scope) :
    signature.rename Rename.id = signature := by
  cases signature with
  | mk entries =>
      simp [rename]

@[simp]
theorem rename_comp {first second third : Sig}
    (signature : Signature first) (firstRename : Rename first second)
    (secondRename : Rename second third) :
    (signature.rename firstRename).rename secondRename =
      signature.rename (firstRename.comp secondRename) := by
  cases signature with
  | mk entries =>
      simp [rename, SignatureEntry.rename_comp, List.map_map,
        Function.comp_def]

@[simp]
theorem constraintsAt_empty {scope : Sig} (label : Name) :
    (empty : Signature scope).constraintsAt label = [] := rfl

@[simp]
theorem constraintsAt_singleton_same {scope : Sig} (label : Name)
    (lower upper : Ty scope) :
    (singleton label lower upper).constraintsAt label = [⟨lower, upper⟩] := by
  simp [constraintsAt, constraintsAtEntries, SignatureEntry.constraintsAt]

@[simp]
theorem constraintsAt_singleton_different {scope : Sig}
    (entryLabel queryLabel : Name) (lower upper : Ty scope)
    (different : entryLabel ≠ queryLabel) :
    (singleton entryLabel lower upper).constraintsAt queryLabel = [] := by
  simp [constraintsAt, constraintsAtEntries,
    SignatureEntry.constraintsAt, different]

@[simp]
theorem merge_empty_right {scope : Sig} (signature : Signature scope) :
    signature.merge empty = signature := by
  cases signature
  rfl

end Signature

/-! ## Two-phase collection boundary -/

/-- Collect exactly a member/intersection tree into a normalized signature.
No target names or evidence are allocated by this phase. -/
def collect? {scope : Sig} : Ty scope → Option (Signature scope)
  | .member label lower upper => some (.singleton label lower upper)
  | .inter left right => do
      let leftSignature ← collect? left
      let rightSignature ← collect? right
      pure (leftSignature.merge rightSignature)
  | .top => none
  | .bot => none
  | .all _ _ => none
  | .sel _ _ => none

@[simp]
theorem collect?_member {scope : Sig} (label : Name)
    (lower upper : Ty scope) :
    collect? (.member label lower upper) =
      some (.singleton label lower upper) := rfl

@[simp]
theorem collect?_inter {scope : Sig} (left right : Ty scope) :
    collect? (.inter left right) = (do
      let leftSignature ← collect? left
      let rightSignature ← collect? right
      pure (leftSignature.merge rightSignature)) := rfl

@[simp] theorem collect?_top {scope : Sig} : collect? (.top : Ty scope) = none := rfl
@[simp] theorem collect?_bot {scope : Sig} : collect? (.bot : Ty scope) = none := rfl

end DotFCI.Source
