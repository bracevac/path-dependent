import Coercions.DOT.Captures.Intersections.SourceMetatheory
import Coercions.Translation.ManySorted.Intersections.Preparation

/-!
# Metatheory of two-phase intersection-signature preparation

Allocation is proved to follow the normalized source-entry order exactly.
Preparation keeps one member field per prepared entry even when that entry
contains several retained interval occurrences.
-/

namespace DOTCaptureToManySortedFC.Intersections.Preparation

open Encoding

namespace Allocation

private theorem renamed_member_labels {source target : Target.Sig}
    (allocated : List (MemberName source)) (rho : ManySortedFC.Rename source target) :
    (allocated.map fun member => member.rename rho).map MemberName.label =
      allocated.map MemberName.label := by
  induction allocated with
  | nil => rfl
  | cons member remaining induction =>
      simp only [List.map_cons]
      rw [MemberName.rename_label, induction]

private theorem renamed_member_sorts {source target : Target.Sig}
    (allocated : List (MemberName source)) (rho : ManySortedFC.Rename source target) :
    (allocated.map fun member => member.rename rho).map MemberName.sort =
      allocated.map MemberName.sort := by
  induction allocated with
  | nil => rfl
  | cons member remaining induction =>
      simp only [List.map_cons]
      rw [MemberName.rename_sort, induction]

@[simp]
theorem symbols_length {scope : Source.Scope}
    (entries : List (Source.Entry (Source.Expr scope))) :
    (symbols entries).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry remaining induction =>
      cases entry <;> simp [symbols, induction]

@[simp]
theorem members_length (targetScope : Target.Sig) {sourceScope : Source.Scope}
    (entries : List (Source.Entry (Source.Expr sourceScope))) :
    (members targetScope entries).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry remaining induction =>
      cases entry <;> simp [members, induction]

/-- Allocation preserves the normalized entry labels in the same order. -/
@[simp]
theorem members_labels (targetScope : Target.Sig)
    {sourceScope : Source.Scope}
    (entries : List (Source.Entry (Source.Expr sourceScope))) :
    (members targetScope entries).map MemberName.label =
      entries.map DOTCapture.Intersections.Entry.label := by
  induction entries with
  | nil => rfl
  | cons entry remaining induction =>
      cases entry <;>
        simp only [members, List.map_cons,
          DOTCapture.Intersections.Entry.label]
      all_goals
        rw [renamed_member_labels, induction]
        rfl

/-- The allocated member sorts are exactly the emitted symbol telescope. -/
@[simp]
theorem members_sorts (targetScope : Target.Sig)
    {sourceScope : Source.Scope}
    (entries : List (Source.Entry (Source.Expr sourceScope))) :
    (members targetScope entries).map MemberName.sort = symbols entries := by
  induction entries with
  | nil => rfl
  | cons entry remaining induction =>
      cases entry <;> simp only [members, symbols, List.map_cons]
      all_goals
        rw [renamed_member_sorts, induction]
        rfl

/-- The target symbol telescope is the sort map of the normalized entries. -/
@[simp]
theorem symbols_eq_entry_sorts {scope : Source.Scope}
    (entries : List (Source.Entry (Source.Expr scope))) :
    symbols entries = entries.map fun entry =>
      targetSort (DOTCapture.Intersections.Entry.sort entry) := by
  induction entries with
  | nil => rfl
  | cons entry remaining induction =>
      cases entry <;> simp [symbols, targetSort, induction,
        DOTCapture.Intersections.Entry.sort]

/-- A normalized source signature allocates exactly one member per label. -/
theorem members_labels_nodup (targetScope : Target.Sig)
    {sourceScope : Source.Scope}
    {signature : Source.Signature (Source.Expr sourceScope)}
    (normalized : signature.Normalized) :
    ((members targetScope signature.entries).map MemberName.label).Nodup := by
  rw [members_labels]
  exact normalized.labels_nodup

end Allocation

/-! ## Prepared-entry sharing -/

/-- The number of primitive interval occurrences retained in one entry. -/
def preparedIntervalCount {scope : Target.Sig} : PreparedEntry scope -> Nat
  | .type _ _ intervals => intervals.length
  | .capture _ _ intervals => intervals.length

/-- Repeat the entry's one allocated member once per retained interval.  This
view makes sharing explicit without changing the preparation representation. -/
def preparedIntervalMembers {scope : Target.Sig}
    (entry : PreparedEntry scope) : List (MemberName scope) :=
  List.replicate (preparedIntervalCount entry) entry.member

@[simp]
theorem prepared_interval_members_length {scope : Target.Sig}
    (entry : PreparedEntry scope) :
    (preparedIntervalMembers entry).length = preparedIntervalCount entry := by
  simp [preparedIntervalMembers]

theorem every_retained_interval_uses_the_shared_member
    {scope : Target.Sig} (entry : PreparedEntry scope)
    {member : MemberName scope}
    (membership : member ∈ preparedIntervalMembers entry) :
    member = entry.member := by
  have result : preparedIntervalCount entry ≠ 0 ∧ member = entry.member := by
    simpa [preparedIntervalMembers] using membership
  exact result.2

@[simp]
theorem prepared_members_labels {scope : Target.Sig}
    (prepared : PreparedSignature scope) :
    prepared.members.map MemberName.label =
      prepared.entries.map PreparedEntry.label := by
  simp [PreparedSignature.members, List.map_map, Function.comp_def]

@[simp]
theorem prepared_members_sorts {scope : Target.Sig}
    (prepared : PreparedSignature scope) :
    prepared.members.map MemberName.sort =
      prepared.entries.map PreparedEntry.sort := by
  simp [PreparedSignature.members, List.map_map, Function.comp_def]

private theorem except_cons_success {error head item : Type}
    {first : Except error head} {rest : Except error (List item)}
    {make : head -> item} {result : List item}
    (success : (do
      pure (make (← first) :: (← rest))) = .ok result) :
    ∃ headValue tail, first = .ok headValue ∧ rest = .ok tail ∧
      result = make headValue :: tail := by
  cases first <;> cases rest <;>
    simp_all [bind, Except.bind, pure, Except.pure]

namespace Compile

/-- Every successful entry-preparation pass retains the source entry labels
and sorts in order.  Bounds may fail to translate, but they cannot change the
allocation shape when translation succeeds. -/
theorem entries_preserve_shape {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (allMembers : List (MemberName targetScope))
    (sourceEntries : List (Source.Entry (Source.Expr sourceScope)))
    (allocated : List (MemberName targetScope))
    {preparedEntries : List (PreparedEntry targetScope)}
    (success : entries layout allMembers sourceEntries allocated =
      .ok preparedEntries) :
    preparedEntries.map PreparedEntry.label =
        sourceEntries.map DOTCapture.Intersections.Entry.label ∧
      preparedEntries.map PreparedEntry.sort =
        sourceEntries.map fun entry =>
          targetSort (DOTCapture.Intersections.Entry.sort entry) := by
  induction sourceEntries generalizing allocated preparedEntries with
  | nil =>
      cases allocated <;> simp_all [entries]
  | cons sourceEntry remaining induction =>
      cases sourceEntry with
      | type label sourceIntervals =>
          cases allocated with
          | nil => simp [entries] at success
          | cons allocated allocatedRemaining =>
              cases allocated with
              | capture allocatedLabel name => simp [entries] at success
              | type allocatedLabel name =>
                  by_cases labelsMatch : label = allocatedLabel
                  · simp only [entries, labelsMatch] at success
                    obtain ⟨translated, preparedRemaining, _intervalSuccess,
                      remainingSuccess, preparedShape⟩ :=
                        except_cons_success success
                    subst allocatedLabel
                    subst preparedEntries
                    have remainingShape := induction allocatedRemaining
                      remainingSuccess
                    constructor <;> simp [remainingShape,
                      PreparedEntry.label, PreparedEntry.sort,
                      DOTCapture.Intersections.Entry.label,
                      DOTCapture.Intersections.Entry.sort, targetSort]
                  · simp [entries, labelsMatch] at success
      | capture label sourceIntervals =>
          cases allocated with
          | nil => simp [entries] at success
          | cons allocated allocatedRemaining =>
              cases allocated with
              | type allocatedLabel name => simp [entries] at success
              | capture allocatedLabel name =>
                  by_cases labelsMatch : label = allocatedLabel
                  · simp only [entries, labelsMatch] at success
                    obtain ⟨translated, preparedRemaining, _intervalSuccess,
                      remainingSuccess, preparedShape⟩ :=
                        except_cons_success success
                    subst allocatedLabel
                    subst preparedEntries
                    have remainingShape := induction allocatedRemaining
                      remainingSuccess
                    constructor <;> simp [remainingShape,
                      PreparedEntry.label, PreparedEntry.sort,
                      DOTCapture.Intersections.Entry.label,
                      DOTCapture.Intersections.Entry.sort, targetSort]
                  · simp [entries, labelsMatch] at success

theorem entries_preserve_labels {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (allMembers : List (MemberName targetScope))
    (sourceEntries : List (Source.Entry (Source.Expr sourceScope)))
    (allocated : List (MemberName targetScope))
    {preparedEntries : List (PreparedEntry targetScope)}
    (success : entries layout allMembers sourceEntries allocated =
      .ok preparedEntries) :
    preparedEntries.map PreparedEntry.label =
      sourceEntries.map DOTCapture.Intersections.Entry.label :=
  (entries_preserve_shape layout allMembers sourceEntries allocated success).1

theorem entries_preserve_sorts {sourceScope : Source.Scope}
    {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (allMembers : List (MemberName targetScope))
    (sourceEntries : List (Source.Entry (Source.Expr sourceScope)))
    (allocated : List (MemberName targetScope))
    {preparedEntries : List (PreparedEntry targetScope)}
    (success : entries layout allMembers sourceEntries allocated =
      .ok preparedEntries) :
    preparedEntries.map PreparedEntry.sort =
      sourceEntries.map fun entry =>
        targetSort (DOTCapture.Intersections.Entry.sort entry) :=
  (entries_preserve_shape layout allMembers sourceEntries allocated success).2

end Compile

/-! ## Successful preparation -/

private theorem prepared_symbols_of_result {targetScope : Target.Sig}
    (symbols : List ManySortedFC.StaticSort)
    (result : Except Error
      (List (PreparedEntry (Target.SymbolScope targetScope symbols))))
    {prepared : PreparedSignature targetScope}
    (success : (do
      let entries ← result
      pure ({ symbols := symbols, entries := entries } :
        PreparedSignature targetScope)) = .ok prepared) :
    prepared.symbols = symbols := by
  cases result with
  | error failure => simp [Functor.map, Except.map] at success
  | ok entries =>
      simp [Functor.map, Except.map] at success
      subst prepared
      rfl

private theorem prepared_result_of_success {targetScope : Target.Sig}
    (symbols : List ManySortedFC.StaticSort)
    (result : Except Error
      (List (PreparedEntry (Target.SymbolScope targetScope symbols))))
    {prepared : PreparedSignature targetScope}
    (success : (do
      let entries ← result
      pure ({ symbols := symbols, entries := entries } :
        PreparedSignature targetScope)) = .ok prepared) :
    ∃ entries, result = .ok entries ∧
      prepared = { symbols := symbols, entries := entries } := by
  cases result with
  | error failure => simp [Functor.map, Except.map] at success
  | ok entries =>
      simp [Functor.map, Except.map] at success
      subst prepared
      exact ⟨entries, rfl, rfl⟩

/-- Preparation cannot alter the symbol telescope fixed by allocation. -/
theorem prepare_preserves_allocated_symbols
    {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (signature : Source.Signature (Source.Expr sourceScope))
    {prepared : PreparedSignature targetScope}
    (success : prepare layout signature = .ok prepared) :
    prepared.symbols = Allocation.symbols signature.entries := by
  unfold prepare at success
  exact prepared_symbols_of_result (Allocation.symbols signature.entries)
    _ success

/-- Consequently, successful preparation allocates one symbol for every
normalized entry, hence one symbol for every normalized label. -/
theorem prepare_symbol_count
    {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (signature : Source.Signature (Source.Expr sourceScope))
    {prepared : PreparedSignature targetScope}
    (success : prepare layout signature = .ok prepared) :
    prepared.symbols.length = signature.entries.length := by
  rw [prepare_preserves_allocated_symbols layout signature success,
    Allocation.symbols_length]

/-- Successful preparation preserves both label order and sort order in its
prepared entries. -/
theorem prepare_preserves_entry_shape
    {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (signature : Source.Signature (Source.Expr sourceScope))
    {prepared : PreparedSignature targetScope}
    (success : prepare layout signature = .ok prepared) :
    prepared.entries.map PreparedEntry.label =
        signature.entries.map DOTCapture.Intersections.Entry.label ∧
      prepared.entries.map PreparedEntry.sort =
        signature.entries.map fun entry =>
          targetSort (DOTCapture.Intersections.Entry.sort entry) := by
  unfold prepare at success
  obtain ⟨preparedEntries, entriesSuccess, preparedShape⟩ :=
    prepared_result_of_success (Allocation.symbols signature.entries) _ success
  subst prepared
  exact Compile.entries_preserve_shape _ _ signature.entries _ entriesSuccess

theorem prepare_preserves_entry_labels
    {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (signature : Source.Signature (Source.Expr sourceScope))
    {prepared : PreparedSignature targetScope}
    (success : prepare layout signature = .ok prepared) :
    prepared.entries.map PreparedEntry.label =
      signature.entries.map DOTCapture.Intersections.Entry.label :=
  (prepare_preserves_entry_shape layout signature success).1

theorem prepare_preserves_entry_sorts
    {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (signature : Source.Signature (Source.Expr sourceScope))
    {prepared : PreparedSignature targetScope}
    (success : prepare layout signature = .ok prepared) :
    prepared.entries.map PreparedEntry.sort =
      signature.entries.map fun entry =>
        targetSort (DOTCapture.Intersections.Entry.sort entry) :=
  (prepare_preserves_entry_shape layout signature success).2

/-- A successful preparation of a normalized signature has one prepared
member—and therefore one target name—for every source label. -/
theorem prepare_member_labels_nodup
    {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : OuterLayout sourceScope targetScope)
    (signature : Source.Signature (Source.Expr sourceScope))
    (normalized : signature.Normalized)
    {prepared : PreparedSignature targetScope}
    (success : prepare layout signature = .ok prepared) :
    (prepared.members.map MemberName.label).Nodup := by
  rw [prepared_members_labels,
    prepare_preserves_entry_labels layout signature success]
  exact normalized.labels_nodup

end DOTCaptureToManySortedFC.Intersections.Preparation
