import Coercions.Translation.ManySorted.Intersections.PreparationMetatheory
import Coercions.Translation.ManySorted.Intersections.TheoryPermutationCoherence

/-!
# Source-to-target coherence for permuted intersection constraints

Normalized source signatures that are `ConstraintEquivalent` have the same
canonical label/sort allocation and differ only by a sort-indexed permutation
of retained intervals at each label.  When their separately stored mixed
constraints are also permutations, successful partial translation preserves
both permutations. Consequently their prepared encodings share a symbol
telescope and their generated target theories differ only by a packed
proposition permutation.

This is the source/preparation bridge consumed by the generic checked theory
maps in `TheoryPermutationCoherence`.
-/

namespace DOTCapture.Intersections

universe u

namespace Entry

inductive ConstraintEquivalent {Expr : StaticSort -> Type u} :
    Entry Expr -> Entry Expr -> Prop where
  | type (label : Nat) {first second : List (Interval (Expr .type))}
      (intervals : first.Perm second) :
      ConstraintEquivalent (.type label first) (.type label second)
  | capture (label : Nat) {first second : List (Interval (Expr .capture))}
      (intervals : first.Perm second) :
      ConstraintEquivalent (.capture label first) (.capture label second)
  | classifier (label : Nat)
      {first second : List (Interval (Expr .classifier))}
      (intervals : first.Perm second) :
      ConstraintEquivalent (.classifier label first)
        (.classifier label second)

end Entry

namespace Signature

inductive EntriesConstraintEquivalent {Expr : StaticSort -> Type u} :
    List (Entry Expr) -> List (Entry Expr) -> Prop where
  | nil : EntriesConstraintEquivalent [] []
  | cons {firstHead secondHead : Entry Expr}
      {firstTail secondTail : List (Entry Expr)}
      (head : firstHead.ConstraintEquivalent secondHead)
      (tail : EntriesConstraintEquivalent firstTail secondTail) :
      EntriesConstraintEquivalent (firstHead :: firstTail)
        (secondHead :: secondTail)

private theorem occurrence_mem_entries
    {Expr : StaticSort -> Type u} {entries : List (Entry Expr)}
    {entry : Entry Expr} (entryMem : entry ∈ entries)
    {occurrence : Occurrence Expr} (occurrenceMem : occurrence ∈ entry.occurrences) :
    occurrence ∈ ({ entries := entries } : Signature Expr).occurrences := by
  simp only [occurrences, List.mem_flatMap]
  exact ⟨entry, entryMem, occurrenceMem⟩

private theorem entry_of_occurrence_mem
    {Expr : StaticSort -> Type u} {entries : List (Entry Expr)}
    {occurrence : Occurrence Expr}
    (membership : occurrence ∈
      ({ entries := entries } : Signature Expr).occurrences) :
    ∃ entry ∈ entries, occurrence ∈ entry.occurrences := by
  simpa [occurrences, List.mem_flatMap] using membership

private theorem head_label_le_of_occurrence_mem
    {Expr : StaticSort -> Type u} {head : Entry Expr}
    {tail : List (Entry Expr)}
    (sorted : (head :: tail).Pairwise Before)
    {occurrence : Occurrence Expr}
    (membership : occurrence ∈
      ({ entries := head :: tail } : Signature Expr).occurrences) :
    head.label ≤ occurrence.label := by
  obtain ⟨entry, entryMem, occurrenceMem⟩ :=
    entry_of_occurrence_mem membership
  have occurrenceLabel := Entry.occurrence_label entry occurrence occurrenceMem
  rcases List.mem_cons.mp entryMem with rfl | tailMem
  · exact Nat.le_of_eq occurrenceLabel.symm
  · cases sorted with
    | cons headBefore _ =>
        exact Nat.le_of_lt (by
          calc
            head.label < entry.label := headBefore entry tailMem
            _ = occurrence.label := occurrenceLabel.symm)

private theorem filter_head_occurrences
    {Expr : StaticSort -> Type u} (head : Entry Expr)
    (tail : List (Entry Expr))
    (sorted : (head :: tail).Pairwise Before) :
    List.filter (fun occurrence => occurrence.label == head.label)
        ({ entries := head :: tail } : Signature Expr).occurrences =
      head.occurrences := by
  simp only [occurrences, List.flatMap_cons, List.filter_append]
  have headFilter :
      List.filter (fun occurrence => occurrence.label == head.label)
          head.occurrences = head.occurrences := by
    apply List.filter_eq_self.mpr
    intro occurrence membership
    rw [Entry.occurrence_label head occurrence membership]
    simp
  have tailFilter :
      List.filter (fun occurrence => occurrence.label == head.label)
          ({ entries := tail } : Signature Expr).occurrences = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro occurrence membership
    obtain ⟨entry, entryMem, occurrenceMem⟩ :=
      entry_of_occurrence_mem membership
    have occurrenceLabel := Entry.occurrence_label entry occurrence occurrenceMem
    cases sorted with
    | cons headBefore _ =>
        have different : occurrence.label ≠ head.label := by
          rw [occurrenceLabel]
          exact Nat.ne_of_gt (headBefore entry entryMem)
        simp [different]
  rw [headFilter]
  have tailFilter' :
      List.filter (fun occurrence => occurrence.label == head.label)
          (List.flatMap Entry.occurrences tail) = [] := by
    simpa [Signature.occurrences] using tailFilter
  rw [tailFilter', List.append_nil]

private theorem filter_tail_occurrences
    {Expr : StaticSort -> Type u} (head : Entry Expr)
    (tail : List (Entry Expr))
    (sorted : (head :: tail).Pairwise Before) :
    List.filter (fun occurrence => !(occurrence.label == head.label))
        ({ entries := head :: tail } : Signature Expr).occurrences =
      ({ entries := tail } : Signature Expr).occurrences := by
  simp only [occurrences, List.flatMap_cons, List.filter_append]
  have headFilter :
      List.filter (fun occurrence => !(occurrence.label == head.label))
          head.occurrences = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro occurrence membership
    rw [Entry.occurrence_label head occurrence membership]
    simp
  have tailFilter :
      List.filter (fun occurrence => !(occurrence.label == head.label))
          ({ entries := tail } : Signature Expr).occurrences =
        ({ entries := tail } : Signature Expr).occurrences := by
    apply List.filter_eq_self.mpr
    intro occurrence membership
    obtain ⟨entry, entryMem, occurrenceMem⟩ :=
      entry_of_occurrence_mem membership
    have occurrenceLabel := Entry.occurrence_label entry occurrence occurrenceMem
    cases sorted with
    | cons headBefore _ =>
        have different : occurrence.label ≠ head.label := by
          rw [occurrenceLabel]
          exact Nat.ne_of_gt (headBefore entry entryMem)
        simp [different]
  rw [headFilter]
  have tailFilter' :
      List.filter (fun occurrence => !(occurrence.label == head.label))
          (List.flatMap Entry.occurrences tail) =
        List.flatMap Entry.occurrences tail := by
    simpa [Signature.occurrences] using tailFilter
  rw [tailFilter', List.nil_append]

private def typeInterval? {Expr : StaticSort -> Type u} :
    Occurrence Expr -> Option (Interval (Expr .type))
  | .type _ interval => some interval
  | .capture _ _ => none
  | .classifier _ _ => none

private def captureInterval? {Expr : StaticSort -> Type u} :
    Occurrence Expr -> Option (Interval (Expr .capture))
  | .type _ _ => none
  | .capture _ interval => some interval
  | .classifier _ _ => none

private def classifierInterval? {Expr : StaticSort -> Type u} :
    Occurrence Expr -> Option (Interval (Expr .classifier))
  | .type _ _ => none
  | .capture _ _ => none
  | .classifier _ interval => some interval

private theorem entry_equivalent_of_occurrences
    {Expr : StaticSort -> Type u} (first second : Entry Expr)
    (sameLabel : first.label = second.label)
    (firstNonempty : first.IsNonempty)
    (secondNonempty : second.IsNonempty)
    (equivalent : first.occurrences.Perm second.occurrences) :
    first.ConstraintEquivalent second := by
  cases first with
  | type firstLabel firstIntervals =>
      cases second with
      | type secondLabel secondIntervals =>
          simp only [Entry.label] at sameLabel
          subst secondLabel
          apply Entry.ConstraintEquivalent.type firstLabel
          simpa [Entry.occurrences, typeInterval?, Function.comp_def] using
            equivalent.filterMap typeInterval?
      | capture secondLabel secondIntervals =>
          simp only [Entry.IsNonempty] at firstNonempty secondNonempty
          cases firstIntervals with
          | nil => exact (firstNonempty rfl).elim
          | cons firstInterval firstTail =>
              have sourceMem :
                  Occurrence.type firstLabel firstInterval ∈
                    (Entry.type firstLabel (firstInterval :: firstTail) :
                      Entry Expr).occurrences := by simp [Entry.occurrences]
              have targetMem := equivalent.mem_iff.mp sourceMem
              simp [Entry.occurrences] at targetMem
      | classifier secondLabel secondIntervals =>
          simp only [Entry.IsNonempty] at firstNonempty secondNonempty
          cases firstIntervals with
          | nil => exact (firstNonempty rfl).elim
          | cons firstInterval firstTail =>
              have sourceMem :
                  Occurrence.type firstLabel firstInterval ∈
                    (Entry.type firstLabel (firstInterval :: firstTail) :
                      Entry Expr).occurrences := by simp [Entry.occurrences]
              have targetMem := equivalent.mem_iff.mp sourceMem
              simp [Entry.occurrences] at targetMem
  | capture firstLabel firstIntervals =>
      cases second with
      | type secondLabel secondIntervals =>
          simp only [Entry.IsNonempty] at firstNonempty secondNonempty
          cases firstIntervals with
          | nil => exact (firstNonempty rfl).elim
          | cons firstInterval firstTail =>
              have sourceMem :
                  Occurrence.capture firstLabel firstInterval ∈
                    (Entry.capture firstLabel (firstInterval :: firstTail) :
                      Entry Expr).occurrences := by simp [Entry.occurrences]
              have targetMem := equivalent.mem_iff.mp sourceMem
              simp [Entry.occurrences] at targetMem
      | capture secondLabel secondIntervals =>
          simp only [Entry.label] at sameLabel
          subst secondLabel
          apply Entry.ConstraintEquivalent.capture firstLabel
          simpa [Entry.occurrences, captureInterval?, Function.comp_def] using
            equivalent.filterMap captureInterval?
      | classifier secondLabel secondIntervals =>
          simp only [Entry.IsNonempty] at firstNonempty secondNonempty
          cases firstIntervals with
          | nil => exact (firstNonempty rfl).elim
          | cons firstInterval firstTail =>
              have sourceMem :
                  Occurrence.capture firstLabel firstInterval ∈
                    (Entry.capture firstLabel (firstInterval :: firstTail) :
                      Entry Expr).occurrences := by simp [Entry.occurrences]
              have targetMem := equivalent.mem_iff.mp sourceMem
              simp [Entry.occurrences] at targetMem
  | classifier firstLabel firstIntervals =>
      cases second with
      | type secondLabel secondIntervals =>
          simp only [Entry.IsNonempty] at firstNonempty secondNonempty
          cases firstIntervals with
          | nil => exact (firstNonempty rfl).elim
          | cons firstInterval firstTail =>
              have sourceMem :
                  Occurrence.classifier firstLabel firstInterval ∈
                    (Entry.classifier firstLabel
                      (firstInterval :: firstTail) : Entry Expr).occurrences := by
                simp [Entry.occurrences]
              have targetMem := equivalent.mem_iff.mp sourceMem
              simp [Entry.occurrences] at targetMem
      | capture secondLabel secondIntervals =>
          simp only [Entry.IsNonempty] at firstNonempty secondNonempty
          cases firstIntervals with
          | nil => exact (firstNonempty rfl).elim
          | cons firstInterval firstTail =>
              have sourceMem :
                  Occurrence.classifier firstLabel firstInterval ∈
                    (Entry.classifier firstLabel
                      (firstInterval :: firstTail) : Entry Expr).occurrences := by
                simp [Entry.occurrences]
              have targetMem := equivalent.mem_iff.mp sourceMem
              simp [Entry.occurrences] at targetMem
      | classifier secondLabel secondIntervals =>
          simp only [Entry.label] at sameLabel
          subst secondLabel
          apply Entry.ConstraintEquivalent.classifier firstLabel
          simpa [Entry.occurrences, classifierInterval?, Function.comp_def]
            using equivalent.filterMap classifierInterval?

private theorem entries_equivalent_of_normalized
    {Expr : StaticSort -> Type u}
    (firstEntries secondEntries : List (Entry Expr))
    (firstSorted : firstEntries.Pairwise Before)
    (secondSorted : secondEntries.Pairwise Before)
    (firstNonempty : ∀ entry ∈ firstEntries, entry.IsNonempty)
    (secondNonempty : ∀ entry ∈ secondEntries, entry.IsNonempty)
    (equivalent :
      ({ entries := firstEntries } : Signature Expr).occurrences.Perm
        ({ entries := secondEntries } : Signature Expr).occurrences) :
    EntriesConstraintEquivalent firstEntries secondEntries := by
  induction firstEntries generalizing secondEntries with
  | nil =>
      cases secondEntries with
      | nil => exact .nil
      | cons secondHead secondTail =>
          obtain ⟨occurrence, occurrenceMem⟩ :=
            Entry.exists_occurrence
              (secondNonempty secondHead (.head secondTail))
          have inSecond := occurrence_mem_entries
            (entries := secondHead :: secondTail) (.head secondTail) occurrenceMem
          have inFirst := equivalent.mem_iff.mpr inSecond
          cases inFirst
  | cons firstHead firstTail induction =>
      cases secondEntries with
      | nil =>
          obtain ⟨occurrence, occurrenceMem⟩ :=
            Entry.exists_occurrence
              (firstNonempty firstHead (.head firstTail))
          have inFirst := occurrence_mem_entries
            (entries := firstHead :: firstTail) (.head firstTail) occurrenceMem
          have inSecond := equivalent.mem_iff.mp inFirst
          cases inSecond
      | cons secondHead secondTail =>
          have firstHeadNonempty := firstNonempty firstHead (.head firstTail)
          have secondHeadNonempty := secondNonempty secondHead (.head secondTail)
          obtain ⟨firstOccurrence, firstOccurrenceMem⟩ :=
            Entry.exists_occurrence firstHeadNonempty
          obtain ⟨secondOccurrence, secondOccurrenceMem⟩ :=
            Entry.exists_occurrence secondHeadNonempty
          have firstOccurrenceInFirst := occurrence_mem_entries
            (entries := firstHead :: firstTail) (.head firstTail)
            firstOccurrenceMem
          have secondOccurrenceInSecond := occurrence_mem_entries
            (entries := secondHead :: secondTail) (.head secondTail)
            secondOccurrenceMem
          have firstOccurrenceInSecond :=
            equivalent.mem_iff.mp firstOccurrenceInFirst
          have secondOccurrenceInFirst :=
            equivalent.mem_iff.mpr secondOccurrenceInSecond
          have secondLeFirst : secondHead.label ≤ firstHead.label := by
            calc
              secondHead.label ≤ firstOccurrence.label :=
                head_label_le_of_occurrence_mem secondSorted
                  firstOccurrenceInSecond
              _ = firstHead.label :=
                Entry.occurrence_label firstHead firstOccurrence
                  firstOccurrenceMem
          have firstLeSecond : firstHead.label ≤ secondHead.label := by
            calc
              firstHead.label ≤ secondOccurrence.label :=
                head_label_le_of_occurrence_mem firstSorted
                  secondOccurrenceInFirst
              _ = secondHead.label :=
                Entry.occurrence_label secondHead secondOccurrence
                  secondOccurrenceMem
          have sameLabel : firstHead.label = secondHead.label :=
            Nat.le_antisymm firstLeSecond secondLeFirst
          have headEquivalent :
              firstHead.occurrences.Perm secondHead.occurrences := by
            have filtered := equivalent.filter
              (fun occurrence => occurrence.label == firstHead.label)
            rw [filter_head_occurrences firstHead firstTail firstSorted] at filtered
            rw [sameLabel,
              filter_head_occurrences secondHead secondTail secondSorted] at filtered
            exact filtered
          have tailEquivalent :
              ({ entries := firstTail } : Signature Expr).occurrences.Perm
                ({ entries := secondTail } : Signature Expr).occurrences := by
            have filtered := equivalent.filter
              (fun occurrence => !(occurrence.label == firstHead.label))
            rw [filter_tail_occurrences firstHead firstTail firstSorted] at filtered
            rw [sameLabel,
              filter_tail_occurrences secondHead secondTail secondSorted] at filtered
            exact filtered
          cases firstSorted with
          | cons firstBefore firstTailSorted =>
              cases secondSorted with
              | cons secondBefore secondTailSorted =>
                  apply EntriesConstraintEquivalent.cons
                  · exact entry_equivalent_of_occurrences firstHead secondHead
                      sameLabel firstHeadNonempty secondHeadNonempty
                      headEquivalent
                  · exact induction secondTail firstTailSorted secondTailSorted
                      (fun entry membership =>
                        firstNonempty entry (.tail firstHead membership))
                      (fun entry membership =>
                        secondNonempty entry (.tail secondHead membership))
                      tailEquivalent

/-- Normalized constraint-equivalent signatures align entry-for-entry; each
aligned label has the same sort and a sort-indexed interval permutation. -/
theorem ConstraintEquivalent.entries
    {Expr : StaticSort -> Type u} {first second : Signature Expr}
    (equivalent : ConstraintEquivalent first second)
    (firstNormalized : first.Normalized)
    (secondNormalized : second.Normalized) :
    EntriesConstraintEquivalent first.entries second.entries :=
  entries_equivalent_of_normalized first.entries second.entries
    firstNormalized.sorted secondNormalized.sorted
    firstNormalized.nonempty secondNormalized.nonempty equivalent

end Signature

end DOTCapture.Intersections

namespace DOTCaptureToManySortedFC.Intersections.ConstraintPermutationCoherence

open DOTCaptureToManySortedFC.Intersections
open DOTCaptureToManySortedFC.Intersections.Encoding
open DOTCaptureToManySortedFC.Intersections.Preparation

private theorem except_cons_success {error head item : Type}
    {first : Except error head} {rest : Except error (List item)}
    {make : head -> item} {result : List item}
    (success : (do
      pure (make (← first) :: (← rest))) = .ok result) :
    ∃ headValue tail, first = .ok headValue ∧ rest = .ok tail ∧
      result = make headValue :: tail := by
  cases first <;> cases rest <;>
    simp_all [bind, Except.bind, pure, Except.pure]

namespace SourceEntries

open DOTCapture.Intersections

private theorem symbols_eq {sourceScope : Preparation.Source.Scope}
    {first second : List
      (Preparation.Source.Entry (Preparation.Source.Expr sourceScope))}
    (equivalent :
      Signature.EntriesConstraintEquivalent first second) :
    Preparation.Allocation.symbols first =
      Preparation.Allocation.symbols second := by
  induction equivalent with
  | nil => rfl
  | @cons firstHead secondHead firstTail secondTail head tail induction =>
      cases head <;>
        simp only [Preparation.Allocation.symbols, induction]

private def castMembers (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (members : List
      (MemberName (Preparation.Target.SymbolScope targetScope firstSymbols))) :
    List (MemberName
      (Preparation.Target.SymbolScope targetScope secondSymbols)) :=
  equality ▸ members

private def weakenMembers (targetScope : Preparation.Target.Sig)
    (sort : ManySortedFC.StaticSort)
    {symbols : List ManySortedFC.StaticSort}
    (members : List
      (MemberName (Preparation.Target.SymbolScope targetScope symbols))) :
    List (MemberName
      (Preparation.Target.SymbolScope targetScope (sort :: symbols))) :=
  members.map fun member => member.rename ManySortedFC.Rename.succ

private theorem castMembers_type_cons
    (targetScope : Preparation.Target.Sig) (label : Nat)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (members : List
      (MemberName (Preparation.Target.SymbolScope targetScope firstSymbols))) :
    castMembers targetScope
        (congrArg (List.cons ManySortedFC.StaticSort.type) equality)
        (MemberName.type label .here ::
          weakenMembers targetScope .type members) =
      MemberName.type label .here ::
        weakenMembers targetScope .type
          (castMembers targetScope equality members) := by
  cases equality
  rfl

private theorem castMembers_capture_cons
    (targetScope : Preparation.Target.Sig) (label : Nat)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (members : List
      (MemberName (Preparation.Target.SymbolScope targetScope firstSymbols))) :
    castMembers targetScope
        (congrArg (List.cons ManySortedFC.StaticSort.capture) equality)
        (MemberName.capture label .here ::
          weakenMembers targetScope .capture members) =
      MemberName.capture label .here ::
        weakenMembers targetScope .capture
          (castMembers targetScope equality members) := by
  cases equality
  rfl

private theorem castMembers_classifier_cons
    (targetScope : Preparation.Target.Sig) (label : Nat)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (members : List
      (MemberName (Preparation.Target.SymbolScope targetScope firstSymbols))) :
    castMembers targetScope
        (congrArg (List.cons ManySortedFC.StaticSort.classifier) equality)
        (MemberName.classifier label .here ::
          weakenMembers targetScope .classifier members) =
      MemberName.classifier label .here ::
        weakenMembers targetScope .classifier
          (castMembers targetScope equality members) := by
  cases equality
  rfl

private theorem members_eq {sourceScope : Preparation.Source.Scope}
    (targetScope : Preparation.Target.Sig)
    {first second : List
      (Preparation.Source.Entry (Preparation.Source.Expr sourceScope))}
    (equivalent :
      Signature.EntriesConstraintEquivalent first second) :
    castMembers targetScope (symbols_eq equivalent)
        (Preparation.Allocation.members targetScope first) =
      Preparation.Allocation.members targetScope second := by
  induction equivalent with
  | nil => rfl
  | @cons firstHead secondHead firstTail secondTail head tail induction =>
      cases head with
      | type label intervals =>
          change castMembers targetScope
              (congrArg (List.cons ManySortedFC.StaticSort.type)
                (SourceEntries.symbols_eq tail))
              (MemberName.type label .here ::
                weakenMembers targetScope .type
                  (Preparation.Allocation.members targetScope firstTail)) =
            MemberName.type label .here ::
              weakenMembers targetScope .type
                (Preparation.Allocation.members targetScope secondTail)
          rw [castMembers_type_cons, induction]
          exact SourceEntries.symbols_eq tail
      | capture label intervals =>
          change castMembers targetScope
              (congrArg (List.cons ManySortedFC.StaticSort.capture)
                (SourceEntries.symbols_eq tail))
              (MemberName.capture label .here ::
                weakenMembers targetScope .capture
                  (Preparation.Allocation.members targetScope firstTail)) =
            MemberName.capture label .here ::
              weakenMembers targetScope .capture
                (Preparation.Allocation.members targetScope secondTail)
          rw [castMembers_capture_cons, induction]
          exact SourceEntries.symbols_eq tail
      | classifier label intervals =>
          change castMembers targetScope
              (congrArg (List.cons ManySortedFC.StaticSort.classifier)
                (SourceEntries.symbols_eq tail))
              (MemberName.classifier label .here ::
                weakenMembers targetScope .classifier
                  (Preparation.Allocation.members targetScope firstTail)) =
            MemberName.classifier label .here ::
              weakenMembers targetScope .classifier
                (Preparation.Allocation.members targetScope secondTail)
          rw [castMembers_classifier_cons, induction]
          exact SourceEntries.symbols_eq tail

private theorem castMembers_symm (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (members : List
      (MemberName (Preparation.Target.SymbolScope targetScope firstSymbols))) :
    castMembers targetScope equality.symm
        (castMembers targetScope equality members) = members := by
  cases equality
  rfl

end SourceEntries

namespace SymbolCast

private def layout {sourceScope : Preparation.Source.Scope}
    (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (value : Preparation.OuterLayout sourceScope
      (ManySortedFC.SymbolScope targetScope firstSymbols)) :
    Preparation.OuterLayout sourceScope
      (ManySortedFC.SymbolScope targetScope secondSymbols) :=
  equality ▸ value

private def preparedEntries (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope targetScope firstSymbols))) :
    List (PreparedEntry
      (ManySortedFC.SymbolScope targetScope secondSymbols)) :=
  equality ▸ entries

private def preparedConstraints (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (constraints : List (PreparedConstraint
      (ManySortedFC.SymbolScope targetScope firstSymbols))) :
    List (PreparedConstraint
      (ManySortedFC.SymbolScope targetScope secondSymbols)) :=
  equality ▸ constraints

private def preparedResult (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (result : Except Preparation.Error (List (PreparedEntry
      (ManySortedFC.SymbolScope targetScope firstSymbols)))) :
    Except Preparation.Error (List (PreparedEntry
      (ManySortedFC.SymbolScope targetScope secondSymbols))) :=
  equality ▸ result

private def preparedConstraintsResult (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (result : Except Preparation.Error (List (PreparedConstraint
      (ManySortedFC.SymbolScope targetScope firstSymbols)))) :
    Except Preparation.Error (List (PreparedConstraint
      (ManySortedFC.SymbolScope targetScope secondSymbols))) :=
  equality ▸ result

private def packedPropositions (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (propositions : List (Encoding.Target.PackedProposition
      (ManySortedFC.SymbolScope targetScope firstSymbols))) :
    List (Encoding.Target.PackedProposition
      (ManySortedFC.SymbolScope targetScope secondSymbols)) :=
  equality ▸ propositions

private theorem layout_weaken {sourceScope : Preparation.Source.Scope}
    (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (outer : Preparation.OuterLayout sourceScope targetScope) :
    layout targetScope equality
        (Preparation.Compile.weakenLayout outer firstSymbols) =
      Preparation.Compile.weakenLayout outer secondSymbols := by
  cases equality
  rfl

private theorem preparedResult_ok (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope targetScope firstSymbols))) :
    preparedResult targetScope equality (.ok entries) =
      .ok (preparedEntries targetScope equality entries) := by
  cases equality
  rfl

private theorem preparedConstraintsResult_ok
    (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (constraints : List (PreparedConstraint
      (ManySortedFC.SymbolScope targetScope firstSymbols))) :
    preparedConstraintsResult targetScope equality (.ok constraints) =
      .ok (preparedConstraints targetScope equality constraints) := by
  cases equality
  rfl

private theorem entries_result {sourceScope : Preparation.Source.Scope}
    (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (sourceLayout : Preparation.OuterLayout sourceScope
      (ManySortedFC.SymbolScope targetScope firstSymbols))
    (allMembers allocated : List (MemberName
      (ManySortedFC.SymbolScope targetScope firstSymbols)))
    (sourceEntries : List
      (Preparation.Source.Entry (Preparation.Source.Expr sourceScope))) :
    preparedResult targetScope equality
        (Preparation.Compile.entries sourceLayout allMembers sourceEntries
          allocated) =
      Preparation.Compile.entries
        (layout targetScope equality sourceLayout)
        (SourceEntries.castMembers targetScope equality allMembers)
        sourceEntries
        (SourceEntries.castMembers targetScope equality allocated) := by
  cases equality
  rfl

private theorem constraints_result {sourceScope : Preparation.Source.Scope}
    (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (sourceLayout : Preparation.OuterLayout sourceScope
      (ManySortedFC.SymbolScope targetScope firstSymbols))
    (members : List (MemberName
      (ManySortedFC.SymbolScope targetScope firstSymbols)))
    (sourceConstraints : List
      (DOTCapture.Intersections.Constraint
        (Preparation.Source.Expr sourceScope))) :
    preparedConstraintsResult targetScope equality
        (Preparation.Compile.translateConstraints sourceLayout members
          sourceConstraints) =
      Preparation.Compile.translateConstraints
        (layout targetScope equality sourceLayout)
        (SourceEntries.castMembers targetScope equality members)
        sourceConstraints := by
  cases equality
  rfl

private theorem preparedEntries_eq_of_heq
    (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    {firstEntries : List (PreparedEntry
      (ManySortedFC.SymbolScope targetScope firstSymbols))}
    {secondEntries : List (PreparedEntry
      (ManySortedFC.SymbolScope targetScope secondSymbols))}
    (same : HEq firstEntries secondEntries) :
    preparedEntries targetScope equality firstEntries = secondEntries := by
  cases equality
  exact eq_of_heq same

private theorem preparedConstraints_eq_of_heq
    (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    {firstConstraints : List (PreparedConstraint
      (ManySortedFC.SymbolScope targetScope firstSymbols))}
    {secondConstraints : List (PreparedConstraint
      (ManySortedFC.SymbolScope targetScope secondSymbols))}
    (same : HEq firstConstraints secondConstraints) :
    preparedConstraints targetScope equality firstConstraints =
      secondConstraints := by
  cases equality
  exact eq_of_heq same

private theorem preparedConstraints_packed
    (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (constraints : List (PreparedConstraint
      (ManySortedFC.SymbolScope targetScope firstSymbols))) :
    (preparedConstraints targetScope equality constraints).map
        PreparedConstraint.packed =
      packedPropositions targetScope equality
        (constraints.map PreparedConstraint.packed) := by
  cases equality
  rfl

private theorem preparedEntries_propositions
    (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope targetScope firstSymbols))) :
    (preparedEntries targetScope equality entries).flatMap
        PreparedEntry.propositions =
      packedPropositions targetScope equality
        (entries.flatMap PreparedEntry.propositions) := by
  cases equality
  rfl

private theorem packedPropositions_perm
    (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    {first second : List (Encoding.Target.PackedProposition
      (ManySortedFC.SymbolScope targetScope firstSymbols))}
    (permutation : first.Perm second) :
    (packedPropositions targetScope equality first).Perm
      (packedPropositions targetScope equality second) := by
  cases equality
  exact permutation

private theorem packedPropositions_trans
    (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols thirdSymbols : List ManySortedFC.StaticSort}
    (firstEquality : firstSymbols = secondSymbols)
    (secondEquality : secondSymbols = thirdSymbols)
    (propositions : List (Encoding.Target.PackedProposition
      (ManySortedFC.SymbolScope targetScope firstSymbols))) :
    packedPropositions targetScope secondEquality
        (packedPropositions targetScope firstEquality propositions) =
      packedPropositions targetScope (firstEquality.trans secondEquality)
        propositions := by
  cases firstEquality
  cases secondEquality
  rfl

private theorem packedPropositions_append
    (targetScope : Preparation.Target.Sig)
    {firstSymbols secondSymbols : List ManySortedFC.StaticSort}
    (equality : firstSymbols = secondSymbols)
    (first second : List (Encoding.Target.PackedProposition
      (ManySortedFC.SymbolScope targetScope firstSymbols))) :
    packedPropositions targetScope equality (first ++ second) =
      packedPropositions targetScope equality first ++
        packedPropositions targetScope equality second := by
  cases equality
  rfl

end SymbolCast

namespace PartialTranslation

open DOTCapture.Intersections

private theorem translateIntervals_success_of_perm
    {sort : Preparation.Source.StaticSort}
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Preparation.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope))
    {first second : List
      (Preparation.Source.Interval (Preparation.Source.Expr sourceScope sort))}
    (permutation : first.Perm second)
    {firstTranslated : List
      (Preparation.Source.Interval
        (ManySortedFC.StaticExpr (Encoding.targetSort sort) targetScope))}
    (firstSuccess :
      Preparation.Compile.translateIntervals layout members first =
        .ok firstTranslated) :
    ∃ secondTranslated,
      Preparation.Compile.translateIntervals layout members second =
          .ok secondTranslated ∧
        firstTranslated.Perm secondTranslated := by
  induction permutation generalizing firstTranslated with
  | nil =>
      simp [Preparation.Compile.translateIntervals] at firstSuccess
      subst firstTranslated
      exact ⟨[], rfl, .nil⟩
  | @cons current firstTail secondTail tailPermutation induction =>
      obtain ⟨translated, translatedTail, currentSuccess, tailSuccess,
          firstTranslatedEq⟩ := except_cons_success firstSuccess
      subst firstTranslated
      obtain ⟨secondTranslated, secondSuccess, translatedPermutation⟩ :=
        induction tailSuccess
      exact ⟨translated :: secondTranslated, by
        simp [Preparation.Compile.translateIntervals, currentSuccess,
          secondSuccess, bind, Except.bind, pure, Except.pure],
        translatedPermutation.cons translated⟩
  | @swap firstHead secondHead tail =>
      obtain ⟨secondTranslatedHead, firstTranslatedTail, secondHeadSuccess,
          firstTailSuccess, firstTranslatedEq⟩ :=
        except_cons_success firstSuccess
      obtain ⟨firstTranslatedHead, translatedTail, firstHeadSuccess,
          tailSuccess, firstTranslatedTailEq⟩ :=
        except_cons_success firstTailSuccess
      subst firstTranslated
      subst firstTranslatedTail
      exact ⟨firstTranslatedHead :: secondTranslatedHead :: translatedTail, by
        simp [Preparation.Compile.translateIntervals, firstHeadSuccess,
          secondHeadSuccess, tailSuccess, bind, Except.bind, pure,
          Except.pure], .swap _ _ _⟩
  | @trans first middle second firstPermutation secondPermutation
      firstInduction secondInduction =>
      obtain ⟨middleTranslated, middleSuccess, firstToMiddle⟩ :=
        firstInduction firstSuccess
      obtain ⟨secondTranslated, secondSuccess, middleToSecond⟩ :=
        secondInduction middleSuccess
      exact ⟨secondTranslated, secondSuccess,
        firstToMiddle.trans middleToSecond⟩

theorem translateIntervals_perm
    {sort : Preparation.Source.StaticSort}
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Preparation.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope))
    {first second : List
      (Preparation.Source.Interval (Preparation.Source.Expr sourceScope sort))}
    (permutation : first.Perm second)
    {firstTranslated secondTranslated : List
      (Preparation.Source.Interval
        (ManySortedFC.StaticExpr (Encoding.targetSort sort) targetScope))}
    (firstSuccess :
      Preparation.Compile.translateIntervals layout members first =
        .ok firstTranslated)
    (secondSuccess :
      Preparation.Compile.translateIntervals layout members second =
        .ok secondTranslated) :
    firstTranslated.Perm secondTranslated := by
  obtain ⟨found, foundSuccess, foundPermutation⟩ :=
    translateIntervals_success_of_perm layout members permutation firstSuccess
  rw [secondSuccess] at foundSuccess
  injection foundSuccess with foundEq
  subst found
  exact foundPermutation

private theorem translateConstraints_success_of_perm
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Preparation.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope))
    {first second : List
      (DOTCapture.Intersections.Constraint
        (Preparation.Source.Expr sourceScope))}
    (permutation : first.Perm second)
    {firstTranslated : List (PreparedConstraint targetScope)}
    (firstSuccess :
      Preparation.Compile.translateConstraints layout members first =
        .ok firstTranslated) :
    ∃ secondTranslated,
      Preparation.Compile.translateConstraints layout members second =
          .ok secondTranslated ∧
        firstTranslated.Perm secondTranslated := by
  induction permutation generalizing firstTranslated with
  | nil =>
      simp [Preparation.Compile.translateConstraints] at firstSuccess
      subst firstTranslated
      exact ⟨[], rfl, .nil⟩
  | @cons current firstTail secondTail tailPermutation induction =>
      obtain ⟨translated, translatedTail, currentSuccess, tailSuccess,
          firstTranslatedEq⟩ := except_cons_success firstSuccess
      subst firstTranslated
      obtain ⟨secondTranslated, secondSuccess, translatedPermutation⟩ :=
        induction tailSuccess
      exact ⟨translated :: secondTranslated, by
        simp [Preparation.Compile.translateConstraints, currentSuccess,
          secondSuccess, bind, Except.bind, pure, Except.pure],
        translatedPermutation.cons translated⟩
  | @swap firstHead secondHead tail =>
      obtain ⟨secondTranslatedHead, firstTranslatedTail, secondHeadSuccess,
          firstTailSuccess, firstTranslatedEq⟩ :=
        except_cons_success firstSuccess
      obtain ⟨firstTranslatedHead, translatedTail, firstHeadSuccess,
          tailSuccess, firstTranslatedTailEq⟩ :=
        except_cons_success firstTailSuccess
      subst firstTranslated
      subst firstTranslatedTail
      exact ⟨firstTranslatedHead :: secondTranslatedHead :: translatedTail, by
        simp [Preparation.Compile.translateConstraints, firstHeadSuccess,
          secondHeadSuccess, tailSuccess, bind, Except.bind, pure,
          Except.pure], .swap _ _ _⟩
  | @trans first middle second firstPermutation secondPermutation
      firstInduction secondInduction =>
      obtain ⟨middleTranslated, middleSuccess, firstToMiddle⟩ :=
        firstInduction firstSuccess
      obtain ⟨secondTranslated, secondSuccess, middleToSecond⟩ :=
        secondInduction middleSuccess
      exact ⟨secondTranslated, secondSuccess,
        firstToMiddle.trans middleToSecond⟩

theorem translateConstraints_perm
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Preparation.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (members : List (MemberName targetScope))
    {first second : List
      (DOTCapture.Intersections.Constraint
        (Preparation.Source.Expr sourceScope))}
    (permutation : first.Perm second)
    {firstTranslated secondTranslated : List (PreparedConstraint targetScope)}
    (firstSuccess :
      Preparation.Compile.translateConstraints layout members first =
        .ok firstTranslated)
    (secondSuccess :
      Preparation.Compile.translateConstraints layout members second =
        .ok secondTranslated) :
    firstTranslated.Perm secondTranslated := by
  obtain ⟨found, foundSuccess, foundPermutation⟩ :=
    translateConstraints_success_of_perm layout members permutation firstSuccess
  rw [secondSuccess] at foundSuccess
  injection foundSuccess with foundEq
  subst found
  exact foundPermutation

end PartialTranslation

namespace PreparedEntries

private theorem type_propositions_perm {scope : Preparation.Target.Sig}
    (label : Nat)
    (name : ManySortedFC.BVar scope (.symbol .type))
    {first second : List
      (Preparation.Source.Interval (ManySortedFC.StaticExpr .type scope))}
    (permutation : first.Perm second) :
    (PreparedEntry.type label name first).propositions.Perm
      (PreparedEntry.type label name second).propositions := by
  simpa [PreparedEntry.propositions] using
    (permutation.map fun interval =>
      [Encoding.Target.PackedProposition.pack
          (.inclusion interval.lower (.type (.tvar name))),
       Encoding.Target.PackedProposition.pack
          (.inclusion (.type (.tvar name)) interval.upper)]).flatten

private theorem capture_propositions_perm {scope : Preparation.Target.Sig}
    (label : Nat)
    (name : ManySortedFC.BVar scope (.symbol .capture))
    {first second : List
      (Preparation.Source.Interval (ManySortedFC.StaticExpr .capture scope))}
    (permutation : first.Perm second) :
    (PreparedEntry.capture label name first).propositions.Perm
      (PreparedEntry.capture label name second).propositions := by
  simpa [PreparedEntry.propositions] using
    (permutation.map fun interval =>
      [Encoding.Target.PackedProposition.pack
          (.inclusion interval.lower (.capture (.cvar name))),
       Encoding.Target.PackedProposition.pack
          (.inclusion (.capture (.cvar name)) interval.upper)]).flatten

private theorem classifier_propositions_perm {scope : Preparation.Target.Sig}
    (label : Nat)
    (name : ManySortedFC.BVar scope (.symbol .classifier))
    {first second : List
      (Preparation.Source.Interval
        (ManySortedFC.StaticExpr .classifier scope))}
    (permutation : first.Perm second) :
    (PreparedEntry.classifier label name first).propositions.Perm
      (PreparedEntry.classifier label name second).propositions := by
  simpa [PreparedEntry.propositions] using
    (permutation.map fun interval =>
      [Encoding.Target.PackedProposition.pack
          (.inclusion interval.lower (.classifier (.var name))),
       Encoding.Target.PackedProposition.pack
          (.inclusion (.classifier (.var name)) interval.upper)]).flatten

theorem propositions_perm {sourceScope : Preparation.Source.Scope}
    {targetScope : Preparation.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (allMembers : List (MemberName targetScope))
    {firstSource secondSource : List
      (Preparation.Source.Entry (Preparation.Source.Expr sourceScope))}
    (sourceEquivalent :
      DOTCapture.Intersections.Signature.EntriesConstraintEquivalent
        firstSource secondSource)
    (allocated : List (MemberName targetScope))
    {firstPrepared secondPrepared : List (PreparedEntry targetScope)}
    (firstSuccess :
      Preparation.Compile.entries layout allMembers firstSource allocated =
        .ok firstPrepared)
    (secondSuccess :
      Preparation.Compile.entries layout allMembers secondSource allocated =
        .ok secondPrepared) :
    (firstPrepared.flatMap PreparedEntry.propositions).Perm
      (secondPrepared.flatMap PreparedEntry.propositions) := by
  induction sourceEquivalent generalizing allocated firstPrepared secondPrepared with
  | nil =>
      cases allocated with
      | nil =>
          simp [Preparation.Compile.entries] at firstSuccess secondSuccess
          subst firstPrepared
          subst secondPrepared
          exact .nil
      | cons allocatedHead allocatedTail =>
          simp [Preparation.Compile.entries] at firstSuccess
  | cons head tail induction =>
      cases head with
      | @type label firstIntervals secondIntervals intervalPermutation =>
          cases allocated with
          | nil => simp [Preparation.Compile.entries] at firstSuccess
          | cons allocatedHead allocatedTail =>
              cases allocatedHead with
              | capture allocatedLabel name =>
                  simp [Preparation.Compile.entries] at firstSuccess
              | classifier allocatedLabel name =>
                  simp [Preparation.Compile.entries] at firstSuccess
              | type allocatedLabel name =>
                  by_cases labelsMatch : label = allocatedLabel
                  · subst allocatedLabel
                    simp [Preparation.Compile.entries]
                      at firstSuccess secondSuccess
                    obtain ⟨firstTranslated, firstPreparedTail,
                        firstIntervalSuccess, firstTailSuccess,
                        firstPreparedEq⟩ := except_cons_success firstSuccess
                    obtain ⟨secondTranslated, secondPreparedTail,
                        secondIntervalSuccess, secondTailSuccess,
                        secondPreparedEq⟩ := except_cons_success secondSuccess
                    subst firstPrepared
                    subst secondPrepared
                    apply List.Perm.append
                    · exact type_propositions_perm label name
                        (PartialTranslation.translateIntervals_perm
                          layout allMembers intervalPermutation
                          firstIntervalSuccess secondIntervalSuccess)
                    · exact induction allocatedTail firstTailSuccess
                        secondTailSuccess
                  · simp [Preparation.Compile.entries, labelsMatch] at firstSuccess
      | @capture label firstIntervals secondIntervals intervalPermutation =>
          cases allocated with
          | nil => simp [Preparation.Compile.entries] at firstSuccess
          | cons allocatedHead allocatedTail =>
              cases allocatedHead with
              | type allocatedLabel name =>
                  simp [Preparation.Compile.entries] at firstSuccess
              | classifier allocatedLabel name =>
                  simp [Preparation.Compile.entries] at firstSuccess
              | capture allocatedLabel name =>
                  by_cases labelsMatch : label = allocatedLabel
                  · subst allocatedLabel
                    simp [Preparation.Compile.entries]
                      at firstSuccess secondSuccess
                    obtain ⟨firstTranslated, firstPreparedTail,
                        firstIntervalSuccess, firstTailSuccess,
                        firstPreparedEq⟩ := except_cons_success firstSuccess
                    obtain ⟨secondTranslated, secondPreparedTail,
                        secondIntervalSuccess, secondTailSuccess,
                        secondPreparedEq⟩ := except_cons_success secondSuccess
                    subst firstPrepared
                    subst secondPrepared
                    apply List.Perm.append
                    · exact capture_propositions_perm label name
                        (PartialTranslation.translateIntervals_perm
                          layout allMembers intervalPermutation
                          firstIntervalSuccess secondIntervalSuccess)
                    · exact induction allocatedTail firstTailSuccess
                        secondTailSuccess
                  · simp [Preparation.Compile.entries, labelsMatch] at firstSuccess
      | @classifier label firstIntervals secondIntervals intervalPermutation =>
          cases allocated with
          | nil => simp [Preparation.Compile.entries] at firstSuccess
          | cons allocatedHead allocatedTail =>
              cases allocatedHead with
              | type allocatedLabel name =>
                  simp [Preparation.Compile.entries] at firstSuccess
              | capture allocatedLabel name =>
                  simp [Preparation.Compile.entries] at firstSuccess
              | classifier allocatedLabel name =>
                  by_cases labelsMatch : label = allocatedLabel
                  · subst allocatedLabel
                    simp [Preparation.Compile.entries]
                      at firstSuccess secondSuccess
                    obtain ⟨firstTranslated, firstPreparedTail,
                        firstIntervalSuccess, firstTailSuccess,
                        firstPreparedEq⟩ := except_cons_success firstSuccess
                    obtain ⟨secondTranslated, secondPreparedTail,
                        secondIntervalSuccess, secondTailSuccess,
                        secondPreparedEq⟩ := except_cons_success secondSuccess
                    subst firstPrepared
                    subst secondPrepared
                    apply List.Perm.append
                    · exact classifier_propositions_perm label name
                        (PartialTranslation.translateIntervals_perm
                          layout allMembers intervalPermutation
                          firstIntervalSuccess secondIntervalSuccess)
                    · exact induction allocatedTail firstTailSuccess
                        secondTailSuccess
                  · simp [Preparation.Compile.entries, labelsMatch] at firstSuccess

end PreparedEntries

/-- Two prepared signatures whose generated target theories differ only by
the order of their packed propositions.  The constructor makes the shared
symbol telescope explicit, avoiding an unsafe heterogeneous permutation. -/
inductive PreparedTheoryPermutation {scope : Preparation.Target.Sig} :
    PreparedSignature scope -> PreparedSignature scope -> Prop where
  | intro {symbols : List ManySortedFC.StaticSort}
      {firstEntries secondEntries : List
        (PreparedEntry (ManySortedFC.SymbolScope scope symbols))}
      {firstConstraints secondConstraints : List
        (PreparedConstraint (ManySortedFC.SymbolScope scope symbols))}
      (permutation :
        (Encoding.Target.Theory.propositions
            (Encoding.encode
              ({ symbols := symbols, entries := firstEntries,
                 constraints := firstConstraints } :
                PreparedSignature scope)).theory).Perm
          (Encoding.Target.Theory.propositions
            (Encoding.encode
              ({ symbols := symbols, entries := secondEntries,
                 constraints := secondConstraints } :
                PreparedSignature scope)).theory)) :
      PreparedTheoryPermutation
        { symbols := symbols, entries := firstEntries,
          constraints := firstConstraints }
        { symbols := symbols, entries := secondEntries,
          constraints := secondConstraints }

/-- Concrete theory maps in both directions between two prepared encodings,
together with acceptance by the independent target checker.  As with
`PreparedTheoryPermutation`, the constructor exposes the common symbol
telescope required by intrinsically indexed target theories. -/
inductive PreparedBidirectionalCheckedMaps
    {scope : Preparation.Target.Sig} (context : ManySortedFC.Ctx scope) :
    PreparedSignature scope -> PreparedSignature scope -> Prop where
  | intro {symbols : List ManySortedFC.StaticSort}
      {firstEntries secondEntries : List
        (PreparedEntry (ManySortedFC.SymbolScope scope symbols))}
      {firstConstraints secondConstraints : List
        (PreparedConstraint (ManySortedFC.SymbolScope scope symbols))}
      (forward : ManySortedFC.TheoryMap
        (Encoding.encode
          ({ symbols := symbols, entries := firstEntries,
             constraints := firstConstraints } :
            PreparedSignature scope)).theory
        (Encoding.encode
          ({ symbols := symbols, entries := secondEntries,
             constraints := secondConstraints } :
            PreparedSignature scope)).theory)
      (backward : ManySortedFC.TheoryMap
        (Encoding.encode
          ({ symbols := symbols, entries := secondEntries,
             constraints := secondConstraints } :
            PreparedSignature scope)).theory
        (Encoding.encode
          ({ symbols := symbols, entries := firstEntries,
             constraints := firstConstraints } :
            PreparedSignature scope)).theory)
      (forwardReusesOpenedSymbols :
        forward.symbols = ManySortedFC.TheoryMap.openedSymbols
          scope symbols
          ({ symbols := symbols, entries := firstEntries,
             constraints := firstConstraints } :
            PreparedSignature scope).relations)
      (backwardReusesOpenedSymbols :
        backward.symbols = ManySortedFC.TheoryMap.openedSymbols
          scope symbols
          ({ symbols := symbols, entries := secondEntries,
             constraints := secondConstraints } :
            PreparedSignature scope).relations)
      (forwardAccepted :
        (ManySortedFC.TheoryMap.check context forward).isSome = true)
      (backwardAccepted :
        (ManySortedFC.TheoryMap.check context backward).isSome = true) :
      PreparedBidirectionalCheckedMaps context
        { symbols := symbols, entries := firstEntries,
          constraints := firstConstraints }
        { symbols := symbols, entries := secondEntries,
          constraints := secondConstraints }

/-- Consume a prepared-theory permutation with the generic target-side map
construction.  Both maps reuse the opened symbol block and reuse matching
source evidence coordinates. -/
theorem PreparedTheoryPermutation.checked_maps
    {scope : Preparation.Target.Sig} (context : ManySortedFC.Ctx scope)
    {first second : PreparedSignature scope}
    (permutation : PreparedTheoryPermutation first second) :
    PreparedBidirectionalCheckedMaps context first second := by
  cases permutation with
  | @intro symbols firstEntries secondEntries firstConstraints
      secondConstraints propositionPermutation =>
      let firstTheory := (Encoding.encode
        ({ symbols := symbols, entries := firstEntries,
           constraints := firstConstraints } :
          PreparedSignature scope)).theory
      let secondTheory := (Encoding.encode
        ({ symbols := symbols, entries := secondEntries,
           constraints := secondConstraints } :
          PreparedSignature scope)).theory
      let accepted :=
        TheoryPermutationCoherence.bidirectional_checked_maps_of_permutation
          context firstTheory secondTheory propositionPermutation
      exact .intro
        (TheoryPermutationCoherence.mapOfPermutation
          firstTheory secondTheory propositionPermutation)
        (TheoryPermutationCoherence.mapOfPermutation
          secondTheory firstTheory propositionPermutation.symm)
        (TheoryPermutationCoherence.mapOfPermutation_reuses_opened_symbols
          firstTheory secondTheory propositionPermutation)
        (TheoryPermutationCoherence.mapOfPermutation_reuses_opened_symbols
          secondTheory firstTheory propositionPermutation.symm)
        accepted.1 accepted.2

theorem encoded_theory_permutation_of_constraintEquivalent
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Preparation.Target.Sig}
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (first second : Preparation.Source.Signature
      (Preparation.Source.Expr sourceScope))
    (equivalent :
      DOTCapture.Intersections.Signature.ConstraintEquivalent first second)
    (mixedEquivalent : first.constraints.Perm second.constraints)
    (firstNormalized : first.Normalized)
    (secondNormalized : second.Normalized)
    {firstPrepared secondPrepared : PreparedSignature targetScope}
    (firstSuccess : Preparation.prepare layout first = .ok firstPrepared)
    (secondSuccess : Preparation.prepare layout second = .ok secondPrepared) :
    PreparedTheoryPermutation firstPrepared secondPrepared := by
  let entriesEquivalent := equivalent.entries firstNormalized secondNormalized
  cases firstPrepared with
  | mk firstSymbols firstPreparedEntries firstPreparedConstraints =>
      cases secondPrepared with
      | mk secondSymbols secondPreparedEntries secondPreparedConstraints =>
          have firstSymbolsEq :=
            Preparation.prepare_preserves_allocated_symbols layout first
              firstSuccess
          have secondSymbolsEq :=
            Preparation.prepare_preserves_allocated_symbols layout second
              secondSuccess
          have symbolsEq : firstSymbols = secondSymbols := by
            exact firstSymbolsEq.trans
              ((SourceEntries.symbols_eq entriesEquivalent).trans
                secondSymbolsEq.symm)
          cases symbolsEq
          unfold Preparation.prepare at firstSuccess secondSuccess
          cases firstResult : Preparation.Compile.entries
              (Preparation.Compile.weakenLayout layout
                (Preparation.Allocation.symbols first.entries))
              (Preparation.Allocation.members targetScope first.entries)
              first.entries
              (Preparation.Allocation.members targetScope first.entries) with
          | error failure =>
              simp [firstResult, bind, Except.bind]
                at firstSuccess
          | ok firstGenerated =>
              cases secondResult : Preparation.Compile.entries
                  (Preparation.Compile.weakenLayout layout
                    (Preparation.Allocation.symbols second.entries))
                  (Preparation.Allocation.members targetScope second.entries)
                  second.entries
                  (Preparation.Allocation.members targetScope second.entries) with
              | error failure =>
                  simp [secondResult, bind, Except.bind]
                    at secondSuccess
              | ok secondGenerated =>
                  cases firstConstraintsResult :
                      Preparation.Compile.translateConstraints
                        (Preparation.Compile.weakenLayout layout
                          (Preparation.Allocation.symbols first.entries))
                        (Preparation.Allocation.members targetScope first.entries)
                        first.constraints with
                  | error failure =>
                      simp [firstResult, firstConstraintsResult, bind,
                        Except.bind] at firstSuccess
                  | ok firstGeneratedConstraints =>
                    cases secondConstraintsResult :
                        Preparation.Compile.translateConstraints
                          (Preparation.Compile.weakenLayout layout
                            (Preparation.Allocation.symbols second.entries))
                          (Preparation.Allocation.members targetScope
                            second.entries)
                          second.constraints with
                    | error failure =>
                        simp [secondResult, secondConstraintsResult, bind,
                          Except.bind] at secondSuccess
                    | ok secondGeneratedConstraints =>
                      simp [firstResult, firstConstraintsResult, bind,
                        Except.bind, pure, Except.pure] at firstSuccess
                      simp [secondResult, secondConstraintsResult, bind,
                        Except.bind, pure, Except.pure] at secondSuccess
                      obtain ⟨firstSymbolsResult, firstGeneratedHEq,
                        firstConstraintsHEq⟩ := firstSuccess
                      obtain ⟨secondSymbolsResult, secondGeneratedHEq,
                        secondConstraintsHEq⟩ := secondSuccess
                      have firstAllocationEq :
                          Preparation.Allocation.symbols first.entries =
                            firstSymbols := by
                        rw [Preparation.Allocation.symbols_eq_entry_sorts]
                        exact firstSymbolsResult
                      have secondAllocationEq :
                          Preparation.Allocation.symbols second.entries =
                            firstSymbols := by
                        rw [Preparation.Allocation.symbols_eq_entry_sorts]
                        exact secondSymbolsResult
                      have sourceSymbolsEq :=
                        SourceEntries.symbols_eq entriesEquivalent
                      have membersForward :=
                        SourceEntries.members_eq targetScope entriesEquivalent
                      have membersBackward :
                          SourceEntries.castMembers targetScope
                              sourceSymbolsEq.symm
                              (Preparation.Allocation.members targetScope
                                second.entries) =
                            Preparation.Allocation.members targetScope
                              first.entries := by
                        rw [← membersForward]
                        exact SourceEntries.castMembers_symm targetScope
                          sourceSymbolsEq
                          (Preparation.Allocation.members targetScope
                            first.entries)
                      have castSecondResult :
                          Preparation.Compile.entries
                              (Preparation.Compile.weakenLayout layout
                                (Preparation.Allocation.symbols first.entries))
                              (Preparation.Allocation.members targetScope
                                first.entries)
                              second.entries
                              (Preparation.Allocation.members targetScope
                                first.entries) =
                            .ok (SymbolCast.preparedEntries targetScope
                              sourceSymbolsEq.symm secondGenerated) := by
                        calc
                          _ = Preparation.Compile.entries
                              (SymbolCast.layout targetScope
                                sourceSymbolsEq.symm
                                (Preparation.Compile.weakenLayout layout
                                  (Preparation.Allocation.symbols
                                    second.entries)))
                              (SourceEntries.castMembers targetScope
                                sourceSymbolsEq.symm
                                (Preparation.Allocation.members targetScope
                                  second.entries))
                              second.entries
                              (SourceEntries.castMembers targetScope
                                sourceSymbolsEq.symm
                                (Preparation.Allocation.members targetScope
                                  second.entries)) := by
                                rw [SymbolCast.layout_weaken, membersBackward]
                          _ = SymbolCast.preparedResult targetScope
                              sourceSymbolsEq.symm
                              (Preparation.Compile.entries
                                (Preparation.Compile.weakenLayout layout
                                  (Preparation.Allocation.symbols
                                    second.entries))
                                (Preparation.Allocation.members targetScope
                                  second.entries)
                                second.entries
                                (Preparation.Allocation.members targetScope
                                  second.entries)) := by
                                exact (SymbolCast.entries_result targetScope
                                  sourceSymbolsEq.symm _ _ _ _).symm
                          _ = SymbolCast.preparedResult targetScope
                              sourceSymbolsEq.symm (.ok secondGenerated) := by
                                exact congrArg
                                  (SymbolCast.preparedResult targetScope
                                    sourceSymbolsEq.symm) secondResult
                          _ = .ok (SymbolCast.preparedEntries targetScope
                              sourceSymbolsEq.symm secondGenerated) :=
                                SymbolCast.preparedResult_ok targetScope
                                  sourceSymbolsEq.symm secondGenerated
                      have castSecondConstraintsResult :
                          Preparation.Compile.translateConstraints
                              (Preparation.Compile.weakenLayout layout
                                (Preparation.Allocation.symbols first.entries))
                              (Preparation.Allocation.members targetScope
                                first.entries)
                              second.constraints =
                            .ok (SymbolCast.preparedConstraints targetScope
                              sourceSymbolsEq.symm
                              secondGeneratedConstraints) := by
                        calc
                          _ = Preparation.Compile.translateConstraints
                              (SymbolCast.layout targetScope
                                sourceSymbolsEq.symm
                                (Preparation.Compile.weakenLayout layout
                                  (Preparation.Allocation.symbols
                                    second.entries)))
                              (SourceEntries.castMembers targetScope
                                sourceSymbolsEq.symm
                                (Preparation.Allocation.members targetScope
                                  second.entries))
                              second.constraints := by
                                rw [SymbolCast.layout_weaken, membersBackward]
                          _ = SymbolCast.preparedConstraintsResult targetScope
                              sourceSymbolsEq.symm
                              (Preparation.Compile.translateConstraints
                                (Preparation.Compile.weakenLayout layout
                                  (Preparation.Allocation.symbols
                                    second.entries))
                                (Preparation.Allocation.members targetScope
                                  second.entries)
                                second.constraints) := by
                                exact
                                  (SymbolCast.constraints_result targetScope
                                    sourceSymbolsEq.symm _ _ _).symm
                          _ = SymbolCast.preparedConstraintsResult targetScope
                              sourceSymbolsEq.symm
                              (.ok secondGeneratedConstraints) := by
                                exact congrArg
                                  (SymbolCast.preparedConstraintsResult
                                    targetScope sourceSymbolsEq.symm)
                                  secondConstraintsResult
                          _ = .ok (SymbolCast.preparedConstraints targetScope
                              sourceSymbolsEq.symm
                              secondGeneratedConstraints) :=
                                SymbolCast.preparedConstraintsResult_ok
                                  targetScope sourceSymbolsEq.symm
                                  secondGeneratedConstraints
                      have generatedEntryPermutation :=
                        PreparedEntries.propositions_perm
                          (Preparation.Compile.weakenLayout layout
                            (Preparation.Allocation.symbols first.entries))
                          (Preparation.Allocation.members targetScope
                            first.entries)
                          entriesEquivalent
                          (Preparation.Allocation.members targetScope
                            first.entries)
                          firstResult castSecondResult
                      have generatedConstraintPermutation :=
                        PartialTranslation.translateConstraints_perm
                          (Preparation.Compile.weakenLayout layout
                            (Preparation.Allocation.symbols first.entries))
                          (Preparation.Allocation.members targetScope
                            first.entries)
                          mixedEquivalent firstConstraintsResult
                          castSecondConstraintsResult
                      have generatedPermutation :=
                        generatedEntryPermutation.append
                          (generatedConstraintPermutation.map
                            PreparedConstraint.packed)
                      have firstEntriesEq :=
                        SymbolCast.preparedEntries_eq_of_heq targetScope
                          firstAllocationEq firstGeneratedHEq
                      have secondEntriesEq :=
                        SymbolCast.preparedEntries_eq_of_heq targetScope
                          secondAllocationEq secondGeneratedHEq
                      have firstConstraintsEq :=
                        SymbolCast.preparedConstraints_eq_of_heq targetScope
                          firstAllocationEq firstConstraintsHEq
                      have secondConstraintsEq :=
                        SymbolCast.preparedConstraints_eq_of_heq targetScope
                          secondAllocationEq secondConstraintsHEq
                      have firstPropositionsEq :
                          SymbolCast.packedPropositions targetScope
                              firstAllocationEq
                              (firstGenerated.flatMap
                                  PreparedEntry.propositions ++
                                firstGeneratedConstraints.map
                                  PreparedConstraint.packed) =
                            firstPreparedEntries.flatMap
                                PreparedEntry.propositions ++
                              firstPreparedConstraints.map
                                PreparedConstraint.packed := by
                        rw [SymbolCast.packedPropositions_append,
                          ← SymbolCast.preparedEntries_propositions,
                          ← SymbolCast.preparedConstraints_packed,
                          firstEntriesEq, firstConstraintsEq]
                      have secondPropositionsEq :
                          SymbolCast.packedPropositions targetScope
                              firstAllocationEq
                              ((SymbolCast.preparedEntries targetScope
                                  sourceSymbolsEq.symm
                                  secondGenerated).flatMap
                                    PreparedEntry.propositions ++
                                (SymbolCast.preparedConstraints targetScope
                                  sourceSymbolsEq.symm
                                  secondGeneratedConstraints).map
                                    PreparedConstraint.packed) =
                            secondPreparedEntries.flatMap
                                PreparedEntry.propositions ++
                              secondPreparedConstraints.map
                                PreparedConstraint.packed := by
                        rw [SymbolCast.packedPropositions_append,
                          SymbolCast.preparedEntries_propositions,
                          SymbolCast.preparedConstraints_packed,
                          SymbolCast.packedPropositions_trans,
                          SymbolCast.packedPropositions_trans]
                        have proofEq :
                            sourceSymbolsEq.symm.trans firstAllocationEq =
                              secondAllocationEq := Subsingleton.elim _ _
                        rw [proofEq,
                          ← SymbolCast.preparedEntries_propositions,
                          ← SymbolCast.preparedConstraints_packed,
                          secondEntriesEq, secondConstraintsEq]
                      have outputPermutation :=
                        SymbolCast.packedPropositions_perm targetScope
                          firstAllocationEq generatedPermutation
                      rw [firstPropositionsEq, secondPropositionsEq]
                        at outputPermutation
                      have firstEncodingEq := Encoding.propositions_eq
                        ({ symbols := firstSymbols,
                           entries := firstPreparedEntries,
                           constraints := firstPreparedConstraints } :
                          PreparedSignature targetScope)
                      have secondEncodingEq := Encoding.propositions_eq
                        ({ symbols := firstSymbols,
                           entries := secondPreparedEntries,
                           constraints := secondPreparedConstraints } :
                          PreparedSignature targetScope)
                      have firstEncodingEq' :
                          Encoding.Target.Theory.propositions
                              (Encoding.encode
                                ({ symbols := firstSymbols,
                                   entries := firstPreparedEntries,
                                   constraints := firstPreparedConstraints } :
                                  PreparedSignature targetScope)).theory =
                            firstPreparedEntries.flatMap
                                PreparedEntry.propositions ++
                              firstPreparedConstraints.map
                                PreparedConstraint.packed := by
                        simpa [PreparedSignature.propositions] using
                          firstEncodingEq
                      have secondEncodingEq' :
                          Encoding.Target.Theory.propositions
                              (Encoding.encode
                                ({ symbols := firstSymbols,
                                   entries := secondPreparedEntries,
                                   constraints := secondPreparedConstraints } :
                                  PreparedSignature targetScope)).theory =
                            secondPreparedEntries.flatMap
                                PreparedEntry.propositions ++
                              secondPreparedConstraints.map
                                PreparedConstraint.packed := by
                        simpa [PreparedSignature.propositions] using
                          secondEncodingEq
                      rw [← firstEncodingEq', ← secondEncodingEq']
                        at outputPermutation
                      apply PreparedTheoryPermutation.intro
                      exact outputPermutation

/-- Full source-facing coherence package: normalized member-equivalent
signatures with permutation-equivalent mixed constraints that both prepare
successfully induce checked target theory maps in both directions. -/
theorem bidirectional_checked_maps_of_constraintEquivalent
    {sourceScope : Preparation.Source.Scope}
    {targetScope : Preparation.Target.Sig}
    (context : ManySortedFC.Ctx targetScope)
    (layout : Preparation.OuterLayout sourceScope targetScope)
    (first second : Preparation.Source.Signature
      (Preparation.Source.Expr sourceScope))
    (equivalent :
      DOTCapture.Intersections.Signature.ConstraintEquivalent first second)
    (mixedEquivalent : first.constraints.Perm second.constraints)
    (firstNormalized : first.Normalized)
    (secondNormalized : second.Normalized)
    {firstPrepared secondPrepared : PreparedSignature targetScope}
    (firstSuccess : Preparation.prepare layout first = .ok firstPrepared)
    (secondSuccess : Preparation.prepare layout second = .ok secondPrepared) :
    PreparedBidirectionalCheckedMaps context firstPrepared secondPrepared :=
  (encoded_theory_permutation_of_constraintEquivalent layout first second
    equivalent mixedEquivalent firstNormalized secondNormalized firstSuccess
    secondSuccess
  ).checked_maps context

end DOTCaptureToManySortedFC.Intersections.ConstraintPermutationCoherence
