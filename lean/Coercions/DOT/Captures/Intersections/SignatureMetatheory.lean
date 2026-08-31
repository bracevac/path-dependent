import Coercions.DOT.Captures.Intersections.Signature

/-!
# Metatheory of normalized many-sorted signatures

Successful executable merge preserves the canonical one-entry-per-label
invariant, retains every primitive interval occurrence, and identifies a
shared label only when both inputs give it the same sort.
-/

namespace DOTCapture.Intersections

universe u

namespace Entry

@[simp]
theorem occurrences_nonempty_iff {Expr : StaticSort -> Type u}
    (entry : Entry Expr) :
    entry.occurrences ≠ [] ↔ entry.IsNonempty := by
  cases entry <;> simp [occurrences, IsNonempty]

/-- A nonempty entry contributes an actual constraint occurrence. -/
theorem exists_occurrence {Expr : StaticSort -> Type u}
    {entry : Entry Expr} (nonempty : entry.IsNonempty) :
    ∃ occurrence, occurrence ∈ entry.occurrences := by
  cases entry with
  | type label intervals =>
      cases intervals with
      | nil => exact (nonempty rfl).elim
      | cons interval remaining =>
          exact ⟨.type label interval, by simp [occurrences]⟩
  | capture label intervals =>
      cases intervals with
      | nil => exact (nonempty rfl).elim
      | cons interval remaining =>
          exact ⟨.capture label interval, by simp [occurrences]⟩

end Entry

namespace Signature

/-! ## Normalization and lookup -/

theorem empty_normalized {Expr : StaticSort -> Type u} :
    (empty : Signature Expr).Normalized := by
  constructor
  · exact .nil
  · intro entry membership
    cases membership

theorem singletonType_normalized {Expr : StaticSort -> Type u}
    (label : Nat) (lower upper : Expr .type) :
    (singletonType label lower upper).Normalized := by
  constructor
  · exact .cons (by simp) .nil
  · intro entry membership
    simp only [singletonType, List.mem_cons, List.not_mem_nil,
      or_false] at membership
    subst entry
    simp [Entry.IsNonempty]

theorem singletonCapture_normalized {Expr : StaticSort -> Type u}
    (label : Nat) (lower upper : Expr .capture) :
    (singletonCapture label lower upper).Normalized := by
  constructor
  · exact .cons (by simp) .nil
  · intro entry membership
    simp only [singletonCapture, List.mem_cons, List.not_mem_nil,
      or_false] at membership
    subst entry
    simp [Entry.IsNonempty]

private theorem labels_nodup_of_sorted {Expr : StaticSort -> Type u}
    (entries : List (Entry Expr)) (sorted : entries.Pairwise Before) :
    (entries.map Entry.label).Nodup := by
  induction entries with
  | nil => exact .nil
  | cons entry remaining induction =>
      cases sorted with
      | cons entryBefore remainingSorted =>
          apply List.Pairwise.cons
          · intro foundLabel membership
            obtain ⟨found, foundMembership, labelEquality⟩ :=
              List.mem_map.mp membership
            intro labelsEqual
            exact Nat.ne_of_lt (entryBefore found foundMembership)
              (labelsEqual.trans labelEquality.symm)
          · exact induction remainingSorted

/-- Sorted allocation implies exactly one entry per label. -/
theorem Normalized.labels_nodup {Expr : StaticSort -> Type u}
    {signature : Signature Expr} (normalized : signature.Normalized) :
    signature.labels.Nodup :=
  labels_nodup_of_sorted signature.entries normalized.sorted

theorem lookupEntries_some_mem {Expr : StaticSort -> Type u}
    {entries : List (Entry Expr)} {label : Nat} {entry : Entry Expr}
    (found : lookupEntries entries label = some entry) :
    entry ∈ entries := by
  induction entries with
  | nil => simp [lookupEntries] at found
  | cons current remaining induction =>
      simp only [lookupEntries] at found
      split at found
      next same =>
        simp only [Option.some.injEq] at found
        subst entry
        exact .head _
      next different => exact .tail current (induction found)

theorem lookupEntries_some_label {Expr : StaticSort -> Type u}
    {entries : List (Entry Expr)} {label : Nat} {entry : Entry Expr}
    (found : lookupEntries entries label = some entry) :
    entry.label = label := by
  induction entries with
  | nil => simp [lookupEntries] at found
  | cons current remaining induction =>
      simp only [lookupEntries] at found
      split at found
      next same =>
        simp only [Option.some.injEq] at found
        subst entry
        exact same
      next different => exact induction found

private theorem lookupEntries_eq_some_of_mem
    {Expr : StaticSort -> Type u} {entries : List (Entry Expr)}
    (nodup : (entries.map Entry.label).Nodup)
    {entry : Entry Expr} (membership : entry ∈ entries) :
    lookupEntries entries entry.label = some entry := by
  induction entries with
  | nil => cases membership
  | cons current remaining induction =>
      have mappedNodup :
          (current.label :: remaining.map Entry.label).Nodup := by
        simpa using nodup
      obtain ⟨currentNotInRemaining, remainingNodup⟩ :=
        List.nodup_cons.mp mappedNodup
      simp only [lookupEntries]
      by_cases same : current.label = entry.label
      · rw [if_pos same]
        have entryEq : current = entry := by
          rcases List.mem_cons.mp membership with headEq | tailMem
          · exact headEq.symm
          · exfalso
            apply currentNotInRemaining
            exact List.mem_map.mpr ⟨entry, tailMem, same.symm⟩
        rw [entryEq]
      · rw [if_neg same]
        apply induction remainingNodup
        rcases List.mem_cons.mp membership with headEq | tailMem
        · subst entry
          exact (same rfl).elim
        · exact tailMem

/-- Every normalized entry is returned by lookup at its unique label. -/
theorem lookup_eq_some_of_mem {Expr : StaticSort -> Type u}
    {signature : Signature Expr} (normalized : signature.Normalized)
    {entry : Entry Expr} (membership : entry ∈ signature.entries) :
    signature.lookup entry.label = some entry :=
  lookupEntries_eq_some_of_mem normalized.labels_nodup membership

theorem lookup_some_mem {Expr : StaticSort -> Type u}
    {signature : Signature Expr} {label : Nat} {entry : Entry Expr}
    (found : signature.lookup label = some entry) :
    entry ∈ signature.entries :=
  lookupEntries_some_mem found

theorem lookup_some_label {Expr : StaticSort -> Type u}
    {signature : Signature Expr} {label : Nat} {entry : Entry Expr}
    (found : signature.lookup label = some entry) :
    entry.label = label :=
  lookupEntries_some_label found

/-! ## Successful insertion preserves normalization -/

private theorem combineSameLabel?_label
    {Expr : StaticSort -> Type u} (existing incoming combined : Entry Expr)
    (success : combineSameLabel? existing incoming = .ok combined) :
    combined.label = existing.label := by
  cases existing with
  | type existingLabel existingIntervals =>
      cases incoming with
      | type incomingLabel incomingIntervals =>
          simp only [combineSameLabel?] at success
          injection success with combinedEq
          subst combined
          rfl
      | capture incomingLabel incomingIntervals =>
          simp [combineSameLabel?] at success
  | capture existingLabel existingIntervals =>
      cases incoming with
      | type incomingLabel incomingIntervals =>
          simp [combineSameLabel?] at success
      | capture incomingLabel incomingIntervals =>
          simp only [combineSameLabel?] at success
          injection success with combinedEq
          subst combined
          rfl

private theorem combineSameLabel?_nonempty
    {Expr : StaticSort -> Type u} (existing incoming combined : Entry Expr)
    (existingNonempty : existing.IsNonempty)
    (success : combineSameLabel? existing incoming = .ok combined) :
    combined.IsNonempty := by
  cases existing with
  | type existingLabel existingIntervals =>
      cases incoming with
      | type incomingLabel incomingIntervals =>
          simp only [combineSameLabel?] at success
          injection success with combinedEq
          subst combined
          exact List.append_ne_nil_of_left_ne_nil existingNonempty _
      | capture incomingLabel incomingIntervals =>
          simp [combineSameLabel?] at success
  | capture existingLabel existingIntervals =>
      cases incoming with
      | type incomingLabel incomingIntervals =>
          simp [combineSameLabel?] at success
      | capture incomingLabel incomingIntervals =>
          simp only [combineSameLabel?] at success
          injection success with combinedEq
          subst combined
          exact List.append_ne_nil_of_left_ne_nil existingNonempty _

private theorem label_of_mem_insertEntry?_ok
    {Expr : StaticSort -> Type u} (incoming : Entry Expr)
    (entries result : List (Entry Expr))
    (success : insertEntry? incoming entries = .ok result)
    {found : Entry Expr} (membership : found ∈ result) :
    found.label = incoming.label ∨
      ∃ original ∈ entries, found.label = original.label := by
  induction entries generalizing result with
  | nil =>
      simp [insertEntry?] at success
      subst result
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      subst found
      exact .inl rfl
  | cons current remaining induction =>
      simp only [insertEntry?] at success
      split at success
      next before =>
        simp only [Except.ok.injEq] at success
        subst result
        rcases List.mem_cons.mp membership with foundEq | oldMembership
        · subst found
          exact .inl rfl
        · exact .inr ⟨found, oldMembership, rfl⟩
      next notBefore =>
        split at success
        next same =>
          cases combinedResult : combineSameLabel? current incoming with
          | error conflict => simp [combinedResult] at success
          | ok combined =>
              simp [combinedResult] at success
              subst result
              rcases List.mem_cons.mp membership with foundEq | tailMembership
              · subst found
                exact .inl ((combineSameLabel?_label current incoming combined
                  combinedResult).trans same.symm)
              · exact .inr ⟨found, .tail current tailMembership, rfl⟩
        next different =>
          cases recursive : insertEntry? incoming remaining with
          | error conflict => simp [recursive] at success
          | ok inserted =>
              simp [recursive] at success
              subst result
              rcases List.mem_cons.mp membership with foundEq | insertedMembership
              · subst found
                exact .inr ⟨current, .head _, rfl⟩
              · rcases induction inserted recursive insertedMembership with
                  incomingLabel | oldLabel
                · exact .inl incomingLabel
                · obtain ⟨original, originalMem, labelEq⟩ := oldLabel
                  exact .inr ⟨original, .tail current originalMem, labelEq⟩

private theorem insertEntry?_sorted
    {Expr : StaticSort -> Type u} (incoming : Entry Expr)
    (entries result : List (Entry Expr))
    (sorted : entries.Pairwise Before)
    (success : insertEntry? incoming entries = .ok result) :
    result.Pairwise Before := by
  induction entries generalizing result with
  | nil =>
      simp [insertEntry?] at success
      subst result
      exact .cons (by simp) .nil
  | cons current remaining induction =>
      cases sorted with
      | cons currentBefore remainingSorted =>
          simp only [insertEntry?] at success
          split at success
          next incomingBefore =>
            simp only [Except.ok.injEq] at success
            subst result
            apply List.Pairwise.cons
            · intro found membership
              rcases List.mem_cons.mp membership with foundEq | tailMembership
              · subst found
                exact incomingBefore
              · exact Nat.lt_trans incomingBefore
                  (currentBefore found tailMembership)
            · exact .cons currentBefore remainingSorted
          next notBefore =>
            split at success
            next same =>
              cases combinedResult : combineSameLabel? current incoming with
              | error conflict => simp [combinedResult] at success
              | ok combined =>
                  simp [combinedResult] at success
                  subst result
                  have combinedLabel : combined.label = current.label := by
                    exact combineSameLabel?_label current incoming combined
                      combinedResult
                  apply List.Pairwise.cons
                  · intro found foundMem
                    simpa [Before, combinedLabel] using
                      currentBefore found foundMem
                  · exact remainingSorted
            next different =>
              cases recursive : insertEntry? incoming remaining with
              | error conflict => simp [recursive] at success
              | ok inserted =>
                  simp [recursive] at success
                  subst result
                  have currentBeforeIncoming : current.label < incoming.label :=
                    Nat.lt_of_le_of_ne (Nat.le_of_not_gt notBefore)
                      (Ne.symm different)
                  apply List.Pairwise.cons
                  · intro found foundMem
                    rcases label_of_mem_insertEntry?_ok incoming remaining
                        inserted recursive foundMem with
                      incomingLabel | oldLabel
                    · unfold Before
                      rw [incomingLabel]
                      exact currentBeforeIncoming
                    · obtain ⟨original, originalMem, labelEq⟩ := oldLabel
                      unfold Before
                      rw [labelEq]
                      exact currentBefore original originalMem
                  · exact induction inserted remainingSorted recursive

private theorem insertEntry?_nonempty
    {Expr : StaticSort -> Type u} (incoming : Entry Expr)
    (entries result : List (Entry Expr))
    (incomingNonempty : incoming.IsNonempty)
    (entriesNonempty : ∀ entry ∈ entries, entry.IsNonempty)
    (success : insertEntry? incoming entries = .ok result) :
    ∀ entry ∈ result, entry.IsNonempty := by
  induction entries generalizing result with
  | nil =>
      simp [insertEntry?] at success
      subst result
      intro entry membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      subst entry
      exact incomingNonempty
  | cons current remaining induction =>
      simp only [insertEntry?] at success
      split at success
      next before =>
        simp only [Except.ok.injEq] at success
        subst result
        intro entry membership
        rcases List.mem_cons.mp membership with entryEq | oldMembership
        · subst entry
          exact incomingNonempty
        · exact entriesNonempty entry oldMembership
      next notBefore =>
        split at success
        next same =>
          cases combinedResult : combineSameLabel? current incoming with
          | error conflict => simp [combinedResult] at success
          | ok combined =>
              simp [combinedResult] at success
              subst result
              intro entry membership
              rcases List.mem_cons.mp membership with entryEq | tailMembership
              · subst entry
                exact combineSameLabel?_nonempty current incoming combined
                  (entriesNonempty current (.head _)) combinedResult
              · exact entriesNonempty entry (.tail current tailMembership)
        next different =>
          cases recursive : insertEntry? incoming remaining with
          | error conflict => simp [recursive] at success
          | ok inserted =>
              simp [recursive] at success
              subst result
              intro entry membership
              rcases List.mem_cons.mp membership with entryEq | insertedMembership
              · subst entry
                exact entriesNonempty current (.head _)
              · exact induction inserted
                  (fun found foundMem =>
                    entriesNonempty found (.tail current foundMem))
                  recursive entry insertedMembership

theorem insertEntry?_normalized {Expr : StaticSort -> Type u}
    (incoming : Entry Expr) (signature : Signature Expr)
    (incomingNonempty : incoming.IsNonempty)
    (normalized : signature.Normalized)
    {entries : List (Entry Expr)}
    (success : insertEntry? incoming signature.entries = .ok entries) :
    ({ entries := entries } : Signature Expr).Normalized := by
  exact ⟨insertEntry?_sorted incoming signature.entries entries
      normalized.sorted success,
    insertEntry?_nonempty incoming signature.entries entries incomingNonempty
      normalized.nonempty success⟩

/-! ## Every occurrence is retained -/

private theorem combineSameLabel?_occurrences
    {Expr : StaticSort -> Type u} (existing incoming combined : Entry Expr)
    (same : incoming.label = existing.label)
    (success : combineSameLabel? existing incoming = .ok combined) :
    combined.occurrences = existing.occurrences ++ incoming.occurrences := by
  cases existing with
  | type existingLabel existingIntervals =>
      cases incoming with
      | type incomingLabel incomingIntervals =>
          simp only [Entry.label] at same
          subst incomingLabel
          simp only [combineSameLabel?] at success
          injection success with combinedEq
          subst combined
          simp [Entry.occurrences]
      | capture incomingLabel incomingIntervals =>
          simp [combineSameLabel?] at success
  | capture existingLabel existingIntervals =>
      cases incoming with
      | type incomingLabel incomingIntervals =>
          simp [combineSameLabel?] at success
      | capture incomingLabel incomingIntervals =>
          simp only [Entry.label] at same
          subst incomingLabel
          simp only [combineSameLabel?] at success
          injection success with combinedEq
          subst combined
          simp [Entry.occurrences]

@[simp]
private theorem occurrences_cons {Expr : StaticSort -> Type u}
    (entry : Entry Expr) (entries : List (Entry Expr)) :
    ({ entries := entry :: entries } : Signature Expr).occurrences =
      entry.occurrences ++
        ({ entries := entries } : Signature Expr).occurrences := by
  simp [occurrences]

private theorem insertEntry?_occurrences
    {Expr : StaticSort -> Type u} (incoming : Entry Expr)
    (entries result : List (Entry Expr))
    (success : insertEntry? incoming entries = .ok result) :
    (({ entries := result } : Signature Expr).occurrences).Perm
      (({ entries := entries } : Signature Expr).occurrences ++
        incoming.occurrences) := by
  induction entries generalizing result with
  | nil =>
      simp [insertEntry?] at success
      subst result
      simp [occurrences]
  | cons current remaining induction =>
      simp only [insertEntry?] at success
      split at success
      next before =>
        simp only [Except.ok.injEq] at success
        subst result
        exact (List.perm_append_comm :
          (incoming.occurrences ++
            ({ entries := current :: remaining } : Signature Expr).occurrences).Perm
          ((({ entries := current :: remaining } : Signature Expr).occurrences) ++
            incoming.occurrences))
      next notBefore =>
        split at success
        next same =>
          cases combinedResult : combineSameLabel? current incoming with
          | error conflict => simp [combinedResult] at success
          | ok combined =>
              simp [combinedResult] at success
              subst result
              rw [occurrences_cons, occurrences_cons,
                combineSameLabel?_occurrences current incoming combined same
                  combinedResult]
              simpa only [List.append_assoc] using ((List.perm_append_comm :
                (incoming.occurrences ++
                  ({ entries := remaining } : Signature Expr).occurrences).Perm
                ((({ entries := remaining } : Signature Expr).occurrences) ++
                  incoming.occurrences)).append_left current.occurrences)
        next different =>
          cases recursive : insertEntry? incoming remaining with
          | error conflict => simp [recursive] at success
          | ok inserted =>
              simp [recursive] at success
              subst result
              simpa [List.append_assoc] using
                (induction inserted recursive).append_left current.occurrences

private theorem mergeEntries?_normalized
    {Expr : StaticSort -> Type u}
    (accumulated incoming result : List (Entry Expr))
    (accumulatedNormalized :
      ({ entries := accumulated } : Signature Expr).Normalized)
    (incomingNormalized :
      ({ entries := incoming } : Signature Expr).Normalized)
    (success : mergeEntries? accumulated incoming = .ok result) :
    ({ entries := result } : Signature Expr).Normalized := by
  induction incoming generalizing accumulated result with
  | nil =>
      simp [mergeEntries?] at success
      subst result
      exact accumulatedNormalized
  | cons entry remaining induction =>
      cases incomingNormalized.sorted with
      | cons entryBefore remainingSorted =>
          have entryNonempty := incomingNormalized.nonempty entry (.head _)
          have remainingNormalized :
              ({ entries := remaining } : Signature Expr).Normalized :=
            { sorted := remainingSorted
              nonempty := fun current membership =>
                incomingNormalized.nonempty current (.tail entry membership) }
          simp only [mergeEntries?] at success
          cases insertedResult : insertEntry? entry accumulated with
          | error conflict => simp [insertedResult] at success
          | ok inserted =>
              simp [insertedResult] at success
              have insertedNormalized := insertEntry?_normalized entry
                ({ entries := accumulated } : Signature Expr)
                entryNonempty accumulatedNormalized insertedResult
              exact induction inserted result insertedNormalized
                remainingNormalized success

theorem merge?_normalized {Expr : StaticSort -> Type u}
    (left right result : Signature Expr)
    (leftNormalized : left.Normalized)
    (rightNormalized : right.Normalized)
    (success : merge? left right = .ok result) :
    result.Normalized := by
  unfold merge? at success
  cases merged : mergeEntries? left.entries right.entries with
  | error conflict => simp [merged] at success
  | ok entries =>
      simp [merged] at success
      subst result
      exact mergeEntries?_normalized left.entries right.entries entries
        leftNormalized rightNormalized merged

private theorem mergeEntries?_occurrences
    {Expr : StaticSort -> Type u}
    (accumulated incoming result : List (Entry Expr))
    (success : mergeEntries? accumulated incoming = .ok result) :
    (({ entries := result } : Signature Expr).occurrences).Perm
      (({ entries := accumulated } : Signature Expr).occurrences ++
        ({ entries := incoming } : Signature Expr).occurrences) := by
  induction incoming generalizing accumulated result with
  | nil =>
      simp [mergeEntries?] at success
      subst result
      simp [occurrences]
  | cons entry remaining induction =>
      simp only [mergeEntries?] at success
      cases insertedResult : insertEntry? entry accumulated with
      | error conflict => simp [insertedResult] at success
      | ok inserted =>
          simp [insertedResult] at success
          have remainingPerm := induction inserted result success
          have insertedPerm := insertEntry?_occurrences entry accumulated
            inserted insertedResult
          exact remainingPerm.trans (by
            simpa [List.append_assoc] using
              insertedPerm.append_right
                (({ entries := remaining } : Signature Expr).occurrences))

theorem merge?_occurrences {Expr : StaticSort -> Type u}
    (left right result : Signature Expr)
    (success : merge? left right = .ok result) :
    result.occurrences.Perm (left.occurrences ++ right.occurrences) := by
  unfold merge? at success
  cases merged : mergeEntries? left.entries right.entries with
  | error conflict => simp [merged] at success
  | ok entries =>
      simp [merged] at success
      subst result
      exact mergeEntries?_occurrences left.entries right.entries entries merged

/-- Constraint lookup after merge is conjunction by accumulation. -/
theorem merge?_constraintsAt {Expr : StaticSort -> Type u}
    (left right result : Signature Expr)
    (success : merge? left right = .ok result) (label : Nat) :
    (result.constraintsAt label).Perm
      (left.constraintsAt label ++ right.constraintsAt label) := by
  have retained := (merge?_occurrences left right result success).filter
    (fun occurrence => occurrence.label == label)
  simpa [constraintsAt, List.filter_append] using retained

/-! ## Determinism and algebraic equivalence -/

/-- Two signatures have the same primitive constraint occurrences, allowing
only order to differ.  This is the relevant equality for conjunction. -/
def ConstraintEquivalent {Expr : StaticSort -> Type u}
    (first second : Signature Expr) : Prop :=
  first.occurrences.Perm second.occurrences

theorem ConstraintEquivalent.constraintsAt
    {Expr : StaticSort -> Type u} {first second : Signature Expr}
    (equivalent : ConstraintEquivalent first second) (label : Nat) :
    (first.constraintsAt label).Perm (second.constraintsAt label) := by
  exact equivalent.filter (fun occurrence => occurrence.label == label)

/-- Executable merge has a unique successful result. -/
theorem merge?_deterministic {Expr : StaticSort -> Type u}
    (left right first second : Signature Expr)
    (firstSuccess : merge? left right = .ok first)
    (secondSuccess : merge? left right = .ok second) :
    first = second := by
  rw [firstSuccess] at secondSuccess
  exact Except.ok.inj secondSuccess

/-- Successful merge is commutative up to the order of conjuncts. -/
theorem merge?_comm_equivalent {Expr : StaticSort -> Type u}
    (left right forward reverse : Signature Expr)
    (forwardSuccess : merge? left right = .ok forward)
    (reverseSuccess : merge? right left = .ok reverse) :
    ConstraintEquivalent forward reverse := by
  have forwardOccurrences := merge?_occurrences left right forward
    forwardSuccess
  have reverseOccurrences := merge?_occurrences right left reverse
    reverseSuccess
  exact forwardOccurrences.trans ((List.perm_append_comm :
    (left.occurrences ++ right.occurrences).Perm
      (right.occurrences ++ left.occurrences)).trans
        reverseOccurrences.symm)

/-- Successful merge is associative up to the order-insensitive conjunction
semantics. -/
theorem merge?_assoc_equivalent {Expr : StaticSort -> Type u}
    (left middle right leftMiddle leftAssociated middleRight rightAssociated :
      Signature Expr)
    (leftMiddleSuccess : merge? left middle = .ok leftMiddle)
    (leftAssociatedSuccess : merge? leftMiddle right = .ok leftAssociated)
    (middleRightSuccess : merge? middle right = .ok middleRight)
    (rightAssociatedSuccess : merge? left middleRight = .ok rightAssociated) :
    ConstraintEquivalent leftAssociated rightAssociated := by
  have leftOuter := merge?_occurrences leftMiddle right leftAssociated
    leftAssociatedSuccess
  have leftInner := merge?_occurrences left middle leftMiddle
    leftMiddleSuccess
  have leftFlat : leftAssociated.occurrences.Perm
      ((left.occurrences ++ middle.occurrences) ++ right.occurrences) :=
    leftOuter.trans (leftInner.append_right right.occurrences)
  have rightOuter := merge?_occurrences left middleRight rightAssociated
    rightAssociatedSuccess
  have rightInner := merge?_occurrences middle right middleRight
    middleRightSuccess
  have rightFlat : rightAssociated.occurrences.Perm
      (left.occurrences ++ (middle.occurrences ++ right.occurrences)) :=
    rightOuter.trans (rightInner.append_left left.occurrences)
  exact leftFlat.trans (by
    simpa only [List.append_assoc] using rightFlat.symm)

/-! ## Shared-label identity and sort coherence -/

private theorem occurrence_mem_of_entry_mem
    {Expr : StaticSort -> Type u} {signature : Signature Expr}
    {entry : Entry Expr} (entryMem : entry ∈ signature.entries)
    {occurrence : Occurrence Expr} (occurrenceMem : occurrence ∈ entry.occurrences) :
    occurrence ∈ signature.occurrences := by
  simp only [occurrences, List.mem_flatMap]
  exact ⟨entry, entryMem, occurrenceMem⟩

private theorem entry_of_occurrence_mem
    {Expr : StaticSort -> Type u} {signature : Signature Expr}
    {occurrence : Occurrence Expr}
    (membership : occurrence ∈ signature.occurrences) :
    ∃ entry ∈ signature.entries, occurrence ∈ entry.occurrences := by
  simpa [occurrences, List.mem_flatMap] using membership

private theorem entries_eq_of_same_label
    {Expr : StaticSort -> Type u} {signature : Signature Expr}
    (normalized : signature.Normalized)
    {first second : Entry Expr}
    (firstMem : first ∈ signature.entries)
    (secondMem : second ∈ signature.entries)
    (same : first.label = second.label) : first = second := by
  have firstLookup := lookup_eq_some_of_mem normalized firstMem
  have secondLookup := lookup_eq_some_of_mem normalized secondMem
  rw [same] at firstLookup
  rw [secondLookup] at firstLookup
  exact Option.some.inj firstLookup.symm

/-- If merge succeeds, two normalized inputs cannot assign different sorts
to the same label. -/
theorem merge?_shared_label_same_sort {Expr : StaticSort -> Type u}
    (left right result : Signature Expr)
    (leftNormalized : left.Normalized)
    (rightNormalized : right.Normalized)
    (success : merge? left right = .ok result)
    {label : Nat} {leftEntry rightEntry : Entry Expr}
    (leftFound : left.lookup label = some leftEntry)
    (rightFound : right.lookup label = some rightEntry) :
    leftEntry.sort = rightEntry.sort := by
  have resultNormalized := merge?_normalized left right result
    leftNormalized rightNormalized success
  have retained := merge?_occurrences left right result success
  have leftEntryMem := lookup_some_mem leftFound
  have rightEntryMem := lookup_some_mem rightFound
  obtain ⟨leftOccurrence, leftOccurrenceMem⟩ :=
    Entry.exists_occurrence
      (leftNormalized.nonempty leftEntry leftEntryMem)
  obtain ⟨rightOccurrence, rightOccurrenceMem⟩ :=
    Entry.exists_occurrence
      (rightNormalized.nonempty rightEntry rightEntryMem)
  have leftInInputs :
      leftOccurrence ∈ left.occurrences ++ right.occurrences :=
    List.mem_append_left _
      (occurrence_mem_of_entry_mem leftEntryMem leftOccurrenceMem)
  have rightInInputs :
      rightOccurrence ∈ left.occurrences ++ right.occurrences :=
    List.mem_append_right _
      (occurrence_mem_of_entry_mem rightEntryMem rightOccurrenceMem)
  have leftInResult : leftOccurrence ∈ result.occurrences :=
    retained.mem_iff.mpr leftInInputs
  have rightInResult : rightOccurrence ∈ result.occurrences :=
    retained.mem_iff.mpr rightInInputs
  obtain ⟨leftResultEntry, leftResultMem, leftInResultEntry⟩ :=
    entry_of_occurrence_mem leftInResult
  obtain ⟨rightResultEntry, rightResultMem, rightInResultEntry⟩ :=
    entry_of_occurrence_mem rightInResult
  have leftEntryLabel := lookup_some_label leftFound
  have rightEntryLabel := lookup_some_label rightFound
  have leftResultLabel :=
    Entry.occurrence_label leftResultEntry leftOccurrence leftInResultEntry
  have rightResultLabel :=
    Entry.occurrence_label rightResultEntry rightOccurrence rightInResultEntry
  have leftOccurrenceLabel :=
    Entry.occurrence_label leftEntry leftOccurrence leftOccurrenceMem
  have rightOccurrenceLabel :=
    Entry.occurrence_label rightEntry rightOccurrence rightOccurrenceMem
  have resultLabelsEqual : leftResultEntry.label = rightResultEntry.label := by
    calc
      leftResultEntry.label = leftOccurrence.label := leftResultLabel.symm
      _ = leftEntry.label := leftOccurrenceLabel
      _ = label := leftEntryLabel
      _ = rightEntry.label := rightEntryLabel.symm
      _ = rightOccurrence.label := rightOccurrenceLabel.symm
      _ = rightResultEntry.label := rightResultLabel
  have resultEntriesEqual := entries_eq_of_same_label resultNormalized
    leftResultMem rightResultMem resultLabelsEqual
  have leftSort := Entry.occurrence_sort leftEntry leftOccurrence
    leftOccurrenceMem
  have leftResultSort := Entry.occurrence_sort leftResultEntry leftOccurrence
    leftInResultEntry
  have rightSort := Entry.occurrence_sort rightEntry rightOccurrence
    rightOccurrenceMem
  have rightResultSort := Entry.occurrence_sort rightResultEntry
    rightOccurrence rightInResultEntry
  calc
    leftEntry.sort = leftOccurrence.sort := leftSort.symm
    _ = leftResultEntry.sort := leftResultSort
    _ = rightResultEntry.sort := congrArg Entry.sort resultEntriesEqual
    _ = rightOccurrence.sort := rightResultSort.symm
    _ = rightEntry.sort := rightSort

/-- Semantic specification realized by executable merge. -/
structure LawfulMerge {Expr : StaticSort -> Type u}
    (left right result : Signature Expr) : Prop where
  normalized : result.Normalized
  constraints : ∀ label,
    (result.constraintsAt label).Perm
      (left.constraintsAt label ++ right.constraintsAt label)
  sharedSort : ∀ {label leftEntry rightEntry},
    left.lookup label = some leftEntry ->
    right.lookup label = some rightEntry ->
    leftEntry.sort = rightEntry.sort

/-- The executable merge is lawful with respect to normalization, primitive
constraint conjunction, and shared-label sort identity. -/
theorem merge?_lawful {Expr : StaticSort -> Type u}
    (left right result : Signature Expr)
    (leftNormalized : left.Normalized)
    (rightNormalized : right.Normalized)
    (success : merge? left right = .ok result) :
    LawfulMerge left right result where
  normalized := merge?_normalized left right result leftNormalized
    rightNormalized success
  constraints := merge?_constraintsAt left right result success
  sharedSort := merge?_shared_label_same_sort left right result
    leftNormalized rightNormalized success

end Signature

end DOTCapture.Intersections
