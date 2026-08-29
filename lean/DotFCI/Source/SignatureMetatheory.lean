import DotFCI.Source.Signature

/-!
# Algebra of normalized source signatures

The exact order of accumulated constraints is administrative.  Theorems use
`Signature.Equiv`, which preserves constraint multiplicity through
`List.Perm`, while label order and identity allocation remain canonical.
-/

namespace DotFCI.Source

open DotFC

namespace Signature

/-! ## Basic extensional laws -/

namespace Equiv

theorem refl {scope : Sig} (signature : Signature scope) :
    signature ≈ₛ signature := by
  intro label
  exact List.Perm.refl _

theorem symm {scope : Sig} {left right : Signature scope}
    (equivalent : left ≈ₛ right) : right ≈ₛ left := by
  intro label
  exact (equivalent label).symm

theorem trans {scope : Sig} {first second third : Signature scope}
    (firstEquivalent : first ≈ₛ second)
    (secondEquivalent : second ≈ₛ third) : first ≈ₛ third := by
  intro label
  exact (firstEquivalent label).trans (secondEquivalent label)

end Equiv

/-! ## Canonical ordering -/

theorem empty_normalized {scope : Sig} :
    (empty : Signature scope).Normalized := by
  exact ⟨List.Pairwise.nil, by simp⟩

theorem singleton_normalized {scope : Sig} (label : Name)
    (lower upper : Ty scope) :
    (singleton label lower upper).Normalized := by
  constructor
  · exact .cons (by simp) .nil
  · intro entry membership
    simp only [singleton_entries, List.mem_cons, List.not_mem_nil,
      or_false] at membership
    subst entry
    simp

/-- Every entry produced by insertion either owns the inserted label or
retains the label of an original entry. -/
theorem label_of_mem_insertEntry {scope : Sig}
    (inserted : SignatureEntry scope) (entries : List (SignatureEntry scope))
    {found : SignatureEntry scope}
    (membership : found ∈ insertEntry inserted entries) :
    found.label = inserted.label ∨
      ∃ original ∈ entries, found.label = original.label := by
  induction entries with
  | nil =>
      simp [insertEntry] at membership
      subst found
      exact Or.inl rfl
  | cons current remaining induction =>
      simp only [insertEntry] at membership
      split at membership
      next insertedBefore =>
        simp only [List.mem_cons] at membership
        rcases membership with insertedEqual | currentOrRemaining
        · subst found
          exact Or.inl rfl
        · exact Or.inr ⟨found, by simpa using currentOrRemaining, rfl⟩
      next notBefore =>
        split at membership
        next same =>
          simp only [List.mem_cons] at membership
          rcases membership with combinedEqual | remainingMembership
          · subst found
            exact Or.inl same.symm
          · exact Or.inr ⟨found, .tail _ remainingMembership, rfl⟩
        next different =>
          simp only [List.mem_cons] at membership
          rcases membership with currentEqual | insertedMembership
          · subst found
            exact Or.inr ⟨current, .head _, rfl⟩
          · rcases induction insertedMembership with insertedLabel | oldLabel
            · exact Or.inl insertedLabel
            · rcases oldLabel with ⟨original, originalMembership, labelEqual⟩
              exact Or.inr
                ⟨original, .tail current originalMembership, labelEqual⟩

/-- Insertion preserves strict label ordering. -/
theorem insertEntry_sorted {scope : Sig}
    (inserted : SignatureEntry scope)
    (entries : List (SignatureEntry scope))
    (sorted : entries.Pairwise Before) :
    (insertEntry inserted entries).Pairwise Before := by
  induction entries with
  | nil =>
      simp [insertEntry]
  | cons current remaining induction =>
      cases sorted with
      | cons currentBefore remainingSorted =>
          simp only [insertEntry]
          split
          next insertedBefore =>
            apply List.Pairwise.cons
            · intro found membership
              simp only [List.mem_cons] at membership
              rcases membership with currentEqual | remainingMembership
              · subst found
                exact insertedBefore
              · exact Nat.lt_trans insertedBefore
                  (currentBefore found remainingMembership)
            · exact .cons currentBefore remainingSorted
          next notBefore =>
            split
            next same =>
              apply List.Pairwise.cons
              · intro found membership
                simpa [Before, same] using currentBefore found membership
              · exact remainingSorted
            next different =>
              have currentBeforeInserted : current.label < inserted.label := by
                exact Nat.lt_of_le_of_ne (Nat.le_of_not_gt notBefore)
                  (Ne.symm different)
              apply List.Pairwise.cons
              · intro found membership
                rcases label_of_mem_insertEntry inserted remaining membership with
                  insertedLabel | originalLabel
                · unfold Before
                  rw [insertedLabel]
                  exact currentBeforeInserted
                · rcases originalLabel with
                    ⟨original, originalMembership, labelEqual⟩
                  unfold Before
                  rw [labelEqual]
                  exact currentBefore original originalMembership
              · exact induction remainingSorted

/-- Insertion preserves nonempty interval lists. -/
theorem insertEntry_nonempty {scope : Sig}
    (inserted : SignatureEntry scope)
    (entries : List (SignatureEntry scope))
    (insertedNonempty : inserted.intervals ≠ [])
    (entriesNonempty : ∀ entry ∈ entries, entry.intervals ≠ []) :
    ∀ entry ∈ insertEntry inserted entries, entry.intervals ≠ [] := by
  induction entries with
  | nil =>
      intro entry membership
      simp [insertEntry] at membership
      subst entry
      exact insertedNonempty
  | cons current remaining induction =>
      intro entry membership
      simp only [insertEntry] at membership
      split at membership
      next insertedBefore =>
        simp only [List.mem_cons] at membership
        rcases membership with insertedEqual | oldMembership
        · subst entry
          exact insertedNonempty
        · exact entriesNonempty entry (by simpa using oldMembership)
      next notBefore =>
        split at membership
        next same =>
          simp only [List.mem_cons] at membership
          rcases membership with combinedEqual | remainingMembership
          · subst entry
            change current.intervals ++ inserted.intervals ≠ []
            exact List.append_ne_nil_of_left_ne_nil
              (entriesNonempty current (.head _)) inserted.intervals
          · exact entriesNonempty entry (.tail current remainingMembership)
        next different =>
          simp only [List.mem_cons] at membership
          rcases membership with currentEqual | insertedMembership
          · subst entry
            exact entriesNonempty current (.head _)
          · apply induction
            · intro old oldMembership
              exact entriesNonempty old (.tail current oldMembership)
            · exact insertedMembership

/-- Inserting a nonempty constraint block into a canonical signature remains
canonical. -/
theorem insertEntry_normalized {scope : Sig}
    (inserted : SignatureEntry scope)
    (signature : Signature scope)
    (insertedNonempty : inserted.intervals ≠ [])
    (normalized : signature.Normalized) :
    ({ entries := insertEntry inserted signature.entries } :
      Signature scope).Normalized := by
  exact ⟨insertEntry_sorted inserted signature.entries normalized.sorted,
    insertEntry_nonempty inserted signature.entries insertedNonempty
      normalized.nonempty⟩

/-- Merging canonical entry lists preserves the canonical invariant. -/
theorem mergeEntries_normalized {scope : Sig}
    (accumulated incoming : List (SignatureEntry scope))
    (accumulatedNormalized :
      ({ entries := accumulated } : Signature scope).Normalized)
    (incomingNormalized :
      ({ entries := incoming } : Signature scope).Normalized) :
    ({ entries := mergeEntries accumulated incoming } :
      Signature scope).Normalized := by
  induction incoming generalizing accumulated with
  | nil =>
      exact accumulatedNormalized
  | cons entry remaining induction =>
      cases incomingNormalized.sorted with
      | cons entryBefore remainingSorted =>
          have entryNonempty : entry.intervals ≠ [] :=
            incomingNormalized.nonempty entry (.head _)
          have remainingNonempty :
              ∀ current ∈ remaining, current.intervals ≠ [] := by
            intro current membership
            exact incomingNormalized.nonempty current (.tail entry membership)
          have insertedNormalized :=
            insertEntry_normalized entry
              ({ entries := accumulated } : Signature scope)
              entryNonempty accumulatedNormalized
          exact induction (insertEntry entry accumulated) insertedNormalized
            ({ sorted := remainingSorted, nonempty := remainingNonempty } :
              ({ entries := remaining } : Signature scope).Normalized)

/-- Canonical signature merge preserves sorted unique labels and nonempty
constraint blocks. -/
theorem merge_normalized {scope : Sig} (left right : Signature scope)
    (leftNormalized : left.Normalized)
    (rightNormalized : right.Normalized) :
    (left.merge right).Normalized := by
  exact mergeEntries_normalized left.entries right.entries
    leftNormalized rightNormalized

private theorem labels_nodup_of_sorted {scope : Sig}
    (entries : List (SignatureEntry scope))
    (sorted : entries.Pairwise Before) :
    (entries.map SignatureEntry.label).Nodup := by
  induction entries with
  | nil => exact .nil
  | cons entry remaining induction =>
      cases sorted with
      | cons entryBefore remainingSorted =>
          change (entry.label :: remaining.map SignatureEntry.label).Nodup
          rw [List.nodup_cons]
          constructor
          · intro membership
            obtain ⟨found, foundMembership, labelEqual⟩ :=
              List.mem_map.mp membership
            have strictlyBefore := entryBefore found foundMembership
            unfold Before at strictlyBefore
            exact (Nat.ne_of_lt strictlyBefore) labelEqual.symm
          · exact induction remainingSorted

/-- Strictly ordered canonical labels are unique. -/
theorem Normalized.labels_nodup {scope : Sig} {signature : Signature scope}
    (normalized : signature.Normalized) : signature.labels.Nodup := by
  exact labels_nodup_of_sorted signature.entries normalized.sorted

/-! ## Constraint lookup through insertion and merge -/

@[simp]
theorem constraintsAt_entries_nil {scope : Sig} (label : Name) :
    ({ entries := [] } : Signature scope).constraintsAt label = [] := rfl

@[simp]
theorem constraintsAt_entries_cons {scope : Sig}
    (entry : SignatureEntry scope) (entries : List (SignatureEntry scope))
    (label : Name) :
    ({ entries := entry :: entries } : Signature scope).constraintsAt label =
      entry.constraintsAt label ++
        ({ entries := entries } : Signature scope).constraintsAt label := rfl

theorem constraintsAt_eq_nil_of_forall_ne {scope : Sig}
    (entries : List (SignatureEntry scope)) (label : Name)
    (absent : ∀ entry ∈ entries, entry.label ≠ label) :
    ({ entries := entries } : Signature scope).constraintsAt label = [] := by
  induction entries with
  | nil => rfl
  | cons entry remaining induction =>
      have entryDifferent := absent entry (.head _)
      have remainingAbsent : ∀ current ∈ remaining,
          current.label ≠ label := by
        intro current membership
        exact absent current (.tail entry membership)
      simp [constraintsAt_entries_cons, SignatureEntry.constraintsAt,
        entryDifferent, induction remainingAbsent]

/-- Inserting one entry appends exactly its constraints at its label and
does not change lookup at any other label. -/
theorem constraintsAt_insertEntry {scope : Sig}
    (inserted : SignatureEntry scope)
    (entries : List (SignatureEntry scope))
    (sorted : entries.Pairwise Before) (label : Name) :
    ({ entries := insertEntry inserted entries } : Signature scope).constraintsAt label =
      ({ entries := entries } : Signature scope).constraintsAt label ++
        inserted.constraintsAt label := by
  induction entries with
  | nil =>
      simp [insertEntry, constraintsAt_entries_cons,
        SignatureEntry.constraintsAt]
  | cons current remaining induction =>
      cases sorted with
      | cons currentBefore remainingSorted =>
          simp only [insertEntry]
          split
          next insertedBefore =>
            by_cases insertedAtLabel : inserted.label = label
            · have oldAbsent : ∀ entry ∈ current :: remaining,
                  entry.label ≠ label := by
                intro entry membership
                simp only [List.mem_cons] at membership
                rcases membership with currentEqual | remainingMembership
                · subst entry
                  rw [← insertedAtLabel]
                  exact Nat.ne_of_gt insertedBefore
                · rw [← insertedAtLabel]
                  exact Nat.ne_of_gt
                    (Nat.lt_trans insertedBefore
                      (currentBefore entry remainingMembership))
              rw [constraintsAt_eq_nil_of_forall_ne _ _ oldAbsent]
              have currentDifferent := oldAbsent current (.head _)
              have remainingAtLabel :
                  ({ entries := remaining } : Signature scope).constraintsAt
                    label = [] := by
                apply constraintsAt_eq_nil_of_forall_ne
                intro entry membership
                exact oldAbsent entry (.tail current membership)
              simp [constraintsAt_entries_cons,
                SignatureEntry.constraintsAt, insertedAtLabel,
                currentDifferent, remainingAtLabel]
            · simp [constraintsAt_entries_cons,
                SignatureEntry.constraintsAt, insertedAtLabel]
          next notInsertedBefore =>
            split
            next sameLabel =>
              have remainingAbsent : ∀ entry ∈ remaining,
                  entry.label ≠ current.label := by
                intro entry membership
                exact Nat.ne_of_gt (currentBefore entry membership)
              by_cases currentAtLabel : current.label = label
              · have remainingAtLabel :
                    ({ entries := remaining } : Signature scope).constraintsAt
                      label = [] := by
                  apply constraintsAt_eq_nil_of_forall_ne
                  intro entry membership
                  intro entryAtLabel
                  apply remainingAbsent entry membership
                  exact entryAtLabel.trans currentAtLabel.symm
                simp [constraintsAt_entries_cons,
                  SignatureEntry.constraintsAt, currentAtLabel,
                  sameLabel, remainingAtLabel]
              · have insertedAtLabel : inserted.label ≠ label := by
                  intro equal
                  exact currentAtLabel (sameLabel.symm.trans equal)
                simp [constraintsAt_entries_cons,
                  SignatureEntry.constraintsAt, currentAtLabel,
                  insertedAtLabel]
            next differentLabel =>
              rw [constraintsAt_entries_cons, constraintsAt_entries_cons,
                induction remainingSorted]
              simp only [List.append_assoc]

/-- Merge lookup is constraint accumulation: no interval occurrence is
collapsed or synthesized. -/
theorem constraintsAt_mergeEntries {scope : Sig}
    (accumulated incoming : List (SignatureEntry scope))
    (accumulatedNormalized :
      ({ entries := accumulated } : Signature scope).Normalized)
    (incomingNormalized :
      ({ entries := incoming } : Signature scope).Normalized)
    (label : Name) :
    ({ entries := mergeEntries accumulated incoming } :
        Signature scope).constraintsAt label =
      ({ entries := accumulated } : Signature scope).constraintsAt label ++
        ({ entries := incoming } : Signature scope).constraintsAt label := by
  induction incoming generalizing accumulated with
  | nil => simp [mergeEntries]
  | cons entry remaining induction =>
      cases incomingNormalized.sorted with
      | cons entryBefore remainingSorted =>
          have entryNonempty : entry.intervals ≠ [] :=
            incomingNormalized.nonempty entry (.head _)
          have remainingNormalized :
              ({ entries := remaining } : Signature scope).Normalized :=
            { sorted := remainingSorted
              nonempty := fun current membership =>
                incomingNormalized.nonempty current (.tail entry membership) }
          have insertedNormalized :=
            insertEntry_normalized entry
              ({ entries := accumulated } : Signature scope)
              entryNonempty accumulatedNormalized
          simp only [mergeEntries]
          rw [induction (insertEntry entry accumulated) insertedNormalized
            remainingNormalized]
          rw [constraintsAt_insertEntry entry accumulated
            accumulatedNormalized.sorted]
          rw [constraintsAt_entries_cons]
          simp only [List.append_assoc]

/-- Canonical merge accumulates the two lists of constraints at every label. -/
theorem constraintsAt_merge {scope : Sig} (left right : Signature scope)
    (leftNormalized : left.Normalized)
    (rightNormalized : right.Normalized) (label : Name) :
    (left.merge right).constraintsAt label =
      left.constraintsAt label ++ right.constraintsAt label := by
  exact constraintsAt_mergeEntries left.entries right.entries
    leftNormalized rightNormalized label

/-! ## Merge algebra -/

/-- Empty is a left identity modulo signature equivalence. -/
theorem merge_empty_left_equiv {scope : Sig} (signature : Signature scope)
    (normalized : signature.Normalized) :
    (empty.merge signature) ≈ₛ signature := by
  intro label
  rw [constraintsAt_merge empty signature empty_normalized normalized]
  exact List.Perm.refl _

/-- Empty is a right identity (and hence also an extensional identity). -/
theorem merge_empty_right_equiv {scope : Sig} (signature : Signature scope) :
    (signature.merge empty) ≈ₛ signature := by
  rw [merge_empty_right]
  exact Equiv.refl signature

/-- Signature merge is associative modulo the administrative order of
constraint occurrences. -/
theorem merge_assoc {scope : Sig} (first second third : Signature scope)
    (firstNormalized : first.Normalized)
    (secondNormalized : second.Normalized)
    (thirdNormalized : third.Normalized) :
    ((first.merge second).merge third) ≈ₛ
      (first.merge (second.merge third)) := by
  intro label
  rw [constraintsAt_merge (first.merge second) third
    (merge_normalized first second firstNormalized secondNormalized)
    thirdNormalized]
  rw [constraintsAt_merge first second firstNormalized secondNormalized]
  rw [constraintsAt_merge first (second.merge third) firstNormalized
    (merge_normalized second third secondNormalized thirdNormalized)]
  rw [constraintsAt_merge second third secondNormalized thirdNormalized]
  exact List.Perm.of_eq (List.append_assoc _ _ _)

/-- Signature merge is commutative modulo permutation of accumulated
constraints.  Canonical label ordering is identical on both sides. -/
theorem merge_comm {scope : Sig} (left right : Signature scope)
    (leftNormalized : left.Normalized)
    (rightNormalized : right.Normalized) :
    (left.merge right) ≈ₛ (right.merge left) := by
  intro label
  rw [constraintsAt_merge left right leftNormalized rightNormalized]
  rw [constraintsAt_merge right left rightNormalized leftNormalized]
  exact List.perm_append_comm

/-- The canonical merge is unique up to `Equiv` among results having exactly
the accumulated constraints at every label. -/
theorem merge_unique {scope : Sig} (left right candidate : Signature scope)
    (leftNormalized : left.Normalized)
    (rightNormalized : right.Normalized)
    (specification : ∀ label,
      (candidate.constraintsAt label).Perm
        (left.constraintsAt label ++ right.constraintsAt label)) :
    candidate ≈ₛ left.merge right := by
  intro label
  rw [constraintsAt_merge left right leftNormalized rightNormalized]
  exact specification label

/-! ## Label support -/

/-- Insertion retains every old label and contributes exactly its own label. -/
theorem label_mem_insertEntry {scope : Sig}
    (inserted : SignatureEntry scope)
    (entries : List (SignatureEntry scope)) (label : Name) :
    label ∈ (insertEntry inserted entries).map SignatureEntry.label ↔
      label = inserted.label ∨
        label ∈ entries.map SignatureEntry.label := by
  induction entries with
  | nil => simp [insertEntry]
  | cons current remaining induction =>
      simp only [insertEntry]
      split
      next insertedBefore => simp
      next notBefore =>
        split
        next same => simp [same]
        next different =>
          simp only [List.map_cons, List.mem_cons, induction]
          constructor
          · intro membership
            rcases membership with currentLabel | insertedOrRemaining
            · exact Or.inr (Or.inl currentLabel)
            · rcases insertedOrRemaining with insertedLabel | remainingLabel
              · exact Or.inl insertedLabel
              · exact Or.inr (Or.inr remainingLabel)
          · intro membership
            rcases membership with insertedLabel | currentOrRemaining
            · exact Or.inr (Or.inl insertedLabel)
            · rcases currentOrRemaining with currentLabel | remainingLabel
              · exact Or.inl currentLabel
              · exact Or.inr (Or.inr remainingLabel)

/-- Entry-list merge has exactly the union of the two label supports. -/
theorem label_mem_mergeEntries {scope : Sig}
    (accumulated incoming : List (SignatureEntry scope)) (label : Name) :
    label ∈ (mergeEntries accumulated incoming).map SignatureEntry.label ↔
      label ∈ accumulated.map SignatureEntry.label ∨
        label ∈ incoming.map SignatureEntry.label := by
  induction incoming generalizing accumulated with
  | nil => simp [mergeEntries]
  | cons entry remaining induction =>
      simp only [mergeEntries, induction,
        label_mem_insertEntry, List.map_cons, List.mem_cons]
      constructor
      · intro membership
        rcases membership with insertedOrAccumulated | remainingLabel
        · rcases insertedOrAccumulated with insertedLabel | accumulatedLabel
          · exact Or.inr (Or.inl insertedLabel)
          · exact Or.inl accumulatedLabel
        · exact Or.inr (Or.inr remainingLabel)
      · intro membership
        rcases membership with accumulatedLabel | insertedOrRemaining
        · exact Or.inl (Or.inr accumulatedLabel)
        · rcases insertedOrRemaining with insertedLabel | remainingLabel
          · exact Or.inl (Or.inl insertedLabel)
          · exact Or.inr remainingLabel

/-- Canonical merge neither loses labels nor invents labels. -/
theorem label_mem_merge {scope : Sig} (left right : Signature scope)
    (label : Name) :
    label ∈ (left.merge right).labels ↔
      label ∈ left.labels ∨ label ∈ right.labels := by
  exact label_mem_mergeEntries left.entries right.entries label

/-! ## Renaming naturality -/

private theorem renameEntries_sorted {source target : Sig}
    (entries : List (SignatureEntry source))
    (rho : Rename source target) (sorted : entries.Pairwise Before) :
    (entries.map fun entry => entry.rename rho).Pairwise Before := by
  induction entries with
  | nil => exact .nil
  | cons entry remaining induction =>
      cases sorted with
      | cons entryBefore remainingSorted =>
          apply List.Pairwise.cons
          · intro renamed membership
            obtain ⟨original, originalMembership, renamedEqual⟩ :=
              List.mem_map.mp membership
            subst renamed
            simpa [Before] using entryBefore original originalMembership
          · exact induction remainingSorted

/-- Renaming paths does not affect signature normalization or label order. -/
theorem Normalized.rename {source target : Sig}
    {signature : Signature source} (normalized : signature.Normalized)
    (rho : Rename source target) : (signature.rename rho).Normalized := by
  constructor
  · exact renameEntries_sorted signature.entries rho normalized.sorted
  · intro renamed membership
    obtain ⟨original, originalMembership, renamedEqual⟩ :=
      List.mem_map.mp membership
    subst renamed
    simp only [SignatureEntry.rename_intervals]
    intro mappedEmpty
    have originalEmpty : original.intervals = [] := by
      simpa using mappedEmpty
    exact normalized.nonempty original originalMembership originalEmpty

private theorem entryConstraintsAt_rename {source target : Sig}
    (entry : SignatureEntry source) (rho : Rename source target)
    (label : Name) :
    (entry.rename rho).constraintsAt label =
      (entry.constraintsAt label).map fun interval => interval.rename rho := by
  by_cases same : entry.label = label
  · simp [SignatureEntry.constraintsAt, SignatureEntry.rename, same]
  · simp [SignatureEntry.constraintsAt, SignatureEntry.rename, same]

private theorem constraintsAtEntries_rename {source target : Sig}
    (entries : List (SignatureEntry source)) (rho : Rename source target)
    (label : Name) :
    constraintsAtEntries (entries.map fun entry => entry.rename rho) label =
      (constraintsAtEntries entries label).map fun interval =>
        interval.rename rho := by
  induction entries with
  | nil => rfl
  | cons entry remaining induction =>
      simp only [List.map_cons, constraintsAtEntries,
        entryConstraintsAt_rename, induction, List.map_append]

/-- Constraint lookup commutes with renaming every interval bound. -/
theorem constraintsAt_rename {source target : Sig}
    (signature : Signature source) (rho : Rename source target)
    (label : Name) :
    (signature.rename rho).constraintsAt label =
      (signature.constraintsAt label).map fun interval =>
        interval.rename rho := by
  exact constraintsAtEntries_rename signature.entries rho label

/-- Insertion is natural because renaming changes bounds but never labels. -/
theorem insertEntry_rename {source target : Sig}
    (inserted : SignatureEntry source)
    (entries : List (SignatureEntry source)) (rho : Rename source target) :
    (insertEntry inserted entries).map (fun entry => entry.rename rho) =
      insertEntry (inserted.rename rho)
        (entries.map fun entry => entry.rename rho) := by
  induction entries with
  | nil => rfl
  | cons current remaining induction =>
      simp only [insertEntry, List.map_cons,
        SignatureEntry.rename_label]
      split
      next insertedBefore => rfl
      next notBefore =>
        split
        next same =>
          simp [SignatureEntry.rename, List.map_append]
        next different =>
          exact congrArg (fun tail => current.rename rho :: tail) induction

/-- Entry-list merge commutes with ambient renaming. -/
theorem mergeEntries_rename {source target : Sig}
    (accumulated incoming : List (SignatureEntry source))
    (rho : Rename source target) :
    (mergeEntries accumulated incoming).map
        (fun entry => entry.rename rho) =
      mergeEntries
        (accumulated.map fun entry => entry.rename rho)
        (incoming.map fun entry => entry.rename rho) := by
  induction incoming generalizing accumulated with
  | nil => rfl
  | cons entry remaining induction =>
      simp only [mergeEntries, List.map_cons]
      rw [induction]
      rw [insertEntry_rename]

/-- Canonical signature merge is natural in the ambient source scope. -/
theorem merge_rename {source target : Sig} (left right : Signature source)
    (rho : Rename source target) :
    (left.merge right).rename rho =
      (left.rename rho).merge (right.rename rho) := by
  cases left
  cases right
  simp [Signature.merge, Signature.rename, mergeEntries_rename]

@[simp]
theorem singleton_rename {source target : Sig} (label : Name)
    (lower upper : Ty source) (rho : Rename source target) :
    (singleton label lower upper).rename rho =
      singleton label (lower.rename rho) (upper.rename rho) := by
  simp [singleton, Signature.rename, SignatureEntry.rename,
    Interval.rename]

end Signature

/-! ## Collection correctness -/

/-- Every successful first-phase collection result is canonical. -/
theorem collect?_normalized {scope : Sig} (type : Ty scope)
    {signature : Signature scope} (collected : collect? type = some signature) :
    signature.Normalized := by
  induction type with
  | top => simp [collect?] at collected
  | bot => simp [collect?] at collected
  | all domain codomain domainInduction codomainInduction =>
      simp [collect?] at collected
  | sel path label => simp [collect?] at collected
  | member label lower upper lowerInduction upperInduction =>
      simp only [collect?_member, Option.some.injEq] at collected
      subst signature
      exact Signature.singleton_normalized label lower upper
  | inter left right leftInduction rightInduction =>
      simp only [collect?_inter] at collected
      obtain ⟨leftSignature, leftCollected, remaining⟩ :=
        Option.bind_eq_some_iff.mp collected
      obtain ⟨rightSignature, rightCollected, merged⟩ :=
        Option.bind_eq_some_iff.mp remaining
      have mergedEq : leftSignature.merge rightSignature = signature := by
        simpa using merged
      subst signature
      exact Signature.merge_normalized leftSignature rightSignature
        (leftInduction leftCollected) (rightInduction rightCollected)

/-- A collected signature allocates at most one entry for each member label. -/
theorem collect?_labels_nodup {scope : Sig} (type : Ty scope)
    {signature : Signature scope} (collected : collect? type = some signature) :
    signature.labels.Nodup :=
  (collect?_normalized type collected).labels_nodup

/-- Successful collection of an intersection is exactly canonical merge of
the two independently collected signatures. -/
theorem collect?_inter_some {scope : Sig} (left right : Ty scope)
    {leftSignature rightSignature : Signature scope}
    (leftCollected : collect? left = some leftSignature)
    (rightCollected : collect? right = some rightSignature) :
    collect? (.inter left right) =
      some (leftSignature.merge rightSignature) := by
  simp [collect?, leftCollected, rightCollected]

/-- The core overlapping-member regression: two views allocate one canonical
label entry and retain both interval occurrences in source order. -/
theorem collect?_overlapping_members {scope : Sig} (label : Name)
    (lower₁ upper₁ lower₂ upper₂ : Ty scope) :
    collect?
        (.inter (.member label lower₁ upper₁)
          (.member label lower₂ upper₂)) =
      some
        ({ entries :=
          [⟨label, [⟨lower₁, upper₁⟩, ⟨lower₂, upper₂⟩]⟩] } :
          Signature scope) := by
  simp [collect?, Signature.merge, Signature.mergeEntries,
    Signature.insertEntry]

/-- Consequently the overlapping regression exposes exactly one allocation
label. -/
theorem overlapping_members_labels {scope : Sig} (label : Name)
    (lower₁ upper₁ lower₂ upper₂ : Ty scope) :
    ({ entries :=
      [⟨label, [⟨lower₁, upper₁⟩, ⟨lower₂, upper₂⟩]⟩] } :
      Signature scope).labels = [label] := rfl

/-- Phase-one signature collection commutes with stable-path renaming. -/
theorem collect?_rename {source target : Sig} (type : Ty source)
    (rho : Rename source target) :
    collect? (type.rename rho) =
      (collect? type).map fun signature => signature.rename rho := by
  induction type generalizing target with
  | top => rfl
  | bot => rfl
  | all domain codomain domainInduction codomainInduction => rfl
  | sel path label => rfl
  | member label lower upper lowerInduction upperInduction =>
      exact congrArg some
        (Signature.singleton_rename label lower upper rho).symm
  | inter left right leftInduction rightInduction =>
      simp only [Ty.rename, collect?_inter, leftInduction, rightInduction]
      cases collect? left with
      | none => rfl
      | some leftSignature =>
          cases collect? right with
          | none => rfl
          | some rightSignature =>
              simp [Signature.merge_rename]

end DotFCI.Source
