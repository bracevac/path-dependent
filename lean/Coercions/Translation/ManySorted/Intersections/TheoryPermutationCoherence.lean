import Coercions.Translation.ManySorted.Intersections.EncodingMetatheory
import Coercions.ManySortedFC.TheoryMapLaws

/-!
# Generic coherence for permuted target constraints

Two names-first theories with the same symbol block may present the same
propositions in different evidence order.  A permutation of their packed
proposition lists induces a checked `TheoryMap` in each direction.  The maps
interpret every symbol by the same opened name and discharge each destination
constraint with the matching source evidence variable.

This theorem is independent of a particular intersection example.  It is the
target-side coherence boundary needed after source preparation has established
that two normalized signatures allocate the same member identities and differ
only by retained-constraint order.

The source-to-target bridge is deliberately separate.  The existing source
`Signature.ConstraintEquivalent` is a flat proposition-valued `List.Perm`;
preparation instead needs a sort-indexed permutation for each normalized label
and a theorem that partial interval translation preserves that permutation.
Adding that dependent bridge is follow-on work.  This module proves the
strongest generic target statement without replacing the derivation-directed
preparation API.
-/

namespace DOTCaptureToManySortedFC.Intersections.TheoryPermutationCoherence

open ManySortedFC
open DOTCaptureToManySortedFC.Intersections.Encoding

namespace PackedTheory

/-- Every proposition of a theory occurs in its packed observable list. -/
theorem packed_proposition_mem {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    {relation : Relation} (reference : ConstraintRef relations relation) :
    Encoding.Target.PackedProposition.pack
        (theory.propositionAt reference) ∈
      Encoding.Target.Theory.propositions theory := by
  induction reference generalizing scope symbols with
  | here =>
      cases theory with
      | cons proposition rest => exact .head _
  | there reference induction =>
      cases theory with
      | cons proposition rest => exact .tail _ (induction rest)

/-- Membership in the packed observable list has an exact intrinsically
related coordinate in the indexed theory. -/
theorem exists_reference_of_mem {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    (packed : Encoding.Target.PackedProposition
      (SymbolScope scope symbols))
    (membership : packed ∈ Encoding.Target.Theory.propositions theory) :
    ∃ relation, ∃ reference : ConstraintRef relations relation,
      packed = Encoding.Target.PackedProposition.pack
        (theory.propositionAt reference) := by
  cases theory with
  | nil => cases membership
  | @cons _ _ relation relations proposition rest =>
      rcases List.mem_cons.mp membership with head | tail
      · exact ⟨relation, .here, head⟩
      · obtain ⟨foundRelation, reference, equality⟩ :=
          exists_reference_of_mem rest packed tail
        exact ⟨foundRelation, .there reference, equality⟩

/-- A packed match preserves the hidden relation index as well as the exact
proposition. -/
theorem exists_matching_reference {scope : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory scope symbols relations) {relation : Relation}
    (proposition : Proposition relation (SymbolScope scope symbols))
    (membership : Encoding.Target.PackedProposition.pack proposition ∈
      Encoding.Target.Theory.propositions theory) :
    ∃ reference : ConstraintRef relations relation,
      theory.propositionAt reference = proposition := by
  obtain ⟨foundRelation, reference, equality⟩ :=
    exists_reference_of_mem theory
      (Encoding.Target.PackedProposition.pack proposition) membership
  cases equality
  exact ⟨reference, rfl⟩

end PackedTheory

namespace Permutation

/-- Pointwise source coordinate selected for every destination constraint of
a packed-proposition permutation. -/
noncomputable def matchingReference {scope : Sig}
    {symbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    (source : Theory scope symbols sourceRelations)
    (target : Theory scope symbols targetRelations)
    (permutation :
      (Encoding.Target.Theory.propositions source).Perm
        (Encoding.Target.Theory.propositions target))
    {relation : Relation} (reference : ConstraintRef targetRelations relation) :
    ConstraintRef sourceRelations relation :=
  Classical.choose (PackedTheory.exists_matching_reference source
    (target.propositionAt reference)
    (permutation.mem_iff.mpr
      (PackedTheory.packed_proposition_mem target reference)))

theorem matchingReference_proposition {scope : Sig}
    {symbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    (source : Theory scope symbols sourceRelations)
    (target : Theory scope symbols targetRelations)
    (permutation :
      (Encoding.Target.Theory.propositions source).Perm
        (Encoding.Target.Theory.propositions target))
    {relation : Relation} (reference : ConstraintRef targetRelations relation) :
    source.propositionAt
        (matchingReference source target permutation reference) =
      target.propositionAt reference :=
  Classical.choose_spec (PackedTheory.exists_matching_reference source
    (target.propositionAt reference)
    (permutation.mem_iff.mpr
      (PackedTheory.packed_proposition_mem target reference)))

/-- Read source evidence variables in an arbitrary sort-preserving target
order. -/
def evidenceOfReferences (symbolScope : Sig)
    {sourceRelations : List Relation} :
    {targetRelations : List Relation} →
      (∀ {relation}, ConstraintRef targetRelations relation →
        ConstraintRef sourceRelations relation) →
      EvidenceArgs
        (Sig.extendMany symbolScope (evidenceKinds sourceRelations))
        targetRelations
  | [], _ => .nil
  | _ :: _, select =>
      .cons (.var ((select .here).toEvidenceBVar symbolScope))
        (evidenceOfReferences symbolScope
          (fun reference => select (.there reference)))

@[simp]
theorem evidenceOfReferences_lookup (symbolScope : Sig)
    {sourceRelations targetRelations : List Relation}
    (select : ∀ {relation}, ConstraintRef targetRelations relation →
      ConstraintRef sourceRelations relation)
    {relation : Relation} (reference : ConstraintRef targetRelations relation) :
    (evidenceOfReferences symbolScope select).lookup reference =
      .var ((select reference).toEvidenceBVar symbolScope) := by
  induction targetRelations with
  | nil => nomatch reference
  | cons newest remaining induction =>
      cases reference with
      | here => rfl
      | there reference =>
          exact induction (fun current => select (.there current)) reference

end Permutation

/-- The raw map induced by a packed-proposition permutation.  All destination
symbols reuse the corresponding opened source symbols. -/
noncomputable def mapOfPermutation {scope : Sig}
    {symbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    (source : Theory scope symbols sourceRelations)
    (target : Theory scope symbols targetRelations)
    (permutation :
      (Encoding.Target.Theory.propositions source).Perm
        (Encoding.Target.Theory.propositions target)) :
    TheoryMap source target where
  symbols := TheoryMap.openedSymbols scope symbols sourceRelations
  evidence := Permutation.evidenceOfReferences (SymbolScope scope symbols)
    (Permutation.matchingReference source target permutation)

private theorem mapOfPermutation_mappedConstraintAt {scope : Sig}
    {symbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    (source : Theory scope symbols sourceRelations)
    (target : Theory scope symbols targetRelations)
    (permutation :
      (Encoding.Target.Theory.propositions source).Perm
        (Encoding.Target.Theory.propositions target))
    {relation : Relation} (reference : ConstraintRef targetRelations relation) :
    (mapOfPermutation source target permutation).mappedConstraintAt reference =
      (target.propositionAt reference).rename
        (Rename.weakenMany (SymbolScope scope symbols)
          (evidenceKinds sourceRelations)) := by
  unfold TheoryMap.mappedConstraintAt TheoryMap.openedTarget mapOfPermutation
  rw [Theory.propositionAt_rename,
    Proposition.rename_instantiateSymbols,
    TheoryMap.identitySymbolSubstitution, Proposition.substitute_ofRename]

/-- Every permutation-induced map is declaratively valid in every ambient
context.  Destination evidence is checked only under the source theory. -/
noncomputable def mapOfPermutation_hasType {scope : Sig}
    {symbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    (context : Ctx scope)
    (source : Theory scope symbols sourceRelations)
    (target : Theory scope symbols targetRelations)
    (permutation :
      (Encoding.Target.Theory.propositions source).Perm
        (Encoding.Target.Theory.propositions target)) :
    TheoryMap.HasType context (mapOfPermutation source target permutation) := by
  apply Theory.SatisfiedBy.ofConstraintAt
  intro relation reference
  change Evidence.Proves (context.extendTheory source)
    ((mapOfPermutation source target permutation).evidenceAt reference)
    ((mapOfPermutation source target permutation).mappedConstraintAt reference)
  change Evidence.Proves (context.extendTheory source)
    ((Permutation.evidenceOfReferences (SymbolScope scope symbols)
      (Permutation.matchingReference source target permutation)).lookup
        reference)
    ((mapOfPermutation source target permutation).mappedConstraintAt reference)
  rw [Permutation.evidenceOfReferences_lookup]
  apply Evidence.Proves.var
  unfold Ctx.extendTheory
  rw [Ctx.lookup_extendTheoryEvidence_constraint]
  rw [mapOfPermutation_mappedConstraintAt]
  rw [Permutation.matchingReference_proposition]

/-- The independent target checker accepts every permutation-induced map. -/
theorem mapOfPermutation_check_isSome {scope : Sig}
    {symbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    (context : Ctx scope)
    (source : Theory scope symbols sourceRelations)
    (target : Theory scope symbols targetRelations)
    (permutation :
      (Encoding.Target.Theory.propositions source).Perm
        (Encoding.Target.Theory.propositions target)) :
    (TheoryMap.check context
      (mapOfPermutation source target permutation)).isSome = true :=
  TheoryMap.check_isSome_iff.mpr
    ⟨mapOfPermutation_hasType context source target permutation⟩

/-- A proposition permutation supplies independently checked maps in both
directions. -/
theorem bidirectional_checked_maps_of_permutation {scope : Sig}
    {symbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    (context : Ctx scope)
    (source : Theory scope symbols sourceRelations)
    (target : Theory scope symbols targetRelations)
    (permutation :
      (Encoding.Target.Theory.propositions source).Perm
        (Encoding.Target.Theory.propositions target)) :
    (TheoryMap.check context
        (mapOfPermutation source target permutation)).isSome = true ∧
      (TheoryMap.check context
        (mapOfPermutation target source permutation.symm)).isSome = true :=
  ⟨mapOfPermutation_check_isSome context source target permutation,
    mapOfPermutation_check_isSome context target source permutation.symm⟩

theorem mapOfPermutation_reuses_opened_symbols {scope : Sig}
    {symbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    (source : Theory scope symbols sourceRelations)
    (target : Theory scope symbols targetRelations)
    (permutation :
      (Encoding.Target.Theory.propositions source).Perm
        (Encoding.Target.Theory.propositions target)) :
    (mapOfPermutation source target permutation).symbols =
      TheoryMap.openedSymbols scope symbols sourceRelations :=
  rfl

end DOTCaptureToManySortedFC.Intersections.TheoryPermutationCoherence
