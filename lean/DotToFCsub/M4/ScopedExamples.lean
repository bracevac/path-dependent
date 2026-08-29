import DotToFCsub.M4.ScopedClosure

/-!
# Scoped M4 closure regressions

These examples exercise actual collectible intersection roots in translated
contexts.  In particular, the shadowing example allocates the same label at
two different variable paths and checks that lookup retains both identities.
-/

namespace DotToFCsub.M4.ScopedExamples

open DotFCI.Source
open SignatureEncoding
open Layout
open StableFragment
open ScopedClosure

def A : Name := 10
def B : Name := 20

def aTop : Ty [] := .member A .bot .top
def aBottom : Ty [] := .member A .bot .bot
def bBottom : Ty [] := .member B .bot .bot

def overlapType : Ty [] := .inter aTop aBottom
def overlapSignature : Signature [] :=
  (Signature.singleton A .bot .top).merge
    (Signature.singleton A .bot .bot)

def overlapCollectible :
    Collectible Ctx.nil overlapType overlapSignature :=
  Collectible.overlappingMembers A .bot .top .bot .bot

def overlapSupport : SupportedSignature overlapSignature :=
  .cons
    (.cons ⟨.bot, .top⟩
      (.cons ⟨.bot, .bot⟩ .nil))
    .nil

def overlapClosed : ClosedSignature overlapSignature :=
  closedSignature overlapSupport

/-- A nonvacuous closed binding: two overlapping occurrences, one name and
four directed constraints. -/
def overlapBinding : ClosedBinding Ctx.nil overlapType where
  signature := overlapSignature
  collectible := overlapCollectible
  closed := overlapClosed

def overlapLayout : Layout.Context (Ctx.nil.snoc overlapType)
    (FCsub.PayloadScope [] 1 4) :=
  overlapBinding.layout Layout.Context.nil

def overlapStableContext : StableContext overlapLayout :=
  .signature .nil overlapBinding

def overlapIndex : EntryIndex 1 4 where
  label := A
  name := ⟨0, by omega⟩
  bounds :=
    [⟨⟨0, by omega⟩, ⟨1, by omega⟩⟩,
      ⟨⟨2, by omega⟩, ⟨3, by omega⟩⟩]

theorem overlapIndex_found :
    allocation? overlapSignature A = some overlapIndex := by
  native_decide

def overlapAllocated : MemberAllocated overlapLayout .here A :=
  .here Layout.Context.nil overlapCollectible overlapClosed A
    overlapIndex overlapIndex_found

theorem overlap_slot_has_all_and_only_two_intervals :
    (MemberSlot.ofIndex [] A overlapIndex).bounds.length =
      (overlapSignature.constraintsAt A).length :=
  slot_bounds_exact [] overlapSignature overlapCollectible.normalized A
    overlapIndex overlapIndex_found

theorem overlap_slot_has_two_bound_pairs :
    (MemberSlot.ofIndex [] A overlapIndex).bounds.length = 2 := by
  native_decide

/-! ## Proof-relevant occurrences at the newest variable path -/

def overlapSignatureW : Signature ([] ▹ .term) :=
  (Signature.singleton A .bot .top).merge
    (Signature.singleton A .bot .bot)

def overlapCollectibleW : Collectible (Ctx.nil.snoc overlapType)
    (overlapType.weaken (kind := .term)) overlapSignatureW :=
  .inter (.member .bot .top) (.member .bot .bot)

def overlapRoot : SignatureRoot (Ctx.nil.snoc overlapType)
    (.here : DotFC.BVar ([] ▹ .term) .term) overlapSignatureW where
  declared := overlapType.weaken
  binding := .here
  collectible := overlapCollectibleW

def overlapLeftOccurrence : MemberOccurrence (Ctx.nil.snoc overlapType)
    (.here : DotFC.BVar ([] ▹ .term) .term) A .bot .top where
  signature := overlapSignatureW
  root := overlapRoot
  member := .left .here

def overlapRightOccurrence : MemberOccurrence (Ctx.nil.snoc overlapType)
    (.here : DotFC.BVar ([] ▹ .term) .term) A .bot .bot where
  signature := overlapSignatureW
  root := overlapRoot
  member := .right .here

noncomputable def overlapLeftAllocatedFromOccurrence :
    MemberAllocated overlapLayout .here A :=
  newestOccurrenceAllocated Layout.Context.nil overlapCollectible
    overlapClosed A overlapLeftOccurrence

noncomputable def overlapRightAllocatedFromOccurrence :
    MemberAllocated overlapLayout .here A :=
  newestOccurrenceAllocated Layout.Context.nil overlapCollectible
    overlapClosed A overlapRightOccurrence

/-- Different structural occurrences compile to the very same complete slot. -/
theorem overlapping_occurrences_share_slot :
    overlapLeftAllocatedFromOccurrence.compile.slot =
      overlapRightAllocatedFromOccurrence.compile.slot :=
  MemberLookup.functional _ _

theorem overlapping_occurrences_share_exact_name :
    overlapLeftAllocatedFromOccurrence.compile.slot.name =
      overlapRightAllocatedFromOccurrence.compile.slot.name :=
  MemberLookup.name_unique _ _

def firstInterval : Interval [] := ⟨.bot, .top⟩

theorem firstInterval_mem :
    firstInterval ∈ overlapSignature.constraintsAt A := by
  native_decide

/-- The generic occurrence coercion is declaratively typed, not merely
accepted in the closed executable example. -/
noncomputable def firstOccurrenceProjectionTyped :
    let source := (encodingAt overlapSupport []).telescope
    let bound := occurrenceBound overlapSignature
      overlapCollectible.normalized A firstInterval firstInterval_mem
      overlapIndex overlapIndex_found
    FCsub.TelMor.HasType FCsub.Ctx.nil (boundMorphism source bound)
      source (boundView source bound) :=
  occurrenceMorphism_hasType [] FCsub.Ctx.nil overlapSignature
    overlapSupport overlapCollectible.normalized A firstInterval
    firstInterval_mem overlapIndex overlapIndex_found

/-! ## Same-label shadowing at distinct variable paths -/

def shadowType : Ty ([] ▹ .term) := .member A .bot .top
def shadowSignature : Signature ([] ▹ .term) :=
  Signature.singleton A .bot .top

def shadowCollectible : Collectible (Ctx.nil.snoc overlapType)
    shadowType shadowSignature :=
  .member .bot .top

def shadowSupport : SupportedSignature shadowSignature :=
  .cons (.cons ⟨.bot, .top⟩ .nil) .nil

def shadowClosed : ClosedSignature shadowSignature :=
  closedSignature shadowSupport

def shadowLayout := Layout.Context.signature shadowSignature overlapLayout
  shadowCollectible shadowClosed

def shadowIndex : EntryIndex 1 2 where
  label := A
  name := ⟨0, by omega⟩
  bounds := [⟨⟨0, by omega⟩, ⟨1, by omega⟩⟩]

theorem shadowIndex_found :
    allocation? shadowSignature A = some shadowIndex := by
  native_decide

def shadowNewestAllocated : MemberAllocated shadowLayout .here A :=
  .here overlapLayout shadowCollectible shadowClosed A
    shadowIndex shadowIndex_found

def shadowOlderAllocated : MemberAllocated shadowLayout (.there .here) A :=
  .signatureThere overlapAllocated shadowCollectible shadowClosed

theorem shadow_newest_lookup_succeeds :
    shadowLayout.slot? .here A =
      some shadowNewestAllocated.compile.slot :=
  shadowNewestAllocated.compiles

theorem shadow_older_lookup_succeeds :
    shadowLayout.slot? (.there .here) A =
      some shadowOlderAllocated.compile.slot :=
  shadowOlderAllocated.compiles

/-- Extending by a same-label signature weakens the older slot; it does not
overwrite or reallocate it. -/
theorem shadow_older_slot_is_exact_weakening :
    shadowOlderAllocated.compile.slot =
      overlapAllocated.compile.slot.rename
        (signatureExtensionRename (FCsub.PayloadScope [] 1 4)
          shadowSignature) := rfl

/-- The key includes the variable path, so same-label shadowing retains two
different static identities. -/
theorem shadow_same_label_distinct_paths_have_distinct_names :
    shadowNewestAllocated.compile.slot.name ≠
      shadowOlderAllocated.compile.slot.name := by
  native_decide

theorem shadow_same_label_distinct_paths_have_distinct_payloads :
    shadowNewestAllocated.compile.slot.payload ≠
      shadowOlderAllocated.compile.slot.payload := by
  native_decide

/-! ## Order and association induce target telescope isomorphisms -/

def aTopSignature : Signature [] := Signature.singleton A .bot .top
def aBottomSignature : Signature [] := Signature.singleton A .bot .bot
def bBottomSignature : Signature [] := Signature.singleton B .bot .bot

def disjointLeft : Signature [] := aTopSignature.merge bBottomSignature
def disjointRight : Signature [] := bBottomSignature.merge aTopSignature

def disjointLeftSupport : SupportedSignature disjointLeft :=
  .cons (.cons ⟨.bot, .top⟩ .nil)
    (.cons (.cons ⟨.bot, .bot⟩ .nil) .nil)

def disjointRightSupport : SupportedSignature disjointRight :=
  .cons (.cons ⟨.bot, .top⟩ .nil)
    (.cons (.cons ⟨.bot, .bot⟩ .nil) .nil)

theorem disjoint_source_order_equiv : disjointLeft ≈ₛ disjointRight :=
  Signature.merge_comm aTopSignature bBottomSignature
    (Signature.singleton_normalized A .bot .top)
    (Signature.singleton_normalized B .bot .bot)

theorem disjoint_target_telescope_eq :
    (encodingAt disjointLeftSupport []).telescope =
      (encodingAt disjointRightSupport []).telescope := by
  native_decide

def disjointTargetIso : TelescopeIsomorphism
    (encodingAt disjointLeftSupport []).telescope
    (encodingAt disjointRightSupport []).telescope :=
  TelescopeIsomorphism.ofEq disjoint_target_telescope_eq

noncomputable def disjointTargetIso_forward_typed :
    FCsub.TelMor.HasType FCsub.Ctx.nil disjointTargetIso.forward
      (encodingAt disjointLeftSupport []).telescope
      (encodingAt disjointRightSupport []).telescope :=
  disjointTargetIso.forward_hasType FCsub.Ctx.nil

theorem disjointTargetIso_reuses_exact_name_vector :
    disjointTargetIso.forward =
      .map (encodingAt disjointLeftSupport []).telescope
        (encodingAt disjointRightSupport []).telescope
        (FCsub.TypeArgs.boundNames [] 2 4)
        (FCsub.LeArgs.selectAssumptions [] 2 4
          disjointTargetIso.permutation.forward) :=
  disjointTargetIso.forward_preserves_names

def associatedLeft : Signature [] :=
  (aTopSignature.merge aBottomSignature).merge bBottomSignature
def associatedRight : Signature [] :=
  aTopSignature.merge (aBottomSignature.merge bBottomSignature)

def associatedLeftSupport : SupportedSignature associatedLeft :=
  .cons
    (.cons ⟨.bot, .top⟩ (.cons ⟨.bot, .bot⟩ .nil))
    (.cons (.cons ⟨.bot, .bot⟩ .nil) .nil)

def associatedRightSupport : SupportedSignature associatedRight :=
  .cons
    (.cons ⟨.bot, .top⟩ (.cons ⟨.bot, .bot⟩ .nil))
    (.cons (.cons ⟨.bot, .bot⟩ .nil) .nil)

theorem associated_source_equiv : associatedLeft ≈ₛ associatedRight :=
  Signature.merge_assoc aTopSignature aBottomSignature bBottomSignature
    (Signature.singleton_normalized A .bot .top)
    (Signature.singleton_normalized A .bot .bot)
    (Signature.singleton_normalized B .bot .bot)

theorem associated_target_telescope_eq :
    (encodingAt associatedLeftSupport []).telescope =
      (encodingAt associatedRightSupport []).telescope := by
  native_decide

def associatedTargetIso : TelescopeIsomorphism
    (encodingAt associatedLeftSupport []).telescope
    (encodingAt associatedRightSupport []).telescope :=
  TelescopeIsomorphism.ofEq associated_target_telescope_eq

noncomputable def associatedTargetIso_roundTrip_typed :
    FCsub.TelMor.HasType FCsub.Ctx.nil
      (FCsub.TelMor.permutationRoundTrip associatedTargetIso.permutation)
      (encodingAt associatedLeftSupport []).telescope
      (encodingAt associatedLeftSupport []).telescope :=
  FCsub.TelMor.HasType.permutationRoundTrip FCsub.Ctx.nil
    associatedTargetIso.permutation

end DotToFCsub.M4.ScopedExamples
