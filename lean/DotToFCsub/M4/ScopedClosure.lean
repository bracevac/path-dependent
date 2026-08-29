import DotToFCsub.M4.Translation
import DotToFCsub.M4.SignatureMorphisms

/-!
# Scoped closure of the acyclic M4 bridge

This file closes the proof-producing boundary used by the variable-path M4
slice. Closed bounds are witnessed explicitly, successful signature
encodings are constructed (rather than postulated), and source member
occurrences are connected to the structural layout allocation judgment.
-/

namespace DotToFCsub.M4.ScopedClosure

open DotFCI.Source
open SignatureEncoding
open Layout

/-! ## Constructive closed-signature support -/

/-- Evidence that a source bound belongs to the currently supported closed
`top`/`bot` grammar. Its index prevents a support proof from being reused for
an unrelated bound. -/
inductive ClosedBound : {scope : DotFC.Sig} → Ty scope → Type where
  | top : ClosedBound .top
  | bot : ClosedBound .bot

namespace ClosedBound

/-- Total translation selected by a closed-bound support proof. -/
def translate {sourceScope : DotFC.Sig} {type : Ty sourceScope}
    (support : ClosedBound type) (targetScope : FCsub.Sig) :
    FCsub.Ty targetScope :=
  match support with
  | .top => .top
  | .bot => .bot

/-- The executable partial translator agrees with the constructive proof. -/
theorem agrees {sourceScope : DotFC.Sig} {type : Ty sourceScope}
    (support : ClosedBound type) (targetScope : FCsub.Sig) :
    closedBoundAt? (targetScope := targetScope) type =
      some (support.translate targetScope) := by
  cases support <;> rfl

end ClosedBound

/-- Both endpoints of one collected interval are in the supported grammar. -/
structure SupportedInterval {scope : DotFC.Sig}
    (interval : Interval scope) : Type where
  lower : ClosedBound interval.lower
  upper : ClosedBound interval.upper

/-- A universe-polymorphic, proof-relevant pointwise list predicate. -/
inductive All {α : Type} (predicate : α → Type) : List α → Type where
  | nil : All predicate []
  | cons {head : α} {tail : List α} :
      predicate head → All predicate tail → All predicate (head :: tail)

/-- Pointwise support for all interval occurrences of one entry. -/
abbrev SupportedEntry {scope : DotFC.Sig} (entry : SignatureEntry scope) :=
  All SupportedInterval entry.intervals

/-- Pointwise support for every interval of a collected signature. -/
abbrev SupportedSignature {scope : DotFC.Sig} (signature : Signature scope) :=
  All SupportedEntry signature.entries

/-- Construct the exact interval telescope from support evidence. -/
def intervalTelescope {sourceScope : DotFC.Sig} {targetScope : FCsub.Sig}
    {names : Nat}
    (name : FCsub.BVar (FCsub.TypeScope targetScope names) .type) :
    (intervals : List (Interval sourceScope)) →
      All SupportedInterval intervals →
      FCsub.Telescope targetScope names (intervalConstraintCount intervals)
  | [], .nil => .nil
  | _interval :: remaining, .cons support remainingSupport =>
      .snoc
        (.snoc (intervalTelescope name remaining remainingSupport)
          (.inclusion (.tvar name) (support.upper.translate _)))
        (.inclusion (support.lower.translate _) (.tvar name))

/-- Construction is extensionally the existing option-valued interval
compiler, so downstream code consumes exactly one encoding API. -/
theorem intervalTelescope_agrees {sourceScope : DotFC.Sig}
    {targetScope : FCsub.Sig} {names : Nat}
    (name : FCsub.BVar (FCsub.TypeScope targetScope names) .type)
    (intervals : List (Interval sourceScope))
    (support : All SupportedInterval intervals) :
    intervalTelescopeAt? name intervals =
      some (intervalTelescope name intervals support) := by
  induction support with
  | nil => rfl
  | @cons interval remaining intervalSupport remainingSupport induction =>
      simp only [intervalTelescopeAt?, intervalTelescope]
      rw [induction, intervalSupport.lower.agrees,
        intervalSupport.upper.agrees]
      rfl

/-- Construct the complete names-first telescope. All names are allocated
before any interval propositions, including in nonempty ambient scopes. -/
def signatureTelescope {sourceScope : DotFC.Sig}
    (targetScope : FCsub.Sig) :
    (entries : List (SignatureEntry sourceScope)) →
      All SupportedEntry entries →
      FCsub.Telescope targetScope entries.length
        (signatureConstraintCount entries)
  | [], .nil => .nil
  | entry :: remaining, .cons entrySupport remainingSupport =>
      let tail := signatureTelescope targetScope remaining remainingSupport
      let current := intervalTelescope
        (targetScope := targetScope)
        (names := remaining.length + 1)
        (FCsub.BVar.here : FCsub.BVar
          (FCsub.TypeScope targetScope (remaining.length + 1)) .type)
        entry.intervals entrySupport
      (tail.reindexNames (FCsub.Rename.succ (kind := .type))).append current

/-- The constructive whole-signature telescope is the result returned by the
existing executable compiler. -/
theorem signatureTelescope_agrees {sourceScope : DotFC.Sig}
    (targetScope : FCsub.Sig)
    (entries : List (SignatureEntry sourceScope))
    (support : All SupportedEntry entries) :
    signatureTelescopeAt? (targetScope := targetScope) entries =
      some (signatureTelescope targetScope entries support) := by
  induction support with
  | nil => rfl
  | @cons entry remaining entrySupport remainingSupport induction =>
      simp only [signatureTelescopeAt?, signatureTelescope]
      rw [induction, intervalTelescope_agrees]
      rfl

/-- A supported signature has a total scope-polymorphic M4 encoding. -/
def encodingAt {sourceScope : DotFC.Sig} {signature : Signature sourceScope}
    (support : SupportedSignature signature) (targetScope : FCsub.Sig) :
    EncodingAt targetScope signature :=
  ⟨signatureTelescope targetScope signature.entries support⟩

/-- Construct the `ClosedSignature` boundary demanded by layout extension.
No choice or classical extraction is involved. -/
def closedSignature {sourceScope : DotFC.Sig}
    {signature : Signature sourceScope}
    (support : SupportedSignature signature) : ClosedSignature signature where
  encoding := encodingAt support
  agrees := fun targetScope => by
    simp only [encodeAt?, encodingAt]
    rw [signatureTelescope_agrees]
    rfl

/-! ## Allocation completeness -/

/-- Allocation metadata has exactly the source entry labels, in the same
canonical order. -/
@[simp]
theorem entryIndex_shift_label {names constraints : Nat}
    (index : EntryIndex names constraints) (additional : Nat) :
    (index.shift additional).label = index.label := rfl

theorem shiftedEntryLabels {names constraints : Nat}
    (indices : List (EntryIndex names constraints)) (additional : Nat) :
    (indices.map fun index => index.shift additional).map EntryIndex.label =
      indices.map EntryIndex.label := by
  induction indices with
  | nil => rfl
  | cons index remaining induction =>
      simp only [List.map_cons, entryIndex_shift_label, induction]

theorem allocations_labels {sourceScope : DotFC.Sig}
    (entries : List (SignatureEntry sourceScope)) :
    (allocations entries).map EntryIndex.label =
      entries.map SignatureEntry.label := by
  induction entries with
  | nil => rfl
  | cons entry remaining induction =>
      simp only [allocations, List.map_cons]
      congr 1
      exact (shiftedEntryLabels (allocations remaining)
        (intervalConstraintCount entry.intervals)).trans induction

/-- Any interval occurrence proves that its label is in the signature
support. This direction does not require normalization. -/
theorem label_mem_of_interval_mem {sourceScope : DotFC.Sig}
    (signature : Signature sourceScope) (label : Name)
    {interval : Interval sourceScope}
    (membership : interval ∈ signature.constraintsAt label) :
    label ∈ signature.labels := by
  cases signature with
  | mk entries =>
      change interval ∈ Signature.constraintsAtEntries entries label at membership
      change label ∈ entries.map SignatureEntry.label
      induction entries with
      | nil => simp at membership
      | cons entry remaining induction =>
          simp only [Signature.constraintsAtEntries,
            List.mem_append] at membership
          rcases membership with current | older
          · by_cases same : entry.label = label
            · exact List.mem_cons.mpr (Or.inl same.symm)
            · simp [SignatureEntry.constraintsAt, same] at current
          · exact List.mem_cons.mpr (Or.inr (induction older))

/-- Membership in the source label support makes executable allocation
search succeed. -/
theorem allocation_isSome_of_label_mem {sourceScope : DotFC.Sig}
    (signature : Signature sourceScope) (label : Name)
    (membership : label ∈ signature.labels) :
    (allocation? signature label).isSome = true := by
  rw [allocation?, List.find?_isSome]
  have allocationMembership :
      label ∈ (allocations signature.entries).map EntryIndex.label := by
    rw [allocations_labels]
    exact membership
  obtain ⟨index, indexMem, indexLabel⟩ := List.mem_map.mp allocationMembership
  exact ⟨index, indexMem, by simp [indexLabel]⟩

/-- Constructive result of the canonical label allocator. -/
structure AllocationResult {sourceScope : DotFC.Sig}
    (signature : Signature sourceScope) (label : Name) : Type where
  index : EntryIndex signature.entries.length
    (signatureConstraintCount signature.entries)
  found : allocation? signature label = some index

/-- Recover the exact canonical index selected by executable lookup. -/
noncomputable def allocationOfLabel {sourceScope : DotFC.Sig}
    (signature : Signature sourceScope) (label : Name)
    (membership : label ∈ signature.labels) :
    AllocationResult signature label := by
  have success := allocation_isSome_of_label_mem signature label membership
  cases found : allocation? signature label with
  | none => simp [found] at success
  | some index => exact ⟨index, found⟩

/-! ## Slot bounds are exactly source intervals -/

@[simp]
theorem entryIndex_shift_bounds_length {names constraints : Nat}
    (index : EntryIndex names constraints) (additional : Nat) :
    (index.shift additional).bounds.length = index.bounds.length := by
  simp [EntryIndex.shift]

/-- Every generated allocation still describes one original entry. Besides
the label, its bound vector retains exactly the entry's interval arity. -/
theorem allocation_mem_describes {sourceScope : DotFC.Sig}
    (entries : List (SignatureEntry sourceScope))
    (index : EntryIndex entries.length (signatureConstraintCount entries))
    (membership : index ∈ allocations entries) :
    ∃ entry, entry ∈ entries ∧ index.label = entry.label ∧
      index.bounds.length = entry.intervals.length := by
  induction entries with
  | nil => cases membership
  | cons head remaining induction =>
      simp only [allocations, List.mem_cons] at membership
      rcases membership with newest | older
      · subst index
        exact ⟨head, .head _, rfl,
          intervalIndices_length head.intervals
            (signatureConstraintCount remaining)⟩
      · obtain ⟨oldIndex, oldMembership, shifted⟩ :=
          List.mem_map.mp older
        obtain ⟨entry, entryMembership, labelEq, boundsEq⟩ :=
          induction oldIndex oldMembership
        subst index
        exact ⟨entry, .tail head entryMembership,
          labelEq, by
            change (oldIndex.bounds.map fun bound =>
              bound.shiftRight
                (intervalConstraintCount head.intervals)).length = _
            rw [List.length_map]
            exact boundsEq⟩

/-- Under unique labels, lookup at an entry's label returns exactly that
entry's full interval list and no intervals from another entry. -/
theorem constraintsAtEntries_eq_of_mem_nodup {sourceScope : DotFC.Sig}
    (entries : List (SignatureEntry sourceScope))
    (unique : (entries.map SignatureEntry.label).Nodup)
    (entry : SignatureEntry sourceScope) (membership : entry ∈ entries) :
    Signature.constraintsAtEntries entries entry.label = entry.intervals := by
  induction entries with
  | nil => simp at membership
  | cons head remaining induction =>
      change (head.label :: remaining.map SignatureEntry.label).Nodup at unique
      rw [List.nodup_cons] at unique
      rcases unique with ⟨headFresh, remainingUnique⟩
      simp only [List.mem_cons] at membership
      rcases membership with newest | older
      · subst entry
        have absent : ∀ current ∈ remaining,
            current.label ≠ head.label := by
          intro current currentMem same
          apply headFresh
          exact List.mem_map.mpr ⟨current, currentMem, same⟩
        have absentEq : Signature.constraintsAtEntries remaining head.label = [] :=
          Signature.constraintsAt_eq_nil_of_forall_ne
            remaining head.label absent
        rw [Signature.constraintsAtEntries, absentEq]
        simp [SignatureEntry.constraintsAt]
      · have different : head.label ≠ entry.label := by
          intro same
          apply headFresh
          exact List.mem_map.mpr ⟨entry, older, same.symm⟩
        rw [Signature.constraintsAtEntries]
        simp only [SignatureEntry.constraintsAt, different, ↓reduceIte,
          List.nil_append]
        exact induction remainingUnique older

/-- A successful canonical allocation contains one and only one bound pair
for every interval accumulated at its label. -/
theorem allocation_bounds_exact {sourceScope : DotFC.Sig}
    (signature : Signature sourceScope) (normalized : signature.Normalized)
    (label : Name)
    (index : EntryIndex signature.entries.length
      (signatureConstraintCount signature.entries))
    (found : allocation? signature label = some index) :
    index.bounds.length = (signature.constraintsAt label).length := by
  have indexMem : index ∈ allocations signature.entries := by
    exact List.mem_of_find?_eq_some found
  obtain ⟨entry, entryMem, indexLabel, boundsLength⟩ :=
    allocation_mem_describes signature.entries index indexMem
  have selected : index.label = label := by
    have predicate := List.find?_some found
    simpa using predicate
  have entryLabel : entry.label = label := indexLabel.symm.trans selected
  have exactIntervals := constraintsAtEntries_eq_of_mem_nodup
    signature.entries normalized.labels_nodup entry entryMem
  change index.bounds.length =
    (Signature.constraintsAtEntries signature.entries label).length
  rw [← entryLabel, exactIntervals]
  exact boundsLength

/-- Materializing an allocation as a payload slot preserves the exact
all-and-only interval count. -/
theorem slot_bounds_exact {sourceScope : DotFC.Sig}
    (targetScope : FCsub.Sig) (signature : Signature sourceScope)
    (normalized : signature.Normalized) (label : Name)
    (index : EntryIndex signature.entries.length
      (signatureConstraintCount signature.entries))
    (found : allocation? signature label = some index) :
    (MemberSlot.ofIndex targetScope label index).bounds.length =
      (signature.constraintsAt label).length := by
  rw [MemberSlot.ofIndex_bounds_length]
  exact allocation_bounds_exact signature normalized label index found

/-- A small proof-relevant bijection type, kept local to the Lean-only bridge. -/
structure Bijection (left : Type) (right : Type) where
  toFun : left → right
  invFun : right → left
  left_inv : ∀ value, invFun (toFun value) = value
  right_inv : ∀ value, toFun (invFun value) = value

/-- Finite positions witness the stronger all-and-only formulation: every
source interval index selects one slot bound and every slot bound index
selects one source interval. -/
def finEquivOfEq {left right : Nat} (equality : left = right) :
    Bijection (Fin left) (Fin right) where
  toFun := Fin.cast equality
  invFun := Fin.cast equality.symm
  left_inv := by
    subst right
    intro index
    rfl
  right_inv := by
    subst right
    intro index
    rfl

def slotIntervalPositions {sourceScope : DotFC.Sig}
    (targetScope : FCsub.Sig) (signature : Signature sourceScope)
    (normalized : signature.Normalized) (label : Name)
    (index : EntryIndex signature.entries.length
      (signatureConstraintCount signature.entries))
    (found : allocation? signature label = some index) :
    Bijection (Fin (MemberSlot.ofIndex targetScope label index).bounds.length)
      (Fin (signature.constraintsAt label).length) :=
  finEquivOfEq (slot_bounds_exact targetScope signature normalized
    label index found)

/-! ## Generic per-occurrence FCsub projections -/

/-- Select the lower and upper positions of one interval pair. -/
def selectBound {constraints : Nat} (bound : BoundIndex constraints) :
    Fin 2 → Fin constraints
  | ⟨0, _⟩ => bound.lower
  | ⟨1, _⟩ => bound.upper
  | ⟨value + 2, smaller⟩ => by omega

/-- The two-constraint view of one occurrence is defined from the complete
source telescope itself; no constraint is reconstructed or synthesized. -/
def boundView {scope : FCsub.Sig} {names constraints : Nat}
    (source : FCsub.Telescope scope names constraints)
    (bound : BoundIndex constraints) : FCsub.Telescope scope names 2 :=
  telescopeOfList
    [source.get bound.lower, source.get bound.upper]

/-- Selecting a bound pair is a structural telescope projection. -/
def boundProjection {scope : FCsub.Sig} {names constraints : Nat}
    (source : FCsub.Telescope scope names constraints)
    (bound : BoundIndex constraints) :
    FCsub.Telescope.Projection source (boundView source bound) where
  constraint := selectBound bound
  preserves := by
    intro index
    rcases index with ⟨value, smaller⟩
    cases value with
    | zero => rfl
    | succ value =>
        cases value with
        | zero => rfl
        | succ value => omega

/-- The explicit coercion witnessing one member occurrence's interface view. -/
def boundMorphism {scope : FCsub.Sig} {names constraints : Nat}
    (source : FCsub.Telescope scope names constraints)
    (bound : BoundIndex constraints) :
    FCsub.TelMor scope names constraints names 2 :=
  FCsub.TelMor.ofProjection (boundProjection source bound)

/-- Every occurrence projection is typed in an arbitrary translated context. -/
noncomputable def boundMorphism_hasType {scope : FCsub.Sig}
    (context : FCsub.Ctx scope) {names constraints : Nat}
    (source : FCsub.Telescope scope names constraints)
    (bound : BoundIndex constraints) :
    FCsub.TelMor.HasType context (boundMorphism source bound)
      source (boundView source bound) :=
  FCsub.TelMor.HasType.ofProjection context (boundProjection source bound)

/-- The projection passes the complete source name vector verbatim. -/
theorem boundMorphism_preserves_names {scope : FCsub.Sig}
    {names constraints : Nat}
    (source : FCsub.Telescope scope names constraints)
    (bound : BoundIndex constraints) :
    boundMorphism source bound =
      .map source (boundView source bound)
        (FCsub.TypeArgs.boundNames scope names constraints)
        (FCsub.LeArgs.selectAssumptions scope names constraints
          (selectBound bound)) := rfl

/-- In particular, an allocated member's name argument is the exact source
`BVar` at the allocation index. -/
theorem boundMorphism_reuses_allocated_name {scope : FCsub.Sig}
    {names constraints : Nat}
    (_source : FCsub.Telescope scope names constraints)
    (_bound : BoundIndex constraints)
    (index : EntryIndex names constraints) :
    (FCsub.TypeArgs.boundNames scope names constraints).get index.name =
      .tvar
        ((FCsub.Rename.weakenN (.evidence .inclusion) constraints).var
          (FCsub.BVar.bound names index.name)) := by
  simp [FCsub.TypeArgs.boundNames]

/-- Pick the exact ordinal of a proof-relevant source occurrence. -/
noncomputable def intervalPosition {sourceScope : DotFC.Sig}
    (signature : Signature sourceScope) (label : Name)
    (interval : Interval sourceScope)
    (membership : interval ∈ signature.constraintsAt label) :
    Fin (signature.constraintsAt label).length :=
  Classical.choose (List.mem_iff_get.mp membership)

@[simp]
theorem intervalPosition_get {sourceScope : DotFC.Sig}
    (signature : Signature sourceScope) (label : Name)
    (interval : Interval sourceScope)
    (membership : interval ∈ signature.constraintsAt label) :
    (signature.constraintsAt label).get
      (intervalPosition signature label interval membership) = interval :=
  Classical.choose_spec (List.mem_iff_get.mp membership)

/-- Recover the canonical target bound pair corresponding to an exact source
interval occurrence. Repeated equal intervals remain distinguishable through
the chosen finite position. -/
noncomputable def occurrenceBound {sourceScope : DotFC.Sig}
    (signature : Signature sourceScope) (normalized : signature.Normalized)
    (label : Name) (interval : Interval sourceScope)
    (membership : interval ∈ signature.constraintsAt label)
    (index : EntryIndex signature.entries.length
      (signatureConstraintCount signature.entries))
    (found : allocation? signature label = some index) :
    BoundIndex (signatureConstraintCount signature.entries) :=
  let positions := finEquivOfEq
    (allocation_bounds_exact signature normalized label index found)
  index.bounds.get
    (positions.invFun (intervalPosition signature label interval membership))

/-- The resulting coercion is the generic typed FCsub projection for that
source occurrence, while retaining the signature's exact shared name block. -/
noncomputable def occurrenceMorphism_hasType {sourceScope : DotFC.Sig}
    (targetScope : FCsub.Sig) (targetContext : FCsub.Ctx targetScope)
    (signature : Signature sourceScope) (support : SupportedSignature signature)
    (normalized : signature.Normalized) (label : Name)
    (interval : Interval sourceScope)
    (membership : interval ∈ signature.constraintsAt label)
    (index : EntryIndex signature.entries.length
      (signatureConstraintCount signature.entries))
    (found : allocation? signature label = some index) :
    let source := (encodingAt support targetScope).telescope
    let bound := occurrenceBound signature normalized label interval
      membership index found
    FCsub.TelMor.HasType targetContext (boundMorphism source bound)
      source (boundView source bound) :=
  boundMorphism_hasType targetContext _ _

/-! ## Target telescope isomorphisms -/

/-- An isomorphism between two target telescopes is an invertible structural
constraint permutation. Its shared `names` index makes preservation of the
simultaneous abstract-name block intrinsic. -/
structure TelescopeIsomorphism {scope : FCsub.Sig}
    {names constraints : Nat}
    (source target : FCsub.Telescope scope names constraints) : Type where
  permutation : FCsub.Telescope.Permutation source target

namespace TelescopeIsomorphism

def forward {scope : FCsub.Sig} {names constraints : Nat}
    {source target : FCsub.Telescope scope names constraints}
    (isomorphism : TelescopeIsomorphism source target) :
    FCsub.TelMor scope names constraints names constraints :=
  FCsub.TelMor.ofPermutation isomorphism.permutation

def backward {scope : FCsub.Sig} {names constraints : Nat}
    {source target : FCsub.Telescope scope names constraints}
    (isomorphism : TelescopeIsomorphism source target) :
    FCsub.TelMor scope names constraints names constraints :=
  FCsub.TelMor.ofPermutation isomorphism.permutation.symm

noncomputable def forward_hasType {scope : FCsub.Sig}
    (context : FCsub.Ctx scope) {names constraints : Nat}
    {source target : FCsub.Telescope scope names constraints}
    (isomorphism : TelescopeIsomorphism source target) :
    FCsub.TelMor.HasType context isomorphism.forward source target :=
  FCsub.TelMor.HasType.ofPermutation context isomorphism.permutation

noncomputable def backward_hasType {scope : FCsub.Sig}
    (context : FCsub.Ctx scope) {names constraints : Nat}
    {source target : FCsub.Telescope scope names constraints}
    (isomorphism : TelescopeIsomorphism source target) :
    FCsub.TelMor.HasType context isomorphism.backward target source :=
  FCsub.TelMor.HasType.ofPermutation context isomorphism.permutation.symm

/-- Both directions pass the exact source name vector, never fresh names. -/
theorem forward_preserves_names {scope : FCsub.Sig}
    {names constraints : Nat}
    {source target : FCsub.Telescope scope names constraints}
    (isomorphism : TelescopeIsomorphism source target) :
    isomorphism.forward =
      .map source target
        (FCsub.TypeArgs.boundNames scope names constraints)
        (FCsub.LeArgs.selectAssumptions scope names constraints
          isomorphism.permutation.forward) := rfl

/-- Definitional telescope equality yields the identity target isomorphism.
Concrete canonical order/association laws use this after collection. -/
def ofEq {scope : FCsub.Sig} {names constraints : Nat}
    {source target : FCsub.Telescope scope names constraints}
    (equality : source = target) : TelescopeIsomorphism source target := by
  subst target
  exact ⟨{
    forward := fun index => index
    backward := fun index => index
    forward_backward := fun _ => rfl
    backward_forward := fun _ => rfl
    preserves := fun _ => rfl
  }⟩

end TelescopeIsomorphism

/-- Every structural source occurrence under the newly opened signature root
allocates a target slot. The occurrence proof supplies label support; the
layout certificate supplies the one shared root package. -/
noncomputable def newestMemberAllocated
    {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
    {targetScope : FCsub.Sig} (outer : Layout.Context sourceContext targetScope)
    {type : Ty sourceScope} {signature : Signature sourceScope}
    (collectible : Collectible sourceContext type signature)
    (closed : ClosedSignature signature) (label : Name)
    {lower upper : Ty sourceScope}
    (member : MemberAt type label lower upper) :
    MemberAllocated (Layout.Context.signature signature outer collectible closed)
      .here label := by
  have intervalMem := collectible.memberInterval_mem member
  have labelMem := label_mem_of_interval_mem signature label intervalMem
  let result := allocationOfLabel signature label labelMem
  exact .here outer collectible closed label result.index result.found

@[simp]
theorem signature_labels_rename {source target : DotFC.Sig}
    (signature : Signature source) (rho : DotFC.Rename source target) :
    (signature.rename rho).labels = signature.labels := by
  cases signature with
  | mk entries =>
      simp [Signature.rename, Signature.labels,
        SignatureEntry.rename]

/-- `MemberOccurrence` form of `newestMemberAllocated`. The occurrence lives
in the extended source context and its `.here` lookup forces its root to be
the weakening of the declaration represented by the layout. Collection
naturality then identifies its renamed signature with the package signature. -/
noncomputable def newestOccurrenceAllocated
    {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
    {targetScope : FCsub.Sig} (outer : Layout.Context sourceContext targetScope)
    {type : Ty sourceScope} {signature : Signature sourceScope}
    (collectible : Collectible sourceContext type signature)
    (closed : ClosedSignature signature) (label : Name)
    {lower upper : Ty (sourceScope ▹ .term)}
    (occurrence : MemberOccurrence (sourceContext.snoc type)
      (.here : DotFC.BVar (sourceScope ▹ .term) .term) label lower upper) :
    MemberAllocated (Layout.Context.signature signature outer collectible closed)
      .here label := by
  rcases occurrence with ⟨occurrenceSignature, root, member⟩
  rcases root with ⟨declared, binding, occurrenceCollectible⟩
  cases binding
  have renamedCollected :
      collect? (type.weaken (kind := .term)) =
        some (signature.rename (DotFC.Rename.succ (k := .term))) := by
    change collect? (type.rename (DotFC.Rename.succ (k := .term))) = _
    rw [collect?_rename, collectible.collected]
    rfl
  have occurrenceCollected := occurrenceCollectible.collected
  rw [renamedCollected] at occurrenceCollected
  have signatureEq : occurrenceSignature =
      signature.rename (DotFC.Rename.succ (k := .term)) := by
    exact Option.some.inj occurrenceCollected.symm
  have intervalMem := occurrenceCollectible.memberInterval_mem member
  have labelMem := label_mem_of_interval_mem occurrenceSignature label intervalMem
  rw [signatureEq, signature_labels_rename] at labelMem
  let result := allocationOfLabel signature label labelMem
  exact .here outer collectible closed label result.index result.found

/-! ## Arbitrary context weakening -/

/-- A path-preserving extension from one layout to a later layout. Each
constructor records the exact target weakening performed by that layout
extension. -/
inductive PathWeakening :
    {sourceScope : DotFC.Sig} → {sourceContext : Ctx sourceScope} →
    {targetScope : FCsub.Sig} →
    (outer : Layout.Context sourceContext targetScope) →
    (path : DotFC.BVar sourceScope .term) →
    {laterSourceScope : DotFC.Sig} → {laterContext : Ctx laterSourceScope} →
    {laterTargetScope : FCsub.Sig} →
    (later : Layout.Context laterContext laterTargetScope) →
    DotFC.BVar laterSourceScope .term → Type where
  | refl {sourceScope sourceContext targetScope}
      {layout : Layout.Context (sourceScope := sourceScope) sourceContext targetScope}
      {path : DotFC.BVar sourceScope .term} :
      PathWeakening layout path layout path
  | plain {sourceScope sourceContext targetScope}
      {outer : Layout.Context (sourceScope := sourceScope) sourceContext targetScope}
      {path : DotFC.BVar sourceScope .term}
      {middleSourceScope middleContext middleTargetScope}
      {middle : Layout.Context (sourceScope := middleSourceScope)
        middleContext middleTargetScope}
      {middlePath : DotFC.BVar middleSourceScope .term}
      (chain : PathWeakening outer path middle middlePath)
      {type : Ty middleSourceScope} (shape : PlainShape type) :
      PathWeakening outer path (Layout.Context.plain middle shape)
        (.there middlePath)
  | signature {sourceScope sourceContext targetScope}
      {outer : Layout.Context (sourceScope := sourceScope) sourceContext targetScope}
      {path : DotFC.BVar sourceScope .term}
      {middleSourceScope middleContext middleTargetScope}
      {middle : Layout.Context (sourceScope := middleSourceScope)
        middleContext middleTargetScope}
      {middlePath : DotFC.BVar middleSourceScope .term}
      (chain : PathWeakening outer path middle middlePath)
      {type : Ty middleSourceScope} {signature : Signature middleSourceScope}
      (collectible : Collectible middleContext type signature)
      (closed : ClosedSignature signature) :
      PathWeakening outer path
        (Layout.Context.signature signature middle collectible closed)
        (.there middlePath)

namespace MemberAllocated

/-- Transport an allocation through any finite chain of plain/signature
layout extensions. The result compiles to repeated target renaming via the
existing `MemberLookup` equations. -/
def weakenAlong {sourceScope : DotFC.Sig} {sourceContext : Ctx sourceScope}
    {targetScope : FCsub.Sig}
    {outer : Layout.Context sourceContext targetScope}
    {path : DotFC.BVar sourceScope .term} {label : Name}
    (allocated : Layout.MemberAllocated outer path label)
    {laterSourceScope : DotFC.Sig} {laterContext : Ctx laterSourceScope}
    {laterTargetScope : FCsub.Sig}
    {later : Layout.Context laterContext laterTargetScope}
    {laterPath : DotFC.BVar laterSourceScope .term}
    (weakening : PathWeakening outer path later laterPath) :
    Layout.MemberAllocated later laterPath label :=
  match weakening with
  | .refl => allocated
  | .plain chain shape => (weakenAlong allocated chain).plainThere shape
  | .signature chain collectible closed =>
      (weakenAlong allocated chain).signatureThere collectible closed

end MemberAllocated

end DotToFCsub.M4.ScopedClosure
