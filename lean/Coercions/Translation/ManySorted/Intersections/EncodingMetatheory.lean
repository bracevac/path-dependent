import Coercions.Translation.ManySorted.Intersections.Encoding

/-!
# Metatheory for names-first intersection encoding

The observable proposition list below packages the intrinsically sorted
propositions of a target theory.  It lets the encoding theorem state the
exact lower/name and name/upper propositions emitted for every retained
interval, rather than merely counting relation tags.
-/

namespace DOTCaptureToManySortedFC.Intersections.Encoding

namespace Target

/-- One opened target-theory proposition paired with its exact evidence
coordinate. -/
structure OpenedProposition (scope : Sig) (symbols : List StaticSort)
    (relations : List Relation) where
  relation : Relation
  proposition : Proposition relation (StaticScope scope symbols relations)
  evidence : BVar (StaticScope scope symbols relations) (.evidence relation)
deriving DecidableEq

namespace OpenedProposition

/-- Weaken an older proposition and its evidence coordinate below one newly
opened assumption. -/
def weakenOne {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (newest : Relation)
    (opened : OpenedProposition scope symbols relations) :
    OpenedProposition scope symbols (newest :: relations) :=
  let rho := ManySortedFC.Rename.succ
    (scope := StaticScope scope symbols relations)
    (kind := .evidence newest)
  { relation := opened.relation
    proposition := opened.proposition.rename rho
    evidence := rho.var opened.evidence }

end OpenedProposition

/-- One proposition with its relation index hidden but its complete syntax
retained. -/
inductive PackedProposition (scope : Sig) where
  | pack {relation : Relation} (proposition : Proposition relation scope) :
      PackedProposition scope
deriving DecidableEq

namespace Theory

/-- Every opened proposition paired with the evidence binder introduced for
it.  List order is theory order, so the head is the newest evidence binder. -/
def openedPropositions {scope : Sig} {symbols : List StaticSort} :
    {relations : List Relation} ->
      Theory scope symbols relations ->
      List (OpenedProposition scope symbols relations)
  | [], .nil => []
  | relation :: relations, .cons proposition rest =>
      let rho := ManySortedFC.Rename.weakenMany
        (SymbolScope scope symbols)
        (ManySortedFC.evidenceKinds (relation :: relations))
      { relation := relation
        proposition := proposition.rename rho
        evidence := .here } ::
      (openedPropositions rest).map fun opened =>
        opened.weakenOne relation

@[simp]
theorem openedPropositions_cons {scope : Sig}
    {symbols : List StaticSort} {relation : Relation}
    {relations : List Relation}
    (proposition : Proposition relation (SymbolScope scope symbols))
    (rest : Theory scope symbols relations) :
    openedPropositions (.cons proposition rest) =
      let rho := ManySortedFC.Rename.weakenMany
        (SymbolScope scope symbols)
        (ManySortedFC.evidenceKinds (relation :: relations))
      { relation := relation
        proposition := proposition.rename rho
        evidence := .here } ::
      (openedPropositions rest).map fun opened =>
        opened.weakenOne relation := rfl

@[simp]
theorem openedPropositions_nil {scope : Sig}
    {symbols : List StaticSort} :
    openedPropositions (.nil : Theory scope symbols []) = [] := rfl

/-- Structural observation of every proposition in theory order. -/
def propositions {scope : Sig} {symbols : List StaticSort} :
    {relations : List Relation} ->
      Theory scope symbols relations ->
      List (PackedProposition (SymbolScope scope symbols))
  | [], .nil => []
  | _ :: _, .cons proposition rest =>
      .pack proposition :: propositions rest

/-- Every coordinate returned by `openedPropositions` looks up the exact
proposition paired with it in the fully opened context. -/
theorem openedPropositions_lookup {scope : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (symbolContext : ManySortedFC.Ctx (SymbolScope scope symbols))
    (theory : Theory scope symbols relations)
    (opened : OpenedProposition scope symbols relations)
    (membership : opened ∈ theory.openedPropositions) :
    (ManySortedFC.Ctx.extendTheoryEvidence symbolContext theory).lookup
        opened.evidence =
      .evidence opened.proposition := by
  cases theory with
  | nil => cases membership
  | @cons _ _ relation relations headProposition tailTheory =>
      simp only [openedPropositions, List.mem_cons] at membership
      rcases membership with head | tail
      · subst opened
        change ManySortedFC.Binding.evidence
            ((headProposition.rename
              (ManySortedFC.Rename.weakenMany
                (SymbolScope scope symbols)
                (ManySortedFC.evidenceKinds relations))).rename
              ManySortedFC.Rename.succ) =
          ManySortedFC.Binding.evidence
            (headProposition.rename
              (ManySortedFC.Rename.weakenMany
                (SymbolScope scope symbols)
                (ManySortedFC.evidenceKinds (relation :: relations))))
        rw [ManySortedFC.Proposition.rename_comp]
        rfl
      · obtain ⟨older, olderMember, openedEq⟩ := List.mem_map.mp tail
        subst opened
        change
          ((ManySortedFC.Ctx.extendTheoryEvidence symbolContext tailTheory).lookup
            older.evidence).weaken =
          ManySortedFC.Binding.evidence
            (older.proposition.rename ManySortedFC.Rename.succ)
        rw [openedPropositions_lookup symbolContext tailTheory older olderMember]
        rfl
termination_by relations.length

end Theory

end Target

namespace PreparedEntry

private theorem intervalRelations_length {α : Type}
    (sort : Target.StaticSort) (items : List α) :
    (PreparedEntry.intervalRelations sort items).length = 2 * items.length := by
  induction items with
  | nil => rfl
  | cons item remaining induction =>
      simp only [PreparedEntry.intervalRelations, List.length_cons, induction]
      omega

/-- Number of source interval occurrences retained by one prepared entry. -/
def occurrenceCount {scope : Target.Sig} : PreparedEntry scope -> Nat
  | .type _ _ intervals => intervals.length
  | .capture _ _ intervals => intervals.length
  | .classifier _ _ intervals => intervals.length

/-- The exact target propositions specified by one prepared entry. -/
def propositions {scope : Target.Sig} : PreparedEntry scope ->
    List (Target.PackedProposition scope)
  | .type _ name intervals =>
      intervals.flatMap fun interval =>
        [.pack (.inclusion interval.lower (.type (.tvar name))),
          .pack (.inclusion (.type (.tvar name)) interval.upper)]
  | .capture _ name intervals =>
      intervals.flatMap fun interval =>
        [.pack (.inclusion interval.lower (.capture (.cvar name))),
          .pack (.inclusion (.capture (.cvar name)) interval.upper)]
  | .classifier _ name intervals =>
      intervals.flatMap fun interval =>
        [.pack (.inclusion interval.lower (.classifier (.var name))),
          .pack (.inclusion (.classifier (.var name)) interval.upper)]

@[simp]
theorem relations_length {scope : Target.Sig} (entry : PreparedEntry scope) :
    entry.relations.length = 2 * entry.occurrenceCount := by
  cases entry with
  | type label name intervals =>
      exact intervalRelations_length .type intervals
  | capture label name intervals =>
      exact intervalRelations_length .capture intervals
  | classifier label name intervals =>
      exact intervalRelations_length .classifier intervals

end PreparedEntry

namespace PreparedConstraint

/-- The packed proposition retained by one mixed-sort source constraint. -/
def packed {scope : Target.Sig} (constraint : PreparedConstraint scope) :
    Target.PackedProposition scope :=
  .pack constraint.proposition

end PreparedConstraint

namespace OpenedOccurrence

/-- The two opened proposition/evidence slots carried by one retained
interval occurrence. -/
def propositions {scope : Target.Sig} {symbols : List Target.StaticSort}
    {relations : List Target.Relation}
    (occurrence : OpenedOccurrence scope symbols relations) :
    List (Target.OpenedProposition scope symbols relations) :=
  [{ relation := .inclusion occurrence.sort
     proposition := occurrence.lowerProposition
     evidence := occurrence.lowerEvidence },
   { relation := .inclusion occurrence.sort
     proposition := occurrence.upperProposition
     evidence := occurrence.upperEvidence }]

@[simp]
theorem propositions_weakenTwo {scope : Target.Sig}
    {symbols : List Target.StaticSort} {relations : List Target.Relation}
    (newest older : Target.Relation)
    (occurrence : OpenedOccurrence scope symbols relations) :
    (occurrence.weakenTwo newest older).propositions =
      ((occurrence.propositions.map fun opened => opened.weakenOne older).map
        fun opened => opened.weakenOne newest) := by
  cases occurrence <;>
    simp [propositions, OpenedOccurrence.weakenTwo,
      Target.OpenedProposition.weakenOne,
      ManySortedFC.Proposition.rename_comp,
      ManySortedFC.Rename.weakenMany,
      ManySortedFC.Rename.comp, ManySortedFC.Rename.succ] <;>
    repeat
      first
      | constructor
      | rfl

@[simp]
theorem flatMap_propositions_map_weakenTwo {scope : Target.Sig}
    {symbols : List Target.StaticSort} {relations : List Target.Relation}
    (newest older : Target.Relation)
    (occurrences : List (OpenedOccurrence scope symbols relations)) :
    (occurrences.map fun occurrence =>
        occurrence.weakenTwo newest older).flatMap propositions =
      (((occurrences.flatMap propositions).map fun opened =>
          opened.weakenOne older).map fun opened =>
        opened.weakenOne newest) := by
  induction occurrences with
  | nil => rfl
  | cons occurrence remaining induction =>
      simp [List.map_append, List.map_map, induction]

end OpenedOccurrence

namespace PreparedSignature

private theorem entriesRelationsWithTail_length {scope : Target.Sig}
    (entries : List (PreparedEntry scope)) (tail : List Target.Relation) :
    (PreparedSignature.entriesRelationsWithTail entries tail).length =
      2 * (entries.map PreparedEntry.occurrenceCount).sum + tail.length := by
  induction entries with
  | nil => simp [PreparedSignature.entriesRelationsWithTail]
  | cons entry remaining induction =>
      simp only [PreparedSignature.entriesRelationsWithTail,
        List.length_append, PreparedEntry.relations_length, List.map_cons,
        List.sum_cons, induction, Nat.mul_add]
      omega

/-- Total number of retained interval occurrences. -/
def occurrenceCount {scope : Target.Sig} (prepared : PreparedSignature scope) :
    Nat :=
  (prepared.entries.map PreparedEntry.occurrenceCount).sum

/-- Exact proposition specification before constructing the indexed theory. -/
def propositions {scope : Target.Sig} (prepared : PreparedSignature scope) :
    List (Target.PackedProposition
      (Target.SymbolScope scope prepared.symbols)) :=
  prepared.entries.flatMap PreparedEntry.propositions ++
    prepared.constraints.map PreparedConstraint.packed

@[simp]
theorem relations_length {scope : Target.Sig}
    (prepared : PreparedSignature scope) :
    prepared.relations.length =
      2 * prepared.occurrenceCount + prepared.constraints.length := by
  rw [show prepared.relations =
      PreparedSignature.entriesRelationsWithTail prepared.entries
        (prepared.constraints.map PreparedConstraint.relation) from rfl,
    entriesRelationsWithTail_length]
  simp only [List.length_map, occurrenceCount]

end PreparedSignature

namespace Encoding

private theorem theoryPropositions_appendTheory {scope : Target.Sig}
    {symbols : List Target.StaticSort}
    {leftRelations rightRelations : List Target.Relation}
    (left : Target.Theory scope symbols leftRelations)
    (right : Target.Theory scope symbols rightRelations) :
    Target.Theory.propositions (appendTheory left right) =
      Target.Theory.propositions left ++
        Target.Theory.propositions right := by
  cases left with
  | nil => rfl
  | @cons _ _ relation relations proposition rest =>
      change Target.PackedProposition.pack proposition ::
          Target.Theory.propositions (appendTheory rest right) =
        Target.PackedProposition.pack proposition ::
          (Target.Theory.propositions rest ++
            Target.Theory.propositions right)
      exact congrArg (Target.PackedProposition.pack proposition :: ·)
        (theoryPropositions_appendTheory rest right)
termination_by leftRelations.length

/-- Encoding emits exactly the structural proposition specification. -/
theorem propositions_eq {scope : Target.Sig}
    (prepared : PreparedSignature scope) :
    Target.Theory.propositions (encode prepared).theory =
      prepared.propositions := by
  have intervalPropositions : forall
      (entry : PreparedEntry
        (Target.SymbolScope scope prepared.symbols)),
      Target.Theory.propositions (entryTheory entry) =
        entry.propositions := by
    intro entry
    cases entry with
    | type label name intervals =>
        induction intervals with
        | nil => rfl
        | cons interval remaining induction =>
            exact congrArg
              (fun tail =>
                Target.PackedProposition.pack
                    (.inclusion interval.lower (.type (.tvar name))) ::
                  Target.PackedProposition.pack
                    (.inclusion (.type (.tvar name)) interval.upper) :: tail)
              induction
    | capture label name intervals =>
        induction intervals with
        | nil => rfl
        | cons interval remaining induction =>
            exact congrArg
              (fun tail =>
                Target.PackedProposition.pack
                    (.inclusion interval.lower (.capture (.cvar name))) ::
                  Target.PackedProposition.pack
                    (.inclusion (.capture (.cvar name)) interval.upper) :: tail)
              induction
    | classifier label name intervals =>
        induction intervals with
        | nil => rfl
        | cons interval remaining induction =>
            exact congrArg
              (fun tail =>
                Target.PackedProposition.pack
                    (.inclusion interval.lower (.classifier (.var name))) ::
                  Target.PackedProposition.pack
                    (.inclusion (.classifier (.var name)) interval.upper) ::
                      tail)
              induction
  have constraintsPropositions : forall
      (constraints : List (PreparedConstraint
        (Target.SymbolScope scope prepared.symbols))),
      Target.Theory.propositions (constraintsTheory constraints) =
        constraints.map PreparedConstraint.packed := by
    intro constraints
    induction constraints with
    | nil => rfl
    | cons constraint remaining induction =>
        exact congrArg
          (Target.PackedProposition.pack constraint.proposition :: ·)
          induction
  have entriesPropositions : forall
      (entries : List (PreparedEntry
        (Target.SymbolScope scope prepared.symbols)))
      {tailRelations : List Target.Relation}
      (tail : Target.Theory scope prepared.symbols tailRelations),
      Target.Theory.propositions
          (entriesTheoryWithTail entries tail) =
        entries.flatMap PreparedEntry.propositions ++
          Target.Theory.propositions tail := by
    intro entries tailRelations tail
    induction entries with
    | nil => rfl
    | cons entry remaining induction =>
        simp only [entriesTheoryWithTail, List.flatMap_cons,
          theoryPropositions_appendTheory, intervalPropositions, induction,
          List.append_assoc]
  exact (entriesPropositions prepared.entries
    (constraintsTheory prepared.constraints)).trans (by
      rw [constraintsPropositions]
      rfl)

private theorem openTypeIntervals_evidenceMatches {scope : Target.Sig}
    {symbols : List Target.StaticSort}
    (symbolContext : ManySortedFC.Ctx (Target.SymbolScope scope symbols))
    (label : Nat)
    (name : Target.BVar (Target.SymbolScope scope symbols) (.symbol .type))
    (intervals : List (Source.Interval
      (Target.StaticExpr .type (Target.SymbolScope scope symbols))))
    (tailRelations : List Target.Relation)
    (tailTheory : Target.Theory scope symbols tailRelations)
    (tail : List (OpenedOccurrence scope symbols tailRelations))
    (tailValidity : ∀ occurrence, occurrence ∈ tail ->
      occurrence.EvidenceMatches
        (ManySortedFC.Ctx.extendTheoryEvidence symbolContext tailTheory)) :
    ∀ occurrence,
      occurrence ∈ openTypeIntervals label name intervals tailRelations tail ->
      occurrence.EvidenceMatches
        (ManySortedFC.Ctx.extendTheoryEvidence symbolContext
          (appendTheory (typeIntervalsTheory name intervals) tailTheory)) := by
  induction intervals with
  | nil => exact tailValidity
  | cons interval remaining induction =>
      intro occurrence membership
      simp only [openTypeIntervals, List.mem_cons, List.mem_map] at membership
      rcases membership with rfl | ⟨older, olderMember, rfl⟩
      · constructor
        · change ManySortedFC.Binding.evidence
            (((ManySortedFC.Proposition.inclusion interval.lower
              (.type (.tvar name))).rename
                (ManySortedFC.Rename.weakenMany
                  (Target.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (.inclusion .type ::
                      PreparedEntry.intervalRelations .type remaining ++
                        tailRelations)))).rename
              ManySortedFC.Rename.succ) = _
          rw [ManySortedFC.Proposition.rename_comp]
          rfl
        · change ManySortedFC.Binding.evidence
            (((((ManySortedFC.Proposition.inclusion
              (.type (.tvar name)) interval.upper).rename
                (ManySortedFC.Rename.weakenMany
                  (Target.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .type remaining ++
                      tailRelations)))).rename
                ManySortedFC.Rename.succ).rename
              ManySortedFC.Rename.succ)) = _
          rw [ManySortedFC.Proposition.rename_comp,
            ManySortedFC.Proposition.rename_comp]
          rfl
      · exact OpenedOccurrence.weakenTwo_evidenceMatches
          (ManySortedFC.Ctx.extendTheoryEvidence symbolContext
            (appendTheory (typeIntervalsTheory name remaining) tailTheory))
          _ _ older (induction older olderMember)

private theorem openCaptureIntervals_evidenceMatches {scope : Target.Sig}
    {symbols : List Target.StaticSort}
    (symbolContext : ManySortedFC.Ctx (Target.SymbolScope scope symbols))
    (label : Nat)
    (name : Target.BVar (Target.SymbolScope scope symbols)
      (.symbol .capture))
    (intervals : List (Source.Interval
      (Target.StaticExpr .capture (Target.SymbolScope scope symbols))))
    (tailRelations : List Target.Relation)
    (tailTheory : Target.Theory scope symbols tailRelations)
    (tail : List (OpenedOccurrence scope symbols tailRelations))
    (tailValidity : ∀ occurrence, occurrence ∈ tail ->
      occurrence.EvidenceMatches
        (ManySortedFC.Ctx.extendTheoryEvidence symbolContext tailTheory)) :
    ∀ occurrence,
      occurrence ∈ openCaptureIntervals label name intervals tailRelations tail ->
      occurrence.EvidenceMatches
        (ManySortedFC.Ctx.extendTheoryEvidence symbolContext
          (appendTheory (captureIntervalsTheory name intervals)
            tailTheory)) := by
  induction intervals with
  | nil => exact tailValidity
  | cons interval remaining induction =>
      intro occurrence membership
      simp only [openCaptureIntervals, List.mem_cons, List.mem_map] at membership
      rcases membership with rfl | ⟨older, olderMember, rfl⟩
      · constructor
        · change ManySortedFC.Binding.evidence
            (((ManySortedFC.Proposition.inclusion interval.lower
              (.capture (.cvar name))).rename
                (ManySortedFC.Rename.weakenMany
                  (Target.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (.inclusion .capture ::
                      PreparedEntry.intervalRelations .capture remaining ++
                        tailRelations)))).rename
              ManySortedFC.Rename.succ) = _
          rw [ManySortedFC.Proposition.rename_comp]
          rfl
        · change ManySortedFC.Binding.evidence
            (((((ManySortedFC.Proposition.inclusion
              (.capture (.cvar name)) interval.upper).rename
                (ManySortedFC.Rename.weakenMany
                  (Target.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .capture remaining ++
                      tailRelations)))).rename
                ManySortedFC.Rename.succ).rename
              ManySortedFC.Rename.succ)) = _
          rw [ManySortedFC.Proposition.rename_comp,
            ManySortedFC.Proposition.rename_comp]
          rfl
      · exact OpenedOccurrence.weakenTwo_evidenceMatches
          (ManySortedFC.Ctx.extendTheoryEvidence symbolContext
            (appendTheory (captureIntervalsTheory name remaining) tailTheory))
          _ _ older (induction older olderMember)

private theorem openClassifierIntervals_evidenceMatches {scope : Target.Sig}
    {symbols : List Target.StaticSort}
    (symbolContext : ManySortedFC.Ctx (Target.SymbolScope scope symbols))
    (label : Nat)
    (name : Target.BVar (Target.SymbolScope scope symbols)
      (.symbol .classifier))
    (intervals : List (Source.Interval
      (Target.StaticExpr .classifier (Target.SymbolScope scope symbols))))
    (tailRelations : List Target.Relation)
    (tailTheory : Target.Theory scope symbols tailRelations)
    (tail : List (OpenedOccurrence scope symbols tailRelations))
    (tailValidity : ∀ occurrence, occurrence ∈ tail ->
      occurrence.EvidenceMatches
        (ManySortedFC.Ctx.extendTheoryEvidence symbolContext tailTheory)) :
    ∀ occurrence,
      occurrence ∈ openClassifierIntervals label name intervals
        tailRelations tail ->
      occurrence.EvidenceMatches
        (ManySortedFC.Ctx.extendTheoryEvidence symbolContext
          (appendTheory (classifierIntervalsTheory name intervals)
            tailTheory)) := by
  induction intervals with
  | nil => exact tailValidity
  | cons interval remaining induction =>
      intro occurrence membership
      simp only [openClassifierIntervals, List.mem_cons, List.mem_map]
        at membership
      rcases membership with rfl | ⟨older, olderMember, rfl⟩
      · constructor
        · change ManySortedFC.Binding.evidence
            (((ManySortedFC.Proposition.inclusion interval.lower
              (.classifier (.var name))).rename
                (ManySortedFC.Rename.weakenMany
                  (Target.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (.inclusion .classifier ::
                      PreparedEntry.intervalRelations .classifier remaining ++
                        tailRelations)))).rename
              ManySortedFC.Rename.succ) = _
          rw [ManySortedFC.Proposition.rename_comp]
          rfl
        · change ManySortedFC.Binding.evidence
            (((((ManySortedFC.Proposition.inclusion
              (.classifier (.var name)) interval.upper).rename
                (ManySortedFC.Rename.weakenMany
                  (Target.SymbolScope scope symbols)
                  (ManySortedFC.evidenceKinds
                    (PreparedEntry.intervalRelations .classifier remaining ++
                      tailRelations)))).rename
                ManySortedFC.Rename.succ).rename
              ManySortedFC.Rename.succ)) = _
          rw [ManySortedFC.Proposition.rename_comp,
            ManySortedFC.Proposition.rename_comp]
          rfl
      · exact OpenedOccurrence.weakenTwo_evidenceMatches
          (ManySortedFC.Ctx.extendTheoryEvidence symbolContext
            (appendTheory (classifierIntervalsTheory name remaining)
              tailTheory))
          _ _ older (induction older olderMember)

private theorem openEntriesWithTail_evidenceMatches {scope : Target.Sig}
    {symbols : List Target.StaticSort}
    (symbolContext : ManySortedFC.Ctx (Target.SymbolScope scope symbols)) :
    (entries : List
      (PreparedEntry (Target.SymbolScope scope symbols))) ->
    {tailRelations : List Target.Relation} ->
    (tailTheory : Target.Theory scope symbols tailRelations) ->
    (tail : List (OpenedOccurrence scope symbols tailRelations)) ->
    (∀ occurrence, occurrence ∈ tail ->
      occurrence.EvidenceMatches
        (ManySortedFC.Ctx.extendTheoryEvidence symbolContext tailTheory)) ->
    ∀ occurrence,
      occurrence ∈ openEntriesWithTail entries tailRelations tail ->
      occurrence.EvidenceMatches
        (ManySortedFC.Ctx.extendTheoryEvidence symbolContext
          (entriesTheoryWithTail entries tailTheory))
  | [], _, _, _, tailValidity, occurrence, membership =>
      tailValidity occurrence membership
  | .type label name intervals :: remaining, tailRelations, tailTheory,
      tail, tailValidity, occurrence, membership =>
      openTypeIntervals_evidenceMatches symbolContext label name intervals
        (PreparedSignature.entriesRelationsWithTail remaining tailRelations)
        (entriesTheoryWithTail remaining tailTheory)
        (openEntriesWithTail remaining tailRelations tail)
        (openEntriesWithTail_evidenceMatches symbolContext remaining
          tailTheory tail tailValidity)
        occurrence membership
  | .capture label name intervals :: remaining, tailRelations, tailTheory,
      tail, tailValidity, occurrence, membership =>
      openCaptureIntervals_evidenceMatches symbolContext label name intervals
        (PreparedSignature.entriesRelationsWithTail remaining tailRelations)
        (entriesTheoryWithTail remaining tailTheory)
        (openEntriesWithTail remaining tailRelations tail)
        (openEntriesWithTail_evidenceMatches symbolContext remaining
          tailTheory tail tailValidity)
        occurrence membership
  | .classifier label name intervals :: remaining, tailRelations, tailTheory,
      tail, tailValidity, occurrence, membership =>
      openClassifierIntervals_evidenceMatches symbolContext label name intervals
        (PreparedSignature.entriesRelationsWithTail remaining tailRelations)
        (entriesTheoryWithTail remaining tailTheory)
        (openEntriesWithTail remaining tailRelations tail)
        (openEntriesWithTail_evidenceMatches symbolContext remaining
          tailTheory tail tailValidity)
        occurrence membership

/-- Every retained occurrence points to the exact two assumptions installed
by its generated theory.  The target theory is derived from the same prepared
signature, so an occurrence can never be paired with unrelated evidence. -/
theorem opened_occurrence_evidence_matches {scope : Target.Sig}
    (context : ManySortedFC.Ctx scope)
    (encoding : Encoding scope)
    (occurrence : OpenedOccurrence scope encoding.symbols encoding.relations)
    (membership : occurrence ∈ encoding.openedOccurrences) :
    occurrence.EvidenceMatches (context.extendTheory encoding.theory) :=
  openEntriesWithTail_evidenceMatches
    (context.extendSymbols encoding.symbols)
    encoding.prepared.entries
    (constraintsTheory encoding.prepared.constraints) []
    (by intro occurrence impossible; cases impossible)
    occurrence membership

/-- An encoded theory has two inclusion binders per retained interval followed
by one binder for each retained mixed-sort constraint. -/
theorem relations_length {scope : Target.Sig} (encoding : Encoding scope) :
    encoding.relations.length =
      2 * encoding.prepared.occurrenceCount +
        encoding.prepared.constraints.length :=
  PreparedSignature.relations_length encoding.prepared

/-- Every retained type interval emits its precise lower-to-shared-name and
shared-name-to-upper propositions. -/
theorem contains_type_interval {scope : Target.Sig}
    (prepared : PreparedSignature scope)
    {label : Nat}
    {name : Target.BVar
      (Target.SymbolScope scope prepared.symbols) (.symbol .type)}
    {intervals : List (Source.Interval
      (Target.StaticExpr .type
        (Target.SymbolScope scope prepared.symbols)))}
    (entryMember : PreparedEntry.type label name intervals ∈ prepared.entries)
    {interval : Source.Interval
      (Target.StaticExpr .type
        (Target.SymbolScope scope prepared.symbols))}
    (intervalMember : interval ∈ intervals) :
    Target.PackedProposition.pack
        (.inclusion interval.lower (.type (.tvar name))) ∈
      Target.Theory.propositions (encode prepared).theory ∧
    Target.PackedProposition.pack
        (.inclusion (.type (.tvar name)) interval.upper) ∈
      Target.Theory.propositions (encode prepared).theory := by
  rw [propositions_eq]
  constructor
  · simp only [PreparedSignature.propositions]
    apply List.mem_append_left
    change Target.PackedProposition.pack
        (.inclusion interval.lower (.type (.tvar name))) ∈
      prepared.entries.flatMap PreparedEntry.propositions
    apply List.mem_flatMap.mpr
    refine ⟨PreparedEntry.type label name intervals, entryMember, ?_⟩
    simp only [PreparedEntry.propositions]
    apply List.mem_flatMap.mpr
    exact ⟨interval, intervalMember, by simp⟩
  · simp only [PreparedSignature.propositions]
    apply List.mem_append_left
    change Target.PackedProposition.pack
        (.inclusion (.type (.tvar name)) interval.upper) ∈
      prepared.entries.flatMap PreparedEntry.propositions
    apply List.mem_flatMap.mpr
    refine ⟨PreparedEntry.type label name intervals, entryMember, ?_⟩
    simp only [PreparedEntry.propositions]
    apply List.mem_flatMap.mpr
    exact ⟨interval, intervalMember, by simp⟩

/-- Every retained capture interval emits its precise lower-to-shared-name and
shared-name-to-upper propositions. -/
theorem contains_capture_interval {scope : Target.Sig}
    (prepared : PreparedSignature scope)
    {label : Nat}
    {name : Target.BVar
      (Target.SymbolScope scope prepared.symbols) (.symbol .capture)}
    {intervals : List (Source.Interval
      (Target.StaticExpr .capture
        (Target.SymbolScope scope prepared.symbols)))}
    (entryMember : PreparedEntry.capture label name intervals ∈
      prepared.entries)
    {interval : Source.Interval
      (Target.StaticExpr .capture
        (Target.SymbolScope scope prepared.symbols))}
    (intervalMember : interval ∈ intervals) :
    Target.PackedProposition.pack
        (.inclusion interval.lower (.capture (.cvar name))) ∈
      Target.Theory.propositions (encode prepared).theory ∧
    Target.PackedProposition.pack
        (.inclusion (.capture (.cvar name)) interval.upper) ∈
      Target.Theory.propositions (encode prepared).theory := by
  rw [propositions_eq]
  constructor
  · simp only [PreparedSignature.propositions]
    apply List.mem_append_left
    change Target.PackedProposition.pack
        (.inclusion interval.lower (.capture (.cvar name))) ∈
      prepared.entries.flatMap PreparedEntry.propositions
    apply List.mem_flatMap.mpr
    refine ⟨PreparedEntry.capture label name intervals, entryMember, ?_⟩
    simp only [PreparedEntry.propositions]
    apply List.mem_flatMap.mpr
    exact ⟨interval, intervalMember, by simp⟩
  · simp only [PreparedSignature.propositions]
    apply List.mem_append_left
    change Target.PackedProposition.pack
        (.inclusion (.capture (.cvar name)) interval.upper) ∈
      prepared.entries.flatMap PreparedEntry.propositions
    apply List.mem_flatMap.mpr
    refine ⟨PreparedEntry.capture label name intervals, entryMember, ?_⟩
    simp only [PreparedEntry.propositions]
    apply List.mem_flatMap.mpr
    exact ⟨interval, intervalMember, by simp⟩

/-- Every retained classifier interval emits its precise lower-to-shared-name
and shared-name-to-upper propositions. -/
theorem contains_classifier_interval {scope : Target.Sig}
    (prepared : PreparedSignature scope)
    {label : Nat}
    {name : Target.BVar
      (Target.SymbolScope scope prepared.symbols) (.symbol .classifier)}
    {intervals : List (Source.Interval
      (Target.StaticExpr .classifier
        (Target.SymbolScope scope prepared.symbols)))}
    (entryMember : PreparedEntry.classifier label name intervals ∈
      prepared.entries)
    {interval : Source.Interval
      (Target.StaticExpr .classifier
        (Target.SymbolScope scope prepared.symbols))}
    (intervalMember : interval ∈ intervals) :
    Target.PackedProposition.pack
        (.inclusion interval.lower (.classifier (.var name))) ∈
      Target.Theory.propositions (encode prepared).theory ∧
    Target.PackedProposition.pack
        (.inclusion (.classifier (.var name)) interval.upper) ∈
      Target.Theory.propositions (encode prepared).theory := by
  rw [propositions_eq]
  constructor
  · simp only [PreparedSignature.propositions]
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨PreparedEntry.classifier label name intervals, entryMember, ?_⟩
    simp only [PreparedEntry.propositions]
    apply List.mem_flatMap.mpr
    exact ⟨interval, intervalMember, by simp⟩
  · simp only [PreparedSignature.propositions]
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨PreparedEntry.classifier label name intervals, entryMember, ?_⟩
    simp only [PreparedEntry.propositions]
    apply List.mem_flatMap.mpr
    exact ⟨interval, intervalMember, by simp⟩

/-- Every retained mixed-sort constraint occurs verbatim in the generated
target theory after all member names have been allocated. -/
theorem contains_constraint {scope : Target.Sig}
    (prepared : PreparedSignature scope)
    {constraint : PreparedConstraint
      (Target.SymbolScope scope prepared.symbols)}
    (membership : constraint ∈ prepared.constraints) :
    constraint.packed ∈
      Target.Theory.propositions (encode prepared).theory := by
  rw [propositions_eq]
  simp only [PreparedSignature.propositions]
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨constraint, membership, rfl⟩

/-- Two retained type intervals at one entry use the very same allocated
de Bruijn name in all four emitted propositions. -/
theorem repeated_type_intervals_share_name {scope : Target.Sig}
    (prepared : PreparedSignature scope)
    {label : Nat}
    {name : Target.BVar
      (Target.SymbolScope scope prepared.symbols) (.symbol .type)}
    {intervals : List (Source.Interval
      (Target.StaticExpr .type
        (Target.SymbolScope scope prepared.symbols)))}
    (entryMember : PreparedEntry.type label name intervals ∈ prepared.entries)
    {first second : Source.Interval
      (Target.StaticExpr .type
        (Target.SymbolScope scope prepared.symbols))}
    (firstMember : first ∈ intervals) (secondMember : second ∈ intervals) :
    (Target.PackedProposition.pack
        (.inclusion first.lower (.type (.tvar name))) ∈
      Target.Theory.propositions (encode prepared).theory ∧
     Target.PackedProposition.pack
        (.inclusion (.type (.tvar name)) first.upper) ∈
      Target.Theory.propositions (encode prepared).theory) ∧
    (Target.PackedProposition.pack
        (.inclusion second.lower (.type (.tvar name))) ∈
      Target.Theory.propositions (encode prepared).theory ∧
     Target.PackedProposition.pack
        (.inclusion (.type (.tvar name)) second.upper) ∈
      Target.Theory.propositions (encode prepared).theory) :=
  ⟨contains_type_interval prepared entryMember firstMember,
    contains_type_interval prepared entryMember secondMember⟩

/-- Two retained capture intervals at one entry use the very same allocated
de Bruijn name in all four emitted propositions. -/
theorem repeated_capture_intervals_share_name {scope : Target.Sig}
    (prepared : PreparedSignature scope)
    {label : Nat}
    {name : Target.BVar
      (Target.SymbolScope scope prepared.symbols) (.symbol .capture)}
    {intervals : List (Source.Interval
      (Target.StaticExpr .capture
        (Target.SymbolScope scope prepared.symbols)))}
    (entryMember : PreparedEntry.capture label name intervals ∈
      prepared.entries)
    {first second : Source.Interval
      (Target.StaticExpr .capture
        (Target.SymbolScope scope prepared.symbols))}
    (firstMember : first ∈ intervals) (secondMember : second ∈ intervals) :
    (Target.PackedProposition.pack
        (.inclusion first.lower (.capture (.cvar name))) ∈
      Target.Theory.propositions (encode prepared).theory ∧
     Target.PackedProposition.pack
        (.inclusion (.capture (.cvar name)) first.upper) ∈
      Target.Theory.propositions (encode prepared).theory) ∧
    (Target.PackedProposition.pack
        (.inclusion second.lower (.capture (.cvar name))) ∈
      Target.Theory.propositions (encode prepared).theory ∧
     Target.PackedProposition.pack
        (.inclusion (.capture (.cvar name)) second.upper) ∈
      Target.Theory.propositions (encode prepared).theory) :=
  ⟨contains_capture_interval prepared entryMember firstMember,
    contains_capture_interval prepared entryMember secondMember⟩

/-- Repeated classifier intervals also reuse one allocated classifier name. -/
theorem repeated_classifier_intervals_share_name {scope : Target.Sig}
    (prepared : PreparedSignature scope)
    {label : Nat}
    {name : Target.BVar
      (Target.SymbolScope scope prepared.symbols) (.symbol .classifier)}
    {intervals : List (Source.Interval
      (Target.StaticExpr .classifier
        (Target.SymbolScope scope prepared.symbols)))}
    (entryMember : PreparedEntry.classifier label name intervals ∈
      prepared.entries)
    {first second : Source.Interval
      (Target.StaticExpr .classifier
        (Target.SymbolScope scope prepared.symbols))}
    (firstMember : first ∈ intervals) (secondMember : second ∈ intervals) :
    (Target.PackedProposition.pack
        (.inclusion first.lower (.classifier (.var name))) ∈
      Target.Theory.propositions (encode prepared).theory ∧
     Target.PackedProposition.pack
        (.inclusion (.classifier (.var name)) first.upper) ∈
      Target.Theory.propositions (encode prepared).theory) ∧
    (Target.PackedProposition.pack
        (.inclusion second.lower (.classifier (.var name))) ∈
      Target.Theory.propositions (encode prepared).theory ∧
     Target.PackedProposition.pack
        (.inclusion (.classifier (.var name)) second.upper) ∈
      Target.Theory.propositions (encode prepared).theory) :=
  ⟨contains_classifier_interval prepared entryMember firstMember,
    contains_classifier_interval prepared entryMember secondMember⟩

/-- Evidence binders only weaken an allocated member; they preserve its exact
label, sort, and de Bruijn coordinate under that weakening. -/
theorem opened_member_exact {scope : Target.Sig} (encoding : Encoding scope)
    {member : MemberName
      (Target.SymbolScope scope encoding.symbols)}
    (membership : member ∈ encoding.prepared.members) :
    member.rename
        (ManySortedFC.Rename.weakenMany
          (Target.SymbolScope scope encoding.symbols)
          (ManySortedFC.evidenceKinds encoding.relations)) ∈
      encoding.openedMembers := by
  exact List.mem_map.mpr ⟨member, membership, rfl⟩

end Encoding

end DOTCaptureToManySortedFC.Intersections.Encoding
