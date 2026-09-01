import Coercions.Translation.ManySorted.ModalIntersections.ConstraintRetention
import Coercions.Translation.ManySorted.ModalIntersections.CompilerContext
import Coercions.Translation.ManySorted.ModalIntersections.EvidenceElaboration

/-!
# Proof-selected object occurrence evidence

This module is the executable bridge between a raw cumulative member
occurrence and the two evidence variables retained for it by normalization.
Public artifact generation selects by the proof's same-label structural
ordinal, so two identical declarations still select different evidence
binders.  Endpoint search below is only a convenience operation.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.ObjectOccurrenceEvidence

open DOTCaptureToManySortedFC.Intersections.Encoding
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext

namespace Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev ClassifierExpr := DOTCapture.ModalIntersections.ClassifierExpr
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr
abbrev Interface := DOTCapture.ModalIntersections.Interface
abbrev ObjectType := DOTCapture.ModalIntersections.ObjectType

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Ctx := ManySortedFC.Ctx
abbrev StaticExpr := ManySortedFC.StaticExpr
abbrev Evidence := ManySortedFC.Evidence

end Target

/-! ## Finite, proof-carrying occurrence search -/

structure TypeSelection {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (candidates : List (OpenedOccurrence scope symbols relations))
    (label : Nat)
    (lower upper : Target.StaticExpr .type
      (ManySortedFC.StaticScope scope symbols relations)) where
  name : ManySortedFC.BVar
    (ManySortedFC.StaticScope scope symbols relations) (.symbol .type)
  lowerEvidence : ManySortedFC.BVar
    (ManySortedFC.StaticScope scope symbols relations)
    (.evidence (.inclusion .type))
  upperEvidence : ManySortedFC.BVar
    (ManySortedFC.StaticScope scope symbols relations)
    (.evidence (.inclusion .type))
  membership : OpenedOccurrence.type label name lower upper lowerEvidence
    upperEvidence ∈ candidates

structure CaptureSelection {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (candidates : List (OpenedOccurrence scope symbols relations))
    (label : Nat)
    (lower upper : Target.StaticExpr .capture
      (ManySortedFC.StaticScope scope symbols relations)) where
  name : ManySortedFC.BVar
    (ManySortedFC.StaticScope scope symbols relations) (.symbol .capture)
  lowerEvidence : ManySortedFC.BVar
    (ManySortedFC.StaticScope scope symbols relations)
    (.evidence (.inclusion .capture))
  upperEvidence : ManySortedFC.BVar
    (ManySortedFC.StaticScope scope symbols relations)
    (.evidence (.inclusion .capture))
  membership : OpenedOccurrence.capture label name lower upper lowerEvidence
    upperEvidence ∈ candidates

/-- A type occurrence selected by same-label ordinal.  The endpoints are
existential because the executable selector does not guess them. -/
structure TypeOrdinalSelection {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (candidates : List (OpenedOccurrence scope symbols relations))
    (label ordinal : Nat) where
  lower : Target.StaticExpr .type
    (ManySortedFC.StaticScope scope symbols relations)
  upper : Target.StaticExpr .type
    (ManySortedFC.StaticScope scope symbols relations)
  selected : TypeSelection candidates label lower upper

/-- Capture-sorted counterpart of `TypeOrdinalSelection`. -/
structure CaptureOrdinalSelection {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (candidates : List (OpenedOccurrence scope symbols relations))
    (label ordinal : Nat) where
  lower : Target.StaticExpr .capture
    (ManySortedFC.StaticScope scope symbols relations)
  upper : Target.StaticExpr .capture
    (ManySortedFC.StaticScope scope symbols relations)
  selected : CaptureSelection candidates label lower upper

def findTypeOrdinalSelection? {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (label : Nat) : (ordinal : Nat) ->
    (candidates : List (OpenedOccurrence scope symbols relations)) ->
      Option (TypeOrdinalSelection candidates label ordinal)
  | _, [] => none
  | ordinal, .capture _ _ _ _ _ _ :: remaining =>
      (findTypeOrdinalSelection? label ordinal remaining).map fun found =>
        { found with
          selected :=
            { found.selected with
              membership := .tail _ found.selected.membership } }
  | ordinal, .classifier _ _ _ _ _ _ :: remaining =>
      (findTypeOrdinalSelection? label ordinal remaining).map fun found =>
        { found with
          selected :=
            { found.selected with
              membership := .tail _ found.selected.membership } }
  | ordinal, .type candidateLabel name lower upper lowerEvidence
        upperEvidence :: remaining =>
      if labelsMatch : candidateLabel = label then
        match ordinal with
        | 0 => some
            { lower, upper
              selected :=
                { name, lowerEvidence, upperEvidence
                  membership := by
                    subst candidateLabel
                    exact .head _ } }
        | next + 1 =>
            (findTypeOrdinalSelection? label next remaining).map fun found =>
              { found with
                selected :=
                  { found.selected with
                    membership := .tail _ found.selected.membership } }
      else
        (findTypeOrdinalSelection? label ordinal remaining).map fun found =>
          { found with
            selected :=
              { found.selected with
                membership := .tail _ found.selected.membership } }

def findCaptureOrdinalSelection? {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (label : Nat) : (ordinal : Nat) ->
    (candidates : List (OpenedOccurrence scope symbols relations)) ->
      Option (CaptureOrdinalSelection candidates label ordinal)
  | _, [] => none
  | ordinal, .type _ _ _ _ _ _ :: remaining =>
      (findCaptureOrdinalSelection? label ordinal remaining).map fun found =>
        { found with
          selected :=
            { found.selected with
              membership := .tail _ found.selected.membership } }
  | ordinal, .classifier _ _ _ _ _ _ :: remaining =>
      (findCaptureOrdinalSelection? label ordinal remaining).map fun found =>
        { found with
          selected :=
            { found.selected with
              membership := .tail _ found.selected.membership } }
  | ordinal, .capture candidateLabel name lower upper lowerEvidence
        upperEvidence :: remaining =>
      if labelsMatch : candidateLabel = label then
        match ordinal with
        | 0 => some
            { lower, upper
              selected :=
                { name, lowerEvidence, upperEvidence
                  membership := by
                    subst candidateLabel
                    exact .head _ } }
        | next + 1 =>
            (findCaptureOrdinalSelection? label next remaining).map fun found =>
              { found with
                selected :=
                  { found.selected with
                    membership := .tail _ found.selected.membership } }
      else
        (findCaptureOrdinalSelection? label ordinal remaining).map fun found =>
          { found with
            selected :=
              { found.selected with
                membership := .tail _ found.selected.membership } }

theorem findTypeOrdinalSelection?_of_getElem {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    {candidates : List (OpenedOccurrence scope symbols relations)}
    {label ordinal : Nat}
    {lower upper : Target.StaticExpr .type
      (ManySortedFC.StaticScope scope symbols relations)}
    (atOrdinal :
      (ConstraintRetention.openedTypeIntervalsAt label candidates)[ordinal]? =
        some { lower, upper }) :
    ∃ found : TypeOrdinalSelection candidates label ordinal,
      findTypeOrdinalSelection? label ordinal candidates = some found ∧
      found.lower = lower ∧ found.upper = upper := by
  induction candidates generalizing ordinal with
  | nil => simp [ConstraintRetention.openedTypeIntervalsAt] at atOrdinal
  | cons current remaining induction =>
      cases current with
      | capture candidateLabel name candidateLower candidateUpper
          lowerEvidence upperEvidence =>
          simp only [ConstraintRetention.openedTypeIntervalsAt] at atOrdinal
          obtain ⟨found, foundResult, lowerEq, upperEq⟩ :=
            induction atOrdinal
          let lifted : TypeOrdinalSelection
              (OpenedOccurrence.capture candidateLabel name candidateLower
                candidateUpper lowerEvidence upperEvidence :: remaining)
              label ordinal :=
            { found with
              selected :=
                { found.selected with
                  membership := .tail _ found.selected.membership } }
          refine ⟨lifted, ?_, lowerEq, upperEq⟩
          simp [findTypeOrdinalSelection?, foundResult, lifted]
      | classifier candidateLabel name candidateLower candidateUpper
          lowerEvidence upperEvidence =>
          simp only [ConstraintRetention.openedTypeIntervalsAt] at atOrdinal
          obtain ⟨found, foundResult, lowerEq, upperEq⟩ :=
            induction atOrdinal
          let lifted : TypeOrdinalSelection
              (OpenedOccurrence.classifier candidateLabel name candidateLower
                candidateUpper lowerEvidence upperEvidence :: remaining)
              label ordinal :=
            { found with
              selected :=
                { found.selected with
                  membership := .tail _ found.selected.membership } }
          refine ⟨lifted, ?_, lowerEq, upperEq⟩
          simp [findTypeOrdinalSelection?, foundResult, lifted]
      | type candidateLabel name candidateLower candidateUpper
          lowerEvidence upperEvidence =>
          by_cases same : candidateLabel = label
          · subst candidateLabel
            cases ordinal with
            | zero =>
                simp only [ConstraintRetention.openedTypeIntervalsAt, if_true]
                  at atOrdinal
                cases atOrdinal
                refine ⟨{
                  lower := lower
                  upper := upper
                  selected :=
                    { name, lowerEvidence, upperEvidence,
                      membership := .head _ } }, ?_, rfl, rfl⟩
                simp [findTypeOrdinalSelection?]
            | succ next =>
                simp only [ConstraintRetention.openedTypeIntervalsAt, if_true]
                  at atOrdinal
                obtain ⟨found, foundResult, lowerEq, upperEq⟩ :=
                  induction atOrdinal
                let lifted : TypeOrdinalSelection
                    (OpenedOccurrence.type label name candidateLower candidateUpper
                      lowerEvidence upperEvidence :: remaining)
                    label (next + 1) :=
                  { found with
                    selected :=
                      { found.selected with
                        membership := .tail _ found.selected.membership } }
                refine ⟨lifted, ?_, lowerEq, upperEq⟩
                simp [findTypeOrdinalSelection?, foundResult, lifted]
          · simp only [ConstraintRetention.openedTypeIntervalsAt,
              if_neg same] at atOrdinal
            obtain ⟨found, foundResult, lowerEq, upperEq⟩ :=
              induction atOrdinal
            let lifted : TypeOrdinalSelection
                (OpenedOccurrence.type candidateLabel name candidateLower
                  candidateUpper lowerEvidence upperEvidence :: remaining)
                label ordinal :=
              { found with
                selected :=
                  { found.selected with
                    membership := .tail _ found.selected.membership } }
            refine ⟨lifted, ?_, lowerEq, upperEq⟩
            simp [findTypeOrdinalSelection?, same, foundResult, lifted]

theorem findCaptureOrdinalSelection?_of_getElem {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    {candidates : List (OpenedOccurrence scope symbols relations)}
    {label ordinal : Nat}
    {lower upper : Target.StaticExpr .capture
      (ManySortedFC.StaticScope scope symbols relations)}
    (atOrdinal :
      (ConstraintRetention.openedCaptureIntervalsAt label candidates)[ordinal]? =
        some { lower, upper }) :
    ∃ found : CaptureOrdinalSelection candidates label ordinal,
      findCaptureOrdinalSelection? label ordinal candidates = some found ∧
      found.lower = lower ∧ found.upper = upper := by
  induction candidates generalizing ordinal with
  | nil => simp [ConstraintRetention.openedCaptureIntervalsAt] at atOrdinal
  | cons current remaining induction =>
      cases current with
      | type candidateLabel name candidateLower candidateUpper
          lowerEvidence upperEvidence =>
          simp only [ConstraintRetention.openedCaptureIntervalsAt] at atOrdinal
          obtain ⟨found, foundResult, lowerEq, upperEq⟩ :=
            induction atOrdinal
          let lifted : CaptureOrdinalSelection
              (OpenedOccurrence.type candidateLabel name candidateLower
                candidateUpper lowerEvidence upperEvidence :: remaining)
              label ordinal :=
            { found with
              selected :=
                { found.selected with
                  membership := .tail _ found.selected.membership } }
          refine ⟨lifted, ?_, lowerEq, upperEq⟩
          simp [findCaptureOrdinalSelection?, foundResult, lifted]
      | classifier candidateLabel name candidateLower candidateUpper
          lowerEvidence upperEvidence =>
          simp only [ConstraintRetention.openedCaptureIntervalsAt] at atOrdinal
          obtain ⟨found, foundResult, lowerEq, upperEq⟩ :=
            induction atOrdinal
          let lifted : CaptureOrdinalSelection
              (OpenedOccurrence.classifier candidateLabel name candidateLower
                candidateUpper lowerEvidence upperEvidence :: remaining)
              label ordinal :=
            { found with
              selected :=
                { found.selected with
                  membership := .tail _ found.selected.membership } }
          refine ⟨lifted, ?_, lowerEq, upperEq⟩
          simp [findCaptureOrdinalSelection?, foundResult, lifted]
      | capture candidateLabel name candidateLower candidateUpper
          lowerEvidence upperEvidence =>
          by_cases same : candidateLabel = label
          · subst candidateLabel
            cases ordinal with
            | zero =>
                simp only [ConstraintRetention.openedCaptureIntervalsAt,
                  if_true]
                  at atOrdinal
                cases atOrdinal
                refine ⟨{
                  lower := lower
                  upper := upper
                  selected :=
                    { name, lowerEvidence, upperEvidence,
                      membership := .head _ } }, ?_, rfl, rfl⟩
                simp [findCaptureOrdinalSelection?]
            | succ next =>
                simp only [ConstraintRetention.openedCaptureIntervalsAt]
                  at atOrdinal
                obtain ⟨found, foundResult, lowerEq, upperEq⟩ :=
                  induction atOrdinal
                let lifted : CaptureOrdinalSelection
                    (OpenedOccurrence.capture label name candidateLower
                      candidateUpper lowerEvidence upperEvidence :: remaining)
                    label (next + 1) :=
                  { found with
                    selected :=
                      { found.selected with
                        membership := .tail _ found.selected.membership } }
                refine ⟨lifted, ?_, lowerEq, upperEq⟩
                simp [findCaptureOrdinalSelection?, foundResult, lifted]
          · simp only [ConstraintRetention.openedCaptureIntervalsAt,
              if_neg same] at atOrdinal
            obtain ⟨found, foundResult, lowerEq, upperEq⟩ :=
              induction atOrdinal
            let lifted : CaptureOrdinalSelection
                (OpenedOccurrence.capture candidateLabel name candidateLower
                  candidateUpper lowerEvidence upperEvidence :: remaining)
                label ordinal :=
              { found with
                selected :=
                  { found.selected with
                    membership := .tail _ found.selected.membership } }
            refine ⟨lifted, ?_, lowerEq, upperEq⟩
            simp [findCaptureOrdinalSelection?, same, foundResult, lifted]

/-! ## Total source-occurrence selection for prepared objects -/

structure PreparedTypeOccurrence {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {sourceObject : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core sourceObject)
    {label : Nat} {lower upper : Source.Ty sourceScope}
    (occurrence : sourceObject.interface.HasTypeOccurrence label lower upper) where
  translated : DOTCapture.Intersections.Interval
    (Target.StaticExpr .type
      (ManySortedFC.SymbolScope targetScope
        prepared.object.encoding.symbols))
  translation : Preparation.Compile.translateMemberIntervals
    (sort := .type)
    (core.layout.renameTarget
      (ManySortedFC.Rename.weakenSymbols
        prepared.object.encoding.symbols))
    prepared.object.encoding.prepared.members
    [{ lower := .type lower, upper := .type upper }] = .ok [translated]
  selection : TypeOrdinalSelection
    prepared.object.encoding.openedOccurrences label
    (ConstraintRetention.RawOccurrence.typeOrdinal occurrence)
  lowerTranslation : selection.lower = translated.lower.rename
    (ManySortedFC.Rename.weakenMany
      (ManySortedFC.SymbolScope targetScope
        prepared.object.encoding.symbols)
      (ManySortedFC.evidenceKinds prepared.object.encoding.relations))
  upperTranslation : selection.upper = translated.upper.rename
    (ManySortedFC.Rename.weakenMany
      (ManySortedFC.SymbolScope targetScope
        prepared.object.encoding.symbols)
      (ManySortedFC.evidenceKinds prepared.object.encoding.relations))

structure PreparedCaptureOccurrence {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {sourceObject : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core sourceObject)
    {label : Nat} {lower upper : Source.Capture sourceScope}
    (occurrence : sourceObject.interface.HasCaptureOccurrence label lower upper) where
  translated : DOTCapture.Intersections.Interval
    (Target.StaticExpr .capture
      (ManySortedFC.SymbolScope targetScope
        prepared.object.encoding.symbols))
  translation : Preparation.Compile.translateMemberIntervals
    (sort := .capture)
    (core.layout.renameTarget
      (ManySortedFC.Rename.weakenSymbols
        prepared.object.encoding.symbols))
    prepared.object.encoding.prepared.members
    [{ lower := .capture lower, upper := .capture upper }] = .ok [translated]
  selection : CaptureOrdinalSelection
    prepared.object.encoding.openedOccurrences label
    (ConstraintRetention.RawOccurrence.captureOrdinal occurrence)
  lowerTranslation : selection.lower = translated.lower.rename
    (ManySortedFC.Rename.weakenMany
      (ManySortedFC.SymbolScope targetScope
        prepared.object.encoding.symbols)
      (ManySortedFC.evidenceKinds prepared.object.encoding.relations))
  upperTranslation : selection.upper = translated.upper.rename
    (ManySortedFC.Rename.weakenMany
      (ManySortedFC.SymbolScope targetScope
        prepared.object.encoding.symbols)
      (ManySortedFC.evidenceKinds prepared.object.encoding.relations))

def selectPreparedTypeOccurrence? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceObject : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core sourceObject)
    {label : Nat} {lower upper : Source.Ty sourceScope}
    (occurrence : sourceObject.interface.HasTypeOccurrence label lower upper) :
    Option (PreparedTypeOccurrence core prepared occurrence) :=
  match translatedResult : Preparation.Compile.translateMemberIntervals
      (sort := .type)
      (core.layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols
          prepared.object.encoding.symbols))
      prepared.object.encoding.prepared.members
      [{ lower := .type lower, upper := .type upper }] with
  | .ok [translated] =>
      let rho := ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope targetScope
          prepared.object.encoding.symbols)
        (ManySortedFC.evidenceKinds prepared.object.encoding.relations)
      match findTypeOrdinalSelection? label
          (ConstraintRetention.RawOccurrence.typeOrdinal occurrence)
          prepared.object.encoding.openedOccurrences with
      | some selection =>
          if lowerTranslation : selection.lower = translated.lower.rename rho then
            if upperTranslation : selection.upper = translated.upper.rename rho then
              some ⟨translated, translatedResult, selection,
                lowerTranslation, upperTranslation⟩
            else none
          else none
      | none => none
  | _ => none

def selectPreparedCaptureOccurrence? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceObject : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core sourceObject)
    {label : Nat} {lower upper : Source.Capture sourceScope}
    (occurrence : sourceObject.interface.HasCaptureOccurrence label lower upper) :
    Option (PreparedCaptureOccurrence core prepared occurrence) :=
  match translatedResult : Preparation.Compile.translateMemberIntervals
      (sort := .capture)
      (core.layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols
          prepared.object.encoding.symbols))
      prepared.object.encoding.prepared.members
      [{ lower := .capture lower, upper := .capture upper }] with
  | .ok [translated] =>
      let rho := ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope targetScope
          prepared.object.encoding.symbols)
        (ManySortedFC.evidenceKinds prepared.object.encoding.relations)
      match findCaptureOrdinalSelection? label
          (ConstraintRetention.RawOccurrence.captureOrdinal occurrence)
          prepared.object.encoding.openedOccurrences with
      | some selection =>
          if lowerTranslation : selection.lower = translated.lower.rename rho then
            if upperTranslation : selection.upper = translated.upper.rename rho then
              some ⟨translated, translatedResult, selection,
                lowerTranslation, upperTranslation⟩
            else none
          else none
      | none => none
  | _ => none

theorem selectPreparedTypeOccurrence?_isSome
    {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceObject : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core sourceObject)
    {label : Nat} {lower upper : Source.Ty sourceScope}
    (occurrence : sourceObject.interface.HasTypeOccurrence label lower upper) :
    (selectPreparedTypeOccurrence? prepared occurrence).isSome = true := by
  have interfaceSuccess := ConstraintRetention.prepareObject_interface
    core.layout sourceObject prepared.prepared
  obtain ⟨retained⟩ := ConstraintRetention.preparedTypeIntervalAt_of_raw
    core.layout sourceObject.interface interfaceSuccess occurrence
  have openedAt :=
    ConstraintRetention.openedTypeIntervalsAt_openEntriesWithTail_getElem label
      (ConstraintRetention.RawOccurrence.typeOrdinal occurrence)
      prepared.object.encoding.prepared.entries
      (prepared.object.encoding.prepared.constraints.map
        PreparedConstraint.relation)
      retained.translated
      retained.targetAt
  have encodingAt :
      (ConstraintRetention.openedTypeIntervalsAt label
        prepared.object.encoding.openedOccurrences)[
          ConstraintRetention.RawOccurrence.typeOrdinal occurrence]? = some {
            lower := retained.translated.lower.rename
              (ManySortedFC.Rename.weakenMany
                (ManySortedFC.SymbolScope targetScope
                  prepared.object.encoding.symbols)
                (ManySortedFC.evidenceKinds
                  prepared.object.encoding.relations))
            upper := retained.translated.upper.rename
              (ManySortedFC.Rename.weakenMany
                (ManySortedFC.SymbolScope targetScope
                  prepared.object.encoding.symbols)
                (ManySortedFC.evidenceKinds
                  prepared.object.encoding.relations)) } := by
    simpa [Encoding.openedOccurrences] using openedAt
  obtain ⟨found, foundResult, lowerEq, upperEq⟩ :=
    findTypeOrdinalSelection?_of_getElem encodingAt
  have translationSuccess : Preparation.Compile.translateMemberIntervals
      (sort := .type)
      (core.layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols
          prepared.object.encoding.symbols))
      prepared.object.encoding.prepared.members
      [{ lower := .type lower, upper := .type upper }] =
        .ok [retained.translated] := by
    simpa only [Encoding.symbols] using retained.translation
  unfold selectPreparedTypeOccurrence?
  split <;> simp_all
  split <;> simp_all
  all_goals first | rfl | contradiction

theorem selectPreparedCaptureOccurrence?_isSome
    {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceObject : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core sourceObject)
    {label : Nat} {lower upper : Source.Capture sourceScope}
    (occurrence : sourceObject.interface.HasCaptureOccurrence label lower upper) :
    (selectPreparedCaptureOccurrence? prepared occurrence).isSome = true := by
  have interfaceSuccess := ConstraintRetention.prepareObject_interface
    core.layout sourceObject prepared.prepared
  obtain ⟨retained⟩ := ConstraintRetention.preparedCaptureIntervalAt_of_raw
    core.layout sourceObject.interface interfaceSuccess occurrence
  have openedAt :=
    ConstraintRetention.openedCaptureIntervalsAt_openEntriesWithTail_getElem label
      (ConstraintRetention.RawOccurrence.captureOrdinal occurrence)
      prepared.object.encoding.prepared.entries
      (prepared.object.encoding.prepared.constraints.map
        PreparedConstraint.relation)
      retained.translated
      retained.targetAt
  have encodingAt :
      (ConstraintRetention.openedCaptureIntervalsAt label
        prepared.object.encoding.openedOccurrences)[
          ConstraintRetention.RawOccurrence.captureOrdinal occurrence]? = some {
            lower := retained.translated.lower.rename
              (ManySortedFC.Rename.weakenMany
                (ManySortedFC.SymbolScope targetScope
                  prepared.object.encoding.symbols)
                (ManySortedFC.evidenceKinds
                  prepared.object.encoding.relations))
            upper := retained.translated.upper.rename
              (ManySortedFC.Rename.weakenMany
                (ManySortedFC.SymbolScope targetScope
                  prepared.object.encoding.symbols)
                (ManySortedFC.evidenceKinds
                  prepared.object.encoding.relations)) } := by
    simpa [Encoding.openedOccurrences] using openedAt
  obtain ⟨found, foundResult, lowerEq, upperEq⟩ :=
    findCaptureOrdinalSelection?_of_getElem encodingAt
  have translationSuccess : Preparation.Compile.translateMemberIntervals
      (sort := .capture)
      (core.layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols
          prepared.object.encoding.symbols))
      prepared.object.encoding.prepared.members
      [{ lower := .capture lower, upper := .capture upper }] =
        .ok [retained.translated] := by
    simpa only [Encoding.symbols] using retained.translation
  unfold selectPreparedCaptureOccurrence?
  split <;> simp_all
  split <;> simp_all
  all_goals first | rfl | contradiction

/-- Convenience endpoint lookup.  Artifact generation uses the ordinal
selectors above. -/
def findTypeSelection? {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (label : Nat)
    (lower upper : Target.StaticExpr .type
      (ManySortedFC.StaticScope scope symbols relations)) :
    (candidates : List (OpenedOccurrence scope symbols relations)) ->
      Option (TypeSelection candidates label lower upper)
  | [] => none
  | .type candidateLabel name candidateLower candidateUpper
        lowerEvidence upperEvidence :: remaining =>
      if labelMatches : candidateLabel = label then
        if lowerMatches : candidateLower = lower then
          if upperMatches : candidateUpper = upper then
            some
              { name := name
                lowerEvidence := lowerEvidence
                upperEvidence := upperEvidence
                membership := by
                  subst candidateLabel
                  subst candidateLower
                  subst candidateUpper
                  exact .head _ }
          else
            (findTypeSelection? label lower upper remaining).map fun found =>
              { found with membership := .tail _ found.membership }
        else
          (findTypeSelection? label lower upper remaining).map fun found =>
            { found with membership := .tail _ found.membership }
      else
        (findTypeSelection? label lower upper remaining).map fun found =>
          { found with membership := .tail _ found.membership }
  | .capture _ _ _ _ _ _ :: remaining =>
      (findTypeSelection? label lower upper remaining).map fun found =>
        { found with membership := .tail _ found.membership }
  | .classifier _ _ _ _ _ _ :: remaining =>
      (findTypeSelection? label lower upper remaining).map fun found =>
        { found with membership := .tail _ found.membership }

def findCaptureSelection? {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (label : Nat)
    (lower upper : Target.StaticExpr .capture
      (ManySortedFC.StaticScope scope symbols relations)) :
    (candidates : List (OpenedOccurrence scope symbols relations)) ->
      Option (CaptureSelection candidates label lower upper)
  | [] => none
  | .capture candidateLabel name candidateLower candidateUpper
        lowerEvidence upperEvidence :: remaining =>
      if labelMatches : candidateLabel = label then
        if lowerMatches : candidateLower = lower then
          if upperMatches : candidateUpper = upper then
            some
              { name := name
                lowerEvidence := lowerEvidence
                upperEvidence := upperEvidence
                membership := by
                  subst candidateLabel
                  subst candidateLower
                  subst candidateUpper
                  exact .head _ }
          else
            (findCaptureSelection? label lower upper remaining).map fun found =>
              { found with membership := .tail _ found.membership }
        else
          (findCaptureSelection? label lower upper remaining).map fun found =>
            { found with membership := .tail _ found.membership }
      else
        (findCaptureSelection? label lower upper remaining).map fun found =>
          { found with membership := .tail _ found.membership }
  | .type _ _ _ _ _ _ :: remaining =>
      (findCaptureSelection? label lower upper remaining).map fun found =>
        { found with membership := .tail _ found.membership }
  | .classifier _ _ _ _ _ _ :: remaining =>
      (findCaptureSelection? label lower upper remaining).map fun found =>
        { found with membership := .tail _ found.membership }

theorem findTypeSelection_isSome_of_mem {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    {candidates : List (OpenedOccurrence scope symbols relations)}
    {label : Nat}
    {name : ManySortedFC.BVar
      (ManySortedFC.StaticScope scope symbols relations) (.symbol .type)}
    {lower upper : Target.StaticExpr .type
      (ManySortedFC.StaticScope scope symbols relations)}
    {lowerEvidence upperEvidence : ManySortedFC.BVar
      (ManySortedFC.StaticScope scope symbols relations)
      (.evidence (.inclusion .type))}
    (membership : OpenedOccurrence.type label name lower upper lowerEvidence
      upperEvidence ∈ candidates) :
    (findTypeSelection? label lower upper candidates).isSome = true := by
  induction candidates with
  | nil => cases membership
  | cons current remaining induction =>
      rcases List.mem_cons.mp membership with head | tailMembership
      · subst current
        simp [findTypeSelection?]
      · cases current with
        | type candidateLabel candidateName candidateLower candidateUpper
            candidateLowerEvidence candidateUpperEvidence =>
            by_cases labelMatches : candidateLabel = label <;>
              by_cases lowerMatches : candidateLower = lower <;>
              by_cases upperMatches : candidateUpper = upper <;>
              simp [findTypeSelection?, labelMatches, lowerMatches,
                upperMatches, induction tailMembership]
        | capture =>
            simp [findTypeSelection?, induction tailMembership]
        | classifier =>
            simp [findTypeSelection?, induction tailMembership]

theorem findCaptureSelection_isSome_of_mem {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    {candidates : List (OpenedOccurrence scope symbols relations)}
    {label : Nat}
    {name : ManySortedFC.BVar
      (ManySortedFC.StaticScope scope symbols relations) (.symbol .capture)}
    {lower upper : Target.StaticExpr .capture
      (ManySortedFC.StaticScope scope symbols relations)}
    {lowerEvidence upperEvidence : ManySortedFC.BVar
      (ManySortedFC.StaticScope scope symbols relations)
      (.evidence (.inclusion .capture))}
    (membership : OpenedOccurrence.capture label name lower upper lowerEvidence
      upperEvidence ∈ candidates) :
    (findCaptureSelection? label lower upper candidates).isSome = true := by
  induction candidates with
  | nil => cases membership
  | cons current remaining induction =>
      rcases List.mem_cons.mp membership with head | tailMembership
      · subst current
        simp [findCaptureSelection?]
      · cases current with
        | type =>
            simp [findCaptureSelection?, induction tailMembership]
        | capture candidateLabel candidateName candidateLower candidateUpper
            candidateLowerEvidence candidateUpperEvidence =>
            by_cases labelMatches : candidateLabel = label <;>
              by_cases lowerMatches : candidateLower = lower <;>
              by_cases upperMatches : candidateUpper = upper <;>
              simp [findCaptureSelection?, labelMatches, lowerMatches,
                upperMatches, induction tailMembership]
        | classifier =>
            simp [findCaptureSelection?, induction tailMembership]

/-! ## Exact prepared-object lookup -/

structure PreparedTypeSelection {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {sourceObject : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core sourceObject)
    (label : Nat) (lower upper : Source.Ty sourceScope) where
  translated : DOTCapture.Intersections.Interval
    (Target.StaticExpr .type
      (ManySortedFC.SymbolScope targetScope
        prepared.object.encoding.symbols))
  translation : Preparation.Compile.translateMemberIntervals
    (sort := .type)
    (core.layout.renameTarget
      (ManySortedFC.Rename.weakenSymbols
        prepared.object.encoding.symbols))
    prepared.object.encoding.prepared.members
    [{ lower := .type lower, upper := .type upper }] = .ok [translated]
  selected : TypeSelection prepared.object.encoding.openedOccurrences label
    (translated.lower.rename
      (ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope targetScope
          prepared.object.encoding.symbols)
        (ManySortedFC.evidenceKinds
          prepared.object.encoding.relations)))
    (translated.upper.rename
      (ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope targetScope
          prepared.object.encoding.symbols)
        (ManySortedFC.evidenceKinds
          prepared.object.encoding.relations)))

structure PreparedCaptureSelection {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {sourceObject : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core sourceObject)
    (label : Nat) (lower upper : Source.Capture sourceScope) where
  translated : DOTCapture.Intersections.Interval
    (Target.StaticExpr .capture
      (ManySortedFC.SymbolScope targetScope
        prepared.object.encoding.symbols))
  translation : Preparation.Compile.translateMemberIntervals
    (sort := .capture)
    (core.layout.renameTarget
      (ManySortedFC.Rename.weakenSymbols
        prepared.object.encoding.symbols))
    prepared.object.encoding.prepared.members
    [{ lower := .capture lower, upper := .capture upper }] = .ok [translated]
  selected : CaptureSelection prepared.object.encoding.openedOccurrences label
    (translated.lower.rename
      (ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope targetScope
          prepared.object.encoding.symbols)
        (ManySortedFC.evidenceKinds
          prepared.object.encoding.relations)))
    (translated.upper.rename
      (ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope targetScope
          prepared.object.encoding.symbols)
        (ManySortedFC.evidenceKinds
          prepared.object.encoding.relations)))

def findPreparedTypeSelection? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceObject : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core sourceObject)
    (label : Nat) (lower upper : Source.Ty sourceScope) :
    Option (PreparedTypeSelection core prepared label lower upper) :=
  match translatedResult : Preparation.Compile.translateMemberIntervals
      (sort := .type)
      (core.layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols
          prepared.object.encoding.symbols))
      prepared.object.encoding.prepared.members
      [{ lower := .type lower, upper := .type upper }] with
  | .ok [translated] =>
      let rho := ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope targetScope
          prepared.object.encoding.symbols)
        (ManySortedFC.evidenceKinds prepared.object.encoding.relations)
      (findTypeSelection? label (translated.lower.rename rho)
        (translated.upper.rename rho)
        prepared.object.encoding.openedOccurrences).map fun selected =>
          { translated, translation := translatedResult, selected }
  | _ => none

def findPreparedCaptureSelection? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceObject : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core sourceObject)
    (label : Nat) (lower upper : Source.Capture sourceScope) :
    Option (PreparedCaptureSelection core prepared label lower upper) :=
  match translatedResult : Preparation.Compile.translateMemberIntervals
      (sort := .capture)
      (core.layout.renameTarget
        (ManySortedFC.Rename.weakenSymbols
          prepared.object.encoding.symbols))
      prepared.object.encoding.prepared.members
      [{ lower := .capture lower, upper := .capture upper }] with
  | .ok [translated] =>
      let rho := ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope targetScope
          prepared.object.encoding.symbols)
        (ManySortedFC.evidenceKinds prepared.object.encoding.relations)
      (findCaptureSelection? label (translated.lower.rename rho)
        (translated.upper.rename rho)
        prepared.object.encoding.openedOccurrences).map fun selected =>
          { translated, translation := translatedResult, selected }
  | _ => none

/-! ## Retained classifier evidence is discoverable -/

/-- A raw classifier-member occurrence contributes a lower-bound assumption
that the compiler's non-consuming evidence search can find in every ambient
context extended by the prepared object theory.  The chosen coordinate also
retains the exact source-to-target interval translation equation. -/
theorem findClassifierLowerEvidenceVariable?_isSome_of_raw
    {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {label : Nat}
    {lower upper : Source.ClassifierExpr sourceScope}
    (occurrence : interface.HasClassifierOccurrence label lower upper)
    (context : Target.Ctx targetScope) :
    let coordinate := ConstraintRetention.classifierCoordinatesOfRaw
      layout interface success occurrence
    let rho := ManySortedFC.Rename.weakenMany
      (ManySortedFC.SymbolScope targetScope prepared.symbols)
      (ManySortedFC.evidenceKinds prepared.relations)
    (EvidenceElaboration.findEvidenceVariable?
      (context.extendTheory (encode prepared).theory)
      ((ManySortedFC.Proposition.inclusion coordinate.translated.lower
        (.classifier (.var coordinate.name))).rename rho)).isSome = true := by
  dsimp only
  exact EvidenceElaboration.findEvidenceVariable?_isSome_of_lookup
    (context.extendTheory (encode prepared).theory)
    ((ManySortedFC.Proposition.inclusion
      (ConstraintRetention.classifierCoordinatesOfRaw
        layout interface success occurrence).translated.lower
      (.classifier (.var
        (ConstraintRetention.classifierCoordinatesOfRaw
          layout interface success occurrence).name))).rename
      (ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope targetScope prepared.symbols)
        (ManySortedFC.evidenceKinds prepared.relations)))
    ((ConstraintRetention.classifierCoordinatesOfRaw
      layout interface success occurrence).lower.toEvidenceBVar
      (ManySortedFC.SymbolScope targetScope prepared.symbols))
    (ConstraintRetention.ClassifierCoordinates.lowerLookup
      (ConstraintRetention.classifierCoordinatesOfRaw
        layout interface success occurrence) context)

/-- Upper-bound counterpart of
`findClassifierLowerEvidenceVariable?_isSome_of_raw`. -/
theorem findClassifierUpperEvidenceVariable?_isSome_of_raw
    {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {label : Nat}
    {lower upper : Source.ClassifierExpr sourceScope}
    (occurrence : interface.HasClassifierOccurrence label lower upper)
    (context : Target.Ctx targetScope) :
    let coordinate := ConstraintRetention.classifierCoordinatesOfRaw
      layout interface success occurrence
    let rho := ManySortedFC.Rename.weakenMany
      (ManySortedFC.SymbolScope targetScope prepared.symbols)
      (ManySortedFC.evidenceKinds prepared.relations)
    (EvidenceElaboration.findEvidenceVariable?
      (context.extendTheory (encode prepared).theory)
      ((ManySortedFC.Proposition.inclusion
        (.classifier (.var coordinate.name)) coordinate.translated.upper).rename
        rho)).isSome = true := by
  dsimp only
  exact EvidenceElaboration.findEvidenceVariable?_isSome_of_lookup
    (context.extendTheory (encode prepared).theory)
    ((ManySortedFC.Proposition.inclusion
      (.classifier (.var
        (ConstraintRetention.classifierCoordinatesOfRaw
          layout interface success occurrence).name))
      (ConstraintRetention.classifierCoordinatesOfRaw
        layout interface success occurrence).translated.upper).rename
      (ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope targetScope prepared.symbols)
        (ManySortedFC.evidenceKinds prepared.relations)))
    ((ConstraintRetention.classifierCoordinatesOfRaw
      layout interface success occurrence).upper.toEvidenceBVar
      (ManySortedFC.SymbolScope targetScope prepared.symbols))
    (ConstraintRetention.ClassifierCoordinates.upperLookup
      (ConstraintRetention.classifierCoordinatesOfRaw
        layout interface success occurrence) context)

/-- A raw classifier-disjointness occurrence survives preparation as an exact
opened-theory assumption, and exact evidence search therefore succeeds. -/
theorem findClassifierDisjointEvidenceVariable?_isSome_of_raw
    {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {left right : Source.ClassifierExpr sourceScope}
    (occurrence : interface.HasClassifierDisjointOccurrence left right)
    (context : Target.Ctx targetScope) :
    let coordinate := ConstraintRetention.classifierDisjointCoordinatesOfRaw
      layout interface success occurrence
    let rho := ManySortedFC.Rename.weakenMany
      (ManySortedFC.SymbolScope targetScope prepared.symbols)
      (ManySortedFC.evidenceKinds prepared.relations)
    (EvidenceElaboration.findEvidenceVariable?
      (context.extendTheory (encode prepared).theory)
      (coordinate.translated.proposition.rename rho)).isSome = true := by
  dsimp only
  exact EvidenceElaboration.findEvidenceVariable?_isSome_of_lookup
    (context.extendTheory (encode prepared).theory)
    ((ConstraintRetention.classifierDisjointCoordinatesOfRaw
      layout interface success occurrence).translated.proposition.rename
      (ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope targetScope prepared.symbols)
        (ManySortedFC.evidenceKinds prepared.relations)))
    ((ConstraintRetention.classifierDisjointCoordinatesOfRaw
      layout interface success occurrence).reference.toEvidenceBVar
      (ManySortedFC.SymbolScope targetScope prepared.symbols))
    (ConstraintRetention.ConstraintCoordinates.lookup
      (ConstraintRetention.classifierDisjointCoordinatesOfRaw
        layout interface success occurrence) context)

/-- A raw capture-has-kind occurrence survives preparation as an exact
opened-theory assumption, and exact evidence search therefore succeeds. -/
theorem findCaptureHasKindEvidenceVariable?_isSome_of_raw
    {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (interface : Source.Interface sourceScope)
    {prepared : PreparedSignature targetScope}
    (success : Preparation.collectAndPrepare layout interface = .ok prepared)
    {capture : Source.Capture sourceScope}
    {classifier : Source.ClassifierExpr sourceScope}
    (occurrence : interface.HasCaptureKindOccurrence capture classifier)
    (context : Target.Ctx targetScope) :
    let coordinate := ConstraintRetention.captureHasKindCoordinatesOfRaw
      layout interface success occurrence
    let rho := ManySortedFC.Rename.weakenMany
      (ManySortedFC.SymbolScope targetScope prepared.symbols)
      (ManySortedFC.evidenceKinds prepared.relations)
    (EvidenceElaboration.findEvidenceVariable?
      (context.extendTheory (encode prepared).theory)
      (coordinate.translated.proposition.rename rho)).isSome = true := by
  dsimp only
  exact EvidenceElaboration.findEvidenceVariable?_isSome_of_lookup
    (context.extendTheory (encode prepared).theory)
    ((ConstraintRetention.captureHasKindCoordinatesOfRaw
      layout interface success occurrence).translated.proposition.rename
      (ManySortedFC.Rename.weakenMany
        (ManySortedFC.SymbolScope targetScope prepared.symbols)
        (ManySortedFC.evidenceKinds prepared.relations)))
    ((ConstraintRetention.captureHasKindCoordinatesOfRaw
      layout interface success occurrence).reference.toEvidenceBVar
      (ManySortedFC.SymbolScope targetScope prepared.symbols))
    (ConstraintRetention.ConstraintCoordinates.lookup
      (ConstraintRetention.captureHasKindCoordinatesOfRaw
        layout interface success occurrence) context)

end DOTCaptureToManySortedFC.ModalIntersections.ObjectOccurrenceEvidence
