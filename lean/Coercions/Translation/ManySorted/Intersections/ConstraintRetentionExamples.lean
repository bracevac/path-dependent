import Coercions.Translation.ManySorted.Intersections.ConstraintRetention

/-!
# End-to-end constraint-retention regressions

The raw tree below repeats one type label and one capture label.  Its first
type interval is deliberately inconsistent.  Collection and preparation
still retain all four occurrences, and the per-occurrence theorem reaches
the exact target propositions under the two shared names.
-/

namespace DOTCaptureToManySortedFC.Intersections.ConstraintRetentionExamples

open DOTCaptureToManySortedFC.Intersections
open Encoding
open Preparation
open ConstraintRetention

def repeatedRaw : Preparation.Source.Interface 0 :=
  .inter
    (.typeMember 7 .top .bot)
    (.inter
      (.captureMember 9 .empty (.union .empty .empty))
      (.inter
        (.typeMember 7 .one .top)
        (.captureMember 9 .empty .empty)))

def repeatedPrepared : PreparedSignature [] where
  symbols := [.type, .capture]
  entries :=
    [.type 7 .here
      [⟨.type .top, .type .bot⟩, ⟨.type .one, .type .top⟩],
      .capture 9 (.there .here)
      [⟨.capture .empty, .capture (.union .empty .empty)⟩,
        ⟨.capture .empty, .capture .empty⟩]]

theorem repeated_raw_prepares_without_satisfiability_check :
    collectAndPrepare (emptyLayout []) repeatedRaw = .ok repeatedPrepared := by
  rfl

def badTypeOccurrence : ConstraintRetention.SourceOccurrence 0 :=
  .type 7 ⟨.type .top, .type .bot⟩

def secondTypeOccurrence : ConstraintRetention.SourceOccurrence 0 :=
  .type 7 ⟨.type .one, .type .top⟩

def firstCaptureOccurrence : ConstraintRetention.SourceOccurrence 0 :=
  .capture 9 ⟨.capture .empty, .capture (.union .empty .empty)⟩

def secondCaptureOccurrence : ConstraintRetention.SourceOccurrence 0 :=
  .capture 9 ⟨.capture .empty, .capture .empty⟩

theorem bad_type_is_a_raw_occurrence :
    badTypeOccurrence ∈ rawOccurrences repeatedRaw := by
  simp [badTypeOccurrence, rawOccurrences, repeatedRaw]

theorem second_type_is_a_raw_occurrence :
    secondTypeOccurrence ∈ rawOccurrences repeatedRaw := by
  simp [secondTypeOccurrence, rawOccurrences, repeatedRaw]

theorem first_capture_is_a_raw_occurrence :
    firstCaptureOccurrence ∈ rawOccurrences repeatedRaw := by
  simp [firstCaptureOccurrence, rawOccurrences, repeatedRaw]

theorem second_capture_is_a_raw_occurrence :
    secondCaptureOccurrence ∈ rawOccurrences repeatedRaw := by
  simp [secondCaptureOccurrence, rawOccurrences, repeatedRaw]

theorem bad_type_reaches_its_exact_shared_name_propositions :
    Emitted repeatedPrepared
      (Compile.weakenLayout (emptyLayout []) repeatedPrepared.symbols)
      badTypeOccurrence :=
  collectAndPrepare_emits_raw_occurrence (emptyLayout []) repeatedRaw
    repeated_raw_prepares_without_satisfiability_check badTypeOccurrence
    bad_type_is_a_raw_occurrence

theorem second_type_reaches_the_same_shared_name :
    Emitted repeatedPrepared
      (Compile.weakenLayout (emptyLayout []) repeatedPrepared.symbols)
      secondTypeOccurrence :=
  collectAndPrepare_emits_raw_occurrence (emptyLayout []) repeatedRaw
    repeated_raw_prepares_without_satisfiability_check secondTypeOccurrence
    second_type_is_a_raw_occurrence

theorem first_capture_reaches_its_exact_shared_name_propositions :
    Emitted repeatedPrepared
      (Compile.weakenLayout (emptyLayout []) repeatedPrepared.symbols)
      firstCaptureOccurrence :=
  collectAndPrepare_emits_raw_occurrence (emptyLayout []) repeatedRaw
    repeated_raw_prepares_without_satisfiability_check firstCaptureOccurrence
    first_capture_is_a_raw_occurrence

theorem second_capture_reaches_the_same_shared_name :
    Emitted repeatedPrepared
      (Compile.weakenLayout (emptyLayout []) repeatedPrepared.symbols)
      secondCaptureOccurrence :=
  collectAndPrepare_emits_raw_occurrence (emptyLayout []) repeatedRaw
    repeated_raw_prepares_without_satisfiability_check secondCaptureOccurrence
    second_capture_is_a_raw_occurrence

theorem repeated_raw_uses_exactly_two_shared_names :
    repeatedPrepared.members =
      [MemberName.type 7 .here, MemberName.capture 9 (.there .here)] := by
  rfl

end DOTCaptureToManySortedFC.Intersections.ConstraintRetentionExamples
