import Coercions.Translation.ManySorted.Intersections.EncodingMetatheory
import Coercions.Translation.ManySorted.Intersections.Preparation
import Coercions.ManySortedFC.TheoryModelChecker

/-!
# Names-first intersection encoding regressions

These examples inspect the emitted type/capture constraints and their exact
opened evidence coordinates.  The final examples distinguish a well-formed
generated theory from a realizable concrete model: contradictory bounds are
retained faithfully, then rejected when a caller supplies bogus reflexivity
evidence as a model.
-/

namespace DOTCaptureToManySortedFC.Intersections.EncodingExamples

open ManySortedFC
open DOTCaptureToManySortedFC.Intersections.Encoding

/-! ## Two type members and two capture members -/

abbrev FourSymbolScope : Sig :=
  SymbolScope [] [.type, .type, .capture, .capture]

def mixedPrepared : PreparedSignature [] where
  symbols := [.type, .type, .capture, .capture]
  entries :=
    [.type 0 .here [⟨.type .bot, .type .top⟩],
      .type 1 (.there .here) [⟨.type .one, .type .one⟩],
      .capture 2 (.there (.there .here))
        [⟨.capture .empty, .capture .empty⟩],
      .capture 3 (.there (.there (.there .here)))
        [⟨.capture .empty, .capture (.union .empty .empty)⟩]]

def mixedEncoding : Encoding [] := encode mixedPrepared

theorem mixed_emits_eight_relations :
    mixedEncoding.relations.length = 8 := by
  native_decide

theorem mixed_retains_source_order_and_sorts :
    mixedEncoding.openedOccurrences.map OpenedOccurrence.label =
        [0, 1, 2, 3] ∧
      mixedEncoding.openedOccurrences.map OpenedOccurrence.sort =
        [.type, .type, .capture, .capture] := by
  native_decide

theorem mixed_opened_occurrences_have_exact_evidence
    (occurrence : OpenedOccurrence [] mixedEncoding.symbols
      mixedEncoding.relations)
    (membership : occurrence ∈ mixedEncoding.openedOccurrences) :
    occurrence.EvidenceMatches
      (Ctx.nil.extendTheory mixedEncoding.theory) :=
  Encoding.opened_occurrence_evidence_matches Ctx.nil mixedEncoding
    occurrence membership

/-! ## Repeated declarations retain distinct evidence and one shared name -/

def repeatedPrepared : PreparedSignature [] where
  symbols := [.type, .capture]
  entries :=
    [.type 7 .here
      [⟨.type .bot, .type .top⟩, ⟨.type .one, .type .top⟩],
      .capture 9 (.there .here)
      [⟨.capture .empty, .capture (.union .empty .empty)⟩,
        ⟨.capture .empty, .capture .empty⟩]]

def repeatedEncoding : Encoding [] := encode repeatedPrepared

theorem repeated_retains_all_four_occurrences :
    repeatedEncoding.openedOccurrences.map OpenedOccurrence.label =
        [7, 7, 9, 9] ∧
      repeatedEncoding.relations.length = 8 := by
  native_decide

theorem repeated_occurrences_share_names_within_each_sort :
    match repeatedEncoding.openedOccurrences with
    | [firstType, secondType, firstCapture, secondCapture] =>
        firstType.member = secondType.member ∧
          firstCapture.member = secondCapture.member
    | _ => False := by
  constructor <;> rfl

theorem repeated_opened_occurrences_have_exact_evidence
    (occurrence : OpenedOccurrence [] repeatedEncoding.symbols
      repeatedEncoding.relations)
    (membership : occurrence ∈ repeatedEncoding.openedOccurrences) :
    occurrence.EvidenceMatches
      (Ctx.nil.extendTheory repeatedEncoding.theory) :=
  Encoding.opened_occurrence_evidence_matches Ctx.nil repeatedEncoding
    occurrence membership

/-! ## Repeated plausible intervals can be jointly inconsistent -/

/-- Each exact interval below has a model by itself, but collection gives
both occurrences one member identity, so their conjunction has no common
`One`/`Top` witness. -/
def jointlyInconsistentRepeated : Preparation.Source.Interface 0 :=
  .inter
    (.typeMember 13 .one .one)
    (.typeMember 13 .top .top)

def jointlyInconsistentPrepared : PreparedSignature [] where
  symbols := [.type]
  entries :=
    [.type 13 .here
      [⟨.type .one, .type .one⟩, ⟨.type .top, .type .top⟩]]

theorem jointly_inconsistent_repeated_prepares_under_one_name :
    Preparation.collectAndPrepare (Preparation.emptyLayout [])
      jointlyInconsistentRepeated = .ok jointlyInconsistentPrepared := by
  rfl

def jointlyInconsistentEncoding : Encoding [] :=
  encode jointlyInconsistentPrepared

theorem jointly_inconsistent_repeated_retains_both_occurrences :
    jointlyInconsistentPrepared.members = [MemberName.type 13 .here] ∧
      jointlyInconsistentEncoding.openedOccurrences.length = 2 ∧
      jointlyInconsistentEncoding.relations.length = 4 := by
  native_decide

theorem jointly_inconsistent_occurrences_use_the_shared_name :
    match jointlyInconsistentEncoding.openedOccurrences with
    | [first, second] => first.member = second.member
    | _ => False := by
  rfl

def exactOnePrepared : PreparedSignature [] where
  symbols := [.type]
  entries := [.type 13 .here [⟨.type .one, .type .one⟩]]

def exactOneEncoding : Encoding [] := encode exactOnePrepared

def exactOneWitness : SymbolArgs [] exactOneEncoding.symbols :=
  .cons (.type .one) .nil

def exactOneEvidence : EvidenceArgs [] exactOneEncoding.relations :=
  .cons (.inclusionRefl (.type .one))
    (.cons (.inclusionRefl (.type .one)) .nil)

theorem exact_one_interval_is_individually_realizable :
    (Theory.checkModel Ctx.nil exactOneEncoding.theory exactOneWitness
      exactOneEvidence).isSome = true := by
  native_decide

def exactTopPrepared : PreparedSignature [] where
  symbols := [.type]
  entries := [.type 13 .here [⟨.type .top, .type .top⟩]]

def exactTopEncoding : Encoding [] := encode exactTopPrepared

def exactTopWitness : SymbolArgs [] exactTopEncoding.symbols :=
  .cons (.type .top) .nil

def exactTopEvidence : EvidenceArgs [] exactTopEncoding.relations :=
  .cons (.inclusionRefl (.type .top))
    (.cons (.inclusionRefl (.type .top)) .nil)

theorem exact_top_interval_is_individually_realizable :
    (Theory.checkModel Ctx.nil exactTopEncoding.theory exactTopWitness
      exactTopEvidence).isSome = true := by
  native_decide

/-- The shared witness `One` satisfies the first retained occurrence.  The
certificate offered for the second occurrence's lower bound proves
`Top ≤ Top`, not the required `Top ≤ One`, so the target checker rejects
the combined model. -/
def jointlyInconsistentWitness :
    SymbolArgs [] jointlyInconsistentEncoding.symbols :=
  .cons (.type .one) .nil

def jointlyInconsistentEvidence :
    EvidenceArgs [] jointlyInconsistentEncoding.relations :=
  .cons (.inclusionRefl (.type .one))
    (.cons (.inclusionRefl (.type .one))
      (.cons (.inclusionRefl (.type .top))
        (.cons (.typeTop .one) .nil)))

theorem jointly_inconsistent_repeated_model_is_rejected :
    (Theory.checkModel Ctx.nil jointlyInconsistentEncoding.theory
      jointlyInconsistentWitness jointlyInconsistentEvidence).isNone =
        true := by
  native_decide

/-! ## Contradictory bounds are retained, not normalized away -/

def badTypePrepared : PreparedSignature [] where
  symbols := [.type]
  entries := [.type 11 .here [⟨.type .top, .type .bot⟩]]

def badTypeEncoding : Encoding [] := encode badTypePrepared

def badTypeWitness : SymbolArgs [] badTypeEncoding.symbols :=
  .cons (.type .top) .nil

def badTypeEvidence : EvidenceArgs [] badTypeEncoding.relations :=
  .cons (.inclusionRefl (.type .top))
    (.cons (.inclusionRefl (.type .top)) .nil)

theorem bad_type_bounds_are_emitted_with_opened_evidence
    (occurrence : OpenedOccurrence [] badTypeEncoding.symbols
      badTypeEncoding.relations)
    (membership : occurrence ∈ badTypeEncoding.openedOccurrences) :
    occurrence.EvidenceMatches
      (Ctx.nil.extendTheory badTypeEncoding.theory) :=
  Encoding.opened_occurrence_evidence_matches Ctx.nil badTypeEncoding
    occurrence membership

theorem bad_type_model_is_rejected :
    (Theory.checkModel Ctx.nil badTypeEncoding.theory badTypeWitness
      badTypeEvidence).isNone = true := by
  native_decide

abbrev CapabilityScope : Sig := ([] : Sig) ▹ .term

def capabilityContext : Ctx CapabilityScope :=
  Ctx.nil.extendTerm .one

def badCapturePrepared : PreparedSignature CapabilityScope where
  symbols := [.capture]
  entries :=
    [.capture 12 .here
      [⟨.capture (.singleton (.there .here)), .capture .empty⟩]]

def badCaptureEncoding : Encoding CapabilityScope :=
  encode badCapturePrepared

def badCaptureWitness : SymbolArgs CapabilityScope
    badCaptureEncoding.symbols :=
  .cons (.capture (.singleton .here)) .nil

def badCaptureEvidence : EvidenceArgs CapabilityScope
    badCaptureEncoding.relations :=
  .cons (.inclusionRefl (.capture (.singleton .here)))
    (.cons (.inclusionRefl (.capture (.singleton .here))) .nil)

theorem bad_capture_bounds_are_emitted_with_opened_evidence
    (occurrence : OpenedOccurrence CapabilityScope
      badCaptureEncoding.symbols badCaptureEncoding.relations)
    (membership : occurrence ∈ badCaptureEncoding.openedOccurrences) :
    occurrence.EvidenceMatches
      (capabilityContext.extendTheory badCaptureEncoding.theory) :=
  Encoding.opened_occurrence_evidence_matches capabilityContext
    badCaptureEncoding occurrence membership

theorem bad_capture_model_is_rejected :
    (Theory.checkModel capabilityContext badCaptureEncoding.theory
      badCaptureWitness badCaptureEvidence).isNone = true := by
  native_decide

end DOTCaptureToManySortedFC.Intersections.EncodingExamples
