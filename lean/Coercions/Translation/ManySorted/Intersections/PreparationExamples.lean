import Coercions.Translation.ManySorted.Intersections.PreparationMetatheory

/-!
# Two-phase preparation regressions

The examples exercise name allocation and bound resolution only.  They do not
choose or inspect a runtime representation for objects.
-/

namespace DOTCaptureToManySortedFC.Intersections.Preparation
namespace Examples

open Encoding

/-! ## Forward and backward local references -/

def mutuallyReferringTypeBounds : Source.Interface 0 :=
  .inter
    (.typeMember 0 (.ref (.localTypeMember 1)) .top)
    (.typeMember 1 .bot (.ref (.localTypeMember 0)))

def mutuallyReferringPrepared : PreparedSignature [] :=
  { symbols := [.type, .type]
    entries :=
      [.type 0 .here
          [⟨.type (.tvar (.there .here)), .type .top⟩],
        .type 1 (.there .here)
          [⟨.type .bot, .type (.tvar .here)⟩]] }

theorem forward_and_backward_type_bounds_prepare :
    collectAndPrepare (emptyLayout []) mutuallyReferringTypeBounds =
      .ok mutuallyReferringPrepared := by
  rfl

theorem mutually_referring_labels_and_sorts_are_preserved :
    mutuallyReferringPrepared.members.map MemberName.label = [0, 1] ∧
      mutuallyReferringPrepared.members.map MemberName.sort = [.type, .type] := by
  decide

/-! ## Mixed local type and capture references -/

def mixedLocalReferences : Source.Interface 0 :=
  .inter
    (.typeMember 0
      (.capturing (.ref (.localCaptureMember 1))
        (.ref (.localTypeMember 0)))
      .top)
    (.captureMember 1 (.ref (.localCaptureMember 1)) .empty)

def mixedLocalPrepared : PreparedSignature [] :=
  { symbols := [.type, .capture]
    entries :=
      [.type 0 .here
          [⟨.type (.capturing (.cvar (.there .here)) (.tvar .here)),
            .type .top⟩],
        .capture 1 (.there .here)
          [⟨.capture (.cvar (.there .here)), .capture .empty⟩]] }

theorem mixed_local_type_and_capture_references_prepare :
    collectAndPrepare (emptyLayout []) mixedLocalReferences =
      .ok mixedLocalPrepared := by
  rfl

/-! ## Repeated intervals share one allocated member -/

def repeatedTypeIntervals : Source.Interface 0 :=
  .inter (.typeMember 5 .bot .top) (.typeMember 5 .one .top)

def repeatedPreparedEntry :
    PreparedEntry (ManySortedFC.SymbolScope [] [.type]) :=
  .type 5 .here
    [⟨.type .bot, .type .top⟩, ⟨.type .one, .type .top⟩]

def repeatedPrepared : PreparedSignature [] :=
  { symbols := [.type]
    entries := [repeatedPreparedEntry] }

theorem repeated_intervals_prepare_under_one_name :
    collectAndPrepare (emptyLayout []) repeatedTypeIntervals =
      .ok repeatedPrepared := by
  rfl

theorem both_intervals_use_the_same_allocated_coordinate :
    preparedIntervalMembers repeatedPreparedEntry =
      [MemberName.type 5 .here, MemberName.type 5 .here] := by
  rfl

/-! ## Failed local resolution -/

def missingLocalLabel : Source.Interface 0 :=
  .typeMember 0 (.ref (.localTypeMember 99)) .top

theorem missing_local_label_is_rejected :
    collectAndPrepare (emptyLayout []) missingLocalLabel =
      .error (.unknownLocalMember 99) := by
  rfl

def wrongSortLocalReference : Source.Interface 0 :=
  .inter
    (.typeMember 0 (.ref (.localTypeMember 1)) .top)
    (.captureMember 1 .empty .empty)

theorem wrong_sort_local_reference_is_rejected :
    collectAndPrepare (emptyLayout []) wrongSortLocalReference =
      .error (.memberSortMismatch 1 .type .capture) := by
  rfl

/-! ## Closed M10 embedding -/

def m10Signature : DOTCapture.Acyclic.ObjectSig 0 :=
  .bounds .bot .top .empty .empty

def m10Prepared : PreparedSignature [] :=
  { symbols := [.type, .capture]
    entries :=
      [.type DOTCapture.Intersections.Source.m10TypeLabel .here
          [⟨.type .bot, .type .top⟩],
        .capture DOTCapture.Intersections.Source.m10CaptureLabel
          (.there .here)
          [⟨.capture .empty, .capture .empty⟩]] }

theorem closed_m10_interface_prepares_to_two_names :
    collectAndPrepare (emptyLayout [])
      (DOTCapture.Intersections.Source.embedM10ObjectSig m10Signature) =
        .ok m10Prepared := by
  simp only [m10Signature,
    DOTCapture.Intersections.Source.embedM10ObjectSig,
    DOTCapture.Intersections.Source.embedM10Ty,
    DOTCapture.Intersections.Source.embedM10Capture,
    DOTCapture.Intersections.Source.m10TypeLabel,
    DOTCapture.Intersections.Source.m10CaptureLabel]
  change collectAndPrepare (emptyLayout [])
      (.inter (.typeMember 0 .bot .top)
        (.captureMember 1 .empty .empty)) = .ok m10Prepared
  have collected :
      ((.inter (.typeMember 0 .bot .top)
        (.captureMember 1 .empty .empty) : Source.Interface 0).collect) =
      (.ok
        { entries :=
            [.type 0
              [⟨.type .bot, .type .top⟩],
              .capture 1
              [⟨.capture .empty, .capture .empty⟩]] } :
        Except Source.SortConflict (Source.Signature (Source.Expr 0))) := by
    rfl
  unfold collectAndPrepare
  rw [collected]
  rfl

theorem closed_m10_prepared_shape_is_type_then_capture :
    m10Prepared.symbols = [.type, .capture] ∧
      m10Prepared.members.map MemberName.label =
        [DOTCapture.Intersections.Source.m10TypeLabel,
          DOTCapture.Intersections.Source.m10CaptureLabel] := by
  decide

end Examples
end DOTCaptureToManySortedFC.Intersections.Preparation
