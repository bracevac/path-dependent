import Coercions.DOT.Captures.Intersections.SourceMetatheory

/-!
# Static captured-DOT intersection examples

These regressions exercise collection only.  They deliberately make no
assumption about an object's runtime payload representation.
-/

namespace DOTCapture.Intersections.Source
namespace Examples

/-! ## Same-label sort coherence -/

def conflictingSorts : Interface 0 :=
  .inter
    (.typeMember 7 .bot .top)
    (.captureMember 7 .empty .empty)

theorem conflicting_same_label_sorts_are_rejected :
    conflictingSorts.collect =
      .error { label := 7, existing := .type, incoming := .capture } := by
  rfl

/-! ## Same-sort intervals are retained, not validated or collapsed -/

def inconsistentTypeIntervals : Interface 0 :=
  .inter
    (.typeMember 4 .top .bot)
    (.typeMember 4 .one .bot)

def retainedInconsistentSignature :
    DOTCapture.Intersections.Signature (Interface.Expr 0) :=
  { entries :=
      [DOTCapture.Intersections.Entry.type 4
        [⟨StaticExpr.type .top, StaticExpr.type .bot⟩,
          ⟨StaticExpr.type .one, StaticExpr.type .bot⟩]] }

theorem inconsistent_same_sort_intervals_are_retained :
    inconsistentTypeIntervals.collect =
      .ok retainedInconsistentSignature := by
  rfl

theorem retained_bad_intervals_have_one_name_and_two_constraints :
    retainedInconsistentSignature.entries.length = 1 ∧
      retainedInconsistentSignature.occurrenceCount = 2 := by
  decide

/-! ## Association does not affect the canonical result -/

def firstTypeLeaf : Interface 0 := .typeMember 4 .top .bot
def captureLeaf : Interface 0 := .captureMember 1 .empty .empty
def secondTypeLeaf : Interface 0 := .typeMember 4 .one .top

def leftAssociated : Interface 0 :=
  .inter (.inter firstTypeLeaf captureLeaf) secondTypeLeaf

def rightAssociated : Interface 0 :=
  .inter firstTypeLeaf (.inter captureLeaf secondTypeLeaf)

theorem association_variants_collect_identically :
    leftAssociated.collect = rightAssociated.collect := by
  rfl

theorem associated_collection_is_successful :
    ∃ signature, leftAssociated.collect = .ok signature := by
  exact ⟨
    { entries :=
        [DOTCapture.Intersections.Entry.capture 1
            [⟨StaticExpr.capture .empty, StaticExpr.capture .empty⟩],
          DOTCapture.Intersections.Entry.type 4
            [⟨StaticExpr.type .top, StaticExpr.type .bot⟩,
              ⟨StaticExpr.type .one, StaticExpr.type .top⟩]] },
    rfl⟩

/-! ## Bounds may refer to other names in the same interface -/

def mutuallyReferentialTypeBounds : Interface 0 :=
  .inter
    (.typeMember 2 (.ref (.localTypeMember 3)) .top)
    (.typeMember 3 .bot (.ref (.localTypeMember 2)))

def mutuallyReferentialSignature :
    DOTCapture.Intersections.Signature (Interface.Expr 0) :=
  { entries :=
      [DOTCapture.Intersections.Entry.type 2
          [⟨StaticExpr.type (.ref (.localTypeMember 3)),
            StaticExpr.type .top⟩],
        DOTCapture.Intersections.Entry.type 3
          [⟨StaticExpr.type .bot,
            StaticExpr.type (.ref (.localTypeMember 2))⟩]] }

theorem local_member_references_survive_collection :
    mutuallyReferentialTypeBounds.collect =
      .ok mutuallyReferentialSignature := by
  rfl

/-! ## M10 embeds into the canonical two-entry layout -/

def m10Signature : DOTCapture.Acyclic.ObjectSig 0 :=
  .bounds .bot .top .empty .empty

theorem m10_embedding_collects_canonically :
    (embedM10ObjectSig m10Signature).collect =
      .ok (embeddedM10Signature m10Signature) :=
  collect_embedM10ObjectSig m10Signature

theorem m10_embedding_has_type_then_capture_entry :
    (embeddedM10Signature m10Signature).entries =
      [DOTCapture.Intersections.Entry.type m10TypeLabel
          [⟨StaticExpr.type .bot, StaticExpr.type .top⟩],
        DOTCapture.Intersections.Entry.capture m10CaptureLabel
          [⟨StaticExpr.capture .empty, StaticExpr.capture .empty⟩]] := by
  simp [embeddedM10Signature, m10Signature, embedM10Ty, embedM10Capture]

end Examples
end DOTCapture.Intersections.Source
