import Coercions.Translation.ManySorted.Intersections.Projection

/-!
# Checked intersection-projection examples

Repeated declarations of one label contribute distinct interval evidence but
share one allocated name.  The accepted maps below project each declaration
back out of the merged theory without allocating another symbol.
-/

namespace DOTCaptureToManySortedFC.Intersections.ProjectionExamples

open ManySortedFC
open DOTCaptureToManySortedFC.Intersections.Encoding
open DOTCaptureToManySortedFC.Intersections.Projection

namespace Source

abbrev Interval := DOTCapture.Intersections.Interval

end Source

/-! ## Repeated type-member components -/

abbrev OneTypeSymbolScope : Sig := SymbolScope [] [.type]

def firstTypeInterval :
    Source.Interval (StaticExpr .type OneTypeSymbolScope) :=
  ⟨.type .bot, .type .top⟩

def secondTypeInterval :
    Source.Interval (StaticExpr .type OneTypeSymbolScope) :=
  ⟨.type .one, .type .top⟩

def repeatedTypePrepared : PreparedSignature [] where
  symbols := [.type]
  entries := [.type 7 .here [firstTypeInterval, secondTypeInterval]]

def repeatedTypeEncoding : Encoding [] := encode repeatedTypePrepared

def openedTypeName : BVar
    (StaticScope [] repeatedTypeEncoding.symbols
      repeatedTypeEncoding.relations) (.symbol .type) :=
  .there (.there (.there (.there .here)))

def firstTypeOccurrence : OpenedOccurrence []
    repeatedTypeEncoding.symbols repeatedTypeEncoding.relations :=
  .type 7 openedTypeName (.type .bot) (.type .top)
    .here (.there .here)

def secondTypeOccurrence : OpenedOccurrence []
    repeatedTypeEncoding.symbols repeatedTypeEncoding.relations :=
  .type 7 openedTypeName (.type .one) (.type .top)
    (.there (.there .here))
    (.there (.there (.there .here)))

def firstTypeSelected : SelectedOccurrence repeatedTypeEncoding where
  occurrence := firstTypeOccurrence
  membership := by native_decide

def secondTypeSelected : SelectedOccurrence repeatedTypeEncoding where
  occurrence := secondTypeOccurrence
  membership := by native_decide

def firstTypeComponent :
    Component [] .type where
  label := 7
  interval := firstTypeInterval

def secondTypeComponent :
    Component [] .type where
  label := 7
  interval := secondTypeInterval

example : Aligned firstTypeSelected firstTypeComponent := by
  constructor <;> rfl

example : Aligned secondTypeSelected secondTypeComponent := by
  constructor <;> rfl

theorem first_type_projection_is_accepted :
    (check Ctx.nil firstTypeSelected firstTypeComponent).isSome = true := by
  exact aligned_check_isSome (by constructor <;> rfl)

theorem second_type_projection_is_accepted :
    (check Ctx.nil secondTypeSelected secondTypeComponent).isSome = true := by
  exact aligned_check_isSome (by constructor <;> rfl)

theorem repeated_type_projections_share_the_allocated_name :
    (map firstTypeSelected firstTypeComponent).symbols =
      (map secondTypeSelected secondTypeComponent).symbols :=
  rfl

example : (map firstTypeSelected firstTypeComponent).symbols =
    .cons (StaticExpr.symbol openedTypeName) .nil := rfl

/-- Reusing evidence from the wrong retained interval is rejected even though
the two components intentionally share their member name. -/
theorem wrong_type_occurrence_evidence_is_rejected :
    check Ctx.nil firstTypeSelected secondTypeComponent = none := by
  native_decide

/-! ## Repeated capture-member components -/

abbrev OneCaptureSymbolScope : Sig := SymbolScope [] [.capture]

def firstCaptureInterval :
    Source.Interval (StaticExpr .capture OneCaptureSymbolScope) :=
  ⟨.capture .empty, .capture (.union .empty .empty)⟩

def secondCaptureInterval :
    Source.Interval (StaticExpr .capture OneCaptureSymbolScope) :=
  ⟨.capture .empty, .capture .empty⟩

def repeatedCapturePrepared : PreparedSignature [] where
  symbols := [.capture]
  entries :=
    [.capture 9 .here [firstCaptureInterval, secondCaptureInterval]]

def repeatedCaptureEncoding : Encoding [] := encode repeatedCapturePrepared

def openedCaptureName : BVar
    (StaticScope [] repeatedCaptureEncoding.symbols
      repeatedCaptureEncoding.relations) (.symbol .capture) :=
  .there (.there (.there (.there .here)))

def firstCaptureOccurrence : OpenedOccurrence []
    repeatedCaptureEncoding.symbols repeatedCaptureEncoding.relations :=
  .capture 9 openedCaptureName (.capture .empty)
    (.capture (.union .empty .empty)) .here (.there .here)

def secondCaptureOccurrence : OpenedOccurrence []
    repeatedCaptureEncoding.symbols repeatedCaptureEncoding.relations :=
  .capture 9 openedCaptureName (.capture .empty) (.capture .empty)
    (.there (.there .here))
    (.there (.there (.there .here)))

def firstCaptureSelected : SelectedOccurrence repeatedCaptureEncoding where
  occurrence := firstCaptureOccurrence
  membership := by native_decide

def secondCaptureSelected : SelectedOccurrence repeatedCaptureEncoding where
  occurrence := secondCaptureOccurrence
  membership := by native_decide

def firstCaptureComponent :
    Component [] .capture where
  label := 9
  interval := firstCaptureInterval

def secondCaptureComponent :
    Component [] .capture where
  label := 9
  interval := secondCaptureInterval

example : Aligned firstCaptureSelected firstCaptureComponent := by
  constructor <;> rfl

example : Aligned secondCaptureSelected secondCaptureComponent := by
  constructor <;> rfl

theorem first_capture_projection_is_accepted :
    (check Ctx.nil firstCaptureSelected firstCaptureComponent).isSome = true := by
  exact aligned_check_isSome (by constructor <;> rfl)

theorem second_capture_projection_is_accepted :
    (check Ctx.nil secondCaptureSelected secondCaptureComponent).isSome = true := by
  exact aligned_check_isSome (by constructor <;> rfl)

theorem repeated_capture_projections_share_the_allocated_name :
    (map firstCaptureSelected firstCaptureComponent).symbols =
      (map secondCaptureSelected secondCaptureComponent).symbols :=
  rfl

example : (map firstCaptureSelected firstCaptureComponent).symbols =
    .cons (StaticExpr.symbol openedCaptureName) .nil := rfl

/-! ## Distinct-label projections -/

abbrev TwoTypeSymbolScope : Sig := SymbolScope [] [.type, .type]

def leftDistinctInterval :
    Source.Interval (StaticExpr .type TwoTypeSymbolScope) :=
  ⟨.type .bot, .type .top⟩

def rightDistinctInterval :
    Source.Interval (StaticExpr .type TwoTypeSymbolScope) :=
  ⟨.type .one, .type .top⟩

def distinctTypePrepared : PreparedSignature [] where
  symbols := [.type, .type]
  entries :=
    [.type 4 .here [leftDistinctInterval],
      .type 8 (.there .here) [rightDistinctInterval]]

def distinctTypeEncoding : Encoding [] := encode distinctTypePrepared

def openedLeftDistinctName : BVar
    (StaticScope [] distinctTypeEncoding.symbols
      distinctTypeEncoding.relations) (.symbol .type) :=
  .there (.there (.there (.there .here)))

def openedRightDistinctName : BVar
    (StaticScope [] distinctTypeEncoding.symbols
      distinctTypeEncoding.relations) (.symbol .type) :=
  .there (.there (.there (.there (.there .here))))

def leftDistinctOccurrence : OpenedOccurrence []
    distinctTypeEncoding.symbols distinctTypeEncoding.relations :=
  .type 4 openedLeftDistinctName (.type .bot) (.type .top)
    .here (.there .here)

def rightDistinctOccurrence : OpenedOccurrence []
    distinctTypeEncoding.symbols distinctTypeEncoding.relations :=
  .type 8 openedRightDistinctName (.type .one) (.type .top)
    (.there (.there .here))
    (.there (.there (.there .here)))

def leftDistinctSelected : SelectedOccurrence distinctTypeEncoding where
  occurrence := leftDistinctOccurrence
  membership := by native_decide

def rightDistinctSelected : SelectedOccurrence distinctTypeEncoding where
  occurrence := rightDistinctOccurrence
  membership := by native_decide

def leftDistinctComponent : Component [] .type where
  label := 4
  interval := ⟨.type .bot, .type .top⟩

def rightDistinctComponent : Component [] .type where
  label := 8
  interval := ⟨.type .one, .type .top⟩

theorem left_distinct_projection_is_accepted :
    (check Ctx.nil leftDistinctSelected leftDistinctComponent).isSome = true :=
  aligned_check_isSome (by constructor <;> rfl)

theorem right_distinct_projection_is_accepted :
    (check Ctx.nil rightDistinctSelected rightDistinctComponent).isSome = true :=
  aligned_check_isSome (by constructor <;> rfl)

theorem distinct_projections_reuse_their_original_names :
    (map leftDistinctSelected leftDistinctComponent).symbols =
        .cons (StaticExpr.symbol openedLeftDistinctName) .nil ∧
      (map rightDistinctSelected rightDistinctComponent).symbols =
        .cons (StaticExpr.symbol openedRightDistinctName) .nil := by
  constructor <;> rfl

theorem distinct_projection_names_are_not_conflated :
    openedLeftDistinctName != openedRightDistinctName := by
  decide

/-- Sort mismatch is excluded by the projection API's index: the component
supplied for a capture occurrence must itself have capture sort. -/
theorem type_and_capture_selections_have_distinct_sorts :
    firstTypeSelected.sort != firstCaptureSelected.sort := by
  decide

/-! ## Missing assumptions cannot be replaced by target self-discharge -/

def unconstrainedPrepared : PreparedSignature [] where
  symbols := [.type]
  entries := [.type 7 .here []]

def unconstrainedEncoding : Encoding [] := encode unconstrainedPrepared

def demandedTypeComponent :
    Component [] .type where
  label := 7
  interval :=
    ⟨.type .bot, .type .top⟩

/-- The source theory has no evidence coordinates.  Reflexivity certificates
are well-sorted syntax, but they do not prove the target interval and the
target's own assumptions are not available to the checker. -/
def selfDischargeAttempt :
    TheoryMap unconstrainedEncoding.theory demandedTypeComponent.theory where
  symbols := .cons (.type (.tvar .here)) .nil
  evidence :=
    .cons (.inclusionRefl (.type (.tvar .here)))
      (.cons (.inclusionRefl (.type (.tvar .here))) .nil)

theorem missing_evidence_self_discharge_is_rejected :
    TheoryMap.check Ctx.nil selfDischargeAttempt = none := by
  native_decide

end DOTCaptureToManySortedFC.Intersections.ProjectionExamples
