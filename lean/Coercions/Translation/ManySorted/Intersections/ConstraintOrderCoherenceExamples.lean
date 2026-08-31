import Coercions.ManySortedFC.TheoryMapLaws

/-!
# Constraint-order coherence

Two intersections can retain the same pair of bounds in different conjunct
orders.  Their encodings below bind one shared member name and differ only in
the order of the two evidence assumptions.  The independently checked maps
in both directions reuse that name and exchange the evidence coordinates.
-/

namespace DOTCaptureToManySortedFC.Intersections.ConstraintOrderCoherenceExamples

open ManySortedFC

abbrev OneTypeSymbolScope : Sig := SymbolScope [] [.type]

def memberName : StaticExpr .type OneTypeSymbolScope :=
  .type (.tvar .here)

def lowerThenUpper : Theory [] [.type]
    [.inclusion .type, .inclusion .type] :=
  .cons (.inclusion (.type .bot) memberName)
    (.cons (.inclusion memberName (.type .top)) .nil)

def upperThenLower : Theory [] [.type]
    [.inclusion .type, .inclusion .type] :=
  .cons (.inclusion memberName (.type .top))
    (.cons (.inclusion (.type .bot) memberName) .nil)

abbrev OpenScope : Sig :=
  StaticScope [] [.type] [.inclusion .type, .inclusion .type]

/-- The one member name after both source assumptions have been opened. -/
def openedMemberName : StaticExpr .type OpenScope :=
  memberName.rename
    (Rename.weakenMany OneTypeSymbolScope
      (evidenceKinds [.inclusion .type, .inclusion .type]))

/-- Reorder the constraints without changing the member interpretation. -/
def lowerUpperToUpperLower : TheoryMap lowerThenUpper upperThenLower where
  symbols := .cons openedMemberName .nil
  evidence := .cons (.var (.there .here)) (.cons (.var .here) .nil)

/-- The inverse evidence permutation, again using the same member name. -/
def upperLowerToLowerUpper : TheoryMap upperThenLower lowerThenUpper where
  symbols := .cons openedMemberName .nil
  evidence := .cons (.var (.there .here)) (.cons (.var .here) .nil)

theorem lower_upper_to_upper_lower_is_accepted :
    (TheoryMap.check Ctx.nil lowerUpperToUpperLower).isSome = true := by
  native_decide

theorem upper_lower_to_lower_upper_is_accepted :
    (TheoryMap.check Ctx.nil upperLowerToLowerUpper).isSome = true := by
  native_decide

theorem both_maps_reuse_the_same_member_name :
    lowerUpperToUpperLower.symbolAt
        (.here : SymbolRef [.type] .type) =
      upperLowerToLowerUpper.symbolAt
        (.here : SymbolRef [.type] .type) :=
  rfl

theorem forward_map_reuses_the_opened_member_name :
    lowerUpperToUpperLower.symbolAt
        (.here : SymbolRef [.type] .type) = openedMemberName :=
  rfl

theorem backward_map_reuses_the_opened_member_name :
    upperLowerToLowerUpper.symbolAt
        (.here : SymbolRef [.type] .type) = openedMemberName :=
  rfl

/-! Applying the evidence permutation twice is the raw identity map. -/

theorem lower_upper_round_trip_is_identity :
    TheoryMap.compose lowerUpperToUpperLower upperLowerToLowerUpper =
      TheoryMap.identity lowerThenUpper := by
  native_decide

theorem upper_lower_round_trip_is_identity :
    TheoryMap.compose upperLowerToLowerUpper lowerUpperToUpperLower =
      TheoryMap.identity upperThenLower := by
  native_decide

/-! A concrete model shows that the static view change keeps one payload. -/

def lowerThenUpperModel : Theory.Model Ctx.nil lowerThenUpper where
  symbols := .cons (.type .one) .nil
  evidence :=
    .cons (.typeBottom .one) (.cons (.typeTop .one) .nil)
  satisfies := .cons (.typeBottom .one) (.cons (.typeTop .one) .nil)

def reorderedModelAndPayload :
    Option (Theory.CheckedModel Ctx.nil upperThenLower × Tm []) :=
  TheoryMap.restrictModelWithPayload? lowerUpperToUpperLower
    lowerThenUpperModel .unit

theorem reordered_model_is_accepted :
    reorderedModelAndPayload.isSome = true := by
  native_decide

theorem reordered_model_keeps_payload_erasure :
    reorderedModelAndPayload.map (fun result => result.2.erase) =
      some Runtime.Tm.unit := by
  native_decide

end DOTCaptureToManySortedFC.Intersections.ConstraintOrderCoherenceExamples
