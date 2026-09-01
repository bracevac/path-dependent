import Coercions.ManySortedFC.EvidenceNormalization

/-!
# Regressions for checked evidence normalization

The examples exercise equality, inclusion, modal, separation, and disjointness
administrative reductions.  The final example is intentionally malformed: its
unchecked syntax candidate is acceptable after a reflexive link is deleted,
but the public normalizer rejects it because the original certificate failed
checking.
-/

namespace ManySortedFC.Evidence.NormalizationExamples

abbrev EmptyScope : Sig := []

def redundantEquality : Evidence (.equality .type) EmptyScope :=
  .equalityTrans
    (.equalitySymm (.equalitySymm (.equalityRefl (.type .one))))
    (.equalityTrans
      (.equalityRefl (.type .one))
      (.equalityRefl (.type .one)))

example : nodeCount redundantEquality = 7 := rfl

example :
    normalizeSyntax redundantEquality = .equalityRefl (.type .one) := rfl

example :
    (normalizeChecked Ctx.nil redundantEquality).map
      (fun result => (result.before, result.after, result.saved)) =
      some (7, 1, 6) := by
  native_decide

def redundantInclusion : Evidence (.inclusion .type) EmptyScope :=
  .inclusionTrans
    (.equalityToInclusion
      (.equalitySymm (.equalitySymm (.equalityRefl (.type .one)))))
    (.inclusionRefl (.type .one))

example : nodeCount redundantInclusion = 6 := rfl

example :
    normalizeSyntax redundantInclusion = .inclusionRefl (.type .one) := rfl

example :
    (normalizeChecked Ctx.nil redundantInclusion).map
      (fun result => (result.before, result.after, result.saved)) =
      some (6, 1, 5) := by
  native_decide

def redundantMode : Evidence (.mode .readOnly) EmptyScope :=
  .modeSubcapture
    (.inclusionTrans
      (.inclusionRefl (.capture (.readOnly .empty)))
      (.inclusionRefl (.capture (.readOnly .empty))))
    (.modeReadOnly .empty)

example : nodeCount redundantMode = 5 := rfl

example : normalizeSyntax redundantMode = .modeReadOnly .empty := rfl

example :
    (normalizeChecked Ctx.nil redundantMode).map
      (fun result => (result.before, result.after, result.saved)) =
      some (5, 1, 4) := by
  native_decide

def redundantSeparation : Evidence .separate EmptyScope :=
  .separateSymm (.separateSymm (.separateEmpty .empty))

example : nodeCount redundantSeparation = 3 := rfl

example : normalizeSyntax redundantSeparation = .separateEmpty .empty := rfl

example :
    (normalizeChecked Ctx.nil redundantSeparation).map
      (fun result => (result.before, result.after, result.saved)) =
      some (3, 1, 2) := by
  native_decide

def redundantDisjointness : Evidence .disjoint EmptyScope :=
  .disjointEquality
    (.equalitySymm
      (.equalitySymm (.equalityRefl (.capture .empty))))
    (.disjointSymm (.disjointSymm (.disjointEmpty .empty)))

example : nodeCount redundantDisjointness = 7 := rfl

example :
    normalizeSyntax redundantDisjointness = .disjointEmpty .empty := rfl

example :
    (normalizeChecked Ctx.nil redundantDisjointness).map
      (fun result => (result.before, result.after, result.saved)) =
      some (7, 1, 6) := by
  native_decide

/-! The malformed tree demonstrates why `normalizeSyntax` is not a public
sanitizer.  Its two reflexive links disagree at their transitivity boundary. -/

def malformedTransitivity : Evidence (.equality .type) EmptyScope :=
  .equalityTrans
    (.equalityRefl (.type .one))
    (.equalityRefl (.type .top))

example : check Ctx.nil malformedTransitivity = none := rfl

example :
    normalizeSyntax malformedTransitivity = .equalityRefl (.type .top) := rfl

example :
    (check Ctx.nil (normalizeSyntax malformedTransitivity)).map
      Checked.proposition =
      some (.equality (.type .top) (.type .top)) := rfl

example : normalizeChecked Ctx.nil malformedTransitivity = none := rfl

end ManySortedFC.Evidence.NormalizationExamples
