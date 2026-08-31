import Coercions.ManySortedFC.SeparationConsistency
import Coercions.ManySortedFC.TheoryMapChecker

/-!
# Static access and separation regressions

These examples exercise the proof-only M13 rules.  They add no terms and no
runtime behavior.
-/

namespace ManySortedFC.SeparationExamples

/-! ## Structural acceptance of every M13 evidence rule -/

def emptyEquality : Evidence (.equality .capture) [] :=
  .equalityRefl (.capture .empty)

def emptySubcapture : Evidence (.inclusion .capture) [] :=
  .captureEmpty .empty

def readOnlyMode : Evidence (.mode .readOnly) [] :=
  .modeReadOnly .empty

def emptySeparation : Evidence .separate [] :=
  .separateEmpty .empty

def emptyDisjointness : Evidence .disjoint [] :=
  .disjointEmpty .empty

theorem equality_capture_read_only_is_accepted :
    (Evidence.check Ctx.nil
      (.equalityCaptureReadOnly emptyEquality)).isSome = true := by
  native_decide

theorem capture_read_only_is_accepted :
    (Evidence.check Ctx.nil (.captureReadOnly (.empty : Capture []))).isSome =
      true := by
  native_decide

theorem capture_read_only_monotonicity_is_accepted :
    (Evidence.check Ctx.nil
      (.captureReadOnlyMono emptySubcapture)).isSome = true := by
  native_decide

theorem mode_empty_is_accepted :
    (Evidence.check Ctx.nil
      (.modeEmpty (scope := []) .readOnly)).isSome = true := by
  native_decide

theorem mode_union_is_accepted :
    (Evidence.check Ctx.nil
      (.modeUnion readOnlyMode readOnlyMode)).isSome = true := by
  native_decide

theorem mode_subcapture_is_accepted :
    (Evidence.check Ctx.nil
      (.modeSubcapture (.captureEmpty (.readOnly .empty))
        readOnlyMode)).isSome = true := by
  native_decide

theorem mode_writable_is_accepted :
    (Evidence.check Ctx.nil
      (.modeWritable (.empty : Capture []))).isSome = true := by
  native_decide

theorem mode_read_only_is_accepted :
    (Evidence.check Ctx.nil readOnlyMode).isSome = true := by
  native_decide

theorem separate_symmetry_is_accepted :
    (Evidence.check Ctx.nil
      (.separateSymm emptySeparation)).isSome = true := by
  native_decide

theorem separate_union_is_accepted :
    (Evidence.check Ctx.nil
      (.separateUnion emptySeparation emptySeparation)).isSome = true := by
  native_decide

theorem separate_empty_is_accepted :
    (Evidence.check Ctx.nil emptySeparation).isSome = true := by
  native_decide

theorem separate_read_only_is_accepted :
    (Evidence.check Ctx.nil
      (.separateReadOnly readOnlyMode readOnlyMode)).isSome = true := by
  native_decide

theorem separate_subcapture_is_accepted :
    (Evidence.check Ctx.nil
      (.separateSubcapture emptySubcapture emptySeparation)).isSome = true := by
  native_decide

theorem separate_of_disjoint_is_accepted :
    (Evidence.check Ctx.nil
      (.separateOfDisjoint emptyDisjointness)).isSome = true := by
  native_decide

theorem disjoint_symmetry_is_accepted :
    (Evidence.check Ctx.nil
      (.disjointSymm emptyDisjointness)).isSome = true := by
  native_decide

theorem disjoint_union_is_accepted :
    (Evidence.check Ctx.nil
      (.disjointUnion emptyDisjointness emptyDisjointness)).isSome = true := by
  native_decide

theorem disjoint_empty_is_accepted :
    (Evidence.check Ctx.nil emptyDisjointness).isSome = true := by
  native_decide

theorem disjoint_equality_transport_is_accepted :
    (Evidence.check Ctx.nil
      (.disjointEquality emptyEquality emptyDisjointness)).isSome = true := by
  native_decide

/-! ## Endpoint alignment failures -/

theorem mode_subcapture_mismatched_upper_is_rejected :
    Evidence.check Ctx.nil
      (.modeSubcapture
        (.captureEmpty (.readOnly (.empty : Capture [])))
        (.modeReadOnly (.union .empty .empty))) = none := by
  native_decide

theorem separate_union_mismatched_other_is_rejected :
    Evidence.check Ctx.nil
      (.separateUnion
        (.separateEmpty (.empty : Capture []))
        (.separateEmpty (.union .empty .empty))) = none := by
  native_decide

theorem separate_subcapture_mismatched_upper_is_rejected :
    Evidence.check Ctx.nil
      (.separateSubcapture
        (.captureEmpty (.union (.empty : Capture []) .empty))
        (.separateEmpty .empty)) = none := by
  native_decide

theorem disjoint_union_mismatched_other_is_rejected :
    Evidence.check Ctx.nil
      (.disjointUnion
        (.disjointEmpty (.empty : Capture []))
        (.disjointEmpty (.union .empty .empty))) = none := by
  native_decide

theorem disjoint_equality_mismatched_original_is_rejected :
    Evidence.check Ctx.nil
      (.disjointEquality
        (.equalityRefl (.capture (.readOnly (.empty : Capture []))))
        (.disjointEmpty .empty)) = none := by
  native_decide

/-! ## Nonempty read-only overlap -/

theorem shared_read_only_overlap_is_accepted :
    (Evidence.check oneCapabilityContext sharedReadOnlySeparation).map
        Evidence.Checked.proposition =
      some (.separate sharedReadOnly sharedReadOnly) := by
  native_decide

/-! ## Models containing all three new proposition families -/

def accessTheory : Theory [] []
    [.mode .readOnly, .separate, .disjoint] :=
  .cons (.mode (.readOnly .empty))
    (.cons (.separate (.readOnly .empty) (.readOnly .empty))
      (.cons (.disjoint .empty .empty) .nil))

def accessEvidence : EvidenceArgs []
    [.mode .readOnly, .separate, .disjoint] :=
  .cons readOnlyMode
    (.cons (.separateReadOnly readOnlyMode readOnlyMode)
      (.cons emptyDisjointness .nil))

theorem access_theory_model_is_accepted :
    (Theory.checkModel Ctx.nil accessTheory .nil accessEvidence).isSome =
      true := by
  native_decide

/-! ## A checked Disjoint-to-Separate theory map -/

def assumedDisjointTheory : Theory [] [] [.disjoint] :=
  .cons (.disjoint (.readOnly .empty) (.readOnly .empty)) .nil

def requiredSeparateTheory : Theory [] [] [.separate] :=
  .cons (.separate (.readOnly .empty) (.readOnly .empty)) .nil

def disjointToSeparate :
    TheoryMap assumedDisjointTheory requiredSeparateTheory where
  symbols := .nil
  evidence := .cons (.separateOfDisjoint (.var .here)) .nil

theorem disjoint_to_separate_map_is_accepted :
    (TheoryMap.check Ctx.nil disjointToSeparate).isSome = true := by
  native_decide

/-! ## No self-discharge -/

/-- This obligation is not derivable in the empty ambient context.  Opening
the theory's own assumption would make it available, but model checking does
not do that. -/
def unsupportedDisjointTheory : Theory [] [] [.disjoint] :=
  .cons (.disjoint (.readOnly .empty) (.readOnly .empty)) .nil

def unsupportedDisjointAttempt : EvidenceArgs [] [.disjoint] :=
  .cons (.disjointEmpty (.readOnly .empty)) .nil

theorem unsupported_disjoint_model_is_rejected :
    Theory.checkModel Ctx.nil unsupportedDisjointTheory .nil
      unsupportedDisjointAttempt = none := by
  native_decide

theorem empty_ambient_has_no_disjoint_assumption
    (index : BVar [] (.evidence .disjoint)) : False := by
  nomatch index

/-! ## Intrinsic negative boundaries -/

/-- A writable-mode certificate cannot be supplied to `separateReadOnly`:
the two evidence indices are distinct before checking starts. -/
theorem writable_mode_is_not_read_only_mode :
    Relation.mode .writable ≠ Relation.mode .readOnly := by
  decide

/-- `disjointEquality` accepts equality transport, not one-way subcapture
evidence.  The required evidence indices are distinct. -/
theorem subcapture_is_not_disjoint_transport :
    Relation.inclusion .capture ≠ Relation.equality .capture := by
  decide

/-! ## Primitive ambient Disjoint facts -/

abbrev TwoCaptureScope : Sig :=
  [] ▹ .symbol .capture ▹ .symbol .capture

def twoCaptureContext : Ctx TwoCaptureScope :=
  Ctx.nil.extendCaptureSymbol.extendCaptureSymbol

def firstCapture : Capture TwoCaptureScope :=
  .cvar (.there .here)

def secondCapture : Capture TwoCaptureScope :=
  .cvar .here

abbrev AssumedDisjointScope : Sig :=
  TwoCaptureScope ▹ .evidence .disjoint

def assumedDisjointContext : Ctx AssumedDisjointScope :=
  twoCaptureContext.extendDisjoint firstCapture secondCapture

/-- A nontrivial primitive fact is represented by an exact ambient evidence
coordinate.  The remaining Disjoint constructors only rearrange checked
facts or introduce the empty-capture law. -/
def assumedDisjointEvidence : Evidence .disjoint AssumedDisjointScope :=
  .var .here

theorem ambient_disjoint_variable_has_exact_endpoints :
    (Evidence.check assumedDisjointContext assumedDisjointEvidence).map
        Evidence.Checked.proposition =
      some (.disjoint firstCapture.weaken secondCapture.weaken) := by
  rfl

end ManySortedFC.SeparationExamples
