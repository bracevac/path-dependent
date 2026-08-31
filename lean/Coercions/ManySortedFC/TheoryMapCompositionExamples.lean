import Coercions.ManySortedFC.TheoryMapComposition
import Coercions.ManySortedFC.TheoryMapExamples

/-!
# Theory-map composition regressions

These examples check both identity orders, a chain that changes signature
shape at each step, and concrete restriction of an ambient source model.
-/

namespace ManySortedFC.TheoryMapCompositionExamples

open TheoryMapExamples

/-! ## A nontrivial cross-shape chain -/

def duplicatedExactTypeTheory :
    Theory [] [.type] [.equality .type, .equality .type] :=
  .cons (.equality typeSymbol (.type .one))
    (.cons (.equality typeSymbol (.type .one)) .nil)

abbrev ExactTypeOpenScope : Sig :=
  StaticScope [] [.type] [.equality .type]

def exactTypeOpened : StaticExpr .type ExactTypeOpenScope :=
  typeSymbol.rename
    (Rename.weakenMany (SymbolScope [] [.type])
      (evidenceKinds [.equality .type]))

/-- Duplicate the one source equality assumption into two target obligations.
Both copies still refer to the same selected type name. -/
def exactToDuplicated :
    TheoryMap exactTypeTheory duplicatedExactTypeTheory where
  symbols := .cons exactTypeOpened .nil
  evidence := .cons (.var .here) (.cons (.var .here) .nil)

theorem exact_to_duplicated_is_accepted :
    (TheoryMap.check Ctx.nil exactToDuplicated).isSome = true := by
  native_decide

/-- First discard the capture part of the mixed theory, then duplicate its
type equality.  Composition substitutes both the selected symbol and the
intermediate evidence variable. -/
def mixedToDuplicated :
    TheoryMap StaticExamples.exactMixedTheory duplicatedExactTypeTheory :=
  TheoryMap.compose mixedToType exactToDuplicated

theorem nontrivial_composite_is_accepted :
    (TheoryMap.check Ctx.nil mixedToDuplicated).isSome = true := by
  native_decide

theorem nontrivial_chain_changes_shape_twice :
    ([.type, .capture] : List StaticSort) ≠ [.type] ∧
      ([.equality .type, .equality .capture] : List Relation) ≠
        [.equality .type] ∧
      ([.equality .type] : List Relation) ≠
        [.equality .type, .equality .type] := by
  decide

/-! ## Executable identity laws -/

theorem left_identity_on_projection :
    TheoryMap.compose
      (TheoryMap.identity StaticExamples.exactMixedTheory) mixedToType =
        mixedToType := by
  native_decide

theorem right_identity_on_projection :
    TheoryMap.compose mixedToType (TheoryMap.identity exactTypeTheory) =
      mixedToType := by
  native_decide

/-! ## Restricting a concrete source model -/

def exactMixedModel : Theory.Model Ctx.nil StaticExamples.exactMixedTheory :=
  ⟨StaticExamples.exactMixedWitnesses, StaticExamples.exactMixedEvidence,
    .cons (.equalityRefl (.type .one))
      (.cons (.equalityRefl (.capture .empty)) .nil)⟩

def restrictedTypeModel :
    Option (Theory.CheckedModel Ctx.nil exactTypeTheory) :=
  TheoryMap.checkModel mixedToType exactMixedModel

theorem concrete_model_restriction_is_accepted :
    restrictedTypeModel.isSome = true := by
  native_decide

end ManySortedFC.TheoryMapCompositionExamples
