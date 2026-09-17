import Coercions.FCdot.CheckerCompleteness

/-!
# Finite inclusion-template examples

Composition reads several facts about the same self block. These checks
exercise nesting and the singleton-premise and endpoint conditions enforced
by the structural checker.
-/

namespace FCdot.TemplateExamples

open scoped FCdot

private def name (i : Nat) : Ty ([],x) := .sel .here (.typ i)

private def source : Telescope ([],x) :=
  .nil ▹ (name 0 ⊑ name 1) ▹ (name 1 ⊑ name 2) ▹ (name 2 ⊑ name 3)

private def fact (i : Nat) : Morphism [] := Morphism.inclusion (.le i)

private def composed : Morphism [] := Morphism.composeInclusions (fact 0) (fact 1)

theorem two_facts :
    synthMorphism Ctx.nil source composed = some (.nil ▹ (name 0 ⊑ name 2)) := by
  decide +kernel

theorem nested_composition :
    synthMorphism Ctx.nil source (Morphism.composeInclusions composed (fact 2)) =
      some (.nil ▹ (name 0 ⊑ name 3)) := by
  decide +kernel

theorem reject_mismatched_middle :
    synthMorphism Ctx.nil source (Morphism.composeInclusions (fact 1) (fact 0)) = none := by
  decide +kernel

theorem reject_empty_premise :
    synthMorphism Ctx.nil source (Morphism.composeInclusions .nil (fact 1)) = none := by
  decide +kernel

theorem reject_nonsingleton_premise :
    synthMorphism Ctx.nil source
      (Morphism.composeInclusions (.le (fact 0) .none (.le 1) .none) (fact 2)) = none := by
  decide +kernel

end FCdot.TemplateExamples
