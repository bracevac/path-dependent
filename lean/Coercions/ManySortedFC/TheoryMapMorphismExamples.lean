import Coercions.ManySortedFC.TheoryMapMorphism
import Coercions.ManySortedFC.TheoryMapCheckerCompleteness
import Coercions.ManySortedFC.TheoryMorphismExamples

/-!
# Same-shape morphism conversion regression
-/

namespace ManySortedFC.TheoryMapMorphismExamples

open TheoryMorphismExamples

/-- The established nontrivial capture-bound morphism, viewed as a map. -/
def strongEntailsWeakMap : TheoryMap strongUpper weakUpper :=
  TheoryMap.ofMorphism strongEntailsWeak

theorem converted_strong_entails_weak_is_accepted :
    (TheoryMap.check outerContext strongEntailsWeakMap).isSome = true := by
  native_decide

theorem converted_strong_entails_weak_is_valid :
    Nonempty (TheoryMap.HasType outerContext strongEntailsWeakMap) :=
  TheoryMap.check_isSome_iff.mp converted_strong_entails_weak_is_accepted

/-- Conversion retains the same source-only certificate block. -/
theorem converted_evidence_is_original :
    strongEntailsWeakMap.evidence = strongEntailsWeak.evidence := rfl

end ManySortedFC.TheoryMapMorphismExamples
