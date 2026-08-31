import Coercions.ManySortedFC.TheoryMapChecker
import Coercions.ManySortedFC.EvidenceCheckerCompleteness

/-!
# Completeness of the cross-shape theory-map checker

Declarative satisfaction is reflected by the proof-producing checker.  With
the checker's existing soundness theorem, executable acceptance is therefore
equivalent to inhabited declarative validity.
-/

namespace ManySortedFC

namespace Theory

/-- Structural satisfaction proofs are complete for `checkSatisfaction`. -/
theorem checkSatisfaction_complete {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {arguments : SymbolArgs scope symbols}
    {relations : List Relation} {theory : Theory scope symbols relations}
    {evidence : EvidenceArgs scope relations}
    (satisfaction : SatisfiedBy context arguments theory evidence) :
    ∃ checked,
      checkSatisfaction context arguments theory evidence = some checked := by
  induction satisfaction with
  | nil => exact ⟨.nil, rfl⟩
  | cons head tail tailIH =>
      obtain ⟨headTyping, headEq⟩ := Evidence.check_complete head
      obtain ⟨tailChecked, tailEq⟩ := tailIH
      simp [checkSatisfaction, headEq, tailEq]

end Theory

namespace TheoryMap

/-- Every declaratively valid map is accepted with an exact validation proof. -/
theorem check_complete {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    {context : Ctx scope} {mapping : TheoryMap source target}
    (typing : HasType context mapping) :
    ∃ checked, check context mapping = some checked :=
  Theory.checkSatisfaction_complete typing

/-- Executable acceptance is equivalent to inhabited declarative validity. -/
theorem check_isSome_iff {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    {context : Ctx scope} {mapping : TheoryMap source target} :
    (check context mapping).isSome = true ↔
      Nonempty (HasType context mapping) := by
  constructor
  · intro accepted
    generalize checkedEq : check context mapping = result at accepted
    cases result with
    | none => simp at accepted
    | some typing => exact check_sound checkedEq
  · rintro ⟨typing⟩
    obtain ⟨checked, checkedEq⟩ := check_complete typing
    simp [checkedEq]

end TheoryMap
end ManySortedFC
