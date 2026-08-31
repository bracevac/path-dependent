import Coercions.ManySortedFC.TheoryMap
import Coercions.ManySortedFC.TheoryModelChecker

/-!
# Structural checking of cross-shape theory maps

Checking opens only the source theory.  The target theory is renamed into that
source-open scope, its symbols are instantiated by the map, and its supplied
evidence is checked proposition by proposition against `context.extendTheory
source`.  In particular, assumptions exported by the target are never present
while target obligations are validated.
-/

namespace ManySortedFC
namespace TheoryMap

/-- View the target theory from the complete scope opened by the source. -/
def openedTarget {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    (_source : Theory scope sourceSymbols sourceRelations)
    (target : Theory scope targetSymbols targetRelations) :
    Theory (StaticScope scope sourceSymbols sourceRelations)
      targetSymbols targetRelations :=
  target.rename (Rename.weakenStatic sourceSymbols sourceRelations)

/-- Declarative validity of a theory map.  Only the source theory contributes
assumptions to the checking context. -/
abbrev HasType {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (context : Ctx scope) (mapping : TheoryMap source target) : Type :=
  Theory.SatisfiedBy (context.extendTheory source) mapping.symbols
    (openedTarget source target) mapping.evidence

/-- Proof-producing structural checker for a cross-shape theory map. -/
def check {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (context : Ctx scope) (mapping : TheoryMap source target) :
    Option (HasType context mapping) :=
  Theory.checkSatisfaction (context.extendTheory source) mapping.symbols
    (openedTarget source target) mapping.evidence

/-- Every successful map check contains its exact declarative validation. -/
theorem check_sound {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    {context : Ctx scope} {mapping : TheoryMap source target}
    {typing : HasType context mapping}
    (_accepted : check context mapping = some typing) :
    Nonempty (HasType context mapping) :=
  ⟨typing⟩

end TheoryMap
end ManySortedFC
