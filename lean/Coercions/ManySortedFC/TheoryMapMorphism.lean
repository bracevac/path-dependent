import Coercions.ManySortedFC.TheoryMapMetatheory
import Coercions.ManySortedFC.TheoryMorphismChecker

/-!
# Same-shape theory morphisms as theory maps

An identity-on-symbols `TheoryMorphism` is the same-shape special case of a
cross-shape `TheoryMap`: every destination symbol is interpreted by the
corresponding opened source symbol, while the morphism's certificate block is
retained literally.
-/

namespace ManySortedFC
namespace TheoryMap

/-- Forget the same-shape restriction of a theory morphism. -/
def ofMorphism {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    {source target : Theory scope symbols relations}
    (morphism : TheoryMorphism source target) : TheoryMap source target where
  symbols := openedSymbols scope symbols relations
  evidence := morphism.evidence

@[simp]
theorem ofMorphism_symbols {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    {source target : Theory scope symbols relations}
    (morphism : TheoryMorphism source target) :
    (ofMorphism morphism).symbols = openedSymbols scope symbols relations :=
  rfl

@[simp]
theorem ofMorphism_evidence {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    {source target : Theory scope symbols relations}
    (morphism : TheoryMorphism source target) :
    (ofMorphism morphism).evidence = morphism.evidence := rfl

/-- The converted map is intrinsically identity-on-symbols. -/
@[simp]
theorem ofMorphism_symbolAt {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    {source target : Theory scope symbols relations}
    (morphism : TheoryMorphism source target) {sort : StaticSort}
    (reference : SymbolRef symbols sort) :
    (ofMorphism morphism).symbolAt reference =
      StaticExpr.symbol
        ((Rename.weakenMany (SymbolScope scope symbols)
          (evidenceKinds relations)).var (reference.toBVar scope)) := by
  simp [ofMorphism, symbolAt, openedSymbols]

end TheoryMap
end ManySortedFC
