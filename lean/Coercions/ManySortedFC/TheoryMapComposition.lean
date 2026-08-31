import Coercions.ManySortedFC.TheoryMapChecker
import Coercions.ManySortedFC.StaticInstantiation

/-!
# Composition and model restriction for cross-shape theory maps

This module sits above the raw `TheoryMap` syntax.  Composition eliminates the
intermediate theory's complete static scope by simultaneously substituting the
first map's symbol and evidence blocks into the second map.  No intermediate
target assumptions are opened or added to a context.
-/

namespace ManySortedFC
namespace TheoryMap

/-- Embed an ambient renaming as an evidence-aware static substitution. -/
private def substitutionOfRename {source target : Sig}
    (rho : Rename source target) : TermStaticSubst source target where
  static := StaticSubst.ofRename rho
  evidenceVar := fun index => .var (rho.var index)

/-- Eliminate the complete scope opened by a map's target using the symbols
and evidence supplied by that map. -/
def substitution {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (mapping : TheoryMap source target) :
    TermStaticSubst
      (StaticScope scope targetSymbols targetRelations)
      (StaticScope scope sourceSymbols sourceRelations) :=
  TermStaticSubst.fromStaticArgs
    (substitutionOfRename
      (Rename.weakenStatic sourceSymbols sourceRelations))
    mapping.symbols mapping.evidence

/-- Compose two cross-shape theory maps.  The intermediate symbol and evidence
binders are removed by one simultaneous evidence-aware substitution. -/
def compose {scope : Sig}
    {sourceSymbols middleSymbols targetSymbols : List StaticSort}
    {sourceRelations middleRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {middle : Theory scope middleSymbols middleRelations}
    {target : Theory scope targetSymbols targetRelations}
    (first : TheoryMap source middle) (second : TheoryMap middle target) :
    TheoryMap source target where
  symbols := second.symbols.substitute first.substitution
  evidence := second.evidence.substitute first.substitution

@[simp]
theorem compose_symbols {scope : Sig}
    {sourceSymbols middleSymbols targetSymbols : List StaticSort}
    {sourceRelations middleRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {middle : Theory scope middleSymbols middleRelations}
    {target : Theory scope targetSymbols targetRelations}
    (first : TheoryMap source middle) (second : TheoryMap middle target) :
    (compose first second).symbols =
      second.symbols.substitute first.substitution := rfl

@[simp]
theorem compose_evidence {scope : Sig}
    {sourceSymbols middleSymbols targetSymbols : List StaticSort}
    {sourceRelations middleRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {middle : Theory scope middleSymbols middleRelations}
    {target : Theory scope targetSymbols targetRelations}
    (first : TheoryMap source middle) (second : TheoryMap middle target) :
    (compose first second).evidence =
      second.evidence.substitute first.substitution := rfl

/-! ## Executable restriction of ambient models

The raw components below instantiate a map using an ambient source model.
Since `TheoryMap` is intentionally raw syntax, `checkModel` validates the
result again before exposing a target model.
-/

/-- Eliminate the source-opened scope of a map using an ambient source model. -/
def modelSubstitution {scope : Sig} {context : Ctx scope}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (_mapping : TheoryMap source target)
    (model : Theory.Model context source) :
    TermStaticSubst (StaticScope scope sourceSymbols sourceRelations) scope :=
  TermStaticSubst.fromStaticArgs TermStaticSubst.id
    model.symbols model.evidence

/-- Target symbols obtained by applying a theory map to a source model. -/
def applySymbols {scope : Sig} {context : Ctx scope}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (mapping : TheoryMap source target)
    (model : Theory.Model context source) : SymbolArgs scope targetSymbols :=
  mapping.symbols.substitute (modelSubstitution mapping model)

/-- Target evidence obtained by applying a theory map to a source model. -/
def applyEvidence {scope : Sig} {context : Ctx scope}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (mapping : TheoryMap source target)
    (model : Theory.Model context source) :
    EvidenceArgs scope targetRelations :=
  mapping.evidence.substitute (modelSubstitution mapping model)

/-- Check the raw restriction of a source model along a theory map.  A
successful result contains a proof-carrying target model; no validity is
claimed for an unchecked raw map. -/
def checkModel {scope : Sig} {context : Ctx scope}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (mapping : TheoryMap source target)
    (model : Theory.Model context source) :
    Option (Theory.CheckedModel context target) :=
  Theory.checkModel context target
    (applySymbols mapping model) (applyEvidence mapping model)

end TheoryMap
end ManySortedFC
