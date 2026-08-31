import Coercions.Translation.ManySorted.Intersections.EncodingMetatheory
import Coercions.ManySortedFC.TheoryMapCheckerCompleteness

/-!
# Checked projections from merged intersection theories

A component view is an independently normalized one-member theory. Its
single abstract name is interpreted by the already-opened name of a selected
occurrence in the merged theory. The two component obligations are proved by
the exact evidence coordinates retained for that occurrence.

The source and target symbol lists therefore have genuinely different shapes
when the merged signature has more than one member. The target component
theory is never opened while its map is checked, so it cannot discharge its
own obligations.
-/

namespace DOTCaptureToManySortedFC.Intersections.Projection

open ManySortedFC
open DOTCaptureToManySortedFC.Intersections.Encoding

namespace Source

abbrev Interval := DOTCapture.Intersections.Interval

end Source

/-- One independently normalized intersection component. Its theory owns
one abstract name, regardless of the number of names in the merged source
theory from which it will be projected. -/
structure Component (scope : Sig) (sort : StaticSort) where
  label : Nat
  interval : Source.Interval (StaticExpr sort (SymbolScope scope [sort]))
deriving DecidableEq

namespace Component

/-- The one-name, one-interval component theory. -/
def theory {scope : Sig} {sort : StaticSort}
    (component : Component scope sort) :
    Theory scope [sort] [.inclusion sort, .inclusion sort] :=
  .cons
    (.inclusion component.interval.lower (StaticExpr.symbol .here))
    (.cons
      (.inclusion (StaticExpr.symbol .here) component.interval.upper)
      .nil)

/-- The component's own abstract member before projection. -/
def member {scope : Sig} {sort : StaticSort}
    (component : Component scope sort) :
    MemberName (SymbolScope scope [sort]) :=
  match sort with
  | .type => .type component.label .here
  | .capture => .capture component.label .here

end Component

/-- A retained occurrence selected from the actual enumeration of a merged
encoding. Membership prevents callers from manufacturing evidence
coordinates unrelated to that encoding. -/
structure SelectedOccurrence {scope : Sig} (encoding : Encoding scope) where
  occurrence : OpenedOccurrence scope encoding.symbols encoding.relations
  membership : occurrence ∈ encoding.openedOccurrences

namespace SelectedOccurrence

def sort {scope : Sig} {encoding : Encoding scope}
    (selected : SelectedOccurrence encoding) : StaticSort :=
  selected.occurrence.sort

/-- The selected merged member as a sort-indexed static expression. -/
private def occurrenceSymbol {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} :
    (occurrence : OpenedOccurrence scope symbols relations) ->
      StaticExpr occurrence.sort (StaticScope scope symbols relations)
  | .type _ name _ _ _ _ => .type (.tvar name)
  | .capture _ name _ _ _ _ => .capture (.cvar name)

def symbol {scope : Sig} {encoding : Encoding scope}
    (selected : SelectedOccurrence encoding) :
    StaticExpr selected.sort
      (StaticScope scope encoding.symbols encoding.relations) :=
  occurrenceSymbol selected.occurrence

/-- Membership in the generated occurrence enumeration supplies the exact
lookup facts for both retained constraints. -/
def evidenceMatches {scope : Sig} {encoding : Encoding scope}
    (context : Ctx scope) (selected : SelectedOccurrence encoding) :
    selected.occurrence.EvidenceMatches
      (context.extendTheory encoding.theory) :=
  Encoding.opened_occurrence_evidence_matches context encoding
    selected.occurrence selected.membership

end SelectedOccurrence

namespace Component

/-- The lower component constraint after the component's independent name is
mapped to the selected name in the complete merged scope. -/
def mappedLower {scope : Sig} {encoding : Encoding scope}
    (selected : SelectedOccurrence encoding)
    (component : Component scope selected.sort) :
    Proposition (.inclusion selected.sort)
      (StaticScope scope encoding.symbols encoding.relations) :=
  (((Proposition.inclusion component.interval.lower
      (StaticExpr.symbol (.here :
        BVar (SymbolScope scope [selected.sort]) (.symbol selected.sort))))
    ).rename
      ((Rename.weakenStatic encoding.symbols encoding.relations).liftSymbols
        [selected.sort])).instantiateSymbols
    (.cons selected.symbol .nil)

/-- The upper component constraint after the same cross-shape name mapping. -/
def mappedUpper {scope : Sig} {encoding : Encoding scope}
    (selected : SelectedOccurrence encoding)
    (component : Component scope selected.sort) :
    Proposition (.inclusion selected.sort)
      (StaticScope scope encoding.symbols encoding.relations) :=
  (((Proposition.inclusion
      (StaticExpr.symbol (.here :
        BVar (SymbolScope scope [selected.sort]) (.symbol selected.sort)))
      component.interval.upper)
    ).rename
      ((Rename.weakenStatic encoding.symbols encoding.relations).liftSymbols
        [selected.sort])).instantiateSymbols
    (.cons selected.symbol .nil)

end Component

/-- Exact correspondence between an independently normalized component and a
selected retained occurrence after the component name is mapped to the merged
name. -/
structure Aligned {scope : Sig} {encoding : Encoding scope}
    (selected : SelectedOccurrence encoding)
    (component : Component scope selected.sort) : Prop where
  label : component.label = selected.occurrence.label
  lower : selected.occurrence.lowerProposition =
    component.mappedLower selected
  upper : selected.occurrence.upperProposition =
    component.mappedUpper selected

/-- The raw cross-shape component projection. -/
def map {scope : Sig} {encoding : Encoding scope}
    (selected : SelectedOccurrence encoding)
    (component : Component scope selected.sort) :
    TheoryMap encoding.theory component.theory where
  symbols := .cons selected.symbol .nil
  evidence :=
    .cons (.var selected.occurrence.lowerEvidence)
      (.cons (.var selected.occurrence.upperEvidence) .nil)

/-- Run the standalone cross-shape checker on a component projection. -/
def check {scope : Sig} {encoding : Encoding scope}
    (context : Ctx scope) (selected : SelectedOccurrence encoding)
    (component : Component scope selected.sort) :
    Option (TheoryMap.HasType context (map selected component)) :=
  TheoryMap.check context (map selected component)

/-- Successful projection checking yields the declarative cross-shape map
judgment. -/
theorem check_sound {scope : Sig} {encoding : Encoding scope}
    {context : Ctx scope} {selected : SelectedOccurrence encoding}
    {component : Component scope selected.sort}
    {typing : TheoryMap.HasType context (map selected component)}
    (accepted : check context selected component = some typing) :
    Nonempty (TheoryMap.HasType context (map selected component)) :=
  TheoryMap.check_sound accepted

/-- Retained lookup facts prove an aligned component projection. -/
def hasType_of_aligned {scope : Sig} {encoding : Encoding scope}
    {context : Ctx scope} {selected : SelectedOccurrence encoding}
    {component : Component scope selected.sort}
    (alignment : Aligned selected component)
    (validity : selected.occurrence.EvidenceMatches
      (context.extendTheory encoding.theory)) :
    TheoryMap.HasType context (map selected component) := by
  rcases validity with ⟨lowerLookup, upperLookup⟩
  apply Theory.SatisfiedBy.cons
  · apply Evidence.Proves.var
    change _ = Binding.evidence (component.mappedLower selected)
    rw [← alignment.lower]
    exact lowerLookup
  · apply Theory.SatisfiedBy.cons
    · apply Evidence.Proves.var
      change _ = Binding.evidence (component.mappedUpper selected)
      rw [← alignment.upper]
      exact upperLookup
    · exact .nil

/-- Every aligned generated projection is declaratively valid. -/
def alignedHasType {scope : Sig} {encoding : Encoding scope}
    {context : Ctx scope} {selected : SelectedOccurrence encoding}
    {component : Component scope selected.sort}
    (alignment : Aligned selected component) :
    TheoryMap.HasType context (map selected component) :=
  hasType_of_aligned alignment (selected.evidenceMatches context)

/-- The standalone checker accepts every aligned generated projection. -/
theorem aligned_check_isSome {scope : Sig} {encoding : Encoding scope}
    {context : Ctx scope} {selected : SelectedOccurrence encoding}
    {component : Component scope selected.sort}
    (alignment : Aligned selected component) :
    (check context selected component).isSome = true :=
  TheoryMap.check_isSome_iff.mpr ⟨alignedHasType alignment⟩

/-! ## Structural identity guarantees -/

/-- Projection allocates no symbol: the component's sole abstract name is
interpreted by the selected merged name. -/
@[simp]
theorem map_symbols {scope : Sig} {encoding : Encoding scope}
    (selected : SelectedOccurrence encoding)
    (component : Component scope selected.sort) :
    (map selected component).symbols = .cons selected.symbol .nil := rfl

/-- Projection cites the two coordinates retained for this exact occurrence. -/
@[simp]
theorem map_evidence {scope : Sig} {encoding : Encoding scope}
    (selected : SelectedOccurrence encoding)
    (component : Component scope selected.sort) :
    (map selected component).evidence =
      .cons (.var selected.occurrence.lowerEvidence)
        (.cons (.var selected.occurrence.upperEvidence) .nil) := rfl

end DOTCaptureToManySortedFC.Intersections.Projection
