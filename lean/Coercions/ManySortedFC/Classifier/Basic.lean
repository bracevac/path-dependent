import Coercions.ManySortedFC.Classifier.Disjoint

/-!
# Projection-facing laws of the ground kind algebra

This file keeps only the extensional laws needed to justify `only`/`except`
projection: intersection bounds and composition, distribution over union,
subtraction order, and disjoint projected views.
-/

namespace ManySortedFC.Classifier.Kind

namespace Equivalent

/-- Extensional membership equality introduces checked kind equivalence. -/
theorem of_contains
    (same : ∀ item, Contains left item ↔ Contains right item) :
    Equivalent left right := by
  constructor
  · apply Subkind.semantics.mpr
    intro item inLeft
    exact (same item).mp inLeft
  · apply Subkind.semantics.mpr
    intro item inRight
    exact (same item).mpr inRight

theorem intersectTopRight (kind : Kind) :
    Equivalent (Kind.intersect kind Kind.top) kind := by
  apply of_contains
  intro item
  constructor
  · intro contained
    exact Contains.intersect.mp contained |>.1
  · intro contained
    exact Contains.intersect.mpr ⟨contained, Contains.top⟩

theorem intersectTopLeft (kind : Kind) :
    Equivalent (Kind.intersect Kind.top kind) kind := by
  apply of_contains
  intro item
  constructor
  · intro contained
    exact Contains.intersect.mp contained |>.2
  · intro contained
    exact Contains.intersect.mpr ⟨Contains.top, contained⟩

theorem intersectComm (left right : Kind) :
    Equivalent (Kind.intersect left right) (Kind.intersect right left) := by
  apply of_contains
  intro item
  constructor
  · intro contained
    have both := Contains.intersect.mp contained
    exact Contains.intersect.mpr ⟨both.2, both.1⟩
  · intro contained
    have both := Contains.intersect.mp contained
    exact Contains.intersect.mpr ⟨both.2, both.1⟩

theorem intersectAssoc (first second third : Kind) :
    Equivalent
      (Kind.intersect (Kind.intersect first second) third)
      (Kind.intersect first (Kind.intersect second third)) := by
  apply of_contains
  intro item
  constructor
  · intro contained
    have outer := Contains.intersect.mp contained
    have inner := Contains.intersect.mp outer.1
    exact Contains.intersect.mpr
      ⟨inner.1, Contains.intersect.mpr ⟨inner.2, outer.2⟩⟩
  · intro contained
    have outer := Contains.intersect.mp contained
    have inner := Contains.intersect.mp outer.2
    exact Contains.intersect.mpr
      ⟨Contains.intersect.mpr ⟨outer.1, inner.1⟩, inner.2⟩

theorem intersectIdem (kind : Kind) :
    Equivalent (Kind.intersect kind kind) kind := by
  apply of_contains
  intro item
  constructor
  · intro contained
    exact Contains.intersect.mp contained |>.1
  · intro contained
    exact Contains.intersect.mpr ⟨contained, contained⟩

/-- Projection distributes over a union of sources. -/
theorem intersectAppendLeft (first second filter : Kind) :
    Equivalent
      (Kind.intersect (first ++ second) filter)
      (Kind.intersect first filter ++ Kind.intersect second filter) := by
  apply of_contains
  intro item
  constructor
  · intro contained
    have both := Contains.intersect.mp contained
    cases both.1.of_append with
    | inl inFirst =>
        exact Contains.append (.inl (Contains.intersect.mpr ⟨inFirst, both.2⟩))
    | inr inSecond =>
        exact Contains.append (.inr (Contains.intersect.mpr ⟨inSecond, both.2⟩))
  · intro contained
    cases contained.of_append with
    | inl inFirst =>
        have both := Contains.intersect.mp inFirst
        exact Contains.intersect.mpr ⟨both.1.appendLeft, both.2⟩
    | inr inSecond =>
        have both := Contains.intersect.mp inSecond
        exact Contains.intersect.mpr ⟨both.1.appendRight, both.2⟩

/-- Intersection distributes over a union of filters. -/
theorem intersectAppendRight (source first second : Kind) :
    Equivalent
      (Kind.intersect source (first ++ second))
      (Kind.intersect source first ++ Kind.intersect source second) := by
  have commutedSource := intersectComm source (first ++ second)
  have distributed := intersectAppendLeft first second source
  have commuteFirst := intersectComm first source
  have commuteSecond := intersectComm second source
  apply commutedSource.trans
  apply distributed.trans
  apply of_contains
  intro item
  constructor
  · intro contained
    cases contained.of_append with
    | inl inFirst => exact Contains.append (.inl (commuteFirst.contains.mp inFirst))
    | inr inSecond => exact Contains.append (.inr (commuteSecond.contains.mp inSecond))
  · intro contained
    cases contained.of_append with
    | inl inFirst => exact Contains.append (.inl (commuteFirst.contains.mpr inFirst))
    | inr inSecond => exact Contains.append (.inr (commuteSecond.contains.mpr inSecond))

/-- Sequential exclusion agrees with excluding a union. -/
theorem subtractAppend (source first second : Kind) :
    Equivalent
      (Kind.subtract source (first ++ second))
      (Kind.subtract (Kind.subtract source first) second) := by
  apply of_contains
  intro item
  constructor
  · intro contained
    have meaning := Contains.subtract.mp contained
    have excludes : ¬ Contains first item ∧ ¬ Contains second item := by
      constructor
      · intro inFirst
        exact meaning.2 inFirst.appendLeft
      · intro inSecond
        exact meaning.2 inSecond.appendRight
    apply Contains.subtract.mpr
    exact ⟨Contains.subtract.mpr ⟨meaning.1, excludes.1⟩, excludes.2⟩
  · intro contained
    have outer := Contains.subtract.mp contained
    have inner := Contains.subtract.mp outer.1
    apply Contains.subtract.mpr
    exact ⟨inner.1, by
      intro inUnion
      cases inUnion.of_append with
      | inl inFirst => exact inner.2 inFirst
      | inr inSecond => exact outer.2 inSecond⟩

end Equivalent

namespace Subkind

theorem intersectLeft (left right : Kind) :
    Subkind (Kind.intersect left right) left := by
  apply semantics.mpr
  intro _ contained
  exact Contains.intersect.mp contained |>.1

theorem intersectRight (left right : Kind) :
    Subkind (Kind.intersect left right) right := by
  apply semantics.mpr
  intro _ contained
  exact Contains.intersect.mp contained |>.2

/-- Intersection is the greatest lower bound. -/
theorem intersectGreatest (toLeft : Subkind source left)
    (toRight : Subkind source right) :
    Subkind source (Kind.intersect left right) := by
  apply semantics.mpr
  intro _ contained
  exact Contains.intersect.mpr
    ⟨toLeft.contains contained, toRight.contains contained⟩

theorem intersectMono (leftMap : Subkind firstLeft secondLeft)
    (rightMap : Subkind firstRight secondRight) :
    Subkind
      (Kind.intersect firstLeft firstRight)
      (Kind.intersect secondLeft secondRight) := by
  apply semantics.mpr
  intro _ contained
  have both := Contains.intersect.mp contained
  exact Contains.intersect.mpr
    ⟨leftMap.contains both.1, rightMap.contains both.2⟩

theorem subtractLeft (source removed : Kind) :
    Subkind (Kind.subtract source removed) source := by
  apply semantics.mpr
  intro _ contained
  exact Contains.subtract.mp contained |>.1

end Subkind

namespace Disjoint

theorem emptyIntersection (disjoint : Disjoint left right) :
    IsEmpty (Kind.intersect left right) := by
  cases disjoint with
  | intersect emptyResult => exact emptyResult

/-- Subtraction is disjoint from the removed kind. -/
theorem subtractRight (source removed : Kind) :
    Disjoint (Kind.subtract source removed) removed := by
  apply semantics.mpr
  intro item inDifference inRemoved
  exact (Contains.subtract.mp inDifference).2 inRemoved

/-- Intersecting arbitrary sources with disjoint filters preserves
disjointness. -/
theorem intersectFilters (filters : Disjoint firstFilter secondFilter) :
    Disjoint
      (Kind.intersect firstSource firstFilter)
      (Kind.intersect secondSource secondFilter) := by
  apply semantics.mpr
  intro item inFirst inSecond
  have firstParts := Contains.intersect.mp inFirst
  have secondParts := Contains.intersect.mp inSecond
  exact filters.not_both firstParts.2 secondParts.2

end Disjoint

namespace IsEmpty

theorem intersectLeft (emptyLeft : IsEmpty left) (right : Kind) :
    IsEmpty (Kind.intersect left right) := by
  apply of_not_contains
  intro _ contained
  exact emptyLeft.not_contains (Contains.intersect.mp contained).1

theorem intersectRight (left : Kind) (emptyRight : IsEmpty right) :
    IsEmpty (Kind.intersect left right) := by
  apply of_not_contains
  intro _ contained
  exact emptyRight.not_contains (Contains.intersect.mp contained).2

end IsEmpty

end ManySortedFC.Classifier.Kind
