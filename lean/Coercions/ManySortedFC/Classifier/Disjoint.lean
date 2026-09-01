import Coercions.ManySortedFC.Classifier.Subkind

/-!
# Kind disjointness

Two kinds are disjoint when their computed intersection is algorithmically
empty.  The relation is executable and coincides with absence of a shared
classifier.
-/

namespace ManySortedFC.Classifier.Kind

/-- Empty-intersection disjointness of ground kinds. -/
inductive Disjoint : Kind -> Kind -> Prop where
  | intersect : IsEmpty (Kind.intersect left right) -> Disjoint left right

namespace Disjoint

def decision (left right : Kind) : Decidable (Disjoint left right) :=
  match IsEmpty.decision (Kind.intersect left right) with
  | isTrue emptyIntersection => isTrue (.intersect emptyIntersection)
  | isFalse nonemptyIntersection => isFalse (by
      intro disjoint
      cases disjoint with
      | intersect contradiction => exact nonemptyIntersection contradiction)

instance : Decidable (Disjoint left right) := decision left right

/-- Empty-intersection disjointness is exactly absence of a common member. -/
theorem semantics :
    Disjoint left right ↔
      ∀ item, Contains left item -> Contains right item -> False := by
  constructor
  · intro disjoint item inLeft inRight
    cases disjoint with
    | intersect emptyIntersection =>
        exact emptyIntersection.not_contains
          (Contains.intersect.mpr ⟨inLeft, inRight⟩)
  · intro noCommon
    apply Kind.Disjoint.intersect
    apply IsEmpty.of_not_contains
    intro item inIntersection
    have both := Contains.intersect.mp inIntersection
    exact noCommon item both.1 both.2

/-- A disjoint pair cannot both contain the same classifier. -/
theorem not_both (disjoint : Disjoint left right)
    (inLeft : Contains left item) (inRight : Contains right item) : False :=
  semantics.mp disjoint item inLeft inRight

theorem symm (disjoint : Disjoint left right) : Disjoint right left := by
  apply semantics.mpr
  intro item inRight inLeft
  exact disjoint.not_both inLeft inRight

theorem emptyLeft (kind : Kind) : Disjoint Kind.empty kind := by
  apply semantics.mpr
  intro _ impossible _
  cases impossible

theorem emptyRight (kind : Kind) : Disjoint kind Kind.empty :=
  (emptyLeft kind).symm

theorem unionLeft (leftDisjoint : Disjoint first right)
    (rightDisjoint : Disjoint second right) :
    Disjoint (first ++ second) right := by
  apply semantics.mpr
  intro item inUnion inRight
  cases inUnion.of_append with
  | inl inFirst => exact leftDisjoint.not_both inFirst inRight
  | inr inSecond => exact rightDisjoint.not_both inSecond inRight

theorem unionRight (leftDisjoint : Disjoint left first)
    (rightDisjoint : Disjoint left second) :
    Disjoint left (first ++ second) :=
  (leftDisjoint.symm.unionLeft rightDisjoint.symm).symm

/-- Disjoint classifier roots induce disjoint complete-subtree kinds. -/
theorem classifiers (roots : Classifier.Disjoint leftRoot rightRoot) :
    Disjoint (Kind.classifier leftRoot) (Kind.classifier rightRoot) := by
  apply semantics.mpr
  intro _ inLeft inRight
  have belowLeft := Contains.classifier_iff.mp inLeft
  have belowRight := Contains.classifier_iff.mp inRight
  cases Subclass.chain belowLeft belowRight with
  | inl contradiction => exact roots.1 contradiction
  | inr contradiction => exact roots.2 contradiction

end Disjoint

end ManySortedFC.Classifier.Kind
