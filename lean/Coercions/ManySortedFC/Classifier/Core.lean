/-!
# Closed classifier trees

The classifier universe is the countably branching tree used by
System Capless(K).  A classifier is a path built from `top`; `a ≤ b` means
that `a` is in the subtree rooted at `b`.

This module is independent of the ManySortedFC term and static languages.  It
is the closed ground theory that a later projected-capture layer can ask the
target checker to recompute.
-/

namespace ManySortedFC

/-- Nodes of the infinite, countably branching classifier tree. -/
inductive Classifier : Type where
  | top
  | child (index : Nat) (parent : Classifier)
deriving DecidableEq, Repr

namespace Classifier

/-- `Subclass a b` means that `a` is a descendant of `b`, including `b`
itself. -/
inductive Subclass : Classifier -> Classifier -> Prop where
  | refl : Subclass classifier classifier
  | child : Subclass classifier ancestor ->
      Subclass (.child index classifier) ancestor

instance : LE Classifier where
  le := Subclass

/-- The depth of a classifier below `top`. -/
def depth : Classifier -> Nat
  | .top => 0
  | .child _ parent => parent.depth + 1

theorem Subclass.trans (first : Subclass a b) (second : Subclass b c) :
    Subclass a c := by
  induction first with
  | refl => exact second
  | child _ induction => exact .child (induction second)

/-- Moving the right endpoint to its parent preserves subclassing. -/
theorem Subclass.parentRight (subclass : Subclass a (.child index parent)) :
    Subclass a parent :=
  subclass.trans (.child .refl)

/-- Descendants are at least as deep as their ancestors. -/
theorem Subclass.depth_le (subclass : Subclass a b) : b.depth ≤ a.depth := by
  induction subclass with
  | refl => exact Nat.le_refl _
  | child _ induction =>
      exact Nat.le_trans induction (Nat.le_succ _)

theorem Subclass.eq_of_depth_eq (subclass : Subclass a b)
    (equalDepth : a.depth = b.depth) : a = b := by
  cases subclass with
  | refl => rfl
  | child inner =>
      have impossible := Nat.le_trans (Nat.le_of_eq equalDepth) inner.depth_le
      exact (Nat.not_succ_le_self _ (by simpa [depth] using impossible)).elim

theorem Subclass.antisymm (first : Subclass a b) (second : Subclass b a) :
    a = b := by
  apply first.eq_of_depth_eq
  exact Nat.le_antisymm second.depth_le first.depth_le

/-- The descendant relation is decidable by walking from the candidate node
towards `top`. -/
def Subclass.decRel (a b : Classifier) : Decidable (Subclass a b) :=
  match a with
  | .top =>
      match b with
      | .top => isTrue .refl
      | .child _ _ => isFalse (by intro impossible; cases impossible)
  | .child index parent =>
      if equal : Classifier.child index parent = b then
        isTrue (equal ▸ Subclass.refl)
      else
        match decRel parent b with
        | isTrue subclass => isTrue (.child subclass)
        | isFalse notSubclass => isFalse (by
            intro subclass
            cases subclass with
            | refl => exact equal rfl
            | child parentSubclass => exact notSubclass parentSubclass)
termination_by a

instance : DecidableRel Subclass := Subclass.decRel

instance : DecidableLE Classifier := Subclass.decRel

@[refl]
theorem le_refl (classifier : Classifier) : classifier ≤ classifier :=
  .refl

theorem le_trans {a b c : Classifier} (first : a ≤ b) (second : b ≤ c) : a ≤ c :=
  first.trans second

theorem le_antisymm {a b : Classifier} (first : a ≤ b) (second : b ≤ a) : a = b :=
  first.antisymm second

/-- Every classifier is below the root. -/
@[simp]
theorem Subclass.top (classifier : Classifier) : classifier ≤ .top := by
  induction classifier with
  | top => exact .refl
  | child _ _ induction => exact .child induction

/-- The root is below no proper classifier. -/
theorem Subclass.top_left (subclass : Classifier.top ≤ classifier) :
    classifier = .top := by
  exact (le_antisymm subclass (Subclass.top classifier)).symm

/-- Two ancestors of one classifier are comparable. -/
theorem Subclass.chain {a b c : Classifier} (left : a ≤ b) (right : a ≤ c) :
    b ≤ c ∨ c ≤ b := by
  induction left generalizing c with
  | refl => exact Or.inl right
  | child left induction =>
      cases right with
      | refl => exact Or.inr (.child left)
      | child right => exact induction right

/-- Classifier roots are disjoint when neither lies below the other. -/
def Disjoint (a b : Classifier) : Prop :=
  (¬ a ≤ b) ∧ (¬ b ≤ a)

instance : DecidableRel Disjoint := fun a b => by
  by_cases left : a ≤ b
  · exact isFalse (by intro disjoint; exact disjoint.1 left)
  · by_cases right : b ≤ a
    · exact isFalse (by intro disjoint; exact disjoint.2 right)
    · exact isTrue ⟨left, right⟩

theorem Disjoint.irrefl (classifier : Classifier) :
    ¬ Disjoint classifier classifier := by
  intro disjoint
  exact disjoint.1 (le_refl classifier)

/-- Every two roots are comparable or disjoint. -/
theorem subclass_or_disjoint (a b : Classifier) :
    a ≤ b ∨ b ≤ a ∨ Disjoint a b := by
  by_cases left : a ≤ b
  · exact Or.inl left
  · by_cases right : b ≤ a
    · exact Or.inr (Or.inl right)
    · exact Or.inr (Or.inr ⟨left, right⟩)

theorem Disjoint.symm (disjoint : Disjoint a b) : Disjoint b a :=
  ⟨disjoint.2, disjoint.1⟩

/-- A descendant of one side of a disjoint pair remains disjoint from the
other side. -/
theorem Disjoint.descendLeft (disjoint : Disjoint a b) (descendant : c ≤ a) :
    Disjoint c b := by
  constructor
  · intro common
    cases Subclass.chain descendant common with
    | inl aBelowB => exact disjoint.1 aBelowB
    | inr bBelowA => exact disjoint.2 bBelowA
  · intro bBelowC
    exact disjoint.2 (Subclass.trans bBelowC descendant)

theorem Disjoint.descendRight (disjoint : Disjoint a b) (descendant : c ≤ b) :
    Disjoint a c :=
  (disjoint.symm.descendLeft descendant).symm

end Classifier

end ManySortedFC
