namespace Classifiers

/-!
# The classifier tree

Classifiers of System Capless(K) (`CaplessK/Classifier/Core.lean`), as data.
A classifier is a path of child indices from the root of an infinite tree, so
every node has infinitely many children by construction.  That is what makes
exclusion sound under separate compilation: no classifier can be singled out
by excluding all the sub-classifiers one module knows.

The subclass order is a `Bool` function here, not an inductive relation with a
`PartialOrder` instance (`Core.lean:36-39,99-104`), in the style of
`Ctx.lvlLeB` (`FCdot/Context.lean:211-212`).  Every order fact is therefore an
equation between `Bool`s, `Decidable` is synthesised for free, and `by decide`
closes an example in the kernel.
-/

namespace Cls

/-- The classifier tree (`Classifier/Core.lean:28-31`).  `child n a` is the
`n`-th child of `a`. -/
inductive Classifier : Type where
  | top : Classifier
  | child : Nat → Classifier → Classifier
deriving DecidableEq, Repr

namespace Classifier

/-- The subclass test: `leB a b` says that `a` lies in the subtree rooted at
`b`, that is, `b` is `a` or an ancestor of `a` (`Classifier/Core.lean:36-39`,
as a function). -/
def leB : Classifier → Classifier → Bool
  | .top, .top => true
  | .top, .child _ _ => false
  | .child n a, b => (Classifier.child n a == b) || leB a b

/-- The subclass order as a proposition. -/
abbrev Le (a b : Classifier) : Prop := leB a b = true

/-- Disjointness of two classifiers: neither is a subclass of the other
(`Classifier/Core.lean:142-145`). -/
def disjointB (a b : Classifier) : Bool := !leB a b && !leB b a

/-- Disjointness as a proposition. -/
abbrev Disjoint (a b : Classifier) : Prop := disjointB a b = true

/-- Reflexivity of the subclass order. -/
theorem leB_refl : ∀ a : Classifier, leB a a = true
  | .top => rfl
  | .child n a => by simp [leB]

/-- `⊤` is the greatest classifier. -/
theorem leB_top : ∀ a : Classifier, leB a .top = true
  | .top => rfl
  | .child n a => by simp [leB, leB_top a]

/-- Transitivity of the subclass order. -/
theorem leB_trans : ∀ {a b c : Classifier}, leB a b = true → leB b c = true → leB a c = true
  | .top, .top, _, _, h2 => h2
  | .child n a, b, c, h1, h2 => by
      simp only [leB, Bool.or_eq_true, beq_iff_eq] at h1 ⊢
      rcases h1 with rfl | h1
      · simpa only [leB, Bool.or_eq_true, beq_iff_eq] using h2
      · exact Or.inr (leB_trans h1 h2)

/-- A superclass is no larger than its subclass, which is what makes the order
antisymmetric. -/
theorem leB_size : ∀ {a b : Classifier}, leB a b = true → sizeOf b ≤ sizeOf a
  | .top, .top, _ => Nat.le_refl _
  | .child n a, b, h => by
      simp only [leB, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with rfl | h
      · exact Nat.le_refl _
      · have := leB_size h
        simp only [Classifier.child.sizeOf_spec]
        omega

/-- Antisymmetry of the subclass order. -/
theorem leB_antisymm : ∀ {a b : Classifier}, leB a b = true → leB b a = true → a = b
  | .top, .top, _, _ => rfl
  | .top, .child n b, h1, _ => by simp [leB] at h1
  | .child n a, b, h1, h2 => by
      simp only [leB, Bool.or_eq_true, beq_iff_eq] at h1
      rcases h1 with rfl | h1
      · rfl
      · exfalso
        have s1 := leB_size h1
        have s2 := leB_size h2
        simp only [Classifier.child.sizeOf_spec] at s2
        omega

/-- Trichotomy (`Classifier/Core.lean:157-160`): two classifiers are subclass
related in one direction or disjoint. -/
theorem subclass_or_disjoint (a b : Classifier) :
    leB a b = true ∨ leB b a = true ∨ disjointB a b = true := by
  cases h1 : leB a b
  · cases h2 : leB b a
    · exact Or.inr (Or.inr (by simp [disjointB, h1, h2]))
    · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

/-- The chain lemma: two superclasses of one classifier are comparable. -/
theorem chain : ∀ {a b c : Classifier}, leB a b = true → leB a c = true →
    leB b c = true ∨ leB c b = true
  | .top, b, c, h1, h2 => by
      cases b with
      | child m b' => simp [leB] at h1
      | top =>
          cases c with
          | child m c' => simp [leB] at h2
          | top => exact Or.inl rfl
  | .child n a, b, c, h1, h2 => by
      simp only [leB, Bool.or_eq_true, beq_iff_eq] at h1 h2
      rcases h1 with rfl | h1
      · rcases h2 with rfl | h2
        · exact Or.inl (leB_refl _)
        · exact Or.inl (by simp [leB, h2])
      · rcases h2 with rfl | h2
        · exact Or.inr (by simp [leB, h1])
        · exact chain h1 h2

/-- Disjoint classifiers have no common subclass, which is the chain lemma
read as a refutation. -/
theorem not_disjoint_of_le {a b c : Classifier} (h1 : leB a b = true) (h2 : leB a c = true) :
    disjointB b c = false := by
  rcases chain h1 h2 with h | h <;> simp [disjointB, h]

end Classifier

end Cls
end Classifiers
