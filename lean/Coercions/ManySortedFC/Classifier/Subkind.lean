import Coercions.ManySortedFC.Classifier.Semantics

/-!
# Executable subkinding and extensional equality

Subkinding is checked by computing `K \ L` and checking that result for
emptiness.  Exact subtraction semantics makes this equivalent to ordinary
inclusion of denotations.
-/

namespace ManySortedFC.Classifier.Kind

/-- `Subkind source target` holds when subtraction leaves an empty kind. -/
inductive Subkind : Kind -> Kind -> Prop where
  | subtract : IsEmpty (Kind.subtract source target) -> Subkind source target

namespace Subkind

def decision (source target : Kind) : Decidable (Subkind source target) :=
  match IsEmpty.decision (Kind.subtract source target) with
  | isTrue emptyDifference => isTrue (.subtract emptyDifference)
  | isFalse nonemptyDifference => isFalse (by
      intro included
      cases included with
      | subtract contradiction => exact nonemptyDifference contradiction)

instance : Decidable (Subkind source target) := decision source target

/-- Subtraction-defined subkinding is exactly semantic inclusion. -/
theorem semantics :
    Subkind source target ↔
      ∀ item, Contains source item -> Contains target item := by
  constructor
  · intro included item inSource
    cases included with
    | subtract emptyDifference =>
        by_cases inTarget : Contains target item
        · exact inTarget
        · have inDifference := Contains.subtract.mpr ⟨inSource, inTarget⟩
          exact (emptyDifference.not_contains inDifference).elim
  · intro semantic
    apply Kind.Subkind.subtract
    apply IsEmpty.of_not_contains
    intro item inDifference
    have meaning := Contains.subtract.mp inDifference
    exact meaning.2 (semantic item meaning.1)

/-- Membership is preserved by subkinding. -/
theorem contains (included : Subkind source target)
    (contained : Contains source item) : Contains target item :=
  semantics.mp included item contained

theorem refl (kind : Kind) : Subkind kind kind :=
  semantics.mpr (fun _ contained => contained)

theorem trans (first : Subkind firstKind secondKind)
    (second : Subkind secondKind thirdKind) :
    Subkind firstKind thirdKind := by
  apply semantics.mpr
  intro item contained
  exact second.contains (first.contains contained)

theorem empty (kind : Kind) : Subkind Kind.empty kind := by
  apply semantics.mpr
  intro _ impossible
  cases impossible

theorem top (kind : Kind) : Subkind kind Kind.top := by
  apply semantics.mpr
  intro item _
  exact Contains.top

theorem appendLeft (left right : Kind) : Subkind left (left ++ right) := by
  apply semantics.mpr
  intro _ contained
  exact contained.appendLeft

theorem appendRight (left right : Kind) : Subkind right (left ++ right) := by
  apply semantics.mpr
  intro _ contained
  exact contained.appendRight

/-- Union is the least upper bound. -/
theorem union (leftIncluded : Subkind left target)
    (rightIncluded : Subkind right target) :
    Subkind (left ++ right) target := by
  apply semantics.mpr
  intro item contained
  cases contained.of_append with
  | inl inLeft => exact leftIncluded.contains inLeft
  | inr inRight => exact rightIncluded.contains inRight

end Subkind

/-- Extensional equality of kinds. -/
def Equivalent (left right : Kind) : Prop :=
  Subkind left right ∧ Subkind right left

namespace Equivalent

def decision (left right : Kind) : Decidable (Equivalent left right) :=
  match Subkind.decision left right with
  | isFalse notForward => isFalse (by
      intro equivalent
      exact notForward equivalent.1)
  | isTrue forward =>
      match Subkind.decision right left with
      | isFalse notBackward => isFalse (by
          intro equivalent
          exact notBackward equivalent.2)
      | isTrue backward => isTrue ⟨forward, backward⟩

instance : Decidable (Equivalent left right) := decision left right

theorem contains (equivalent : Equivalent left right) :
    Contains left item ↔ Contains right item :=
  ⟨equivalent.1.contains, equivalent.2.contains⟩

theorem refl (kind : Kind) : Equivalent kind kind :=
  ⟨Subkind.refl kind, Subkind.refl kind⟩

theorem symm (equivalent : Equivalent left right) :
    Equivalent right left :=
  ⟨equivalent.2, equivalent.1⟩

theorem trans (first : Equivalent firstKind secondKind)
    (second : Equivalent secondKind thirdKind) :
    Equivalent firstKind thirdKind :=
  ⟨first.1.trans second.1, second.2.trans first.2⟩

end Equivalent

end ManySortedFC.Classifier.Kind
