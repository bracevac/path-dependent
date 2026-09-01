import Coercions.ManySortedFC.Classifier.Subtract

/-!
# Set semantics of closed classifier kinds

`Kind.Contains K c` is the denotation of a ground kind at classifier `c`.
This module proves that the executable operations compute literal set
intersection and set difference, and that algorithmic emptiness is exact.
-/

namespace ManySortedFC.Classifier

/-- A classifier lies below none of the roots in an exclusion list. -/
inductive Avoids (classifier : ManySortedFC.Classifier) :
    List ManySortedFC.Classifier -> Prop where
  | nil : Avoids classifier []
  | cons : (¬ classifier ≤ head) -> Avoids classifier tail ->
      Avoids classifier (head :: tail)

namespace Avoids

def decision : (classifier : ManySortedFC.Classifier) ->
    (exclusions : List ManySortedFC.Classifier) ->
    Decidable (Avoids classifier exclusions)
  | _, [] => isTrue .nil
  | classifier, head :: tail =>
      match Subclass.decRel classifier head with
      | isTrue below => isFalse (by
          intro avoids
          cases avoids with
          | cons notBelow _ => exact notBelow below)
      | isFalse notBelow =>
          match decision classifier tail with
          | isTrue avoidsTail => isTrue (.cons notBelow avoidsTail)
          | isFalse notAvoidsTail => isFalse (by
              intro avoids
              cases avoids with
              | cons _ contradiction => exact notAvoidsTail contradiction)

instance : Decidable (Avoids classifier exclusions) :=
  decision classifier exclusions

theorem append (left : Avoids classifier first)
    (right : Avoids classifier second) :
    Avoids classifier (first ++ second) := by
  induction left with
  | nil => exact right
  | cons notBelow _ induction => exact .cons notBelow induction

theorem of_append (both : Avoids classifier (first ++ second)) :
    Avoids classifier first ∧ Avoids classifier second := by
  induction first with
  | nil => exact ⟨.nil, both⟩
  | cons _ tail induction =>
      cases both with
      | cons notBelow rest =>
          have split := induction rest
          exact ⟨.cons notBelow split.1, split.2⟩

/-- An avoided list cannot contain an ancestor of the classifier. -/
theorem conflicts (avoids : Avoids classifier exclusions)
    (contains : ContainsSupOf exclusions ancestor)
    (below : classifier ≤ ancestor) : False := by
  induction contains with
  | here ancestorBelow =>
      cases avoids with
      | cons notBelow _ => exact notBelow (le_trans below ancestorBelow)
  | there inTail induction =>
      cases avoids with
      | cons _ avoidsTail => exact induction avoidsTail below

/-- Failure to avoid a finite list is exactly the presence of an ancestor. -/
theorem not_iff_containsSup :
    (¬ Avoids classifier exclusions) ↔ ContainsSupOf exclusions classifier := by
  constructor
  · intro notAvoids
    induction exclusions with
    | nil => exact (notAvoids .nil).elim
    | cons head tail induction =>
        by_cases below : classifier ≤ head
        · exact .here below
        · apply ContainsSupOf.there
          apply induction
          intro avoidsTail
          exact notAvoids (.cons below avoidsTail)
  · intro contains avoids
    exact avoids.conflicts contains (le_refl classifier)

end Avoids

namespace Subtree

/-- A classifier is in a holed subtree when it is below the root and avoids
every excluded root. -/
structure Contains (subtree : Subtree)
    (classifier : ManySortedFC.Classifier) : Prop where
  belowRoot : classifier ≤ subtree.root
  avoids : Avoids classifier subtree.exclusions

namespace Contains

def decision (subtree : Subtree) (classifier : ManySortedFC.Classifier) :
    Decidable (Contains subtree classifier) :=
  match Subclass.decRel classifier subtree.root with
  | isFalse notBelow => isFalse (by
      intro contained
      exact notBelow contained.belowRoot)
  | isTrue below =>
      match Avoids.decision classifier subtree.exclusions with
      | isTrue avoids => isTrue ⟨below, avoids⟩
      | isFalse notAvoids => isFalse (by
          intro contained
          exact notAvoids contained.avoids)

instance : Decidable (Contains subtree classifier) :=
  decision subtree classifier

theorem appendExclusions
    (left : Contains { root := rootClassifier, exclusions := first } classifier)
    (right : Contains { root := rootClassifier, exclusions := second } classifier) :
    Contains { root := rootClassifier, exclusions := first ++ second } classifier :=
  ⟨left.belowRoot, left.avoids.append right.avoids⟩

theorem of_appendExclusions
    (both : Contains { root := rootClassifier, exclusions := first ++ second } classifier) :
    Contains { root := rootClassifier, exclusions := first } classifier ∧
      Contains { root := rootClassifier, exclusions := second } classifier := by
  have split := both.avoids.of_append
  exact ⟨⟨both.belowRoot, split.1⟩, ⟨both.belowRoot, split.2⟩⟩

theorem weakenRoot (contained : Contains subtree classifier)
    (rootBelow : subtree.root ≤ largerRoot) :
    Contains { root := largerRoot, exclusions := subtree.exclusions } classifier :=
  ⟨le_trans contained.belowRoot rootBelow, contained.avoids⟩

end Contains

end Subtree

namespace Kind

/-- Membership in one component of a finite kind union. -/
inductive Contains : Kind -> ManySortedFC.Classifier -> Prop where
  | here : Subtree.Contains head item ->
      Contains (head :: tail) item
  | there : Contains tail item ->
      Contains (head :: tail) item

namespace Contains

def decision : (kind : Kind) -> (item : ManySortedFC.Classifier) ->
    Decidable (Contains kind item)
  | [], _ => isFalse (by intro impossible; cases impossible)
  | head :: tail, item =>
      match Subtree.Contains.decision head item with
      | isTrue inHead => isTrue (.here inHead)
      | isFalse notInHead =>
          match decision tail item with
          | isTrue inTail => isTrue (.there inTail)
          | isFalse notInTail => isFalse (by
              intro contained
              cases contained with
              | here contradiction => exact notInHead contradiction
              | there contradiction => exact notInTail contradiction)

instance : Decidable (Contains kind item) :=
  decision kind item

theorem singleton (contained : Subtree.Contains subtree item) :
    Contains [subtree] item := .here contained

theorem of_singleton (contained : Contains [subtree] item) :
    Subtree.Contains subtree item := by
  cases contained with
  | here inHead => exact inHead
  | there impossible => cases impossible

theorem appendLeft (contained : Contains left item) :
    Contains (left ++ right) item := by
  induction contained with
  | here inHead => exact .here inHead
  | there _ induction => exact .there induction

theorem appendRight (contained : Contains right item) :
    Contains (left ++ right) item := by
  induction left with
  | nil => exact contained
  | cons _ _ induction => exact .there induction

/-- Introduce membership into a kind union. -/
theorem append (contained : Contains left item ∨ Contains right item) :
    Contains (left ++ right) item := by
  cases contained with
  | inl inLeft => exact inLeft.appendLeft
  | inr inRight => exact inRight.appendRight

/-- Eliminate membership from a kind union. -/
theorem of_append (contained : Contains (left ++ right) item) :
    Contains left item ∨ Contains right item := by
  induction left with
  | nil => exact .inr contained
  | cons _ tail induction =>
      cases contained with
      | here inHead => exact .inl (.here inHead)
      | there inRest =>
          cases induction inRest with
          | inl inLeft => exact .inl (.there inLeft)
          | inr inRight => exact .inr inRight

theorem append_iff :
    Contains (left ++ right) item ↔
      Contains left item ∨ Contains right item :=
  ⟨of_append, append⟩

theorem node
    (contained : Subtree.Contains
      { root := rootClassifier, exclusions := exclusions } item) :
    Contains (node rootClassifier exclusions) item := by
  exact .here contained

theorem of_node (contained : Contains (Kind.node rootClassifier exclusions) item) :
    Subtree.Contains { root := rootClassifier, exclusions := exclusions } item := by
  exact of_singleton contained

theorem classifier (below : item ≤ rootClassifier) :
    Contains (Kind.classifier rootClassifier) item :=
  .node ⟨below, .nil⟩

theorem classifier_iff :
    Contains (Kind.classifier rootClassifier) item ↔ item ≤ rootClassifier := by
  constructor
  · intro contained
    exact contained.of_node.belowRoot
  · exact classifier

theorem top : Contains Kind.top item := by
  exact classifier (Subclass.top item)

end Contains

namespace IsEmpty

/-- Algorithmic emptiness excludes every semantic member. -/
theorem not_contains (emptyKind : IsEmpty kind)
    (contained : Contains kind item) : False := by
  induction emptyKind with
  | empty => cases contained
  | absurd absurdHead _ induction =>
      cases contained with
      | here inHead =>
          exact inHead.avoids.conflicts absurdHead inHead.belowRoot
      | there inTail => exact induction inTail

/-- Semantic emptiness implies the executable emptiness judgment. -/
theorem of_not_contains
    (none : ∀ item, ¬ Contains kind item) : IsEmpty kind := by
  induction kind with
  | nil => exact .empty
  | cons subtree rest induction =>
      by_cases absurdHead : ContainsSupOf subtree.exclusions subtree.root
      · apply Kind.IsEmpty.absurd absurdHead
        apply induction
        intro item inRest
        exact none item (.there inRest)
      · have avoidsRoot : Avoids subtree.root subtree.exclusions := by
          cases Avoids.decision subtree.root subtree.exclusions with
          | isTrue avoids => exact avoids
          | isFalse notAvoids =>
              exact (absurdHead (Avoids.not_iff_containsSup.mp notAvoids)).elim
        exact (none subtree.root (.here ⟨le_refl subtree.root, avoidsRoot⟩)).elim

theorem iff_not_contains :
    IsEmpty kind ↔ ∀ item, ¬ Contains kind item := by
  constructor
  · intro emptyKind item contained
    exact emptyKind.not_contains contained
  · exact of_not_contains

end IsEmpty

end Kind

namespace Subtree.Contains

/-- Executable subtree intersection has exact conjunctive semantics. -/
theorem intersect_iff (left right : Subtree)
    (item : ManySortedFC.Classifier) :
    Kind.Contains (Subtree.intersect left right) item ↔
      Subtree.Contains left item ∧ Subtree.Contains right item := by
  unfold Subtree.intersect
  by_cases leftBelow : left.root ≤ right.root
  · rw [if_pos leftBelow]
    constructor
    · intro inResult
      have split := Kind.Contains.of_node inResult |>.of_appendExclusions
      exact ⟨split.1, split.2.weakenRoot leftBelow⟩
    · intro both
      apply Kind.Contains.node
      apply both.1.appendExclusions
      exact ⟨both.1.belowRoot, both.2.avoids⟩
  · rw [if_neg leftBelow]
    by_cases rightBelow : right.root ≤ left.root
    · rw [if_pos rightBelow]
      constructor
      · intro inResult
        have split := Kind.Contains.of_node inResult |>.of_appendExclusions
        exact ⟨split.1.weakenRoot rightBelow, split.2⟩
      · intro both
        apply Kind.Contains.node
        apply (show Subtree.Contains
            { root := right.root, exclusions := left.exclusions } item from
          ⟨both.2.belowRoot, both.1.avoids⟩).appendExclusions
        exact both.2
    · rw [if_neg rightBelow]
      constructor
      · intro impossible
        change Kind.Contains [] item at impossible
        cases impossible
      · intro both
        cases Subclass.chain both.1.belowRoot both.2.belowRoot with
        | inl contradiction => exact (leftBelow contradiction).elim
        | inr contradiction => exact (rightBelow contradiction).elim

end Subtree.Contains

namespace Kind.Contains

private theorem intersectOne_iff (left : Subtree) (right : Kind)
    (item : ManySortedFC.Classifier) :
    Contains (Kind.intersectOne left right) item ↔
      Subtree.Contains left item ∧ Contains right item := by
  induction right with
  | nil =>
      constructor
      · intro impossible
        change Contains [] item at impossible
        cases impossible
      · intro impossible
        cases impossible.2
  | cons head tail induction =>
      constructor
      · intro inResult
        cases inResult.of_append with
        | inl inHead =>
            have both := (Subtree.Contains.intersect_iff left head item).mp inHead
            exact ⟨both.1, .here both.2⟩
        | inr inTail =>
            have both := induction.mp inTail
            exact ⟨both.1, .there both.2⟩
      · intro both
        cases both.2 with
        | here inHead =>
            apply append (.inl ?_)
            exact (Subtree.Contains.intersect_iff left head item).mpr
              ⟨both.1, inHead⟩
        | there inTail =>
            apply append (.inr ?_)
            exact induction.mpr ⟨both.1, inTail⟩

/-- Executable kind intersection denotes exact set intersection. -/
theorem intersect :
    Contains (Kind.intersect left right) item ↔
      Contains left item ∧ Contains right item := by
  induction left with
  | nil =>
      constructor
      · intro impossible
        change Contains [] item at impossible
        cases impossible
      · intro impossible
        cases impossible.1
  | cons head tail induction =>
      constructor
      · intro inResult
        cases inResult.of_append with
        | inl inHead =>
            have both := intersectOne_iff head right item |>.mp inHead
            exact ⟨.here both.1, both.2⟩
        | inr inTail =>
            have both := induction.mp inTail
            exact ⟨.there both.1, both.2⟩
      · intro both
        cases both.1 with
        | here inHead =>
            apply append (.inl ?_)
            exact intersectOne_iff head right item |>.mpr ⟨inHead, both.2⟩
        | there inTail =>
            apply append (.inr ?_)
            exact induction.mpr ⟨inTail, both.2⟩

end Kind.Contains

namespace Subtree

private theorem restore_contains_iff (source : Subtree)
    (removedRoot : ManySortedFC.Classifier)
    (exclusions : List ManySortedFC.Classifier)
    (item : ManySortedFC.Classifier) :
    Kind.Contains (restore source removedRoot exclusions) item ↔
      Contains source item ∧ item ≤ removedRoot ∧
        ContainsSupOf exclusions item := by
  induction exclusions with
  | nil =>
      constructor
      · intro impossible
        change Kind.Contains [] item at impossible
        cases impossible
      · intro impossible
        cases impossible.2.2
  | cons exclusion rest induction =>
      constructor
      · intro inResult
        cases Kind.Contains.of_append inResult with
        | inl inRestored =>
            have outer := Kind.Contains.intersect.mp inRestored
            have inner := Kind.Contains.intersect.mp outer.1
            exact ⟨Kind.Contains.of_singleton inner.1,
              Kind.Contains.classifier_iff.mp inner.2,
              .here (Kind.Contains.classifier_iff.mp outer.2)⟩
        | inr inTail =>
            have restored := induction.mp inTail
            exact ⟨restored.1, restored.2.1, .there restored.2.2⟩
      · intro desired
        cases desired.2.2 with
        | here belowExclusion =>
            apply Kind.Contains.append (.inl ?_)
            apply Kind.Contains.intersect.mpr
            constructor
            · apply Kind.Contains.intersect.mpr
              exact ⟨Kind.Contains.singleton desired.1,
                Kind.Contains.classifier desired.2.1⟩
            · exact Kind.Contains.classifier belowExclusion
        | there inTail =>
            apply Kind.Contains.append (.inr ?_)
            exact induction.mpr ⟨desired.1, desired.2.1, inTail⟩

private theorem outside_contains_iff (source : Subtree)
    (removedRoot item : ManySortedFC.Classifier) :
    Kind.Contains
        (Kind.node source.root (removedRoot :: source.exclusions)) item ↔
      Contains source item ∧ ¬ item ≤ removedRoot := by
  constructor
  · intro inOutside
    have raw := Kind.Contains.of_node inOutside
    cases raw.avoids with
    | cons notBelow avoidsSource =>
        exact ⟨⟨raw.belowRoot, avoidsSource⟩, notBelow⟩
  · intro desired
    exact Kind.Contains.node
      ⟨desired.1.belowRoot, .cons desired.2 desired.1.avoids⟩

/-- Executable subtree subtraction denotes exact set difference. -/
theorem Contains.subtract (source removed : Subtree)
    (item : ManySortedFC.Classifier) :
    Kind.Contains (Subtree.subtract source removed) item ↔
      Contains source item ∧ ¬ Contains removed item := by
  unfold Subtree.subtract
  constructor
  · intro inResult
    cases Kind.Contains.of_append inResult with
    | inl outside =>
        have outsideMeaning := outside_contains_iff source removed.root item |>.mp outside
        exact ⟨outsideMeaning.1, by
          intro inRemoved
          exact outsideMeaning.2 inRemoved.belowRoot⟩
    | inr restored =>
        have restoredMeaning :=
          restore_contains_iff source removed.root removed.exclusions item |>.mp restored
        exact ⟨restoredMeaning.1, by
          intro inRemoved
          exact inRemoved.avoids.conflicts restoredMeaning.2.2 (le_refl item)⟩
  · intro desired
    by_cases belowRemoved : item ≤ removed.root
    · have notAvoids : ¬ Avoids item removed.exclusions := by
        intro avoids
        exact desired.2 ⟨belowRemoved, avoids⟩
      apply Kind.Contains.append (.inr ?_)
      exact restore_contains_iff source removed.root removed.exclusions item |>.mpr
        ⟨desired.1, belowRemoved,
          Avoids.not_iff_containsSup.mp notAvoids⟩
    · apply Kind.Contains.append (.inl ?_)
      exact outside_contains_iff source removed.root item |>.mpr
        ⟨desired.1, belowRemoved⟩

end Subtree

namespace Kind.Contains

private theorem subtractOne_iff (source : Kind) (removed : Subtree)
    (item : ManySortedFC.Classifier) :
    Contains (Kind.subtractOne source removed) item ↔
      Contains source item ∧ ¬ Subtree.Contains removed item := by
  induction source with
  | nil =>
      constructor
      · intro impossible
        change Contains [] item at impossible
        cases impossible
      · intro impossible
        cases impossible.1
  | cons head tail induction =>
      constructor
      · intro inResult
        cases inResult.of_append with
        | inl inHead =>
            have meaning := Subtree.Contains.subtract head removed item |>.mp inHead
            exact ⟨.here meaning.1, meaning.2⟩
        | inr inTail =>
            have meaning := induction.mp inTail
            exact ⟨.there meaning.1, meaning.2⟩
      · intro desired
        cases desired.1 with
        | here inHead =>
            apply append (.inl ?_)
            exact Subtree.Contains.subtract head removed item |>.mpr
              ⟨inHead, desired.2⟩
        | there inTail =>
            apply append (.inr ?_)
            exact induction.mpr ⟨inTail, desired.2⟩

private theorem subtractFrom_iff (removed source : Kind)
    (item : ManySortedFC.Classifier) :
    Contains (Kind.subtractFrom removed source) item ↔
      Contains source item ∧ ¬ Contains removed item := by
  induction removed generalizing source with
  | nil =>
      constructor
      · intro inSource
        exact ⟨inSource, by intro impossible; cases impossible⟩
      · intro desired
        exact desired.1
  | cons head tail induction =>
      constructor
      · intro inResult
        have afterTail := (induction (Kind.subtractOne source head)).mp inResult
        have afterHead := subtractOne_iff source head item |>.mp afterTail.1
        exact ⟨afterHead.1, by
          intro inRemoved
          cases inRemoved with
          | here inHead => exact afterHead.2 inHead
          | there inTail => exact afterTail.2 inTail⟩
      · intro desired
        apply (induction (Kind.subtractOne source head)).mpr
        constructor
        · apply subtractOne_iff source head item |>.mpr
          exact ⟨desired.1, by
            intro inHead
            exact desired.2 (.here inHead)⟩
        · intro inTail
          exact desired.2 (.there inTail)

/-- Executable kind subtraction denotes exact set difference. -/
theorem subtract :
    Contains (Kind.subtract source removed) item ↔
      Contains source item ∧ ¬ Contains removed item := by
  exact subtractFrom_iff removed source item

end Kind.Contains

end ManySortedFC.Classifier
