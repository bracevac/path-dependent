import Coercions.ManySortedFC.Classifier.Core

/-!
# Closed classifier kinds

A kind is a finite union of holed classifier subtrees.  This is the ground
kind language used by the classifier projection experiment; it contains no
variables and does not depend on the ManySortedFC syntax.
-/

namespace ManySortedFC.Classifier

/-- A subtree rooted at `root`, with the listed descendant subtrees removed. -/
structure Subtree : Type where
  root : ManySortedFC.Classifier
  exclusions : List ManySortedFC.Classifier
deriving DecidableEq, Repr

/-- A finite union of holed subtrees. -/
def Kind : Type := List Subtree
deriving DecidableEq, Repr

namespace Kind

instance : Append Kind where
  append := List.append

/-- A singleton holed subtree. -/
def node (root : ManySortedFC.Classifier)
    (exclusions : List ManySortedFC.Classifier) : Kind :=
  [{ root, exclusions }]

/-- The complete subtree rooted at one classifier. -/
def classifier (root : ManySortedFC.Classifier) : Kind :=
  node root []

/-- The empty kind. -/
def empty : Kind := []

/-- The kind of every classifier. -/
def top : Kind := classifier .top

@[simp] theorem append_eq (left right : Kind) :
    left ++ right = List.append left right := rfl

@[simp] theorem node_ne_empty : node root exclusions ≠ empty := by
  intro impossible
  cases impossible

end Kind

/-- An exclusion list contains an ancestor of `classifier`. -/
inductive ContainsSupOf : List ManySortedFC.Classifier ->
    ManySortedFC.Classifier -> Prop where
  | here : classifier ≤ head -> ContainsSupOf (head :: tail) classifier
  | there : ContainsSupOf tail classifier ->
      ContainsSupOf (head :: tail) classifier

namespace ContainsSupOf

def decision : (exclusions : List ManySortedFC.Classifier) ->
    (classifier : ManySortedFC.Classifier) ->
    Decidable (ContainsSupOf exclusions classifier)
  | [], _ => isFalse (by intro impossible; cases impossible)
  | head :: tail, classifier =>
      match Subclass.decRel classifier head with
      | isTrue below => isTrue (.here below)
      | isFalse notBelow =>
          match decision tail classifier with
          | isTrue inTail => isTrue (.there inTail)
          | isFalse notInTail => isFalse (by
              intro contained
              cases contained with
              | here contradiction => exact notBelow contradiction
              | there contradiction => exact notInTail contradiction)

instance : Decidable (ContainsSupOf exclusions classifier) :=
  decision exclusions classifier

theorem appendLeft (contained : ContainsSupOf left classifier) :
    ContainsSupOf (left ++ right) classifier := by
  induction contained with
  | here below => exact .here below
  | there _ induction => exact .there induction

theorem appendRight (contained : ContainsSupOf right classifier) :
    ContainsSupOf (left ++ right) classifier := by
  induction left with
  | nil => exact contained
  | cons _ _ induction => exact .there induction

theorem of_append (contained : ContainsSupOf (left ++ right) classifier) :
    ContainsSupOf left classifier ∨ ContainsSupOf right classifier := by
  induction left with
  | nil => exact .inr contained
  | cons _ tail induction =>
      cases contained with
      | here below => exact .inl (.here below)
      | there inRest =>
          cases induction inRest with
          | inl inLeft => exact .inl (.there inLeft)
          | inr inRight => exact .inr inRight

theorem descend (contained : ContainsSupOf exclusions ancestor)
    (below : classifier ≤ ancestor) :
    ContainsSupOf exclusions classifier := by
  induction contained generalizing classifier with
  | here ancestorBelow => exact .here (le_trans below ancestorBelow)
  | there _ induction => exact .there (induction below)

end ContainsSupOf

namespace Kind

/-- Algorithmic emptiness.  Every component is empty because one of its own
exclusions is an ancestor of its root. -/
inductive IsEmpty : Kind -> Prop where
  | empty : IsEmpty []
  | absurd : ContainsSupOf subtree.exclusions subtree.root ->
      IsEmpty rest -> IsEmpty (subtree :: rest)

namespace IsEmpty

def decision : (kind : Kind) -> Decidable (IsEmpty kind)
  | [] => isTrue .empty
  | subtree :: rest =>
      match ContainsSupOf.decision subtree.exclusions subtree.root with
      | isFalse nonabsurd => isFalse (by
          intro emptyAll
          cases emptyAll with
          | absurd contradiction _ => exact nonabsurd contradiction)
      | isTrue absurdHead =>
          match decision rest with
          | isTrue emptyRest => isTrue (.absurd absurdHead emptyRest)
          | isFalse nonemptyRest => isFalse (by
              intro emptyAll
              cases emptyAll with
              | absurd _ contradiction => exact nonemptyRest contradiction)

instance : Decidable (IsEmpty kind) := decision kind

theorem append (leftEmpty : IsEmpty left) (rightEmpty : IsEmpty right) :
    IsEmpty (left ++ right) := by
  induction leftEmpty with
  | empty => exact rightEmpty
  | absurd absurdHead _ induction => exact .absurd absurdHead induction

theorem of_append (emptyAppend : IsEmpty (left ++ right)) :
    IsEmpty left ∧ IsEmpty right := by
  induction left with
  | nil => exact ⟨.empty, emptyAppend⟩
  | cons subtree rest induction =>
      cases emptyAppend with
      | absurd absurdHead emptyTail =>
          have split := induction emptyTail
          exact ⟨.absurd absurdHead split.1, split.2⟩

end IsEmpty

end Kind

end ManySortedFC.Classifier
