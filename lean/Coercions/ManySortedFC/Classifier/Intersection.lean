import Coercions.ManySortedFC.Classifier.Kind

/-!
# Executable kind intersection

The intersection of two holed subtrees uses their deeper root and accumulates
both exclusion lists.  Disjoint roots have empty intersection.  Kind
intersection distributes this operation over the two finite unions.
-/

namespace ManySortedFC.Classifier

namespace Subtree

/-- Executable intersection of two holed subtrees. -/
def intersect (left right : Subtree) : Kind :=
  if left.root ≤ right.root then
    Kind.node left.root (left.exclusions ++ right.exclusions)
  else if right.root ≤ left.root then
    Kind.node right.root (left.exclusions ++ right.exclusions)
  else
    Kind.empty

end Subtree

namespace Kind

/-- Intersect one subtree with every component of a kind. -/
def intersectOne (left : Subtree) : Kind -> Kind
  | [] => empty
  | right :: rest => left.intersect right ++ intersectOne left rest

@[simp] theorem intersectOne_empty (left : Subtree) :
    intersectOne left empty = empty := rfl

/-- Executable intersection of two kinds. -/
def intersect : Kind -> Kind -> Kind
  | [], _ => empty
  | left :: rest, right => intersectOne left right ++ intersect rest right

@[simp] theorem intersect_empty_left (kind : Kind) :
    intersect empty kind = empty := rfl

@[simp] theorem intersect_empty_right (kind : Kind) :
    intersect kind empty = empty := by
  induction kind with
  | nil => rfl
  | cons _ _ induction =>
      rw [intersect, intersectOne_empty, induction]
      rfl

@[simp] theorem intersect_cons_left (left : Subtree) (rest right : Kind) :
    intersect (left :: rest) right =
      intersectOne left right ++ intersect rest right := rfl

@[simp] theorem intersectOne_cons (left right : Subtree) (rest : Kind) :
    intersectOne left (right :: rest) =
      left.intersect right ++ intersectOne left rest := rfl

end Kind

end ManySortedFC.Classifier
