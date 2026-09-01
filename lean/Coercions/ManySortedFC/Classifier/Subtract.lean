import Coercions.ManySortedFC.Classifier.Intersection

/-!
# Executable kind subtraction

For holed subtrees `A` and `B`, `A \ B` is split into two finite parts:
classifiers outside `B`'s root, and classifiers restored by one of `B`'s
exclusions.  Subtraction from a union then runs these single-subtree
subtractions from left to right.  `Semantics.lean` proves that this executable
operation denotes exact set difference.
-/

namespace ManySortedFC.Classifier

namespace Subtree

/-- The part of `source` restored by exclusions from `removed`. -/
def restore (source : Subtree) (removedRoot : ManySortedFC.Classifier) :
    List ManySortedFC.Classifier -> Kind
  | [] => Kind.empty
  | exclusion :: rest =>
      Kind.intersect
          (Kind.intersect [source] (Kind.classifier removedRoot))
          (Kind.classifier exclusion) ++
        restore source removedRoot rest

/-- Executable difference of two holed subtrees. -/
def subtract (source removed : Subtree) : Kind :=
  Kind.node source.root (removed.root :: source.exclusions) ++
    restore source removed.root removed.exclusions

end Subtree

namespace Kind

/-- Subtract one holed subtree from every component of a kind. -/
def subtractOne : Kind -> Subtree -> Kind
  | [], _ => empty
  | source :: rest, removed =>
      source.subtract removed ++ subtractOne rest removed

/-- Internal left-to-right fold over the right-hand components. -/
def subtractFrom : Kind -> Kind -> Kind
  | [], source => source
  | removed :: rest, source => subtractFrom rest (subtractOne source removed)

/-- Executable kind difference.  Right-hand components are removed in list
order, matching set difference by a finite union. -/
def subtract (source removed : Kind) : Kind :=
  subtractFrom removed source

@[simp] theorem subtract_empty_right (source : Kind) :
    subtract source empty = source := by
  rfl

private theorem subtractFrom_empty (removed : Kind) :
    subtractFrom removed empty = empty := by
  induction removed with
  | nil => rfl
  | cons _ _ induction => exact induction

@[simp] theorem subtract_empty_left (removed : Kind) :
    subtract empty removed = empty :=
  subtractFrom_empty removed

@[simp] theorem subtract_cons (source rest : Kind) (removed : Subtree) :
    subtract source (removed :: rest) =
      subtract (subtractOne source removed) rest := rfl

end Kind

end ManySortedFC.Classifier
