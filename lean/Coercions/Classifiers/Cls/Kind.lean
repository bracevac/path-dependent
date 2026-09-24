import Coercions.Classifiers.Cls.Core

namespace Classifiers

/-!
# Classifier kinds

Kinds of System Capless(K) (`CaplessK/Classifier/Kind.lean`, Figure 5), as
data.  A kind denotes a set of classifiers.  It is a list of holed subtrees: a
root classifier minus a list of excluded subtrees.  Union is list append, the
empty list is the empty kind, and `Kind.top` is the kind of every classifier.

Every operation is a total `Bool` or `Kind` valued function with an `abbrev`
proposition on top, in the style of `Ctx.isRootB` and `Ctx.IsRoot`
(`FCdot/Context.lean:204,227`), so that `Decidable` is synthesised and
`by decide` closes an example in the kernel.  Capless(K) states the same
operations as inductive judgments beside their executable versions and proves
the two agree.  Only the functions are copied here, and the semantic content
is the bridge lemmas at the end of the file: membership in `top`, in a union,
in an intersection, and in an empty kind.
-/

namespace Cls

/-- A subtree of a single root minus a list of excluded subtrees
(`Classifier/Kind.lean:28-31`). -/
structure Subtree : Type where
  root : Classifier
  excls : List Classifier
deriving DecidableEq, Repr

/-- A kind: a list of holed subtrees, read as the union of their denotations
(`Classifier/Kind.lean:34`). -/
abbrev Kind : Type := List Subtree

namespace Kind

/-- Kind union is list append (`Classifier/Kind.lean:38-39`). -/
instance instUnionKind : Union Kind := ⟨List.append⟩

@[simp] theorem union_eq (K L : Kind) : K ∪ L = K ++ L := rfl

/-- A single holed subtree (`Classifier/Kind.lean:48`). -/
def node (c : Classifier) (excls : List Classifier) : Kind := [Subtree.mk c excls]

/-- The kind of one classifier and its subclasses (`Classifier/Kind.lean:51`). -/
def classifier (c : Classifier) : Kind := node c []

/-- The empty kind (`Classifier/Kind.lean:55`).  A non-empty list can still
denote the empty set, which is what `isEmptyB` decides. -/
def empty : Kind := []

/-- The kind of every classifier (`Classifier/Kind.lean:58`). -/
def top : Kind := classifier .top

/-- Does `xs` hold a superclass of `c`?  (`ContainsSupOf`,
`Classifier/Kind.lean:62-65`, as a function.) -/
def containsSupOfB (xs : List Classifier) (c : Classifier) : Bool :=
  xs.any (fun e => Classifier.leB c e)

end Kind

/-- Membership of a classifier in a holed subtree: below the root and below no
exclusion (`Classifier/Semantics.lean:29-33`, as a function). -/
def Subtree.containsB (t : Subtree) (c : Classifier) : Bool :=
  Classifier.leB c t.root && t.excls.all (fun e => !Classifier.leB c e)

/-- The intersection of two holed subtrees: the deeper root, both exclusion
lists, and nothing when the roots are disjoint
(`Classifier/Intersection.lean:42`). -/
def Subtree.interB (t u : Subtree) : Kind :=
  if Classifier.leB t.root u.root then Kind.node t.root (t.excls ++ u.excls)
  else if Classifier.leB u.root t.root then Kind.node u.root (t.excls ++ u.excls)
  else Kind.empty

namespace Kind

/-- Membership of a classifier in a kind: membership in one of its subtrees
(`Classifier/Semantics.lean:29-33,101`, as a function). -/
def containsB (K : Kind) (c : Classifier) : Bool := K.any (fun t => t.containsB c)

/-- Emptiness of a kind: every subtree is excluded by one of its own
exclusions (`Classifier/Kind.lean:115-119`, as a function). -/
def isEmptyB : Kind → Bool
  | [] => true
  | Subtree.mk r exs :: K => containsSupOfB exs r && isEmptyB K

/-- Intersection of two kinds: the union of all pairwise subtree
intersections (`Classifier/Intersection.lean:64`). -/
def interB (K L : Kind) : Kind := K.flatMap (fun t => L.flatMap (fun u => t.interB u))

/-- Membership as a proposition. -/
abbrev Contains (K : Kind) (c : Classifier) : Prop := K.containsB c = true

/-- Emptiness as a proposition. -/
abbrev IsEmpty (K : Kind) : Prop := K.isEmptyB = true

/-! ## Membership, clause by clause -/

@[simp] theorem containsB_nil (c : Classifier) : containsB [] c = false := rfl

@[simp] theorem containsB_cons (t : Subtree) (K : Kind) (c : Classifier) :
    containsB (t :: K) c = (t.containsB c || containsB K c) := rfl

theorem containsB_node (r : Classifier) (exs : List Classifier) (c : Classifier) :
    containsB (node r exs) c
      = (Classifier.leB c r && exs.all (fun e => !Classifier.leB c e)) := by
  simp [node, Subtree.containsB]

theorem containsB_append (K L : Kind) (c : Classifier) :
    containsB (K ++ L) c = (containsB K c || containsB L c) := by
  simp [containsB, List.any_append]

theorem containsB_flatMap (K : Kind) (f : Subtree → Kind) (c : Classifier) :
    containsB (K.flatMap f) c = K.any (fun t => containsB (f t) c) := by
  induction K with
  | nil => rfl
  | cons t K ih =>
      rw [List.flatMap_cons, containsB_append, ih, List.any_cons]

/-! ## The bridge lemmas

The whole semantic content of the classifier data, and no more.  `containsB`
is the denotation, and each lemma reads one operation through it. -/

/-- `top` contains every classifier. -/
theorem contains_top (c : Classifier) : top.containsB c = true := by
  simp [top, classifier, containsB_node, Classifier.leB_top]

/-- Membership in a union is membership in one side
(`Classifier/Semantics.lean:134,140,149`). -/
theorem contains_append (K L : Kind) (c : Classifier) :
    (K ∪ L).containsB c = (K.containsB c || L.containsB c) := by
  rw [union_eq, containsB_append]

/-- Membership in the intersection of two holed subtrees. -/
theorem contains_interB_subtree (t u : Subtree) (c : Classifier) :
    containsB (t.interB u) c = (t.containsB c && u.containsB c) := by
  unfold Subtree.interB
  split
  · rename_i h
    rw [containsB_node]
    cases hc : Classifier.leB c t.root with
    | false => simp [Subtree.containsB, hc]
    | true =>
        have hu : Classifier.leB c u.root = true := Classifier.leB_trans hc h
        simp [Subtree.containsB, hc, hu, List.all_append]
  · split
    · rename_i h1 h2
      rw [containsB_node]
      cases hc : Classifier.leB c u.root with
      | false => simp [Subtree.containsB, hc]
      | true =>
          have ht : Classifier.leB c t.root = true := Classifier.leB_trans hc h2
          simp [Subtree.containsB, hc, ht, List.all_append]
    · rename_i h1 h2
      cases hc1 : Classifier.leB c t.root with
      | false => simp [empty, Subtree.containsB, hc1]
      | true =>
          cases hc2 : Classifier.leB c u.root with
          | false => simp [empty, Subtree.containsB, hc2]
          | true =>
              rcases Classifier.chain hc1 hc2 with h | h
              · exact absurd h h1
              · exact absurd h h2

/-- Membership in an intersection is membership in both sides
(`Classifier/Semantics.lean:431,451`). -/
theorem contains_inter (K L : Kind) (c : Classifier) :
    (K.interB L).containsB c = (K.containsB c && L.containsB c) := by
  have hL : ∀ t : Subtree, containsB (L.flatMap (fun u => t.interB u)) c
      = (t.containsB c && containsB L c) := by
    intro t
    rw [containsB_flatMap]
    induction L with
    | nil => simp
    | cons u L ihL =>
        rw [List.any_cons, contains_interB_subtree, ihL, containsB_cons]
        cases t.containsB c <;> simp
  rw [interB, containsB_flatMap]
  induction K with
  | nil => simp
  | cons t K ih =>
      rw [List.any_cons, hL t, ih, containsB_cons]
      cases containsB L c <;> simp

/-- A holed subtree excluded by one of its own exclusions contains nothing. -/
theorem subtree_contains_of_absurd {t : Subtree} (h : containsSupOfB t.excls t.root = true)
    (c : Classifier) : t.containsB c = false := by
  rcases List.any_eq_true.mp h with ⟨e, he, hle⟩
  cases hc : Classifier.leB c t.root with
  | false => simp [Subtree.containsB, hc]
  | true =>
      simp only [Subtree.containsB, hc, Bool.true_and]
      refine Bool.eq_false_iff.mpr (fun hall => ?_)
      have hne := List.all_eq_true.mp hall e he
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hne
      rw [Classifier.leB_trans hc hle] at hne
      exact Bool.noConfusion hne

/-- An empty kind contains no classifier (`Classifier/Semantics.lean:209`, the
direction the development consumes). -/
theorem isEmpty_contains {K : Kind} (h : K.IsEmpty) (c : Classifier) : K.containsB c = false := by
  induction K with
  | nil => rfl
  | cons t K ih =>
      obtain ⟨r, exs⟩ := t
      simp only [IsEmpty, isEmptyB, Bool.and_eq_true] at h
      rw [containsB_cons, subtree_contains_of_absurd h.1 c, ih h.2]
      rfl

end Kind

end Cls
end Classifiers
