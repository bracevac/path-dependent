import Coercions.Classifiers.Cls.Kind

namespace Classifiers

/-!
# Kind subtraction, subkinding and kind disjointness

The three derived operations of Figure 5 of System Capless(K)
(`CaplessK/Classifier/Subtract.lean:923,958`, `Subkind.lean:19-23`,
`Disjoint.lean:23-34`), as total functions, and the one fact about them that
the development consumes.

Subtraction is the executable algorithm of `Subtree.subtract` and
`Kind.subtract`.  `Kind.subtract` there is a well-founded recursion on the
pair of list lengths whose clauses subtract the head subtree of the right kind
and then recurse, so it is the left fold of one-subtree subtraction over the
right kind, and that is how it is written here.  The fold is structural, so
`by decide` reduces it in the kernel, which a well-founded recursion would
not.

The semantic content is one lemma, `Kind.contains_subtract_of`, the sound
direction of the subtraction bridge, and its consumer `Kind.Subkind.contains`.
The converse is not proved here.  See the note before the examples.

The file closes with the example classifiers of the plan and their `decide`
facts, which is the acceptance of the classifier data.
-/

namespace Cls

namespace Classifier

/-- The strict subclass test.  Capless(K) writes it `<`, the strict order of
the `PartialOrder` instance on classifiers (`Classifier/Core.lean:100-109`),
and the subtraction algorithm is stated with it. -/
def ltB (a b : Classifier) : Bool := leB a b && !leB b a

end Classifier

namespace Kind

/-- Subtree subtraction, recursing on the exclusions of the subtrahend
(`Classifier/Subtract.lean:923`).  The branches are the rules of Figure 5,
decided by the subclass-or-disjoint trichotomy. -/
def subtractAux (r1 : Classifier) (E1 : List Classifier) (r2 : Classifier) :
    List Classifier → Kind
  | [] => [Subtree.mk r1 (r2 :: E1)]
  | a :: E =>
      if Classifier.ltB r2 a then [Subtree.mk r1 E1]
      else if Classifier.disjointB r2 a then subtractAux r1 E1 r2 E
      else if Classifier.leB a r1 then Subtree.mk a E1 :: subtractAux r1 E1 r2 E
      else if Classifier.ltB r1 a then [Subtree.mk r1 E1]
      else subtractAux r1 E1 r2 E

end Kind

/-- Subtraction of two holed subtrees (`Classifier/Subtract.lean:923`). -/
def Subtree.subtractB (t u : Subtree) : Kind :=
  Kind.subtractAux t.root t.excls u.root u.excls

namespace Kind

/-- A kind minus one holed subtree: subtract that subtree from every subtree
of the kind (`Classifier/Subtract.lean:958`, the singleton clause). -/
def subtract1 (K : Kind) (u : Subtree) : Kind := K.flatMap (fun t => t.subtractB u)

/-- Kind subtraction: subtract the subtrees of `L` from `K`, left to right
(`Classifier/Subtract.lean:958`). -/
def subtractB (K L : Kind) : Kind := L.foldl subtract1 K

/-- Subkinding is empty subtraction (`Classifier/Subkind.lean:19-23`). -/
def subkindB (K L : Kind) : Bool := isEmptyB (subtractB K L)

/-- Kind disjointness is empty intersection (`Classifier/Disjoint.lean:23-34`). -/
def disjointB (K L : Kind) : Bool := isEmptyB (interB K L)

/-- Subkinding as a proposition. -/
abbrev Subkind (K L : Kind) : Prop := K.subkindB L = true

/-- Kind disjointness as a proposition. -/
abbrev Disjoint (K L : Kind) : Prop := K.disjointB L = true

/-! ## The subtraction bridge, the sound direction -/

/-- The subtree step of `contains_subtract_of`.  A classifier inside
`⟨r1, E1⟩` and outside `⟨r2, E2⟩` survives every branch of the algorithm. -/
theorem contains_subtractAux_of {r1 r2 c : Classifier} {E1 : List Classifier}
    (hr1 : Classifier.leB c r1 = true)
    (hE1 : E1.all (fun e => !Classifier.leB c e) = true) :
    ∀ E2 : List Classifier, (Subtree.mk r2 E2).containsB c = false →
      (subtractAux r1 E1 r2 E2).containsB c = true := by
  intro E2
  induction E2 with
  | nil =>
      intro h2
      simp only [Subtree.containsB, List.all_nil, Bool.and_true] at h2
      simp [subtractAux, containsB_cons, Subtree.containsB, hr1, hE1, h2]
  | cons a E ih =>
      intro h2
      -- the subtree of `r1` with its own exclusions still holds `c`
      have htriv : containsB [Subtree.mk r1 E1] c = true := by
        simp [containsB_cons, Subtree.containsB, hr1, hE1]
      -- dropping an exclusion that `c` is not below keeps `c` outside
      have hstep : Classifier.leB c a = false → (Subtree.mk r2 E).containsB c = false := by
        intro ha
        have he : (Subtree.mk r2 (a :: E)).containsB c = (Subtree.mk r2 E).containsB c := by
          simp [Subtree.containsB, ha]
        rw [← he]
        exact h2
      cases hA : Classifier.ltB r2 a with
      | true =>
          have eqA : subtractAux r1 E1 r2 (a :: E) = [Subtree.mk r1 E1] := by
            simp [subtractAux, hA]
          rw [eqA]
          exact htriv
      | false =>
        cases hB : Classifier.disjointB r2 a with
        | true =>
            have eqB : subtractAux r1 E1 r2 (a :: E) = subtractAux r1 E1 r2 E := by
              simp [subtractAux, hA, hB]
            rw [eqB]
            refine ih ?_
            -- `c` cannot lie below both `r2` and `a`, which are disjoint
            cases hc : Classifier.leB c a with
            | false => exact hstep hc
            | true =>
                cases hr2 : Classifier.leB c r2 with
                | false => simp [Subtree.containsB, hr2]
                | true =>
                    have hnd := Classifier.not_disjoint_of_le hr2 hc
                    rw [hB] at hnd
                    exact Bool.noConfusion hnd
        | false =>
          cases hC : Classifier.leB a r1 with
          | true =>
              have eqC : subtractAux r1 E1 r2 (a :: E)
                  = Subtree.mk a E1 :: subtractAux r1 E1 r2 E := by
                simp [subtractAux, hA, hB, hC]
              rw [eqC, containsB_cons]
              cases hc : Classifier.leB c a with
              | true =>
                  have hin : (Subtree.mk a E1).containsB c = true := by
                    simp [Subtree.containsB, hc, hE1]
                  rw [hin]
                  rfl
              | false =>
                  rw [ih (hstep hc), Bool.or_true]
          | false =>
            cases hD : Classifier.ltB r1 a with
            | true =>
                have eqD : subtractAux r1 E1 r2 (a :: E) = [Subtree.mk r1 E1] := by
                  simp [subtractAux, hA, hB, hC, hD]
                rw [eqD]
                exact htriv
            | false =>
                have eqE : subtractAux r1 E1 r2 (a :: E) = subtractAux r1 E1 r2 E := by
                  simp [subtractAux, hA, hB, hC, hD]
                rw [eqE]
                refine ih (hstep ?_)
                -- `c` lies below `r1`, so `c` below `a` would make `a` and `r1`
                -- comparable, and this branch refutes both comparabilities
                cases hc : Classifier.leB c a with
                | false => rfl
                | true =>
                    rcases Classifier.chain hc hr1 with h | h
                    · rw [h] at hC
                      exact Bool.noConfusion hC
                    · have hlt : Classifier.ltB r1 a = true := by
                        simp [Classifier.ltB, h, hC]
                      rw [hlt] at hD
                      exact Bool.noConfusion hD

/-- A classifier inside `t` and outside `u` is inside `t` minus `u`. -/
theorem contains_subtractB_subtree {t u : Subtree} {c : Classifier}
    (ht : t.containsB c = true) (hu : u.containsB c = false) :
    (t.subtractB u).containsB c = true := by
  obtain ⟨r1, E1⟩ := t
  obtain ⟨r2, E2⟩ := u
  simp only [Subtree.containsB, Bool.and_eq_true] at ht
  exact contains_subtractAux_of ht.1 ht.2 E2 hu

/-- Subtracting one subtree splits over the head of the kind. -/
theorem subtract1_cons (t : Subtree) (K : Kind) (u : Subtree) :
    subtract1 (t :: K) u = t.subtractB u ++ subtract1 K u := by
  simp [subtract1, List.flatMap_cons]

/-- A classifier inside `K` and outside `u` is inside `K` minus `u`. -/
theorem contains_subtract1_of : ∀ (K : Kind) (u : Subtree) (c : Classifier),
    K.containsB c = true → u.containsB c = false → (subtract1 K u).containsB c = true := by
  intro K
  induction K with
  | nil =>
      intro u c hK _
      rw [containsB_nil] at hK
      exact Bool.noConfusion hK
  | cons t K ih =>
      intro u c hK hu
      rw [containsB_cons] at hK
      rw [subtract1_cons, containsB_append]
      cases ht : t.containsB c with
      | true =>
          rw [contains_subtractB_subtree ht hu]
          rfl
      | false =>
          rw [ht, Bool.false_or] at hK
          rw [ih u c hK hu, Bool.or_true]

private theorem contains_subtract_go : ∀ (L K : Kind) (c : Classifier),
    K.containsB c = true → L.containsB c = false → (K.subtractB L).containsB c = true := by
  intro L
  induction L with
  | nil => intro K c hK _; exact hK
  | cons u L ih =>
      intro K c hK hL
      rw [containsB_cons] at hL
      have hu : u.containsB c = false := by
        cases h : u.containsB c with
        | false => rfl
        | true =>
            rw [h, Bool.true_or] at hL
            exact Bool.noConfusion hL
      have hL' : containsB L c = false := by
        rw [hu, Bool.false_or] at hL
        exact hL
      exact ih _ c (contains_subtract1_of K u c hK hu) hL'

/-- The subtraction bridge, the sound direction
(`Classifier/Semantics.lean:318,355`, one direction).  A classifier that `K`
holds and `L` does not is held by `K` minus `L`. -/
theorem contains_subtract_of {K L : Kind} {c : Classifier}
    (hK : K.containsB c = true) (hL : L.containsB c = false) :
    (K.subtractB L).containsB c = true :=
  contains_subtract_go L K c hK hL

/-- The only fact the development consumes about subkinding: a subkind's
classifiers are the superkind's. -/
theorem Subkind.contains {K L : Kind} (h : K.Subkind L) {c : Classifier}
    (hc : K.Contains c) : L.Contains c := by
  by_cases hL : L.containsB c = true
  · exact hL
  · simp only [Bool.not_eq_true] at hL
    have h0 : (K.subtractB L).containsB c = false := isEmpty_contains h c
    rw [contains_subtract_of hc hL] at h0
    exact Bool.noConfusion h0

end Kind

/-! ## The converse, and what it would cost

`Kind.Subkind.refl` and `Kind.Subkind.trans` are not proved here, and neither
is the converse of `Kind.contains_subtract_of`.  The converse says that a
classifier the difference holds is held by `K` and not by `L`, and together
with the right-to-left direction of `Kind.isEmpty_iff`
(`Classifier/Semantics.lean:194-209`) it turns containment back into
subkinding, which is what reflexivity and transitivity follow from in
Capless(K) (`Subkind.lean:37-46`, through `Subkind.semantics`).  That
direction of `isEmpty_iff` builds a classifier no exclusion of the kind covers
out of the child indices the exclusion lists use, and the converse of the
bridge is the bulk of `Classifier/Subtract.lean`, 991 lines with 17 `aesop`
calls.  This tree allows neither `aesop` nor Mathlib, so the port is a
development of its own, and K0 does not need it: `Subkind.contains` is the
sound direction and it is the only fact the stage consumes.  This is decision
6 of plan V-C.

The fallback for `refl` and `trans`, if a later stage wants them, is a direct
induction on the shape of `subtractB`.  The cost of not having the converse is
that the kinding checker of K1 is stated sound and not stated complete. -/

/-! ## The example classifiers

`exceptions.tex:91` of the write-up: `Control` is a subclass of `ThreadLocal`.
`IO` is disjoint from both.  These are the classifiers the K0.9 and K3
examples use, and the `decide` facts below are the acceptance of the data. -/

/-- The thread-local classifier. -/
def ThreadLocal : Classifier := .child 1 .top

/-- The control classifier, a subclass of `ThreadLocal` (`exceptions.tex:91`). -/
def Control : Classifier := .child 0 ThreadLocal

/-- An input-output classifier, disjoint from `ThreadLocal` and from `Control`. -/
def IO : Classifier := .child 0 .top

/-- `only c`: the kind of `c` and its subclasses. -/
def only (c : Classifier) : Kind := Kind.classifier c

/-- `except c`: the kind of every classifier outside the subtree of `c`. -/
def except (c : Classifier) : Kind := Kind.node .top [c]

/-! ### The `decide` facts

Every proposition here is an equation between `Bool`s or an `abbrev` on top of
one, so `Decidable` is synthesised and the kernel evaluates it. -/

-- `Control` lies below `ThreadLocal`, and not the other way round.
example : Classifier.leB Control ThreadLocal = true := by decide
example : Classifier.leB ThreadLocal Control = false := by decide
example : Classifier.Le Control ThreadLocal := by decide

-- `IO` is disjoint from both.
example : Classifier.disjointB IO ThreadLocal = true := by decide
example : Classifier.disjointB IO Control = true := by decide

-- `Kind.top` holds every classifier, `⊤` included.
example : Kind.top.containsB .top = true := by decide
example : Kind.top.containsB Control = true := by decide

-- Membership, the K1x shape: `only Control` admits `Control` and nothing else here.
example : Kind.containsB (only Control) Control = true := by decide
example : Kind.containsB (only Control) IO = false := by decide
example : Kind.containsB (only Control) .top = false := by decide
example : Kind.containsB (only ThreadLocal) Control = true := by decide

-- Membership, the K2x shape: `except ThreadLocal` excludes `Control`, because
-- `Control` lies below `ThreadLocal`, and it still admits `⊤`.
example : Kind.containsB (except ThreadLocal) Control = false := by decide
example : Kind.containsB (except ThreadLocal) ThreadLocal = false := by decide
example : Kind.containsB (except ThreadLocal) IO = true := by decide
example : Kind.containsB (except ThreadLocal) .top = true := by decide

-- The emptiness of `Control` intersected with the complement of `ThreadLocal`.
example : Kind.isEmptyB ((only Control).interB (except ThreadLocal)) = true := by decide
example : Kind.Disjoint (only Control) (except ThreadLocal) := by decide

-- Subkinding, decided by the subtraction algorithm.
example : Kind.subkindB (only Control) (only ThreadLocal) = true := by decide
example : Kind.subkindB (only ThreadLocal) (only Control) = false := by decide
example : Kind.Subkind Kind.top Kind.top := by decide
example : Kind.subkindB (only Control) (except ThreadLocal) = false := by decide
-- Decision 2: a root is kinded only at a kind that admits every classifier,
-- and `Kind.top` is not a subkind of an `except` kind.
example : Kind.subkindB Kind.top (except ThreadLocal) = false := by decide

-- Union is list append, and membership reads it as a union.
example : Kind.containsB ((only Control) ∪ (only IO)) IO = true := by decide

end Cls
end Classifiers
