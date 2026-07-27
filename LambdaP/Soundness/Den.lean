import LambdaP.Soundness.Store

/-!
The semantic denotation of closed types over a heap.

`Den n T ℓ` reads "location ℓ inhabits T at approximation depth n". The
denotation is a *function* (well-founded recursion), so the mixed-variance
interval clauses are unproblematic — no positivity constraint, hence no
possible-types inductives and no sized judgments. Design (DESIGN.md,
inversion architecture):

- Shape clauses (`arrow`, and the lookup part of the pair clauses) are
  shallow: they expose the stored value plus syntactic typing/subtyping
  facts, which is all progress and preservation consume.
- `tsel q A` follows the stored alias of the member at `q`'s target.
- The interval views of a pair type are phrased against the selection
  `tsel ℓ A` *of the pair's own location* — a type of path-erased size 0,
  which is what lets the views recurse at full index while the alias hop
  consumes the index. The approximation index `n` bounds alias-hop depth;
  in a bounded heap hops descend store positions, so all lemmas hold at
  every `n` (the classical approximation discipline, confined to `Den`).

Measure: lexicographic (approximation depth, path-erased structural size).
-/

namespace LambdaP

/-- Path-erased structural size. Paths (hence singletons and selections)
count zero, so substitution preserves the size. -/
def Ty.structSize : Ty s -> Nat
| .top => 0
| .bot => 0
| .single _ => 0
| .tsel _ _ => 0
| .arrow S T => S.structSize + T.structSize + 1
| .pairTm S _ T => S.structSize + T.structSize + 1
| .pairTy S _ T1 T2 => S.structSize + T1.structSize + T2.structSize + 1

@[simp]
theorem Ty.structSize_subst {T : Ty s1} {σ : Subst s1 s2} :
    (T.subst σ).structSize = T.structSize := by
  induction T generalizing s2 <;> simp [Ty.subst, Ty.structSize, *]

@[simp]
theorem Ty.structSize_open {T : Ty (s+1)} {p : Path s} :
    (T.open p).structSize = T.structSize := by
  simp [Ty.open]

/-- The denotation of a closed type as a set of heap locations, at
approximation depth `n`. -/
def Den (Θ : Sto) (h : Heap) : Nat -> Ty 0 -> Nat -> Prop
| _, .top, _ => True
| _, .bot, _ => False
| _, .single q, ℓ => PathEval h q ℓ
| n, .tsel q A, ℓ =>
    ∃ m ℓ1 W, PathEval h q m ∧
      Heap.Lookup h m (.pairTy (.free ℓ1) A W) ∧
      ∀ j, j < n -> Den Θ h j W ℓ
| _, .arrow S T, ℓ =>
    ∃ T0 t T1, Heap.Lookup h ℓ (.abs T0 t) ∧
      Wf Θ .empty (.ty T0) ∧
      HasType Θ (Ctx.empty.push T0) t T1 ∧
      Sub Θ .empty (.ty S) (.ty T0) ∧
      Sub Θ (Ctx.empty.push S) (.ty T1) (.ty T)
| n, .pairTm S a T, ℓ =>
    ∃ ℓ1 ℓ2, Heap.Lookup h ℓ (.pairTm (.free ℓ1) a (.free ℓ2)) ∧
      Sub Θ .empty (.ty (.single (.var (.free ℓ1)))) (.ty S) ∧
      Den Θ h n S ℓ1 ∧
      ∀ (q : Path 0), PathEval h q ℓ1 -> Den Θ h n (T.open q) ℓ2
| n, .pairTy S A T1 T2, ℓ =>
    ∃ ℓ1 W, Heap.Lookup h ℓ (.pairTy (.free ℓ1) A W) ∧
      Sub Θ .empty (.ty (.single (.var (.free ℓ1)))) (.ty S) ∧
      Den Θ h n S ℓ1 ∧
      ∀ (q : Path 0), PathEval h q ℓ1 -> ∀ j, j ≤ n ->
        (∀ y, Den Θ h j (T1.open q) y -> Den Θ h j (.tsel (.var (.free ℓ)) A) y) ∧
        (∀ y, Den Θ h j (.tsel (.var (.free ℓ)) A) y -> Den Θ h j (T2.open q) y)
termination_by n T _ => (n, T.structSize)
decreasing_by
  all_goals simp_wf
  all_goals simp only [Ty.structSize]
  all_goals
    first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; omega)
    | (rcases Nat.lt_or_ge j n with hlt | hge
       · apply Prod.Lex.left; omega
       · have hEq : j = n := by omega
         subst hEq
         apply Prod.Lex.right
         omega)

end LambdaP
