import LambdaP.Soundness.PathLemmas

/-!
Support lemmas for the denotation: antitonicity in the approximation
depth, and the precise-store lemma — every heap location inhabits the
denotation of its recorded precise type at every depth. The latter is
the seed of the closure argument (the `var_free` case) and the empirical
check that `Den`'s clause shapes are right for alias-only stores.
-/

namespace LambdaP

/-- Membership at every approximation depth (the limit denotation). -/
def DenAll (Θ : Sto) (h : Heap) (T : Ty 0) (ℓ : Nat) : Prop :=
  ∀ n, Den Θ h n T ℓ

private theorem Den.antitone_aux {Θ : Sto} {h : Heap} :
    ∀ (sz : Nat) (T : Ty 0), T.structSize < sz ->
    ∀ {m n ℓ : Nat}, m ≤ n -> Den Θ h n T ℓ -> Den Θ h m T ℓ := by
  intro sz
  induction sz with
  | zero =>
    intro T hsz
    exact absurd hsz (Nat.not_lt_zero _)
  | succ sz ih =>
    intro T hsz m n ℓ hmn hd
    cases T with
    | top => simp [Den]
    | bot => simp [Den] at hd
    | single q =>
      simp only [Den] at hd ⊢
      exact hd
    | arrow S T =>
      simp only [Den] at hd ⊢
      exact hd
    | tsel q A =>
      simp only [Den] at hd ⊢
      obtain ⟨m', ℓ1, W, hev, hlk, hW⟩ := hd
      exact ⟨m', ℓ1, W, hev, hlk, fun j hj => hW j (Nat.lt_of_lt_of_le hj hmn)⟩
    | pairTm S a T =>
      simp only [Den] at hd ⊢
      obtain ⟨ℓ1, ℓ2, hlk, hsub, hS, hOp⟩ := hd
      refine ⟨ℓ1, ℓ2, hlk, hsub, ?_, ?_⟩
      · exact ih S (by simp only [Ty.structSize] at hsz; omega) hmn hS
      · intro q hq
        refine ih (T.open q) ?_ hmn (hOp q hq)
        simp only [Ty.structSize_open]
        simp only [Ty.structSize] at hsz
        omega
    | pairTy S A T1 T2 =>
      simp only [Den] at hd ⊢
      obtain ⟨ℓ1, W, hlk, hsub, hS, hViews⟩ := hd
      refine ⟨ℓ1, W, hlk, hsub, ?_, ?_⟩
      · exact ih S (by simp only [Ty.structSize] at hsz; omega) hmn hS
      · intro q hq j hj
        exact hViews q hq j (Nat.le_trans hj hmn)

/-- `Den` is antitone in the approximation depth. -/
theorem Den.antitone {Θ : Sto} {h : Heap} {T : Ty 0} {m n ℓ : Nat}
    (hmn : m ≤ n) (hd : Den Θ h n T ℓ) : Den Θ h m T ℓ :=
  Den.antitone_aux (T.structSize + 1) T (Nat.lt_succ_self _) hmn hd

/-- Every store location inhabits the denotation of its precise type, at
every depth. The pair-type case is where the alias-only discipline pays:
both interval views are identities up to antitonicity. -/
theorem HeapTyped.den_precise {Θ : Sto} {h : Heap} (hh : HeapTyped Θ h)
    {ℓ : Nat} {T : Ty 0} (hT : Sto.Lookup Θ ℓ T) :
    DenAll Θ h T ℓ := by
  intro n
  obtain ⟨-, v, hv, -, hpre⟩ := hh.2 hT
  cases hpre with
  | abs hwf hty =>
    simp only [Den]
    exact ⟨_, _, _, hv, hwf, hty, .refl, .refl⟩
  | pair_tm h1 h2 =>
    simp only [Den]
    refine ⟨_, _, hv, .refl, ?_, ?_⟩
    · exact .var
    · intro q hq
      rw [Ty.weaken_open]
      simp only [Den]
      exact .var
  | pair_ty h1 hwf =>
    simp only [Den]
    refine ⟨_, _, hv, .refl, ?_, ?_⟩
    · exact .var
    · intro q hq j hj
      constructor
      · intro y hy
        rw [Ty.weaken_open] at hy
        exact ⟨ℓ, _, _, .var, hv, fun i hij => Den.antitone (Nat.le_of_lt hij) hy⟩
      · intro y hy i hij
        rw [Ty.weaken_open]
        obtain ⟨m', ℓ1', W', hev, hlk, hW⟩ := hy
        cases hev
        have heq := Option.some.inj (hlk.symm.trans hv)
        injection heq with hs hy1 hA hWeq
        subst hWeq
        exact hW i hij

end LambdaP
