import LambdaP.Soundness.DenLemmas

/-!
Data for the closure lemma (soundness of subtyping for the denotation).

`View` is the limit-level semantic content of a pair-type membership: the
stored member together with interval views stated against the all-depth
denotation. `DenAll.pairTy_view` extracts a `View` from a pair-type
membership — the approximation shifts of `Den`'s per-depth views vanish
in the limit. `SemSubst` packages a closing substitution that is both
syntactically conforming and semantically realized.
-/

namespace LambdaP

/-- The limit-level view of a pair-type membership at location `ℓ`:
the stored member `(ℓ1, W)` with interval views against the (opened)
bounds, all at the limit denotation. -/
def View (Θ : Sto) (h : Heap) (ℓ : Nat) (S : Ty 0) (A : Name)
    (T1 T2 : Ty 1) : Prop :=
  ∃ ℓ1 W,
    Heap.Lookup h ℓ (.pairTy (.free ℓ1) A W) ∧
    Sub Θ .empty (.ty (.single (.var (.free ℓ1)))) (.ty S) ∧
    DenAll Θ h S ℓ1 ∧
    (∀ (q : Path 0), PathEval h q ℓ1 ->
      ∀ y, DenAll Θ h (T1.open q) y -> DenAll Θ h W y) ∧
    (∀ (q : Path 0), PathEval h q ℓ1 ->
      ∀ y, DenAll Θ h W y -> DenAll Θ h (T2.open q) y)

/-- Extracting the limit view from a pair-type membership: the per-depth
approximation shifts in `Den`'s clause vanish at the limit. -/
theorem DenAll.pairTy_view {Θ : Sto} {h : Heap} {ℓ : Nat}
    {S : Ty 0} {A : Name} {T1 T2 : Ty 1}
    (hd : DenAll Θ h (.pairTy S A T1 T2) ℓ) :
    View Θ h ℓ S A T1 T2 := by
  have h0 := hd 0
  simp only [Den] at h0
  obtain ⟨ℓ1, W, hlk, hsub, -, -⟩ := h0
  refine ⟨ℓ1, W, hlk, hsub, ?_, ?_, ?_⟩
  · -- first component, at every depth
    intro n
    have hn := hd n
    simp only [Den] at hn
    obtain ⟨ℓ1', W', hlk', -, hS, -⟩ := hn
    have heq := Option.some.inj (hlk'.symm.trans hlk)
    injection heq with _ hy _ hW
    injection hy with hy
    subst hy
    exact hS
  · -- lower view at the limit
    intro q hq y hy i
    have hn := hd (i + 1)
    simp only [Den] at hn
    obtain ⟨ℓ1', W', hlk', -, -, hViews⟩ := hn
    have heq := Option.some.inj (hlk'.symm.trans hlk)
    injection heq with _ hy1 _ hW
    injection hy1 with hy1
    subst hy1; subst hW
    have hlow := (hViews q hq (i + 1) (Nat.le_refl _)).1 y (hy (i + 1))
    obtain ⟨m', ℓ1'', W'', hev, hlk'', hcontent⟩ := hlow
    cases hev
    have heq2 := Option.some.inj (hlk''.symm.trans hlk)
    injection heq2 with _ _ _ hW2
    subst hW2
    exact hcontent i (Nat.lt_succ_self _)
  · -- upper view at the limit
    intro q hq y hy i
    have hn := hd (i + 1)
    simp only [Den] at hn
    obtain ⟨ℓ1', W', hlk', -, -, hViews⟩ := hn
    have heq := Option.some.inj (hlk'.symm.trans hlk)
    injection heq with _ hy1 _ hW
    injection hy1 with hy1
    subst hy1; subst hW
    refine (hViews q hq (i + 1) (Nat.le_refl _)).2 y ?_ i (Nat.lt_succ_self _)
    exact ⟨ℓ, _, _, .var, hlk, fun j _ => hy j⟩

/-- A closing substitution that is syntactically conforming and whose
images evaluate into the limit denotations of their declared types. -/
structure SemSubst (Θ : Sto) (h : Heap) (σ : Subst s 0) (Γ : Ctx s) : Prop where
  conforms : SubstTyping Θ σ Γ .empty
  realized : ∀ {x : BVar s} {T : Ty s}, Ctx.LookupVar Γ x T ->
    ∃ m, PathEval h (σ.var x) m ∧ DenAll Θ h (T.subst σ) m

end LambdaP
