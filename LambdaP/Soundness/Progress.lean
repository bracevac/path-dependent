import LambdaP.Soundness.Embedding

/-! Syntactic progress: replaces the quarantined semantic version.
Ports the heap-transfer helpers from the superseded precise layer,
then value-or-step by induction on typing, consuming path progress
(Wf.chains), canonical forms, and store-to-heap resolution transfer. -/

namespace LambdaP

theorem HeapTyped.lookup_shape {Θ : Sto} {h : Heap} {ℓ : Nat} {T : Ty 0}
    (hh : HeapTyped Θ h) (hl : Sto.Lookup Θ ℓ T) :
    (∃ S B, T = .arrow S B) ∨
    (∃ ℓ1 a ℓ2, T = .pairTm (.single (.var (.free ℓ1))) a
      (Ty.single (.var (.free ℓ2))).weaken) ∨
    (∃ (ℓ1 : Nat) (A : Name) (W : Ty 0),
      T = .pairTy (.single (.var (.free ℓ1))) A W.weaken W.weaken) := by
  obtain ⟨-, v, -, -, hpre⟩ := hh.2 hl
  cases hpre with
  | abs _ _ => exact .inl ⟨_, _, rfl⟩
  | pair_tm _ _ => exact .inr (.inl ⟨_, _, _, rfl⟩)
  | pair_ty _ _ => exact .inr (.inr ⟨_, _, _, rfl⟩)

theorem HeapTyped.entry_value_tm {Θ : Sto} {h : Heap} {ℓ ℓ1 : Nat}
    {a : Name} {Tc : Ty 1}
    (hh : HeapTyped Θ h)
    (hl : Sto.Lookup Θ ℓ (.pairTm (.single (.var (.free ℓ1))) a Tc)) :
    ∃ ℓ2, Tc = (Ty.single (.var (.free ℓ2))).weaken ∧
      Heap.Lookup h ℓ (.pairTm (.free ℓ1) a (.free ℓ2)) := by
  obtain ⟨-, v, hvl, -, hpre⟩ := hh.2 hl
  cases hpre with
  | pair_tm hy hz => exact ⟨_, rfl, hvl⟩

theorem HeapTyped.entry_value_ty {Θ : Sto} {h : Heap} {ℓ ℓ1 : Nat}
    {A : Name} {T1 T2 : Ty 1}
    (hh : HeapTyped Θ h)
    (hl : Sto.Lookup Θ ℓ (.pairTy (.single (.var (.free ℓ1))) A T1 T2)) :
    ∃ W, T1 = W.weaken ∧ T2 = W.weaken ∧
      Heap.Lookup h ℓ (.pairTy (.free ℓ1) A W) := by
  obtain ⟨-, v, hvl, -, hpre⟩ := hh.2 hl
  cases hpre with
  | pair_ty hy hwf => exact ⟨_, rfl, rfl, hvl⟩

/-- Store-side resolution transfers to heap evaluation. -/
theorem Chains.pathEval {Θ : Sto} {h : Heap} {p : Path 0} {ℓ : Nat}
    (hh : HeapTyped Θ h) (hc : Chains Θ p ℓ) : PathEval h p ℓ := by
  induction hc with
  | loc _ => exact .var
  | fst_tm _ hl ih =>
    obtain ⟨ℓ2, -, hvl⟩ := hh.entry_value_tm hl
    exact .fst_tm ih hvl
  | fst_ty _ hl ih =>
    obtain ⟨W, -, -, hvl⟩ := hh.entry_value_ty hl
    exact .fst_ty ih hvl
  | sel hc hl ih =>
    rcases hh.lookup_shape hl with ⟨_, _, he⟩ | ⟨ℓ1', a', ℓ2', he⟩ | ⟨_, _, _, he⟩ <;>
      cases he
    obtain ⟨ℓ2'', heq, hvl⟩ := hh.entry_value_tm hl
    simp only [Ty.weaken, Ty.rename, Path.rename, Var.rename] at heq
    cases heq
    exact .sel ih hvl
  | sel_skip_tm hc hl hne hin ihc ihin =>
    rcases hh.lookup_shape hl with ⟨_, _, he⟩ | ⟨ℓ1', b', ℓ2', he⟩ | ⟨_, _, _, he⟩ <;>
      cases he
    obtain ⟨ℓ2'', heq, hvl⟩ := hh.entry_value_tm hl
    exact .sel_skip_tm ihc hvl hne ihin
  | sel_skip_ty hc hl hin ihc ihin =>
    rcases hh.lookup_shape hl with ⟨_, _, he⟩ | ⟨_, _, _, he⟩ | ⟨ℓ1', B', W', he⟩ <;>
      cases he
    obtain ⟨W'', heq1, heq2, hvl⟩ := hh.entry_value_ty hl
    exact .sel_skip_ty ihc hvl ihin

/-- Progress: a closed well-typed term is final or steps. -/
theorem progress {Θ : Sto} {h : Heap} :
    ∀ {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s},
      HasType Θ Γ t T -> Sto.ResidueCollapse Θ -> HeapTyped Θ h -> ∀ (hs : s = 0),
      Final (hs ▸ t) ∨ ∃ h' t', Step h (hs ▸ t) h' t' := by
  intro s Γ t T ht
  induction ht with
  | path hp =>
    intro hcol hh' hs
    subst hs
    have hE := Ctx.eq_empty' ‹Ctx 0›
    subst hE
    obtain ⟨ℓ, hc⟩ := (Path.Wf.chains hh'.shaped hcol hp) rfl
    rename_i p
    by_cases hpe : p = .var (.free ℓ)
    · subst hpe
      exact .inl .loc
    · exact .inr ⟨h, _, .path (hc.pathEval hh') hpe⟩
  | sub _ _ _ ih =>
    intro hcol hh' hs
    exact ih hcol hh' hs
  | abs _ _ _ =>
    intro hcol hh' hs
    subst hs
    exact .inl (.val .abs)
  | app hf ha _ _ =>
    intro hcol hh' hs
    subst hs
    have hE := Ctx.eq_empty' ‹Ctx 0›
    subst hE
    obtain ⟨hwp, hsubp⟩ := hf.path_inv rfl
    obtain ⟨hwq, hsubq⟩ := ha.path_inv rfl
    obtain ⟨ℓ0, S0, T0, t0, hcp, hlv, -, -, -, -⟩ :=
      Sub.canonical_arrow hh' hcol hsubp
    obtain ⟨ℓa, hca⟩ := (Path.Wf.chains hh'.shaped hcol hwq) rfl
    exact .inr ⟨h, _, .apply (hcp.pathEval hh') (hca.pathEval hh') hlv⟩
  | pair_tm _ _ =>
    intro hcol hh' hs
    subst hs
    exact .inl (.val .pairTm)
  | pair_ty _ _ =>
    intro hcol hh' hs
    subst hs
    exact .inl (.val .pairTy)
  | letin ht1 _ _ ih1 _ =>
    intro hcol hh' hs
    subst hs
    rcases ih1 hcol hh' rfl with hfin | ⟨h', t1', hstep⟩
    · cases hfin with
      | val hv => exact .inr ⟨_, _, .let_val hv⟩
      | loc => exact .inr ⟨h, _, .let_path .var⟩
    · exact .inr ⟨h', _, .let_ctx hstep⟩
  | typed _ _ _ =>
    intro hcol hh' hs
    subst hs
    exact .inr ⟨h, _, .ascribe⟩

end LambdaP
