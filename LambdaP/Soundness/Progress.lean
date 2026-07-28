import LambdaP.Soundness.Closure

/-!
Canonical forms and progress, harvested from the closure lemma at the
empty context: a well-typed closed term is final or steps.
-/

namespace LambdaP

/-- The empty scope has a unique context. -/
theorem Ctx.eq_empty (Γ : Ctx 0) : Γ = .empty := by
  cases Γ
  rfl

/-- The identity substitution realizes the empty context. -/
theorem SemSubst.empty {Θ : Sto} {Ξ : SemSto} {h : Heap} :
    SemSubst Θ Ξ h Subst.id .empty := by
  constructor
  · constructor
    · intro x T hx
      exact absurd hx (fun hx => nomatch hx)
    · intro x
      exact nomatch x
  · intro x T hx
    exact nomatch hx

/-- Closure at the empty context, with the identity substitution erased. -/
theorem Sub.den_empty {Θ : Sto} {Ξ : SemSto} {h : Heap} {U1 U2 : Ty 0}
    (hs : Sub Θ .empty (.ty U1) (.ty U2))
    (hh : HeapTyped Θ h) (hok : SemStoOk Θ Ξ h) :
    ∀ n ℓ, Den Θ Ξ h n U1 ℓ -> Den Θ Ξ h n U2 ℓ := by
  have := hs.den hh hok SemSubst.empty
  rwa [Tau.subst_id, Tau.subst_id] at this

/-- Wellformed closed paths evaluate. -/
theorem Path.Wf.eval_empty {Θ : Sto} {Ξ : SemSto} {h : Heap} {p : Path 0}
    (hw : Path.Wf Θ .empty p)
    (hh : HeapTyped Θ h) (hok : SemStoOk Θ Ξ h) :
    ∃ m, PathEval h p m := by
  have := hw.den_eval hh hok (SemSubst.empty (Ξ := Ξ))
  rwa [Path.subst_id] at this

/-- Canonical forms at arrow type: a path typed at a function type
evaluates to a stored λ with a compatible signature. -/
theorem canonical_arrow {Θ : Sto} {Ξ : SemSto} {h : Heap} {p : Path 0}
    {S : Ty 0} {T : Ty 1}
    (hh : HeapTyped Θ h) (hok : SemStoOk Θ Ξ h)
    (ht : HasType Θ .empty (.path p) (.arrow S T)) :
    ∃ ℓf T0 t T1, PathEval h p ℓf ∧ Heap.Lookup h ℓf (.abs T0 t) ∧
      Wf Θ .empty (.ty T0) ∧ HasType Θ (Ctx.empty.push T0) t T1 ∧
      Sub Θ .empty (.ty S) (.ty T0) ∧
      Sub Θ (Ctx.empty.push S) (.ty T1) (.ty T) := by
  obtain ⟨hw, hsub⟩ := ht.path_inv rfl
  obtain ⟨ℓf, hev⟩ := hw.eval_empty hh hok
  have hd := Sub.den_empty hsub hh hok 0 ℓf (by simp only [Den]; exact hev)
  simp only [Den] at hd
  obtain ⟨T0, t, T1, hlk, hwf0, hty, hdom, hcod⟩ := hd
  exact ⟨ℓf, T0, t, T1, hev, hlk, hwf0, hty, hdom, hcod⟩

/-- Progress: a closed well-typed term is final or steps. -/
theorem progress {Θ : Sto} {Ξ : SemSto} {h : Heap} {t : Tm 0} {T : Ty 0}
    (hh : HeapTyped Θ h) (hok : SemStoOk Θ Ξ h)
    (ht : HasType Θ .empty t T) :
    Final t ∨ ∃ h' t', Step h t h' t' := by
  suffices go : ∀ {s : Sig} {Γ : Ctx s} {t' : Tm s} {T' : Ty s},
      HasType Θ Γ t' T' -> HeapTyped Θ h -> SemStoOk Θ Ξ h -> ∀ (hs : s = 0),
      Final (hs ▸ t') ∨ ∃ h' t'', Step h (hs ▸ t') h' t'' by
    exact go ht hh hok rfl
  clear hh hok ht
  intro s Γ t' T' ht'
  induction ht' with
  | path hp =>
    intro hh hok hs
    subst hs
    have hE := Ctx.eq_empty ‹Ctx 0›
    subst hE
    rename_i px
    obtain ⟨m, hev⟩ := hp.eval_empty hh hok
    match px, hev with
    | .var (.free ℓ), _ => exact .inl .loc
    | .fst p', hev => exact .inr ⟨_, _, .path hev (by intro hcontra; cases hcontra)⟩
    | .sel p' a, hev => exact .inr ⟨_, _, .path hev (by intro hcontra; cases hcontra)⟩
  | sub _ _ _ ih => exact ih
  | abs _ _ _ =>
    intro _ _ hs
    subst hs
    exact .inl (.val .abs)
  | app h1 h2 =>
    intro hh hok hs
    subst hs
    have hE := Ctx.eq_empty ‹Ctx 0›
    subst hE
    obtain ⟨ℓf, T0, tb, T1, hevf, hlk, -, -, -, -⟩ := canonical_arrow hh hok h1
    obtain ⟨hwq, -⟩ := h2.path_inv rfl
    obtain ⟨ℓa, heva⟩ := hwq.eval_empty hh hok
    exact .inr ⟨_, _, .apply hevf heva hlk⟩
  | pair_tm _ _ =>
    intro _ _ hs
    subst hs
    exact .inl (.val .pairTm)
  | pair_ty _ _ =>
    intro _ _ hs
    subst hs
    exact .inl (.val .pairTy)
  | letin h1 hwf h2 ih1 ih2 =>
    intro hh hok hs
    subst hs
    rcases ih1 hh hok rfl with hfin | ⟨h', t1', hstep⟩
    · cases hfin with
      | val hv => exact .inr ⟨_, _, .let_val hv⟩
      | loc => exact .inr ⟨_, _, .let_path .var⟩
    · exact .inr ⟨_, _, .let_ctx hstep⟩
  | typed _ _ _ =>
    intro _ _ hs
    subst hs
    exact .inr ⟨_, _, .ascribe⟩

end LambdaP
