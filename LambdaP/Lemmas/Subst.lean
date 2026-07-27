import LambdaP.Lemmas.Renaming

/-!
Substitution lemmas for the judgments.

A substitution σ *conforms* from `Γ` to `Δ` (`SubstTyping`) when each image
`σ.var x` is a wellformed path whose singleton type is below the
substituted image of x's declared type. All judgments are closed under
conforming substitutions. The opening instances (`SubstTyping.openPath`,
`SubstTyping.openVar`) are the forms used by preservation.

The pure-subtyping formulation is what makes these lemmas true: the paper's
precise path typing (`p :: T`) is not closed under path substitution
(see DESIGN.md).
-/

namespace LambdaP

/-- Total lookup: every bound variable has a declared type. -/
theorem Ctx.lookupVar_total (Γ : Ctx s) (x : BVar s) : ∃ T, Ctx.LookupVar Γ x T := by
  induction Γ with
  | empty => exact nomatch x
  | push Γ S ih =>
    cases x with
    | here => exact ⟨S.weaken, .here⟩
    | there x' =>
      obtain ⟨T, hT⟩ := ih x'
      exact ⟨T.weaken, .there hT⟩

/-- A conforming substitution from `Γ` to `Δ`: images are wellformed paths
whose singletons are below the substituted declared types. -/
structure SubstTyping (Θ : Sto) (σ : Subst s1 s2) (Γ : Ctx s1) (Δ : Ctx s2) : Prop where
  conforms : ∀ {x : BVar s1} {T : Ty s1},
    Ctx.LookupVar Γ x T -> Sub Θ Δ (.ty (.single (σ.var x))) (.ty (T.subst σ))
  wf : ∀ (x : BVar s1), Path.Wf Θ Δ (σ.var x)

/-- Conforming substitutions extend under a binder. -/
theorem SubstTyping.lift {s1 s2 : Sig} {Θ : Sto} {σ : Subst s1 s2} {Γ : Ctx s1} {Δ : Ctx s2}
    (hσ : SubstTyping Θ σ Γ Δ) {S : Ty s1} :
    SubstTyping Θ σ.lift (Γ.push S) (Δ.push (S.subst σ)) := by
  constructor
  · intro x T h
    cases h with
    | here =>
      rw [Ty.weaken_subst_comm]
      exact Sub.var_bound .here
    | there h' =>
      rw [Ty.weaken_subst_comm]
      exact (hσ.conforms h').weaken
  · intro x
    cases x with
    | here => exact .var_bound .here
    | there x' => exact (hσ.wf x').weaken

/-- Subtyping is closed under conforming substitution. -/
theorem Sub.subst {Θ} {Γ : Ctx s1} {τ1 τ2 : Tau s1} (h : Sub Θ Γ τ1 τ2) :
    ∀ {s2} {σ : Subst s1 s2} {Δ : Ctx s2}, SubstTyping Θ σ Γ Δ ->
      Sub Θ Δ (τ1.subst σ) (τ2.subst σ) := by
  induction h with
  | refl =>
    intro _ _ _ _
    exact .refl
  | trans _ _ ih1 ih2 =>
    intro _ _ _ hσ
    exact .trans (ih1 hσ) (ih2 hσ)
  | bot =>
    intro _ _ _ _
    exact .bot
  | top =>
    intro _ _ _ _
    exact .top
  | var_bound hx =>
    intro _ _ _ hσ
    exact hσ.conforms hx
  | var_free hl =>
    intro _ _ _ _
    simp only [Tau.subst, Ty.subst, Path.subst, Var.subst, Ty.fromClosed_subst]
    exact .var_free hl
  | symm _ ih =>
    intro _ _ _ hσ
    exact .symm (ih hσ)
  | fst_tm _ ih =>
    intro _ _ _ hσ
    exact .fst_tm (ih hσ)
  | fst_ty _ ih =>
    intro _ _ _ hσ
    exact .fst_ty (ih hσ)
  | sel_tm _ ih =>
    intro _ _ _ hσ
    simp only [Tau.subst, Ty.subst, Path.subst]
    rw [← Ty.open_subst_comm]
    exact .sel_tm (ih hσ)
  | sel_ty _ ih =>
    intro _ _ _ hσ
    simp only [Tau.subst, Ty.subst]
    rw [← Ty.open_subst_comm, ← Ty.open_subst_comm]
    exact .sel_ty (ih hσ)
  | sel_hi _ _ ih1 ih2 =>
    intro _ _ _ hσ
    exact .sel_hi (ih1 hσ) (ih2 hσ)
  | sel_lo _ _ ih1 ih2 =>
    intro _ _ _ hσ
    exact .sel_lo (ih1 hσ) (ih2 hσ)
  | arrow _ _ ih1 ih2 =>
    intro _ _ _ hσ
    exact .arrow (ih1 hσ) (ih2 hσ.lift)
  | pair_tm _ _ ih1 ih2 =>
    intro _ _ _ hσ
    exact .pair_tm (ih1 hσ) (ih2 hσ.lift)
  | pair_ty _ _ ih1 ih2 =>
    intro _ _ _ hσ
    exact .pair_ty (ih1 hσ) (ih2 hσ.lift)
  | ival _ _ _ ih1 ih2 ih3 =>
    intro _ _ _ hσ
    exact .ival (ih1 hσ) (ih2 hσ) (ih3 hσ)

/-- Path wellformedness is closed under conforming substitution. -/
theorem Path.Wf.subst {Θ} {Γ : Ctx s1} {p : Path s1} (h : Path.Wf Θ Γ p) :
    ∀ {s2} {σ : Subst s1 s2} {Δ : Ctx s2}, SubstTyping Θ σ Γ Δ ->
      Path.Wf Θ Δ (p.subst σ) := by
  induction h with
  | var_bound hx =>
    intro _ _ _ hσ
    exact hσ.wf _
  | var_free hl =>
    intro _ _ _ _
    exact .var_free hl
  | fst_tm _ hsub ih =>
    intro _ _ _ hσ
    exact .fst_tm (ih hσ) (hsub.subst hσ)
  | fst_ty _ hsub ih =>
    intro _ _ _ hσ
    exact .fst_ty (ih hσ) (hsub.subst hσ)
  | sel _ hsub ih =>
    intro _ _ _ hσ
    exact .sel (ih hσ) (hsub.subst hσ)

/-- Type wellformedness is closed under conforming substitution. -/
theorem Wf.subst {Θ} {Γ : Ctx s1} {τ : Tau s1} (h : Wf Θ Γ τ) :
    ∀ {s2} {σ : Subst s1 s2} {Δ : Ctx s2}, SubstTyping Θ σ Γ Δ ->
      Wf Θ Δ (τ.subst σ) := by
  induction h with
  | bot =>
    intro _ _ _ _
    exact .bot
  | top =>
    intro _ _ _ _
    exact .top
  | single hp =>
    intro _ _ _ hσ
    exact .single (hp.subst hσ)
  | tsel hp hsub =>
    intro _ _ _ hσ
    exact .tsel (hp.subst hσ) (hsub.subst hσ)
  | arrow _ _ ih1 ih2 =>
    intro _ _ _ hσ
    exact .arrow (ih1 hσ) (ih2 hσ.lift)
  | pair_tm _ _ ih1 ih2 =>
    intro _ _ _ hσ
    exact .pair_tm (ih1 hσ) (ih2 hσ.lift)
  | pair_ty _ _ ih1 ih2 =>
    intro _ _ _ hσ
    exact .pair_ty (ih1 hσ) (ih2 hσ.lift)
  | intv _ _ hsub ih1 ih2 =>
    intro _ _ _ hσ
    exact .intv (ih1 hσ) (ih2 hσ) (hsub.subst hσ)

/-- Variable substitution followed by `toSubst` is `vsubst`. -/
theorem Var.subst_toSubst {y : Var s1} {σ : VSubst s1 s2} :
    y.subst σ.toSubst = .var (y.vsubst σ) := by
  cases y <;> rfl

/-- `SubstTyping.lift` for variable substitutions, phrased through `toSubst`. -/
theorem SubstTyping.liftV {s1 s2 : Sig} {Θ : Sto} {σ : VSubst s1 s2} {Γ : Ctx s1} {Δ : Ctx s2}
    (hσ : SubstTyping Θ σ.toSubst Γ Δ) {S : Ty s1} :
    SubstTyping Θ σ.lift.toSubst (Γ.push S) (Δ.push (S.subst σ.toSubst)) := by
  rw [VSubst.toSubst_lift]
  exact hσ.lift

/-- Term typing is closed under conforming variable substitution. -/
theorem HasType.subst {Θ} {Γ : Ctx s1} {t : Tm s1} {T : Ty s1} (h : HasType Θ Γ t T) :
    ∀ {s2} {σ : VSubst s1 s2} {Δ : Ctx s2}, SubstTyping Θ σ.toSubst Γ Δ ->
      HasType Θ Δ (t.subst σ) (T.subst σ.toSubst) := by
  induction h with
  | path hp =>
    intro _ _ _ hσ
    exact .path (hp.subst hσ)
  | sub _ hsub hwf ih =>
    intro _ _ _ hσ
    exact .sub (ih hσ) (hsub.subst hσ) (hwf.subst hσ)
  | abs hwf _ ih =>
    intro _ σ _ hσ
    have hbody := ih hσ.liftV
    rw [VSubst.toSubst_lift] at hbody
    exact .abs (hwf.subst hσ) hbody
  | app _ _ ih1 ih2 =>
    intro _ _ _ hσ
    simp only [Tm.subst]
    rw [← Ty.open_subst_comm]
    exact .app (ih1 hσ) (ih2 hσ)
  | pair_tm hy hz =>
    intro _ σ _ hσ
    have hy' := hy.subst hσ
    have hz' := hz.subst hσ
    simp only [Path.subst, Var.subst_toSubst] at hy' hz'
    simp only [Tm.subst, Ty.subst, Path.subst, Var.subst_toSubst, Ty.weaken_subst_comm]
    exact .pair_tm hy' hz'
  | pair_ty hy hwf =>
    intro _ σ _ hσ
    have hy' := hy.subst hσ
    simp only [Path.subst, Var.subst_toSubst] at hy'
    simp only [Tm.subst, Ty.subst, Path.subst, Var.subst_toSubst, Ty.weaken_subst_comm]
    exact .pair_ty hy' (hwf.subst hσ)
  | letin _ hwf _ ih1 ih2 =>
    intro _ σ _ hσ
    have hbody := ih2 hσ.liftV
    rw [VSubst.toSubst_lift, Ty.weaken_subst_comm] at hbody
    exact .letin (ih1 hσ) (hwf.subst hσ) hbody
  | typed _ hwf ih =>
    intro _ _ _ hσ
    exact .typed (ih hσ) (hwf.subst hσ)

/-! ### Opening instances -/

/-- Opening a binder with a conforming path is a conforming substitution:
if `q` is wellformed with `single q <: S`, then `[x := q]` conforms from
`Γ, x: S` to `Γ`. -/
theorem SubstTyping.openPath {Θ} {Γ : Ctx s} {q : Path s} {S : Ty s}
    (hq : Path.Wf Θ Γ q) (hsub : Sub Θ Γ (.ty (.single q)) (.ty S)) :
    SubstTyping Θ (Subst.openPath q) (Γ.push S) Γ := by
  have wsub : ∀ (T : Ty s), T.weaken.subst (Subst.openPath q) = T := fun _ => Ty.weaken_open
  constructor
  · intro x T h
    cases h with
    | here =>
      rw [wsub]
      exact hsub
    | there h' =>
      rw [wsub]
      exact .var_bound h'
  · intro x
    cases x with
    | here => exact hq
    | there x' =>
      obtain ⟨T, hT⟩ := Ctx.lookupVar_total Γ x'
      exact .var_bound hT

/-- The variable-substitution version of `SubstTyping.openPath`. -/
theorem SubstTyping.openVar {Θ} {Γ : Ctx s} {y : Var s} {S : Ty s}
    (hy : Path.Wf Θ Γ (.var y)) (hsub : Sub Θ Γ (.ty (.single (.var y))) (.ty S)) :
    SubstTyping Θ (VSubst.openVar y).toSubst (Γ.push S) Γ := by
  rw [VSubst.openVar_toSubst]
  exact SubstTyping.openPath hy hsub

/-- Opening for term typing: a let/β body typed under a binder can be opened
with any wellformed variable conforming to the binder's type. -/
theorem HasType.open {Θ} {Γ : Ctx s} {t : Tm (s+1)} {T : Ty (s+1)} {y : Var s} {S : Ty s}
    (h : HasType Θ (Γ.push S) t T)
    (hy : Path.Wf Θ Γ (.var y)) (hsub : Sub Θ Γ (.ty (.single (.var y))) (.ty S)) :
    HasType Θ Γ (t.open y) (T.open (.var y)) := by
  have := h.subst (SubstTyping.openVar hy hsub)
  rwa [VSubst.openVar_toSubst] at this

/-- Opening for term typing when the result type does not use the binder. -/
theorem HasType.open_weaken {Θ} {Γ : Ctx s} {t : Tm (s+1)} {T : Ty s} {y : Var s} {S : Ty s}
    (h : HasType Θ (Γ.push S) t T.weaken)
    (hy : Path.Wf Θ Γ (.var y)) (hsub : Sub Θ Γ (.ty (.single (.var y))) (.ty S)) :
    HasType Θ Γ (t.open y) T := by
  have := HasType.open h hy hsub
  rwa [Ty.weaken_open] at this

end LambdaP
