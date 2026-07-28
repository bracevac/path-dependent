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
  rooted : ∀ (x : BVar s1), (σ.var x).root.IsBound

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
  · intro x
    cases x with
    | here => trivial
    | there x' => exact Path.root_isBound_rename (hσ.rooted x')

mutual

/-- Subtyping is closed under conforming substitution. -/
theorem Sub.subst {Θ} {Γ : Ctx s1} {τ1 τ2 : Tau s1} (h : Sub Θ Γ τ1 τ2) :
    ∀ {s2 : Sig} {σ : Subst s1 s2} {Δ : Ctx s2}, SubstTyping Θ σ Γ Δ ->
      Sub Θ Δ (τ1.subst σ) (τ2.subst σ) :=
  match h with
  | .refl => fun _ => .refl
  | .trans h1 h2 => fun hσ => .trans (h1.subst hσ) (h2.subst hσ)
  | .bot => fun _ => .bot
  | .top => fun _ => .top
  | .var_bound hx => fun hσ => hσ.conforms hx
  | .var_free hl => fun _ => by
    simp only [Tau.subst, Ty.subst, Path.subst, Var.subst, Ty.fromClosed_subst]
    exact .var_free hl
  | .symm hw h1 => fun hσ => .symm (hw.subst hσ) (h1.subst hσ)
  | .fst_tm h1 => fun hσ => .fst_tm (h1.subst hσ)
  | .fst_ty h1 => fun hσ => .fst_ty (h1.subst hσ)
  | .sel_tm hr h1 => fun hσ => by
    simp only [Tau.subst, Ty.subst, Path.subst]
    rw [← Ty.open_subst_comm]
    exact Sub.sel_tm (Path.root_isBound_subst hr hσ.rooted) (h1.subst hσ)
  | .sel_tm_loc hc hl => fun _ => by
    simp only [Tau.subst, Ty.subst, Path.subst, Var.subst]
    exact Sub.sel_tm_loc hc.subst hl
  | .sel_hi hr hw h1 h2 => fun hσ => by
    have h2' := h2.subst hσ
    simp only [Tau.subst] at h2'
    rw [← Ty.open_subst_comm, ← Ty.open_subst_comm] at h2'
    simp only [Tau.subst, Ty.subst]
    rw [← Ty.open_subst_comm]
    exact Sub.sel_hi (Path.root_isBound_subst hr hσ.rooted) (hw.subst hσ)
      (h1.subst hσ) h2'
  | .sel_lo hr hw h1 h2 => fun hσ => by
    have h2' := h2.subst hσ
    simp only [Tau.subst] at h2'
    rw [← Ty.open_subst_comm, ← Ty.open_subst_comm] at h2'
    simp only [Tau.subst, Ty.subst]
    rw [← Ty.open_subst_comm]
    exact Sub.sel_lo (Path.root_isBound_subst hr hσ.rooted) (hw.subst hσ)
      (h1.subst hσ) h2'
  | .sel_hi_loc hc hl => fun _ => by
    simp only [Tau.subst, Ty.subst, Ty.fromClosed_subst]
    exact Sub.sel_hi_loc hc.subst hl
  | .sel_lo_loc hc hl => fun _ => by
    simp only [Tau.subst, Ty.subst, Ty.fromClosed_subst]
    exact Sub.sel_lo_loc hc.subst hl
  | .arrow h1 h2 => fun hσ => .arrow (h1.subst hσ) (h2.subst hσ.lift)
  | .pair_tm h1 h2 => fun hσ => .pair_tm (h1.subst hσ) (h2.subst hσ.lift)
  | .pair_ty h1 h2 h3 => fun hσ =>
    .pair_ty (h1.subst hσ) (h2.subst hσ.lift) (h3.subst hσ.lift)
  | .repl hwp hwq h1 h2 => fun hσ => by
    simp only [Tau.subst]
    rw [← Ty.open_subst_comm, ← Ty.open_subst_comm]
    exact Sub.repl (hwp.subst hσ) (hwq.subst hσ) (h1.subst hσ) (h2.subst hσ)
  | .skip_tm hr h1 hne => fun hσ =>
    .skip_tm (Path.root_isBound_subst hr hσ.rooted) (h1.subst hσ) hne
  | .skip_ty hr h1 => fun hσ =>
    .skip_ty (Path.root_isBound_subst hr hσ.rooted) (h1.subst hσ)
  | .skip_tm_loc hc hl hne => fun _ => by
    simp only [Tau.subst, Ty.subst, Path.subst]
    exact Sub.skip_tm_loc hc.subst hl hne
  | .skip_ty_loc hc hl => fun _ => by
    simp only [Tau.subst, Ty.subst, Path.subst]
    exact Sub.skip_ty_loc hc.subst hl

/-- Path wellformedness is closed under conforming substitution. -/
theorem Path.Wf.subst {Θ} {Γ : Ctx s1} {p : Path s1} (h : Path.Wf Θ Γ p) :
    ∀ {s2 : Sig} {σ : Subst s1 s2} {Δ : Ctx s2}, SubstTyping Θ σ Γ Δ ->
      Path.Wf Θ Δ (p.subst σ) :=
  match h with
  | .var_bound _ => fun hσ => hσ.wf _
  | .var_free hl => fun _ => .var_free hl
  | .fst_tm h1 hsub => fun hσ => .fst_tm (h1.subst hσ) (hsub.subst hσ)
  | .fst_ty h1 hsub => fun hσ => .fst_ty (h1.subst hσ) (hsub.subst hσ)
  | .sel h1 hsub => fun hσ => .sel (h1.subst hσ) (hsub.subst hσ)
  | .sel_skip_tm h1 hsub hne => fun hσ =>
    .sel_skip_tm (h1.subst hσ) (hsub.subst hσ) hne
  | .sel_skip_ty h1 hsub => fun hσ =>
    .sel_skip_ty (h1.subst hσ) (hsub.subst hσ)

end

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
    (hq : Path.Wf Θ Γ q) (hsub : Sub Θ Γ (.ty (.single q)) (.ty S))
    (hroot : q.root.IsBound) :
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
  · intro x
    cases x with
    | here => exact hroot
    | there x' => trivial

/-- The variable-substitution version of `SubstTyping.openPath`. -/
theorem SubstTyping.openVar {Θ} {Γ : Ctx s} {y : Var s} {S : Ty s}
    (hy : Path.Wf Θ Γ (.var y)) (hsub : Sub Θ Γ (.ty (.single (.var y))) (.ty S))
    (hroot : Var.IsBound y) :
    SubstTyping Θ (VSubst.openVar y).toSubst (Γ.push S) Γ := by
  rw [VSubst.openVar_toSubst]
  exact SubstTyping.openPath hy hsub hroot

/-- Opening for term typing: a let/β body typed under a binder can be opened
with any wellformed variable conforming to the binder's type. -/
theorem HasType.open {Θ} {Γ : Ctx s} {t : Tm (s+1)} {T : Ty (s+1)} {y : Var s} {S : Ty s}
    (h : HasType Θ (Γ.push S) t T)
    (hy : Path.Wf Θ Γ (.var y)) (hsub : Sub Θ Γ (.ty (.single (.var y))) (.ty S))
    (hroot : Var.IsBound y) :
    HasType Θ Γ (t.open y) (T.open (.var y)) := by
  have := h.subst (SubstTyping.openVar hy hsub hroot)
  rwa [VSubst.openVar_toSubst] at this

/-- Opening for term typing when the result type does not use the binder. -/
theorem HasType.open_weaken {Θ} {Γ : Ctx s} {t : Tm (s+1)} {T : Ty s} {y : Var s} {S : Ty s}
    (h : HasType Θ (Γ.push S) t T.weaken)
    (hy : Path.Wf Θ Γ (.var y)) (hsub : Sub Θ Γ (.ty (.single (.var y))) (.ty S))
    (hroot : Var.IsBound y) :
    HasType Θ Γ (t.open y) T := by
  have := HasType.open h hy hsub hroot
  rwa [Ty.weaken_open] at this

/-! ### Narrowing

Narrowing is the identity substitution viewed as a conforming substitution
from `Γ, x: S` to `Γ, x: S1` when `S1 <: S`. -/

/-- The identity substitution conforms from a context to its narrowing. -/
theorem SubstTyping.narrow {Θ} {Γ : Ctx s} {S1 S : Ty s}
    (hsub : Sub Θ Γ (.ty S1) (.ty S)) :
    SubstTyping Θ Subst.id (Γ.push S) (Γ.push S1) := by
  constructor
  · intro x T h
    cases h with
    | here =>
      rw [Ty.subst_id]
      exact .trans (.var_bound .here) hsub.weaken
    | there h' =>
      rw [Ty.subst_id]
      exact .var_bound (.there h')
  · intro x
    obtain ⟨T, hT⟩ := Ctx.lookupVar_total (Γ.push S1) x
    exact .var_bound hT
  · intro x
    trivial

/-- Narrowing for subtyping. -/
theorem Sub.narrow {Θ} {Γ : Ctx s} {S1 S : Ty s} {τ1 τ2 : Tau (s+1)}
    (h : Sub Θ (Γ.push S) τ1 τ2) (hsub : Sub Θ Γ (.ty S1) (.ty S)) :
    Sub Θ (Γ.push S1) τ1 τ2 := by
  have := h.subst (SubstTyping.narrow hsub)
  rwa [Tau.subst_id, Tau.subst_id] at this

/-- Narrowing for path wellformedness. -/
theorem Path.Wf.narrow {Θ} {Γ : Ctx s} {S1 S : Ty s} {p : Path (s+1)}
    (h : Path.Wf Θ (Γ.push S) p) (hsub : Sub Θ Γ (.ty S1) (.ty S)) :
    Path.Wf Θ (Γ.push S1) p := by
  have := h.subst (SubstTyping.narrow hsub)
  rwa [Path.subst_id] at this

/-- Narrowing for type wellformedness. -/
theorem Wf.narrow {Θ} {Γ : Ctx s} {S1 S : Ty s} {τ : Tau (s+1)}
    (h : Wf Θ (Γ.push S) τ) (hsub : Sub Θ Γ (.ty S1) (.ty S)) :
    Wf Θ (Γ.push S1) τ := by
  have := h.subst (SubstTyping.narrow hsub)
  rwa [Tau.subst_id] at this

/-- Narrowing for term typing. -/
theorem HasType.narrow {Θ} {Γ : Ctx s} {S1 S : Ty s} {t : Tm (s+1)} {T : Ty (s+1)}
    (h : HasType Θ (Γ.push S) t T) (hsub : Sub Θ Γ (.ty S1) (.ty S)) :
    HasType Θ (Γ.push S1) t T := by
  have hst : SubstTyping Θ (VSubst.id).toSubst (Γ.push S) (Γ.push S1) := by
    rw [VSubst.toSubst_id]
    exact SubstTyping.narrow hsub
  have := h.subst hst
  rwa [Tm.subst_id, VSubst.toSubst_id, Ty.subst_id] at this

end LambdaP
