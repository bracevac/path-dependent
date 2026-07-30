import LambdaP.Semantics

/-!
Renaming lemmas for the judgments: all judgments are preserved under
context-respecting renamings. Weakening is the instance at `Rename.succ`.

The store typing `Θ` is untouched throughout — renamings act only on bound
variables, and heap locations are free names.
-/

namespace LambdaP

/-- A renaming `f` is context-respecting from `Γ` to `Δ` if it maps each
binding of `Γ` to a binding of `Δ` at the renamed type. -/
def Renaming (Γ : Ctx s1) (f : Rename s1 s2) (Δ : Ctx s2) : Prop :=
  ∀ {x : BVar s1} {T : Ty s1},
    Ctx.LookupVar Γ x T -> Ctx.LookupVar Δ (f.var x) (T.rename f)

/-- Extends a context-respecting renaming under a binder. -/
theorem Renaming.ext {s1 s2 : Sig} {Γ : Ctx s1} {f : Rename s1 s2} {Δ : Ctx s2}
    (ρ : Renaming Γ f Δ) {T : Ty s1} :
    Renaming (Γ.push T) f.lift (Δ.push (T.rename f)) := by
  intro x S h
  cases h with
  | here =>
    rw [Ty.weaken_rename_comm]
    exact .here
  | there h' =>
    rw [Ty.weaken_rename_comm]
    exact .there (ρ h')

/-- The weakening renaming is context-respecting. -/
theorem Renaming.succ {Γ : Ctx s} {S : Ty s} :
    Renaming Γ Rename.succ (Γ.push S) := by
  intro x T h
  exact .there h

mutual

/-- Subtyping is preserved under renaming. -/
theorem Sub.rename {Θ} {Γ : Ctx s1} {τ1 τ2 : Tau s1} (h : Sub Θ Γ τ1 τ2) :
    ∀ {s2 : Sig} {f : Rename s1 s2} {Δ : Ctx s2}, Renaming Γ f Δ ->
      Sub Θ Δ (τ1.rename f) (τ2.rename f) :=
  match h with
  | .refl => fun _ => .refl
  | .trans h1 h2 => fun ρ => .trans (h1.rename ρ) (h2.rename ρ)
  | .bot => fun _ => .bot
  | .top => fun _ => .top
  | .var_bound hx => fun ρ => .var_bound (ρ hx)
  | .var_free hl => fun _ => by
    simp only [Tau.rename, Ty.rename, Path.rename, Var.rename, Ty.fromClosed_rename]
    exact .var_free hl
  | .symm hw h1 => fun ρ => .symm (hw.rename ρ) (h1.rename ρ)
  | .fst_tm h1 => fun ρ => .fst_tm (h1.rename ρ)
  | .fst_ty h1 => fun ρ => .fst_ty (h1.rename ρ)
  | .sel_tm hr hw h1 => fun ρ => by
    simp only [Tau.rename, Ty.rename, Path.rename]
    rw [← Ty.open_rename_comm]
    exact Sub.sel_tm (Path.root_isBound_rename hr) (hw.rename ρ) (h1.rename ρ)
  | .sel_tm_loc hc hl => fun _ => by
    simp only [Tau.rename, Ty.rename, Path.rename, Var.rename]
    exact Sub.sel_tm_loc hc.rename hl
  | .sel_hi hr hw h1 h2 => fun ρ => by
    have h2' := h2.rename ρ
    simp only [Tau.rename] at h2'
    rw [← Ty.open_rename_comm, ← Ty.open_rename_comm] at h2'
    simp only [Tau.rename, Ty.rename]
    rw [← Ty.open_rename_comm]
    exact Sub.sel_hi (Path.root_isBound_rename hr) (hw.rename ρ) (h1.rename ρ) h2'
  | .sel_lo hr hw h1 h2 => fun ρ => by
    have h2' := h2.rename ρ
    simp only [Tau.rename] at h2'
    rw [← Ty.open_rename_comm, ← Ty.open_rename_comm] at h2'
    simp only [Tau.rename, Ty.rename]
    rw [← Ty.open_rename_comm]
    exact Sub.sel_lo (Path.root_isBound_rename hr) (hw.rename ρ) (h1.rename ρ) h2'
  | .sel_hi_loc hc hl => fun _ => by
    simp only [Tau.rename, Ty.rename, Ty.fromClosed_rename]
    exact Sub.sel_hi_loc hc.rename hl
  | .sel_lo_loc hc hl => fun _ => by
    simp only [Tau.rename, Ty.rename, Ty.fromClosed_rename]
    exact Sub.sel_lo_loc hc.rename hl
  | .arrow h1 h2 => fun ρ => .arrow (h1.rename ρ) (h2.rename (Renaming.ext ρ))
  | .pair_tm h1 h2 => fun ρ => .pair_tm (h1.rename ρ) (h2.rename (Renaming.ext ρ))
  | .pair_ty h1 h2 h3 => fun ρ =>
    .pair_ty (h1.rename ρ) (h2.rename (Renaming.ext ρ)) (h3.rename (Renaming.ext ρ))
  | .repl hwp hwq h1 h2 => fun ρ => by
    simp only [Tau.rename]
    rw [← Ty.open_rename_comm, ← Ty.open_rename_comm]
    exact Sub.repl (hwp.rename ρ) (hwq.rename ρ) (h1.rename ρ) (h2.rename ρ)
  | .skip_tm hr hw h1 hne => fun ρ =>
    .skip_tm (Path.root_isBound_rename hr) (hw.rename ρ) (h1.rename ρ) hne
  | .skip_ty hr hw h1 => fun ρ =>
    .skip_ty (Path.root_isBound_rename hr) (hw.rename ρ) (h1.rename ρ)
  | .skip_tm_loc hc hl hne => fun _ => by
    simp only [Tau.rename, Ty.rename, Path.rename]
    exact Sub.skip_tm_loc hc.rename hl hne
  | .skip_ty_loc hc hl => fun _ => by
    simp only [Tau.rename, Ty.rename, Path.rename]
    exact Sub.skip_ty_loc hc.rename hl

/-- Path wellformedness is preserved under renaming. -/
theorem Path.Wf.rename {Θ} {Γ : Ctx s1} {p : Path s1} (h : Path.Wf Θ Γ p) :
    ∀ {s2 : Sig} {f : Rename s1 s2} {Δ : Ctx s2}, Renaming Γ f Δ ->
      Path.Wf Θ Δ (p.rename f) :=
  match h with
  | .var_bound hx => fun ρ => .var_bound (ρ hx)
  | .var_free hl => fun _ => .var_free hl
  | .fst_tm h1 hsub => fun ρ => .fst_tm (h1.rename ρ) (hsub.rename ρ)
  | .fst_ty h1 hsub => fun ρ => .fst_ty (h1.rename ρ) (hsub.rename ρ)
  | .sel h1 hsub => fun ρ => .sel (h1.rename ρ) (hsub.rename ρ)
  | .sel_skip_tm h1 hsub hne => fun ρ =>
    .sel_skip_tm (h1.rename ρ) (hsub.rename ρ) hne
  | .sel_skip_ty h1 hsub => fun ρ =>
    .sel_skip_ty (h1.rename ρ) (hsub.rename ρ)

end

/-- Type wellformedness is preserved under renaming. -/
theorem Wf.rename {Θ} {Γ : Ctx s1} {τ : Tau s1} (h : Wf Θ Γ τ) :
    ∀ {s2} {f : Rename s1 s2} {Δ : Ctx s2}, Renaming Γ f Δ ->
      Wf Θ Δ (τ.rename f) := by
  induction h with
  | bot =>
    intro _ _ _ _
    exact .bot
  | top =>
    intro _ _ _ _
    exact .top
  | single hp =>
    intro _ _ _ ρ
    exact .single (hp.rename ρ)
  | tsel hp hsub =>
    intro _ _ _ ρ
    exact .tsel (hp.rename ρ) (hsub.rename ρ)
  | arrow _ _ ih1 ih2 =>
    intro _ _ _ ρ
    exact .arrow (ih1 ρ) (ih2 (Renaming.ext ρ))
  | pair_tm _ _ ih1 ih2 =>
    intro _ _ _ ρ
    exact .pair_tm (ih1 ρ) (ih2 (Renaming.ext ρ))
  | pair_ty _ _ ih1 ih2 =>
    intro _ _ _ ρ
    exact .pair_ty (ih1 ρ) (ih2 (Renaming.ext ρ))
  | intv _ _ hsub ih1 ih2 =>
    intro _ _ _ ρ
    exact .intv (ih1 ρ) (ih2 ρ) (hsub.rename ρ)

/-- Term typing is preserved under renaming. -/
theorem HasType.rename {Θ} {Γ : Ctx s1} {t : Tm s1} {T : Ty s1} (h : HasType Θ Γ t T) :
    ∀ {s2} {f : Rename s1 s2} {Δ : Ctx s2}, Renaming Γ f Δ ->
      HasType Θ Δ (t.rename f) (T.rename f) := by
  induction h with
  | path hp =>
    intro _ _ _ ρ
    exact .path (hp.rename ρ)
  | sub _ hsub hwf ih =>
    intro _ _ _ ρ
    exact .sub (ih ρ) (hsub.rename ρ) (hwf.rename ρ)
  | abs hwf _ ih =>
    intro _ _ _ ρ
    exact .abs (hwf.rename ρ) (ih (Renaming.ext ρ))
  | app _ _ ih1 ih2 =>
    intro _ _ _ ρ
    simp only [Tm.rename]
    rw [← Ty.open_rename_comm]
    exact HasType.app (ih1 ρ) (ih2 ρ)
  | pair_tm hy hz =>
    intro _ _ _ ρ
    have hy' := hy.rename ρ
    have hz' := hz.rename ρ
    simp only [Path.rename] at hy' hz'
    simp only [Tm.rename, Ty.rename, Path.rename, Ty.weaken_rename_comm]
    exact HasType.pair_tm hy' hz'
  | pair_ty hy hwf =>
    intro _ _ _ ρ
    have hy' := hy.rename ρ
    have hwf' := hwf.rename ρ
    simp only [Path.rename] at hy'
    simp only [Tm.rename, Ty.rename, Path.rename, Ty.weaken_rename_comm]
    exact HasType.pair_ty hy' hwf'
  | letin _ hwf _ ih1 ih3 =>
    intro _ _ _ ρ
    refine .letin (ih1 ρ) (hwf.rename ρ) ?_
    have h3 := ih3 (Renaming.ext ρ)
    rwa [Ty.weaken_rename_comm] at h3
  | typed _ hwf ih =>
    intro _ _ _ ρ
    exact .typed (ih ρ) (hwf.rename ρ)

/-! ### Weakening -/

/-- Weakening for subtyping. -/
theorem Sub.weaken {Θ} {Γ : Ctx s} {τ1 τ2 : Tau s} {S : Ty s} (h : Sub Θ Γ τ1 τ2) :
    Sub Θ (Γ.push S) τ1.weaken τ2.weaken :=
  h.rename Renaming.succ

/-- Weakening for path wellformedness. -/
theorem Path.Wf.weaken {Θ} {Γ : Ctx s} {p : Path s} {S : Ty s} (h : Path.Wf Θ Γ p) :
    Path.Wf Θ (Γ.push S) p.weaken :=
  h.rename Renaming.succ

/-- Weakening for type wellformedness. -/
theorem Wf.weaken {Θ} {Γ : Ctx s} {τ : Tau s} {S : Ty s} (h : Wf Θ Γ τ) :
    Wf Θ (Γ.push S) τ.weaken :=
  h.rename Renaming.succ

/-- Weakening for term typing. -/
theorem HasType.weaken {Θ} {Γ : Ctx s} {t : Tm s} {T S : Ty s} (h : HasType Θ Γ t T) :
    HasType Θ (Γ.push S) t.weaken T.weaken :=
  h.rename Renaming.succ

end LambdaP
