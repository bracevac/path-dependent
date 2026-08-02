import LambdaPFC.Typing

/-!
Renaming for every static judgment of the calculus.  A renaming is
admissible when it preserves context lookup; lifting it under a dependent
binder supplies the induction hypothesis needed by functions and pairs.
-/

namespace LambdaPFC

/-- A finite-variable renaming that respects the types recorded by two
contexts. -/
abbrev Renaming (Γ : Ctx n) (f : FinFun n m) (Δ : Ctx m) : Prop :=
  ∀ {x T}, Ctx.Binds Γ x T -> Ctx.Binds Δ (f x) (T.rename f)

/-- Identity is a context-respecting renaming. -/
theorem Renaming.id (Γ : Ctx n) : Renaming Γ FinFun.id Γ := by
  intro x T hx
  simpa only [Ty.rename_id] using hx

/-- Context-respecting renamings are closed under composition. -/
theorem Renaming.comp
    (ρ : Renaming Γ f Δ) (θ : Renaming Δ g Ξ) :
    Renaming Γ (f.comp g) Ξ := by
  intro x T hx
  simpa only [FinFun.comp_apply, Ty.rename_rename] using θ (ρ hx)

/-- Extend a context-respecting renaming below one dependent binder. -/
theorem Renaming.ext (ρ : Renaming Γ f Δ) :
    Renaming (Γ.snoc T) f.ext (Δ.snoc (T.rename f)) := by
  intro x U hx
  cases hx with
  | here =>
      simpa [Ty.weaken_rename] using
        (Ctx.Binds.here (Γ := Δ) (T := T.rename f))
  | there hx =>
      simpa [Ty.weaken_rename] using
        (Ctx.Binds.there (S := T.rename f) (ρ hx))

/-- Weakening is a context-respecting renaming. -/
theorem Renaming.weaken : Renaming Γ FinFun.weaken (Γ.snoc S) := by
  intro x T hx
  simpa [Ty.weaken] using (Ctx.Binds.there (S := S) hx)

/-- Precise path typing is preserved by a context-respecting renaming. -/
theorem Path.Ty.rename {Γ : Ctx n} {p : Path n} {τ : Tau n k}
    (h : Path.Ty Γ p τ) :
    ∀ {m} {f : FinFun n m} {Δ : Ctx m},
      Renaming Γ f Δ -> Path.Ty Δ (p.rename f) (τ.rename f) := by
  induction h with
  | var hx =>
      intro m f Δ ρ
      simpa [Path.rename, Tau.rename] using Path.Ty.var (ρ hx)
  | fst hp ih =>
      intro m f Δ ρ
      simpa [Path.rename, Ty.rename, Tau.rename] using Path.Ty.fst (ih ρ)
  | sel_r hp ih =>
      intro m f Δ ρ
      simpa [Path.rename, Ty.rename, Tau.rename, Tau.open_rename] using
        Path.Ty.sel_r (ih ρ)
  | sel_l hp htail hne ihp ihtail =>
      intro m f Δ ρ
      simpa [Path.rename, Ty.rename, Tau.rename] using
        Path.Ty.sel_l (ihp ρ) (ihtail ρ) hne

/-- Subtyping is preserved by a context-respecting renaming. -/
theorem Tau.Sub.rename {Γ : Ctx n} {τ1 τ2 : Tau n k}
    (h : Tau.Sub Γ τ1 τ2) :
    ∀ {m} {f : FinFun n m} {Δ : Ctx m},
      Renaming Γ f Δ -> Tau.Sub Δ (τ1.rename f) (τ2.rename f) := by
  induction h with
  | refl =>
      intro m f Δ ρ
      exact .refl
  | trans h1 h2 ih1 ih2 =>
      intro m f Δ ρ
      exact .trans (ih1 ρ) (ih2 ρ)
  | bot =>
      intro m f Δ ρ
      simp only [Tau.rename, Ty.rename]
      exact .bot
  | top =>
      intro m f Δ ρ
      simp only [Tau.rename, Ty.rename]
      exact .top
  | widen hp =>
      intro m f Δ ρ
      simpa [Tau.rename, Ty.rename, Path.rename] using
        Tau.Sub.widen (hp.rename ρ)
  | symm hp =>
      intro m f Δ ρ
      simpa [Tau.rename, Ty.rename, Path.rename] using
        Tau.Sub.symm (hp.rename ρ)
  | sel_hi hp hbounds ihbounds =>
      intro m f Δ ρ
      simpa [Tau.rename, Ty.rename, Path.rename] using
        Tau.Sub.sel_hi (hp.rename ρ) (ihbounds ρ)
  | sel_lo hp hbounds ihbounds =>
      intro m f Δ ρ
      simpa [Tau.rename, Ty.rename, Path.rename] using
        Tau.Sub.sel_lo (hp.rename ρ) (ihbounds ρ)
  | «fun» hdom hcod ihdom ihcod =>
      intro m f Δ ρ
      simpa [Tau.rename, Ty.rename] using
        Tau.Sub.fun (ihdom ρ) (ihcod (Renaming.ext ρ))
  | pair hfst hmember ihfst ihmember =>
      intro m f Δ ρ
      simpa [Tau.rename, Ty.rename] using
        Tau.Sub.pair (ihfst ρ) (ihmember (Renaming.ext ρ))
  | bounds hlo hhi hnonempty ihlo ihhi ihnonempty =>
      intro m f Δ ρ
      simpa [Tau.rename] using
        Tau.Sub.bounds (ihlo ρ) (ihhi ρ) (ihnonempty ρ)

/-- Well-formed generalized types are preserved by renaming. -/
theorem Tau.Wf.rename {Γ : Ctx n} {τ : Tau n k}
    (h : Tau.Wf Γ τ) :
    ∀ {m} {f : FinFun n m} {Δ : Ctx m},
      Renaming Γ f Δ -> Tau.Wf Δ (τ.rename f) := by
  induction h with
  | bot =>
      intro m f Δ ρ
      simp only [Tau.rename, Ty.rename]
      exact .bot
  | top =>
      intro m f Δ ρ
      simp only [Tau.rename, Ty.rename]
      exact .top
  | path hp =>
      intro m f Δ ρ
      simpa [Tau.rename, Ty.rename, Path.rename] using
        Tau.Wf.path (hp.rename ρ)
  | sel hp =>
      intro m f Δ ρ
      simpa [Tau.rename, Ty.rename, Path.rename] using
        Tau.Wf.sel (hp.rename ρ)
  | «fun» hdom hcod ihdom ihcod =>
      intro m f Δ ρ
      simpa [Tau.rename, Ty.rename] using
        Tau.Wf.fun (ihdom ρ) (ihcod (Renaming.ext ρ))
  | pair hfst hsnd ihfst ihsnd =>
      intro m f Δ ρ
      simpa [Tau.rename, Ty.rename] using
        Tau.Wf.pair (ihfst ρ) (ihsnd (Renaming.ext ρ))
  | bounds_wf hlo hhi hsub ihlo ihhi =>
      intro m f Δ ρ
      simpa [Tau.rename] using
        Tau.Wf.bounds_wf (ihlo ρ) (ihhi ρ) (hsub.rename ρ)

/-- Term typing is preserved by a context-respecting renaming. -/
theorem Tm.Ty.rename {Γ : Ctx n} {t : Tm n}
    {T : LambdaPFC.Ty n}
    (h : Tm.Ty Γ t T) :
    ∀ {m} {f : FinFun n m} {Δ : Ctx m},
      Renaming Γ f Δ -> Tm.Ty Δ (t.rename f) (T.rename f) := by
  induction h with
  | path hp =>
      intro m f Δ ρ
      simpa [Tm.rename, Ty.rename, Path.rename] using
        Tm.Ty.path (hp.rename ρ)
  | abs ht hwf iht =>
      intro m f Δ ρ
      simpa [Tm.rename, Ty.rename] using
        Tm.Ty.abs (iht (Renaming.ext ρ)) (hwf.rename ρ)
  | app hp hq ihp ihq =>
      intro m f Δ ρ
      simpa [Tm.rename, Ty.rename, Ty.open_rename] using
        Tm.Ty.app (ihp ρ) (ihq ρ)
  | pair hy hz =>
      intro m f Δ ρ
      simpa [Tm.rename, Def.rename, Ty.rename, Tau.rename, Path.rename,
        Path.weaken_rename] using
        Tm.Ty.pair (ρ hy) (ρ hz)
  | tpair hy hwf =>
      intro m f Δ ρ
      simpa only [Tm.rename, Def.rename, LambdaPFC.Ty.rename,
        Tau.rename, Path.rename, ← Tau.weaken_rename] using
        Tm.Ty.tpair (ρ hy) (hwf.rename ρ)
  | «let» hs hwf ht ihs iht =>
      intro m f Δ ρ
      simp only [Tm.rename]
      apply Tm.Ty.let (ihs ρ) (hwf.rename ρ)
      rw [Ty.weaken_rename]
      exact iht (Renaming.ext ρ)
  | typed ht hwf iht =>
      intro m f Δ ρ
      simpa [Tm.rename] using
        Tm.Ty.typed (iht ρ) (hwf.rename ρ)
  | sub ht hsub hwf iht =>
      intro m f Δ ρ
      exact Tm.Ty.sub (iht ρ) (hsub.rename ρ) (hwf.rename ρ)

/-! Weakening corollaries used by store typing and allocation. -/

theorem Path.Ty.weaken (h : Path.Ty Γ p τ) :
    Path.Ty (Γ.snoc S) p.weaken τ.weaken := by
  simpa [Path.weaken, Tau.weaken] using h.rename (Renaming.weaken (S := S))

theorem Tau.Sub.weaken (h : Tau.Sub Γ τ1 τ2) :
    Tau.Sub (Γ.snoc S) τ1.weaken τ2.weaken := by
  simpa [Tau.weaken] using h.rename (Renaming.weaken (S := S))

theorem Tau.Wf.weaken (h : Tau.Wf Γ τ) :
    Tau.Wf (Γ.snoc S) τ.weaken := by
  simpa [Tau.weaken] using h.rename (Renaming.weaken (S := S))

theorem Tm.Ty.weaken (h : Tm.Ty Γ t T) :
    Tm.Ty (Γ.snoc S) t.weaken T.weaken := by
  simpa [Tm.weaken, Ty.weaken] using h.rename (Renaming.weaken (S := S))

/-! Exact variable opening. -/

theorem Renaming.open
    {n : Nat} {Γ : Ctx n} {S : Ty n} {x : Fin n}
    (hx : Ctx.Binds Γ x S) :
    Renaming (Γ.snoc S) (FinFun.openAt x) Γ := by
  intro y T hy
  cases hy with
  | here =>
      simpa only [FinFun.openAt_zero, Ty.weaken, Ty.rename_rename,
        FinFun.openAt_weaken, Ty.rename_id] using hx
  | there hy =>
      simpa only [FinFun.openAt_succ, Ty.weaken, Ty.rename_rename,
        FinFun.openAt_weaken, Ty.rename_id] using hy

theorem Path.Ty.open_var
    (h : Path.Ty (Γ.snoc S) p τ)
    (hx : Ctx.Binds Γ x S) :
    Path.Ty Γ (p.rename (FinFun.openAt x))
      (τ.rename (FinFun.openAt x)) :=
  h.rename (Renaming.open hx)

theorem Tau.Sub.open_var
    (h : Tau.Sub (Γ.snoc S) τ₁ τ₂)
    (hx : Ctx.Binds Γ x S) :
    Tau.Sub Γ (τ₁.rename (FinFun.openAt x))
      (τ₂.rename (FinFun.openAt x)) :=
  h.rename (Renaming.open hx)

theorem Tau.Wf.open_var
    (h : Tau.Wf (Γ.snoc S) τ)
    (hx : Ctx.Binds Γ x S) :
    Tau.Wf Γ (τ.rename (FinFun.openAt x)) :=
  h.rename (Renaming.open hx)

theorem Tm.Ty.open_var
    (h : Tm.Ty (Γ.snoc S) t T)
    (hx : Ctx.Binds Γ x S) :
    Tm.Ty Γ (t.open x) (T.rename (FinFun.openAt x)) := by
  simpa [Tm.open] using h.rename (Renaming.open hx)

theorem Tm.Ty.open_var_weaken
    (h : Tm.Ty (Γ.snoc S) t T.weaken)
    (hx : Ctx.Binds Γ x S) :
    Tm.Ty Γ (t.open x) T := by
  have hT : T.weaken.rename (FinFun.openAt x) = T := by
    rw [LambdaPFC.Ty.weaken,
      LambdaPFC.Ty.rename_rename,
      FinFun.openAt_weaken, LambdaPFC.Ty.rename_id]
  rw [← hT]
  exact h.open_var hx

end LambdaPFC
