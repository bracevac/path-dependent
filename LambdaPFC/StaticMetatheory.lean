import LambdaPFC.Typing

/-!
Renaming for every static judgment of the calculus.  A renaming is
admissible when it preserves context lookup; lifting it under a dependent
binder supplies the induction hypothesis needed by functions and pairs.
-/

namespace LambdaPFC

noncomputable section

/-- A finite-variable renaming that respects the types recorded by two
contexts. -/
abbrev Renaming (Γ : Ctx n) (f : FinFun n m) (Δ : Ctx m) : Prop :=
  ∀ x, Δ.lookup (f x) = (Γ.lookup x).rename f

/-- Extend a context-respecting renaming below one dependent binder. -/
theorem Renaming.ext (ρ : Renaming Γ f Δ) :
    Renaming (Γ.snoc T) f.ext (Δ.snoc (T.rename f)) := by
  intro x
  refine Fin.cases ?_ (fun i => ?_) x
  · simpa only [Ctx.lookup, FinFun.ext_zero] using
      Ty.weaken_rename T f
  · change (Δ.lookup (f i)).weaken =
      (Γ.lookup i).weaken.rename f.ext
    rw [ρ i, Ty.weaken_rename]

/-- Weakening is a context-respecting renaming. -/
theorem Renaming.weaken : Renaming Γ FinFun.weaken (Γ.snoc S) := by
  intro x
  rfl

/-- Precise path typing is preserved by a context-respecting renaming. -/
def Path.Ty.rename {Γ : Ctx n} {p : Path n} {τ : Tau n k}
    (h : Path.Ty Γ p τ) :
    ∀ {m} {f : FinFun n m} {Δ : Ctx m},
      Renaming Γ f Δ -> Path.Ty Δ (p.rename f) (τ.rename f) := by
  induction h with
  | @var _ x =>
      intro m f Δ ρ
      simpa only [Path.rename, Tau.rename, ρ x] using
        (Path.Ty.var (Γ := Δ) (x := f x))
  | fst hp ih =>
      intro m f Δ ρ
      simpa [Path.rename, LambdaPFC.Ty.rename, Tau.rename] using
        Path.Ty.fst (ih ρ)
  | sel_r hp ih =>
      intro m f Δ ρ
      simpa [Path.rename, LambdaPFC.Ty.rename, Tau.rename,
        Tau.open_rename] using
        Path.Ty.sel_r (ih ρ)
  | sel_l hp htail hne ihp ihtail =>
      intro m f Δ ρ
      simpa [Path.rename, LambdaPFC.Ty.rename, Tau.rename] using
        Path.Ty.sel_l (ihp ρ) (ihtail ρ) hne

/-- Subtyping is preserved by a context-respecting renaming. -/
def Tau.Sub.rename {Γ : Ctx n} {τ1 τ2 : Tau n k}
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
def Tau.Wf.rename {Γ : Ctx n} {τ : Tau n k}
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

/-! Weakening corollaries used by store typing and allocation. -/

def Tau.Sub.weaken (h : Tau.Sub Γ τ1 τ2) :
    Tau.Sub (Γ.snoc S) τ1.weaken τ2.weaken := by
  simpa [Tau.weaken] using h.rename (Renaming.weaken (S := S))

def Tau.Wf.weaken (h : Tau.Wf Γ τ) :
    Tau.Wf (Γ.snoc S) τ.weaken := by
  simpa [Tau.weaken] using h.rename (Renaming.weaken (S := S))

end
end LambdaPFC
