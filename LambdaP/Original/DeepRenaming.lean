import LambdaP.Original.DeepRuntimeTyping

/-!
Relation-respecting renaming for the deep runtime judgments.

A renaming transports both context lookup and the abstract path-conversion
environment.  Under a source binder these two pieces lift in lockstep:
`Renaming.ext` transports the context, while `Path.ConvLift.rename` transports
the relation along `f.ext` without inventing an equation for the fresh
variable.
-/

namespace LambdaP.Original

/-! ## Relation morphisms under binders -/

/-- A morphism of path relations lifts through `Path.ConvLift` and the
extended renaming. -/
theorem Path.ConvLift.rename
    {R : Path.ConvRel n} {R' : Path.ConvRel m}
    {f : FinFun n m}
    (hmap : ∀ {p q}, R p q -> R' (p.rename f) (q.rename f))
    (h : Path.ConvLift R p q) :
    Path.ConvLift R' (p.rename f.ext) (q.rename f.ext) := by
  cases h with
  | bound =>
      exact .bound
  | @weaken p q hpq =>
      simpa only [Path.weaken_rename] using
        (Path.ConvLift.weaken (hmap hpq))

/-! ## Deep conversion and subtyping -/

theorem Tau.DeepConv.rename
    {R : Path.ConvRel n} {R' : Path.ConvRel m}
    {f : FinFun n m}
    (h : Tau.DeepConv R d₁ d₂)
    (hmap : ∀ {p q}, R p q -> R' (p.rename f) (q.rename f)) :
    Tau.DeepConv R' (d₁.rename f) (d₂.rename f) := by
  induction h with
  | refl => exact .refl
  | symm h ih => exact .symm ih
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂
  | replace template hpq =>
      simpa only [Tau.open_rename] using
        (Tau.DeepConv.replace (template.rename f.ext) (hmap hpq))

theorem Tau.DeepSub.rename
    {R : Path.ConvRel n} {R' : Path.ConvRel m}
    {f : FinFun n m}
    (h : Tau.DeepSub Γ R d₁ d₂)
    (ρ : Renaming Γ f Δ)
    (hmap : ∀ {p q}, R p q -> R' (p.rename f) (q.rename f)) :
    Tau.DeepSub Δ R' (d₁.rename f) (d₂.rename f) := by
  induction h with
  | refl => exact .refl
  | source hs => exact .source (hs.rename ρ)
  | conv hc => exact .conv (hc.rename hmap)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

/-! ## Paths -/

theorem Path.DeepCheck.rename
    {R : Path.ConvRel n} {R' : Path.ConvRel m}
    {f : FinFun n m}
    (h : Path.DeepCheck Γ R p d)
    (ρ : Renaming Γ f Δ)
    (hmap : ∀ {p q}, R p q -> R' (p.rename f) (q.rename f)) :
    Path.DeepCheck Δ R' (p.rename f) (d.rename f) := by
  induction h with
  | var hb =>
      simpa only [Path.rename, Tau.rename] using
        (Path.DeepCheck.var (ρ hb))
  | sub hp hs ih =>
      exact .sub ih (hs.rename ρ hmap)
  | fst hp ih =>
      simpa only [Path.rename, Tau.rename, Ty.rename] using
        Path.DeepCheck.fst ih
  | sel_r hp ih =>
      simpa only [Path.rename, Tau.rename, Ty.rename, Tau.open_rename] using
        Path.DeepCheck.sel_r ih
  | sel_l hp htail hne ihp ihtail =>
      simpa only [Path.rename, Tau.rename, Ty.rename] using
        Path.DeepCheck.sel_l ihp ihtail hne

/-! ## Deep well-formedness -/

theorem Tau.DeepWf.rename
    {R : Path.ConvRel n}
    (h : Tau.DeepWf Γ R d) :
    ∀ {m : Nat} {f : FinFun n m} {Δ : Ctx m} {R' : Path.ConvRel m},
      Renaming Γ f Δ ->
      (∀ {p q}, R p q -> R' (p.rename f) (q.rename f)) ->
      Tau.DeepWf Δ R' (d.rename f) := by
  induction h with
  | bot =>
      intro m f Δ R' ρ hmap
      simpa only [Tau.rename, Ty.rename] using
        (Tau.DeepWf.bot (Gamma := Δ) (R := R'))
  | top =>
      intro m f Δ R' ρ hmap
      simpa only [Tau.rename, Ty.rename] using
        (Tau.DeepWf.top (Gamma := Δ) (R := R'))
  | path hp =>
      intro m f Δ R' ρ hmap
      simpa only [Tau.rename, Ty.rename, Path.rename] using
        Tau.DeepWf.path (hp.rename ρ hmap)
  | sel hp =>
      intro m f Δ R' ρ hmap
      simpa only [Tau.rename, Ty.rename, Path.rename] using
        Tau.DeepWf.sel (hp.rename ρ hmap)
  | «fun» hS hT ihS ihT =>
      intro m f Δ R' ρ hmap
      simpa only [Tau.rename, Ty.rename] using
        Tau.DeepWf.fun (ihS ρ hmap)
          (ihT (ρ.ext) (Path.ConvLift.rename hmap))
  | pair hS hd ihS ihd =>
      intro m f Δ R' ρ hmap
      simpa only [Tau.rename, Ty.rename] using
        Tau.DeepWf.pair (ihS ρ hmap)
          (ihd (ρ.ext) (Path.ConvLift.rename hmap))
  | bounds_wf hS hT hs ihS ihT =>
      intro m f Δ R' ρ hmap
      simpa only [Tau.rename] using
        Tau.DeepWf.bounds_wf (ihS ρ hmap) (ihT ρ hmap)
          (hs.rename ρ hmap)

/-! ## Terms -/

theorem Tm.DeepCheck.rename
    {R : Path.ConvRel n}
    (h : Tm.DeepCheck Γ R t T) :
    ∀ {m : Nat} {f : FinFun n m} {Δ : Ctx m} {R' : Path.ConvRel m},
      Renaming Γ f Δ ->
      (∀ {p q}, R p q -> R' (p.rename f) (q.rename f)) ->
      Tm.DeepCheck Δ R' (t.rename f) (T.rename f) := by
  induction h with
  | path hp =>
      intro m f Δ R' ρ hmap
      simpa only [Tm.rename, Ty.rename, Path.rename] using
        Tm.DeepCheck.path (hp.rename ρ hmap)
  | abs ht hwf iht =>
      intro m f Δ R' ρ hmap
      simpa only [Tm.rename, Ty.rename] using
        Tm.DeepCheck.abs
          (iht (ρ.ext) (Path.ConvLift.rename hmap))
          (hwf.rename ρ hmap)
  | app hp hq ihp ihq =>
      intro m f Δ R' ρ hmap
      simpa only [Tm.rename, Ty.rename, Ty.open_rename] using
        Tm.DeepCheck.app (ihp ρ hmap) (ihq ρ hmap)
  | pair hy hz =>
      intro m f Δ R' ρ hmap
      simpa [Tm.rename, Def.rename, Ty.rename, Tau.rename, Path.rename,
        Path.weaken_rename] using
        Tm.DeepCheck.pair (ρ hy) (ρ hz)
  | tpair hy hwf =>
      intro m f Δ R' ρ hmap
      simpa only [Tm.rename, Def.rename, LambdaP.Original.Ty.rename,
        Tau.rename, Path.rename, ← Tau.weaken_rename] using
        Tm.DeepCheck.tpair (ρ hy) (hwf.rename ρ hmap)
  | «let» hs hwf ht ihs iht =>
      intro m f Δ R' ρ hmap
      simp only [Tm.rename]
      apply Tm.DeepCheck.let (ihs ρ hmap) (hwf.rename ρ hmap)
      rw [Ty.weaken_rename]
      exact iht (ρ.ext) (Path.ConvLift.rename hmap)
  | typed ht hwf iht =>
      intro m f Δ R' ρ hmap
      simpa only [Tm.rename] using
        Tm.DeepCheck.typed (iht ρ hmap) (hwf.rename ρ hmap)
  | sub ht hs hwf iht =>
      intro m f Δ R' ρ hmap
      exact Tm.DeepCheck.sub (iht ρ hmap) (hs.rename ρ hmap)
        (hwf.rename ρ hmap)

/-! ## Runtime-store weakening -/

private theorem Path.RuntimeEq.weaken_map
    {n : Nat} {σ : Store n} {p q : Path n}
    (h : Path.RuntimeEq σ p q) (v : Tm n) (hv : v.IsValue) :
    Path.RuntimeEq (Store.val σ v hv)
      (p.rename FinFun.weaken) (q.rename FinFun.weaken) := by
  simpa only [Path.weaken] using h.weaken v hv

theorem Tau.DeepConv.weaken_runtime
    {n : Nat} {k : Kind} {σ : Store n} {d₁ d₂ : Tau n k}
    (h : Tau.DeepConv (Path.RuntimeEq σ) d₁ d₂)
    (v : Tm n) (hv : v.IsValue) :
    Tau.DeepConv (Path.RuntimeEq (Store.val σ v hv))
      d₁.weaken d₂.weaken := by
  simpa only [Tau.weaken] using
    h.rename (fun hpq => Path.RuntimeEq.weaken_map hpq v hv)

theorem Tau.DeepSub.weaken_runtime
    {n : Nat} {k : Kind} {Γ : Ctx n} {σ : Store n}
    {d₁ d₂ : Tau n k}
    (h : Tau.DeepSub Γ (Path.RuntimeEq σ) d₁ d₂)
    (S : LambdaP.Original.Ty n) (v : Tm n) (hv : v.IsValue) :
    Tau.DeepSub (Γ.snoc S) (Path.RuntimeEq (Store.val σ v hv))
      d₁.weaken d₂.weaken := by
  simpa only [Tau.weaken] using
    h.rename (Renaming.weaken (S := S))
      (fun hpq => Path.RuntimeEq.weaken_map hpq v hv)

theorem Path.DeepCheck.weaken_runtime
    {n : Nat} {k : Kind} {Γ : Ctx n} {σ : Store n}
    {p : Path n} {d : Tau n k}
    (h : Path.DeepCheck Γ (Path.RuntimeEq σ) p d)
    (S : LambdaP.Original.Ty n) (v : Tm n) (hv : v.IsValue) :
    Path.DeepCheck (Γ.snoc S) (Path.RuntimeEq (Store.val σ v hv))
      p.weaken d.weaken := by
  simpa only [Path.weaken, Tau.weaken] using
    h.rename (Renaming.weaken (S := S))
      (fun hpq => Path.RuntimeEq.weaken_map hpq v hv)

theorem Tau.DeepWf.weaken_runtime
    {n : Nat} {k : Kind} {Γ : Ctx n} {σ : Store n}
    {d : Tau n k}
    (h : Tau.DeepWf Γ (Path.RuntimeEq σ) d)
    (S : LambdaP.Original.Ty n) (v : Tm n) (hv : v.IsValue) :
    Tau.DeepWf (Γ.snoc S) (Path.RuntimeEq (Store.val σ v hv)) d.weaken := by
  simpa only [Tau.weaken] using
    h.rename (Renaming.weaken (S := S))
      (fun hpq => Path.RuntimeEq.weaken_map hpq v hv)

theorem Tm.DeepCheck.weaken_runtime
    {n : Nat} {Γ : Ctx n} {σ : Store n} {t : Tm n}
    {T : LambdaP.Original.Ty n}
    (h : Tm.DeepCheck Γ (Path.RuntimeEq σ) t T)
    (S : LambdaP.Original.Ty n) (v : Tm n) (hv : v.IsValue) :
    Tm.DeepCheck (Γ.snoc S) (Path.RuntimeEq (Store.val σ v hv))
      t.weaken T.weaken := by
  simpa only [Tm.weaken, Ty.weaken] using
    h.rename (Renaming.weaken (S := S))
      (fun hpq => Path.RuntimeEq.weaken_map hpq v hv)

end LambdaP.Original
