import LambdaP.Lemmas.Subst

/-!
Store-typing weakening: all judgments are monotone under `Sto.Extends`.
Locations are stable names, so this is purely structural — the only
interesting cases are the `var_free` lookups.
-/

namespace LambdaP

mutual

/-- Subtyping is monotone under store-typing extension. -/
theorem Sub.sto_weaken {Θ Θ' : Sto} {Γ : Ctx s} {τ1 τ2 : Tau s}
    (h : Sub Θ Γ τ1 τ2) (hext : Θ'.Extends Θ) : Sub Θ' Γ τ1 τ2 :=
  match h with
  | .refl => .refl
  | .trans h1 h2 => .trans (h1.sto_weaken hext) (h2.sto_weaken hext)
  | .bot => .bot
  | .top => .top
  | .var_bound hx => .var_bound hx
  | .var_free hl => .var_free (hext hl)
  | .symm hw h1 => .symm (hw.sto_weaken hext) (h1.sto_weaken hext)
  | .fst_tm h1 => .fst_tm (h1.sto_weaken hext)
  | .fst_ty h1 => .fst_ty (h1.sto_weaken hext)
  | .sel_tm h1 => .sel_tm (h1.sto_weaken hext)
  | .sel_hi h1 h2 => .sel_hi (h1.sto_weaken hext) (h2.sto_weaken hext)
  | .sel_lo hw h1 h2 =>
    .sel_lo (hw.sto_weaken hext) (h1.sto_weaken hext) (h2.sto_weaken hext)
  | .arrow h1 h2 => .arrow (h1.sto_weaken hext) (h2.sto_weaken hext)
  | .pair_tm h1 h2 => .pair_tm (h1.sto_weaken hext) (h2.sto_weaken hext)
  | .pair_ty h1 h2 => .pair_ty (h1.sto_weaken hext) (h2.sto_weaken hext)
  | .ival h1 h2 h3 =>
    .ival (h1.sto_weaken hext) (h2.sto_weaken hext) (h3.sto_weaken hext)
  | .repl hwp hwq h1 h2 =>
    .repl (hwp.sto_weaken hext) (hwq.sto_weaken hext)
      (h1.sto_weaken hext) (h2.sto_weaken hext)

/-- Path wellformedness is monotone under store-typing extension. -/
theorem Path.Wf.sto_weaken {Θ Θ' : Sto} {Γ : Ctx s} {p : Path s}
    (h : Path.Wf Θ Γ p) (hext : Θ'.Extends Θ) : Path.Wf Θ' Γ p :=
  match h with
  | .var_bound hx => .var_bound hx
  | .var_free hl => .var_free (hext hl)
  | .fst_tm h1 hsub => .fst_tm (h1.sto_weaken hext) (hsub.sto_weaken hext)
  | .fst_ty h1 hsub => .fst_ty (h1.sto_weaken hext) (hsub.sto_weaken hext)
  | .sel h1 hsub => .sel (h1.sto_weaken hext) (hsub.sto_weaken hext)

end

/-- Type wellformedness is monotone under store-typing extension. -/
theorem Wf.sto_weaken {Θ Θ' : Sto} {Γ : Ctx s} {τ : Tau s}
    (h : Wf Θ Γ τ) (hext : Θ'.Extends Θ) : Wf Θ' Γ τ := by
  induction h with
  | bot => exact .bot
  | top => exact .top
  | single hp => exact .single (hp.sto_weaken hext)
  | tsel hp hsub => exact .tsel (hp.sto_weaken hext) (hsub.sto_weaken hext)
  | arrow _ _ ih1 ih2 => exact .arrow (ih1 hext) (ih2 hext)
  | pair_tm _ _ ih1 ih2 => exact .pair_tm (ih1 hext) (ih2 hext)
  | pair_ty _ _ ih1 ih2 => exact .pair_ty (ih1 hext) (ih2 hext)
  | intv _ _ hsub ih1 ih2 => exact .intv (ih1 hext) (ih2 hext) (hsub.sto_weaken hext)

/-- Term typing is monotone under store-typing extension. -/
theorem HasType.sto_weaken {Θ Θ' : Sto} {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : HasType Θ Γ t T) (hext : Θ'.Extends Θ) : HasType Θ' Γ t T := by
  induction h with
  | path hp => exact .path (hp.sto_weaken hext)
  | sub _ hsub hwf ih => exact .sub (ih hext) (hsub.sto_weaken hext) (hwf.sto_weaken hext)
  | abs hwf _ ih => exact .abs (hwf.sto_weaken hext) (ih hext)
  | app _ _ ih1 ih2 => exact .app (ih1 hext) (ih2 hext)
  | pair_tm hy hz => exact .pair_tm (hy.sto_weaken hext) (hz.sto_weaken hext)
  | pair_ty hy hwf => exact .pair_ty (hy.sto_weaken hext) (hwf.sto_weaken hext)
  | letin _ hwf _ ih1 ih2 => exact .letin (ih1 hext) (hwf.sto_weaken hext) (ih2 hext)
  | typed _ hwf ih => exact .typed (ih hext) (hwf.sto_weaken hext)

/-- Precise value typing is monotone under store-typing extension. -/
theorem Val.PreciseTy.sto_weaken {Θ Θ' : Sto} {v : Tm 0} {T : Ty 0}
    (h : Val.PreciseTy Θ v T) (hext : Θ'.Extends Θ) : Val.PreciseTy Θ' v T := by
  cases h with
  | abs hwf hty => exact .abs (hwf.sto_weaken hext) (hty.sto_weaken hext)
  | pair_tm h1 h2 => exact .pair_tm (h1.sto_weaken hext) (h2.sto_weaken hext)
  | pair_ty h1 hwf => exact .pair_ty (h1.sto_weaken hext) (hwf.sto_weaken hext)

end LambdaP
