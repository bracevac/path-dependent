import LambdaPHistory.PathPreservation

/-!
Totality of term-path lookup under the syntax-directed store invariant.

This is the progress counterpart of `Path.reduce_preserves_typing`.  It is
intentionally first stated for `Store.PreciseTy`: exact context entries make
the constructor inversion direct.  The public-store theorem needs the
separate canonical-shape argument recorded in the soundness report.
-/

namespace LambdaPHistory

private def Path.Lookupable
    (σ : Store n) (p : Path n) (d : Tau n k) : Prop :=
  match d with
  | .ty _ => ∃ x, Path.lookup p σ x
  | .intv _ _ => True

private theorem Path.lookupable_fst
    (hσ : Store.PreciseTy Γ σ)
    (hp : Path.Ty Γ p (Tau.ty (Ty.Pair S a d)))
    (ih : Path.Lookupable σ p (Tau.ty (Ty.Pair S a d))) :
    Path.Lookupable σ p.fst (Tau.ty S) := by
  obtain ⟨x, hx⟩ := ih
  rcases Path.lookup_type_shape hσ hx hp with hbind | heq
  · obtain ⟨v, hv, hprecise⟩ := hσ.of_ctx_binds hbind
    cases hprecise with
    | pair =>
        exact ⟨_, .fst hx hv⟩
    | tpair =>
        exact ⟨_, .fst hx hv⟩
  · cases heq

private theorem Path.lookupable_sel_r
    (hσ : Store.PreciseTy Γ σ)
    (hp : Path.Ty Γ p (Tau.ty (Ty.Pair S a d)))
    (ih : Path.Lookupable σ p (Tau.ty (Ty.Pair S a d))) :
    Path.Lookupable σ (p.sel a) (d.open p.fst) := by
  cases d with
  | ty D =>
      obtain ⟨x, hx⟩ := ih
      rcases Path.lookup_type_shape hσ hx hp with hbind | heq
      · obtain ⟨v, hv, hprecise⟩ := hσ.of_ctx_binds hbind
        cases hprecise with
        | pair =>
            exact ⟨_, .sel_hit hx hv⟩
      · cases heq
  | intv L U =>
      trivial

private theorem Path.lookupable_sel_l
    (hσ : Store.PreciseTy Γ σ)
    (hp : Path.Ty Γ p (Tau.ty (Ty.Pair S b d')))
    (htail : Path.Ty Γ (p.fst.sel a) d)
    (hne : a ≠ b)
    (ihp : Path.Lookupable σ p (Tau.ty (Ty.Pair S b d')))
    (ihtail : Path.Lookupable σ (p.fst.sel a) d) :
    Path.Lookupable σ (p.sel a) d := by
  cases d with
  | ty D =>
      obtain ⟨x, hx⟩ := ihp
      obtain ⟨z, hz⟩ := ihtail
      rcases Path.lookup_type_shape hσ hx hp with hbind | heq
      · obtain ⟨v, hv, hprecise⟩ := hσ.of_ctx_binds hbind
        cases hprecise with
        | pair =>
            exact ⟨z, .sel_miss hx hv hne hz⟩
        | tpair =>
            exact ⟨z, .sel_miss hx hv hne hz⟩
      · cases heq
  | intv L U =>
      trivial

private theorem Path.lookupable_precise
    (hσ : Store.PreciseTy Γ σ)
    (hp : Path.Ty Γ p d) : Path.Lookupable σ p d := by
  induction hp with
  | var hb =>
      exact ⟨_, .var⟩
  | fst hp ih =>
      exact Path.lookupable_fst hσ hp (ih hσ)
  | sel_r hp ih =>
      exact Path.lookupable_sel_r hσ hp (ih hσ)
  | sel_l hp htail hne ihp ihtail =>
      exact Path.lookupable_sel_l hσ hp htail hne (ihp hσ) (ihtail hσ)

/-- A precisely typed path of proper kind resolves to a store location. -/
theorem Path.lookup_progress_precise
    (hσ : Store.PreciseTy Γ σ)
    (hp : Path.Ty Γ p (Tau.ty T)) :
    ∃ x, Path.lookup p σ x :=
  Path.lookupable_precise hσ hp

/-- The same totality statement for the literal historical reduction. -/
theorem Path.reduce_progress_precise
    (hσ : Store.PreciseTy Γ σ)
    (hp : Path.Ty Γ p (Tau.ty T)) :
    ∃ x, Path.reduce p σ x := by
  obtain ⟨x, hx⟩ := Path.lookup_progress_precise hσ hp
  exact ⟨x, hx.toReduce⟩

end LambdaPHistory
