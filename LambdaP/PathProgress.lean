import LambdaP.PathPreservation

/-! Totality of proper term-path lookup under the exact-store invariant. -/

namespace LambdaP

private def Path.Lookupable
    (sigma : Store n) (p : Path n) (d : Tau n k) : Prop :=
  match d with
  | .ty _ => exists x, Path.lookup p sigma x
  | .intv _ _ => True

private theorem Path.lookupable_fst
    (hsigma : Store.PreciseTy Gamma sigma)
    (hp : Path.Ty Gamma p (Tau.ty (Ty.Pair S a d)))
    (ih : Path.Lookupable sigma p (Tau.ty (Ty.Pair S a d))) :
    Path.Lookupable sigma p.fst (Tau.ty S) := by
  obtain ⟨x, hx⟩ := ih
  rcases Path.lookup_type_shape hsigma hx hp with hbind | heq
  · obtain ⟨v, hv, hprecise⟩ := hsigma.of_ctx_binds hbind
    cases hprecise with
    | pair => exact ⟨_, .fst hx hv⟩
    | tpair => exact ⟨_, .fst hx hv⟩
  · cases heq

private theorem Path.lookupable_sel_r
    (hsigma : Store.PreciseTy Gamma sigma)
    (hp : Path.Ty Gamma p (Tau.ty (Ty.Pair S a d)))
    (ih : Path.Lookupable sigma p (Tau.ty (Ty.Pair S a d))) :
    Path.Lookupable sigma (p.sel a) (d.open p.fst) := by
  cases d with
  | ty D =>
      obtain ⟨x, hx⟩ := ih
      rcases Path.lookup_type_shape hsigma hx hp with hbind | heq
      · obtain ⟨v, hv, hprecise⟩ := hsigma.of_ctx_binds hbind
        cases hprecise with
        | pair => exact ⟨_, .sel_hit hx hv⟩
      · cases heq
  | intv L U => trivial

private theorem Path.lookupable_sel_l
    (hsigma : Store.PreciseTy Gamma sigma)
    (hp : Path.Ty Gamma p (Tau.ty (Ty.Pair S b d')))
    (htail : Path.Ty Gamma (p.fst.sel a) d)
    (hne : a ≠ b)
    (ihp : Path.Lookupable sigma p (Tau.ty (Ty.Pair S b d')))
    (ihtail : Path.Lookupable sigma (p.fst.sel a) d) :
    Path.Lookupable sigma (p.sel a) d := by
  cases d with
  | ty D =>
      obtain ⟨x, hx⟩ := ihp
      obtain ⟨z, hz⟩ := ihtail
      rcases Path.lookup_type_shape hsigma hx hp with hbind | heq
      · obtain ⟨v, hv, hprecise⟩ := hsigma.of_ctx_binds hbind
        cases hprecise with
        | pair => exact ⟨z, .sel_miss hx hv hne hz⟩
        | tpair => exact ⟨z, .sel_miss hx hv hne hz⟩
      · cases heq
  | intv L U => trivial

private theorem Path.lookupable_precise
    (hsigma : Store.PreciseTy Gamma sigma)
    (hp : Path.Ty Gamma p d) : Path.Lookupable sigma p d := by
  induction hp with
  | var hb => exact ⟨_, .var⟩
  | fst hp ih => exact Path.lookupable_fst hsigma hp (ih hsigma)
  | sel_r hp ih => exact Path.lookupable_sel_r hsigma hp (ih hsigma)
  | sel_l hp htail hne ihp ihtail =>
      exact Path.lookupable_sel_l hsigma hp htail hne (ihp hsigma) (ihtail hsigma)

theorem Path.lookup_progress_precise
    (hsigma : Store.PreciseTy Gamma sigma)
    (hp : Path.Ty Gamma p (Tau.ty T)) :
    exists x, Path.lookup p sigma x :=
  Path.lookupable_precise hsigma hp

theorem Path.reduce_progress_precise
    (hsigma : Store.PreciseTy Gamma sigma)
    (hp : Path.Ty Gamma p (Tau.ty T)) :
    exists x, Path.reduce p sigma x := by
  obtain ⟨x, hx⟩ := Path.lookup_progress_precise hsigma hp
  exact ⟨x, hx.toReduce⟩

end LambdaP
