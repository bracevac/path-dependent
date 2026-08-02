import LambdaP.Repaired.Lookup
import LambdaP.Repaired.PreciseStore
import LambdaP.Repaired.PathFunctionality
import LambdaP.Repaired.TypingInversion

/-! Typing preservation for big-step path lookup under an exact store. -/

namespace LambdaP.Repaired

theorem Ctx.Binds.exists (Gamma : Ctx n) (x : Fin n) :
    exists T, Ctx.Binds Gamma x T := by
  induction Gamma with
  | nil => exact Fin.elim0 x
  | snoc Gamma S ih =>
      refine Fin.cases ?_ (fun y => ?_) x
      · exact ⟨S.weaken, .here⟩
      · obtain ⟨T, hT⟩ := ih y
        exact ⟨T.weaken, .there hT⟩

theorem Ty.weaken_subst_openAt {T : Ty n} {p : Path n} :
    T.weaken.subst (PathSubst.openAt p) = T := by
  simpa [Ty.open] using Ty.weaken_open T p

theorem Path.lookup_type_shape
    (hsigma : Store.PreciseTy Gamma sigma)
    (hr : Path.lookup p sigma x)
    (hp : Path.Ty Gamma p (Tau.ty T)) :
    Ctx.Binds Gamma x T \/ T = Ty.Single (Path.var x) := by
  induction hr generalizing T with
  | var =>
      cases hp with
      | var hT => exact .inl hT
  | fst hr hb ih =>
      cases hp with
      | fst hp =>
          rcases ih hsigma hp with hT | hbad
          · have hv := hsigma.lookup hb hT
            cases hv with
            | pair => exact .inr rfl
            | tpair => exact .inr rfl
          · cases hbad
  | sel_hit hr hb ih =>
      rcases hp.invert_sel with
        ⟨S, k, d, hparent, heq⟩ | ⟨S, b, k, d, hparent, _, hne⟩
      · cases d with
        | ty D =>
            cases heq
            rcases ih hsigma hparent with hT | hbad
            · have hv := hsigma.lookup hb hT
              cases hv with
              | pair => exact .inr rfl
            · cases hbad
        | intv L U => cases heq
      · rcases ih hsigma hparent with hT | hbad
        · have hv := hsigma.lookup hb hT
          cases hv with
          | pair => exact (hne rfl).elim
        · cases hbad
  | sel_miss hr hb hne hin ih ihr =>
      rcases hp.invert_sel with
        ⟨S, k, d, hparent, heq⟩ | ⟨S, b, k, d, hparent, htail, hne'⟩
      · cases d with
        | ty D =>
            cases heq
            rcases ih hsigma hparent with hT | hbad
            · have hv := hsigma.lookup hb hT
              cases hv with
              | pair => exact (hne rfl).elim
            · cases hbad
        | intv L U => cases heq
      · exact ihr hsigma htail

theorem Path.lookup_type_shape_strong
    (hsigma : Store.PreciseTy Gamma sigma)
    (hr : Path.lookup p sigma x)
    (hp : Path.Ty Gamma p (Tau.ty T)) :
    (p = Path.var x /\ Ctx.Binds Gamma x T) \/
      T = Ty.Single (Path.var x) := by
  induction hr generalizing T with
  | var =>
      cases hp with
      | var hT => exact .inl ⟨rfl, hT⟩
  | fst hr hb ih =>
      cases hp with
      | fst hp =>
          rcases ih hsigma hp with hT | hbad
          · have hv := hsigma.lookup hb hT.2
            cases hv with
            | pair => exact .inr rfl
            | tpair => exact .inr rfl
          · cases hbad
  | sel_hit hr hb ih =>
      rcases hp.invert_sel with
        ⟨S, k, d, hparent, heq⟩ | ⟨S, b, k, d, hparent, _, hne⟩
      · cases d with
        | ty D =>
            cases heq
            rcases ih hsigma hparent with hT | hbad
            · have hv := hsigma.lookup hb hT.2
              cases hv with
              | pair => exact .inr rfl
            · cases hbad
        | intv L U => cases heq
      · rcases ih hsigma hparent with hT | hbad
        · have hv := hsigma.lookup hb hT.2
          cases hv with
          | pair => exact (hne rfl).elim
        · cases hbad
  | sel_miss hr hb hne hin ih ihr =>
      rcases hp.invert_sel with
        ⟨S, k, d, hparent, heq⟩ | ⟨S, b, k, d, hparent, htail, hne'⟩
      · cases d with
        | ty D =>
            cases heq
            rcases ih hsigma hparent with hT | hbad
            · have hv := hsigma.lookup hb hT.2
              cases hv with
              | pair => exact (hne rfl).elim
            · cases hbad
        | intv L U => cases heq
      · rcases ihr hsigma htail with hbad | hT
        · cases hbad.1
        · exact .inr hT

theorem Path.lookup_preserves_singleton_alias
    (hsigma : Store.PreciseTy Gamma sigma)
    (hr : Path.lookup p sigma x)
    (hp : Path.Ty Gamma p (Tau.ty T)) :
    Tau.Sub Gamma
      (Tau.ty (Ty.Single (Path.var x)))
      (Tau.ty (Ty.Single p)) := by
  rcases Path.lookup_type_shape_strong hsigma hr hp with hvar | hsingle
  · cases hvar.1
    exact .refl
  · cases hsingle
    exact .symm hp

theorem Path.lookup_preserves_subtyping
    (hsigma : Store.PreciseTy Gamma sigma)
    (hr : Path.lookup p sigma x)
    (hp : Path.Ty Gamma p (Tau.ty T)) :
    Tau.Sub Gamma (Tau.ty (Ty.Single (Path.var x))) (Tau.ty T) := by
  rcases Path.lookup_type_shape hsigma hr hp with hT | hT
  · exact Tau.Sub.widen (Path.Ty.var hT)
  · cases hT
    exact .refl

theorem Path.lookup_preserves_typing
    (hsigma : Store.PreciseTy Gamma sigma)
    (hr : Path.lookup p sigma x)
    (hp : Path.Ty Gamma p (Tau.ty T))
    (hwf : Tau.Wf Gamma (Tau.ty T)) :
    Tm.Ty Gamma (Tm.path (Path.var x)) T := by
  obtain ⟨U, hU⟩ := Ctx.Binds.exists Gamma x
  exact Tm.Ty.sub (Tm.Ty.path (Path.Ty.var hU))
    (Path.lookup_preserves_subtyping hsigma hr hp) hwf

theorem Path.reduce_preserves_typing
    (hsigma : Store.PreciseTy Gamma sigma)
    (hr : Path.reduce p sigma x)
    (hp : Path.Ty Gamma p (Tau.ty T))
    (hwf : Tau.Wf Gamma (Tau.ty T)) :
    Tm.Ty Gamma (Tm.path (Path.var x)) T :=
  Path.lookup_preserves_typing hsigma hr.toLookup hp hwf

theorem Path.reduce_preserves_source_typing
    (hsigma : Store.PreciseTy Gamma sigma)
    (hr : Path.reduce p sigma x)
    (ht : Tm.Ty Gamma (Tm.path p) T) :
    Tm.Ty Gamma (Tm.path (Path.var x)) T := by
  obtain ⟨U, hp, hsub, hwf⟩ := ht.path_inversion rfl
  obtain ⟨X, hx⟩ := Ctx.Binds.exists Gamma x
  exact Tm.Ty.sub (Tm.Ty.path (Path.Ty.var hx))
    (.trans (Path.lookup_preserves_singleton_alias hsigma hr.toLookup hp) hsub)
    hwf

end LambdaP.Repaired
