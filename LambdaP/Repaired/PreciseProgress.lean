import LambdaP.Repaired.Progress
import LambdaP.Repaired.PathProgress
import LambdaP.Repaired.Canonical
import LambdaP.Repaired.TypingInversion

/-! Full progress for states whose store context records exact introduction types. -/

namespace LambdaP.Repaired

theorem Path.reduce_fun_value_precise
    {n : Nat} {Gamma : Ctx n} {sigma : Store n} {p : Path n} {x : Fin n}
    {S : LambdaP.Repaired.Ty n}
    {T : LambdaP.Repaired.Ty (n + 1)}
    (hsigma : Store.PreciseTy Gamma sigma)
    (hr : Path.reduce p sigma x)
    (ht : Tm.Ty Gamma (Tm.path p) (Ty.Fun S T)) :
    exists A body, Store.Binds sigma x (Tm.abs A body) := by
  obtain ⟨U, hp, hsub, hwf⟩ := ht.path_inversion rfl
  rcases Path.lookup_type_shape hsigma hr.toLookup hp with hbind | heq
  · obtain ⟨v, hv, hprecise⟩ := hsigma.of_ctx_binds hbind
    cases hprecise with
    | abs hbody hdom => exact ⟨_, _, hv⟩
    | pair hy hz =>
        have hm : Tau.MayHead Gamma
            (Tau.ty (Ty.Single p)) (.pair _) :=
          .single hp .pair
        have hbad := hsub.mayHead hm
        cases hbad
    | tpair hy hU =>
        have hm : Tau.MayHead Gamma
            (Tau.ty (Ty.Single p)) (.pair _) :=
          .single hp .pair
        have hbad := hsub.mayHead hm
        cases hbad
  · cases heq
    obtain ⟨P, hP⟩ := Ctx.Binds.exists Gamma x
    obtain ⟨v, hv, hprecise⟩ := hsigma.of_ctx_binds hP
    cases hprecise with
    | abs hbody hdom => exact ⟨_, _, hv⟩
    | pair hy hz =>
        have hx : Path.Ty Gamma (Path.var x)
            (Tau.ty (Ty.Pair _ _ _)) := .var hP
        have hmX : Tau.MayHead Gamma
            (Tau.ty (Ty.Single (Path.var x))) (.pair _) :=
          .single hx .pair
        have hmP : Tau.MayHead Gamma
            (Tau.ty (Ty.Single p)) (.pair _) :=
          .single hp hmX
        have hbad := hsub.mayHead hmP
        cases hbad
    | tpair hy hU =>
        have hx : Path.Ty Gamma (Path.var x)
            (Tau.ty (Ty.Pair _ _ _)) := .var hP
        have hmX : Tau.MayHead Gamma
            (Tau.ty (Ty.Single (Path.var x))) (.pair _) :=
          .single hx .pair
        have hmP : Tau.MayHead Gamma
            (Tau.ty (Ty.Single p)) (.pair _) :=
          .single hp hmX
        have hbad := hsub.mayHead hmP
        cases hbad

theorem State.progress_precise
    {n : Nat} {Gamma : Ctx n} {sigma : Store n} {k : Tm.Cont n}
    {t : Tm n} {S R : LambdaP.Repaired.Ty n}
    (hsigma : Store.PreciseTy Gamma sigma)
    (_hk : Tm.Cont.Ty Gamma S k R)
    (ht : Tm.Ty Gamma t S) :
    State.Progress ⟨sigma, k, t⟩ := by
  cases t with
  | path p =>
      obtain ⟨U, hp, hsub, hwf⟩ := ht.path_inversion rfl
      obtain ⟨x, hr⟩ := Path.reduce_progress_precise hsigma hp
      cases p with
      | var y => exact State.Progress.path_var hsigma.toTy y k
      | fst p => exact State.Progress.path hr (by intro h; cases h)
      | sel p a => exact State.Progress.path hr (by intro h; cases h)
  | abs A body =>
      exact State.Progress.value Tm.IsValue.abs sigma k
  | pair y a d =>
      exact State.Progress.value Tm.IsValue.pair sigma k
  | app p q =>
      obtain ⟨A, B, hp, hq⟩ := ht.app_inversion
      obtain ⟨P, hpp, _, _⟩ := hp.path_inversion rfl
      obtain ⟨Q, hpq, _, _⟩ := hq.path_inversion rfl
      obtain ⟨x, hrp⟩ := Path.reduce_progress_precise hsigma hpp
      obtain ⟨y, hrq⟩ := Path.reduce_progress_precise hsigma hpq
      obtain ⟨A', body, hv⟩ := Path.reduce_fun_value_precise hsigma hrp hp
      exact State.Progress.app hrp hrq hv
  | «let» s body =>
      exact State.Progress.let_term sigma k s body
  | typed u A =>
      exact State.Progress.typed sigma k u A

theorem State.Ty.progress_of_precise_store
    {n : Nat} {Gamma : Ctx n} {sigma : Store n} {k : Tm.Cont n}
    {t : Tm n} {R : LambdaP.Repaired.Ty n}
    (h : State.Ty Gamma ⟨sigma, k, t⟩ R)
    (hsigma : Store.PreciseTy Gamma sigma) :
    State.Progress ⟨sigma, k, t⟩ := by
  cases h with
  | ok _ hk ht => exact State.progress_precise hsigma hk ht

end LambdaP.Repaired
