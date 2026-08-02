import LambdaPHistory.Progress
import LambdaPHistory.PathProgress
import LambdaPHistory.Canonical
import LambdaPHistory.TypingInversion

/-!
Full progress for the syntax-directed store fragment.

This theorem is useful both as a checked baseline and as a localization of
the public-store problem: no runtime conversion or DOT-style auxiliary
typing is needed when context entries are the exact value-introduction types.
-/

namespace LambdaPHistory

/-- Under an exact store, a resolving path typed as a function points to an
abstraction.  The proof uses only the two-head interpretation of source
subtyping, so primitive transitivity is harmless. -/
theorem Path.reduce_fun_value_precise
    {n : Nat} {Γ : Ctx n} {σ : Store n} {p : Path n} {x : Fin n}
    {S : LambdaPHistory.Ty n}
    {T : LambdaPHistory.Ty (n + 1)}
    (hσ : Store.PreciseTy Γ σ)
    (hr : Path.reduce p σ x)
    (ht : Tm.Ty Γ (Tm.path p) (Ty.Fun S T)) :
    ∃ A body, Store.Binds σ x (Tm.abs A body) := by
  obtain ⟨U, hp, hsub, hwf⟩ := ht.path_inversion rfl
  rcases Path.lookup_type_shape hσ hr.toLookup hp with hbind | heq
  · obtain ⟨v, hv, hprecise⟩ := hσ.of_ctx_binds hbind
    cases hprecise with
    | abs hbody hdom =>
        exact ⟨_, _, hv⟩
    | pair hy hz =>
        have hm : Tau.MayHead Γ
            (Tau.ty (Ty.Single p)) (.pair _) :=
          .single_ty hp .pair
        have hbad := hsub.mayHead hm
        cases hbad
    | tpair hy hU =>
        have hm : Tau.MayHead Γ
            (Tau.ty (Ty.Single p)) (.pair _) :=
          .single_ty hp .pair
        have hbad := hsub.mayHead hm
        cases hbad
  · cases heq
    obtain ⟨P, hP⟩ := Ctx.Binds.exists Γ x
    obtain ⟨v, hv, hprecise⟩ := hσ.of_ctx_binds hP
    cases hprecise with
    | abs hbody hdom =>
        exact ⟨_, _, hv⟩
    | pair hy hz =>
        have hx : Path.Ty Γ (Path.var x)
            (Tau.ty (Ty.Pair _ _ _)) := .var hP
        have hmX : Tau.MayHead Γ
            (Tau.ty (Ty.Single (Path.var x))) (.pair _) :=
          .single_ty hx .pair
        have hmP : Tau.MayHead Γ
            (Tau.ty (Ty.Single p)) (.pair _) :=
          .single_ty hp hmX
        have hbad := hsub.mayHead hmP
        cases hbad
    | tpair hy hU =>
        have hx : Path.Ty Γ (Path.var x)
            (Tau.ty (Ty.Pair _ _ _)) := .var hP
        have hmX : Tau.MayHead Γ
            (Tau.ty (Ty.Single (Path.var x))) (.pair _) :=
          .single_ty hx .pair
        have hmP : Tau.MayHead Γ
            (Tau.ty (Ty.Single p)) (.pair _) :=
          .single_ty hp hmX
        have hbad := hsub.mayHead hmP
        cases hbad

/-- Every state whose store context records exact value-introduction types is
final or takes a machine step. -/
theorem State.progress_precise
    {n : Nat} {Γ : Ctx n} {σ : Store n} {k : Tm.Cont n}
    {t : Tm n} {S R : LambdaPHistory.Ty n}
    (hσ : Store.PreciseTy Γ σ)
    (_hk : Tm.Cont.Ty Γ S k R)
    (ht : Tm.Ty Γ t S) :
    State.Progress ⟨σ, k, t⟩ := by
  cases t with
  | path p =>
      obtain ⟨U, hp, hsub, hwf⟩ := ht.path_inversion rfl
      obtain ⟨x, hr⟩ := Path.reduce_progress_precise hσ hp
      cases p with
      | var y =>
          exact State.Progress.path_var hσ.toTy y k
      | fst p =>
          exact State.Progress.path hr (by intro h; cases h)
      | sel p a =>
          exact State.Progress.path hr (by intro h; cases h)
  | abs A body =>
      exact State.Progress.value Tm.IsValue.abs σ k
  | pair y a d =>
      exact State.Progress.value Tm.IsValue.pair σ k
  | app p q =>
      obtain ⟨A, B, hp, hq⟩ := ht.app_inversion
      obtain ⟨P, hpp, _, _⟩ := hp.path_inversion rfl
      obtain ⟨Q, hpq, _, _⟩ := hq.path_inversion rfl
      obtain ⟨x, hrp⟩ := Path.reduce_progress_precise hσ hpp
      obtain ⟨y, hrq⟩ := Path.reduce_progress_precise hσ hpq
      obtain ⟨A', body, hv⟩ :=
        Path.reduce_fun_value_precise hσ hrp hp
      exact State.Progress.app hrp hrq hv
  | «let» s body =>
      exact State.Progress.let_term σ k s body
  | typed u A =>
      exact State.Progress.typed σ k u A

/-- State-typing wrapper for the precise-store progress theorem. -/
theorem State.Ty.progress_of_precise_store
    {n : Nat} {Γ : Ctx n} {σ : Store n} {k : Tm.Cont n}
    {t : Tm n} {R : LambdaPHistory.Ty n}
    (h : State.Ty Γ ⟨σ, k, t⟩ R)
    (hσ : Store.PreciseTy Γ σ) :
    State.Progress ⟨σ, k, t⟩ := by
  cases h with
  | ok _ hk ht => exact State.progress_precise hσ hk ht

end LambdaPHistory
