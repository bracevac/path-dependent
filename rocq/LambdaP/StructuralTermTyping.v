From PathDependent.LambdaP Require Import FinFun Syntax Context Typing
  Renaming ScopedRuntimeEq Opening StructuralRuntimeTyping.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Local Coercion FinFun.apply : FinFun.t >-> Funclass.

(** Generalized-type well-formedness with structural path and subtyping
    premises. *)
Inductive Tau_StructWf : forall {n : nat}, Ctx n ->
    (Path n -> Path n -> Prop) -> forall {k : Kind}, Tau n k -> Prop :=
| tau_struct_wf_bot {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) :
    Tau_StructWf G R (tau_ty ty_bot)
| tau_struct_wf_top {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) :
    Tau_StructWf G R (tau_ty ty_top)
| tau_struct_wf_path {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (p : Path n) (T : Ty n) :
    Path_StructCheck G R p (tau_ty T) ->
    Tau_StructWf G R (tau_ty (ty_single p))
| tau_struct_wf_sel {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (p : Path n) (S0 : Ty n)
    (T U : Ty (S n)) (A : Name) :
    Path_StructCheck G R p
      (tau_ty (ty_pair S0 A (tau_intv T U))) ->
    Tau_StructWf G R (tau_ty (ty_tsel p A))
| tau_struct_wf_fun {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (S0 : Ty n) (T : Ty (S n)) :
    Tau_StructWf G R (tau_ty S0) ->
    Tau_StructWf (ctx_snoc G S0) (Path_ScopedLift R) (tau_ty T) ->
    Tau_StructWf G R (tau_ty (ty_fun S0 T))
| tau_struct_wf_pair {n : nat} {k : Kind} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (S0 : Ty n) (a : Name)
    (d : Tau (S n) k) :
    Tau_StructWf G R (tau_ty S0) ->
    Tau_StructWf (ctx_snoc G S0) (Path_ScopedLift R) d ->
    Tau_StructWf G R (tau_ty (ty_pair S0 a d))
| tau_struct_wf_bounds {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (S0 T : Ty n) :
    Tau_StructWf G R (tau_ty S0) ->
    Tau_StructWf G R (tau_ty T) ->
    Tau_StructSub G R (tau_ty S0) (tau_ty T) ->
    Tau_StructWf G R (tau_intv S0 T).

Arguments tau_struct_wf_bot {n} G R.
Arguments tau_struct_wf_top {n} G R.
Arguments tau_struct_wf_path {n} G R p T _.
Arguments tau_struct_wf_sel {n} G R p S0 T U A _.
Arguments tau_struct_wf_fun {n} G R S0 T _ _.
Arguments tau_struct_wf_pair {n k} G R S0 a d _ _.
Arguments tau_struct_wf_bounds {n} G R S0 T _ _ _.

(** Every source well-formedness derivation embeds, including premises below
    binders. *)
Theorem Tau_StructWf_of_source {n : nat} {G : Ctx n} {k : Kind}
    {d : Tau n k} (H : Tau_Wf G d) :
    forall R : Path n -> Path n -> Prop, Tau_StructWf G R d.
Proof.
  induction H; intro R.
  - apply tau_struct_wf_bot.
  - apply tau_struct_wf_top.
  - eapply tau_struct_wf_path. exact (Path_StructCheck_of_source H R).
  - eapply tau_struct_wf_sel. exact (Path_StructCheck_of_source H R).
  - apply tau_struct_wf_fun.
    + exact (IHTau_Wf1 R).
    + exact (IHTau_Wf2 (Path_ScopedLift R)).
  - apply tau_struct_wf_pair.
    + exact (IHTau_Wf1 R).
    + exact (IHTau_Wf2 (Path_ScopedLift R)).
  - apply tau_struct_wf_bounds.
    + exact (IHTau_Wf1 R).
    + exact (IHTau_Wf2 R).
    + exact (Tau_StructSub_of_source H1 R).
Qed.

(** Term checking with every source constructor and subsidiary judgment
    represented structurally. *)
Inductive Tm_StructCheck : forall {n : nat}, Ctx n ->
    (Path n -> Path n -> Prop) -> Tm n -> Ty n -> Prop :=
| tm_struct_check_path {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (p : Path n) (T : Ty n) :
    Path_StructCheck G R p (tau_ty T) ->
    Tm_StructCheck G R (tm_path p) (ty_single p)
| tm_struct_check_abs {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (S0 : Ty n)
    (t : Tm (S n)) (T : Ty (S n)) :
    Tm_StructCheck (ctx_snoc G S0) (Path_ScopedLift R) t T ->
    Tau_StructWf G R (tau_ty S0) ->
    Tm_StructCheck G R (tm_abs S0 t) (ty_fun S0 T)
| tm_struct_check_app {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (p q : Path n)
    (S0 : Ty n) (T : Ty (S n)) :
    Tm_StructCheck G R (tm_path p) (ty_fun S0 T) ->
    Tm_StructCheck G R (tm_path q) S0 ->
    Tm_StructCheck G R (tm_app p q) (Ty_open T q)
| tm_struct_check_pair {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (y z : Fin.t n)
    (S0 T : Ty n) (a : Name) :
    Ctx_Binds G y S0 -> Ctx_Binds G z T ->
    Tm_StructCheck G R (tm_pair y a (def_val z))
      (ty_pair (ty_single (path_var y)) a
        (tau_ty (ty_single (Path_weaken (path_var z)))))
| tm_struct_check_tpair {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (y : Fin.t n)
    (S0 T : Ty n) (A : Name) :
    Ctx_Binds G y S0 -> Tau_StructWf G R (tau_ty T) ->
    Tm_StructCheck G R (tm_pair y A (def_type T))
      (ty_pair (ty_single (path_var y)) A
        (Tau_weaken (tau_intv T T)))
| tm_struct_check_let {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (s : Tm n) (S0 T : Ty n)
    (t : Tm (S n)) :
    Tm_StructCheck G R s S0 ->
    Tau_StructWf G R (tau_ty T) ->
    Tm_StructCheck (ctx_snoc G S0) (Path_ScopedLift R)
      t (Ty_weaken T) ->
    Tm_StructCheck G R (tm_let s t) T
| tm_struct_check_typed {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (t : Tm n) (T : Ty n) :
    Tm_StructCheck G R t T -> Tau_StructWf G R (tau_ty T) ->
    Tm_StructCheck G R (tm_typed t T) T
| tm_struct_check_sub {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (t : Tm n) (S0 T : Ty n) :
    Tm_StructCheck G R t S0 ->
    Tau_StructSub G R (tau_ty S0) (tau_ty T) ->
    Tau_StructWf G R (tau_ty T) ->
    Tm_StructCheck G R t T.

Arguments tm_struct_check_path {n} G R p T _.
Arguments tm_struct_check_abs {n} G R S0 t T _ _.
Arguments tm_struct_check_app {n} G R p q S0 T _ _.
Arguments tm_struct_check_pair {n} G R y z S0 T a _ _.
Arguments tm_struct_check_tpair {n} G R y S0 T A _ _.
Arguments tm_struct_check_let {n} G R s S0 T t _ _ _.
Arguments tm_struct_check_typed {n} G R t T _ _.
Arguments tm_struct_check_sub {n} G R t S0 T _ _ _.

(** Every source term-typing derivation embeds at every abstract relation. *)
Theorem Tm_StructCheck_of_source {n : nat} {G : Ctx n}
    {t : Tm n} {T : Ty n} (H : Tm_Ty G t T) :
    forall R : Path n -> Path n -> Prop, Tm_StructCheck G R t T.
Proof.
  induction H; intro R.
  - eapply tm_struct_check_path. exact (Path_StructCheck_of_source H R).
  - apply tm_struct_check_abs.
    + exact (IHTm_Ty (Path_ScopedLift R)).
    + exact (Tau_StructWf_of_source H0 R).
  - eapply tm_struct_check_app;
      [exact (IHTm_Ty1 R) | exact (IHTm_Ty2 R)].
  - eapply tm_struct_check_pair; eassumption.
  - eapply tm_struct_check_tpair.
    + eassumption.
    + exact (Tau_StructWf_of_source H0 R).
  - eapply tm_struct_check_let.
    + exact (IHTm_Ty1 R).
    + exact (Tau_StructWf_of_source H0 R).
    + exact (IHTm_Ty2 (Path_ScopedLift R)).
  - apply tm_struct_check_typed.
    + exact (IHTm_Ty R).
    + exact (Tau_StructWf_of_source H0 R).
  - eapply tm_struct_check_sub.
    + exact (IHTm_Ty R).
    + exact (Tau_StructSub_of_source H0 R).
    + exact (Tau_StructWf_of_source H1 R).
Qed.

(** Structural well-formedness is preserved by an exact context renaming
    and a compatible relation morphism. *)
Theorem Tau_StructWf_renameExact {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {k : Kind} {d : Tau n k}
    (H : Tau_StructWf G R d) :
    forall {m : nat} {f : FinFun.t n m} {D : Ctx m}
      {E : Path m -> Path m -> Prop},
      Renaming G f D -> Path_RelHom R E f ->
      Tau_StructWf D E (Tau_rename d f).
Proof.
  induction H; intros m f D E rho Hrel;
    cbn [Path_rename Ty_rename Tau_rename].
  - apply tau_struct_wf_bot.
  - apply tau_struct_wf_top.
  - eapply tau_struct_wf_path.
    exact (Path_StructCheck_renameExact H rho Hrel).
  - eapply tau_struct_wf_sel.
    exact (Path_StructCheck_renameExact H rho Hrel).
  - apply tau_struct_wf_fun.
    + exact (IHTau_StructWf1 _ _ _ _ rho Hrel).
    + exact (IHTau_StructWf2 _ _ _ _ (Renaming_ext rho)
        (Path_RelHom_scoped Hrel)).
  - apply tau_struct_wf_pair.
    + exact (IHTau_StructWf1 _ _ _ _ rho Hrel).
    + exact (IHTau_StructWf2 _ _ _ _ (Renaming_ext rho)
        (Path_RelHom_scoped Hrel)).
  - apply tau_struct_wf_bounds.
    + exact (IHTau_StructWf1 _ _ _ _ rho Hrel).
    + exact (IHTau_StructWf2 _ _ _ _ rho Hrel).
    + exact (Tau_StructSub_renameExact H1 rho Hrel).
Qed.

(** Structural term checking is preserved by exact context renaming. *)
Theorem Tm_StructCheck_renameExact {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {t : Tm n} {T : Ty n}
    (H : Tm_StructCheck G R t T) :
    forall {m : nat} {f : FinFun.t n m} {D : Ctx m}
      {E : Path m -> Path m -> Prop},
      Renaming G f D -> Path_RelHom R E f ->
      Tm_StructCheck D E (Tm_rename t f) (Ty_rename T f).
Proof.
  induction H; intros m f D E rho Hrel.
  - cbn [Tm_rename Ty_rename Path_rename].
    eapply tm_struct_check_path.
    exact (Path_StructCheck_renameExact H rho Hrel).
  - cbn [Tm_rename Ty_rename]. apply tm_struct_check_abs.
    + exact (IHTm_StructCheck _ _ _ _ (Renaming_ext rho)
        (Path_RelHom_scoped Hrel)).
    + exact (Tau_StructWf_renameExact H0 rho Hrel).
  - cbn [Tm_rename Ty_rename]. rewrite Ty_open_rename.
    eapply tm_struct_check_app.
    + exact (IHTm_StructCheck1 _ _ _ _ rho Hrel).
    + exact (IHTm_StructCheck2 _ _ _ _ rho Hrel).
  - cbn [Tm_rename Def_rename Ty_rename Tau_rename Path_rename].
    rewrite <- Path_weaken_rename.
    eapply tm_struct_check_pair.
    + exact (rho y S0 H).
    + exact (rho z T H0).
  - cbn [Tm_rename Def_rename Ty_rename Tau_rename Path_rename].
    rewrite <- Tau_weaken_rename.
    eapply tm_struct_check_tpair.
    + exact (rho y S0 H).
    + exact (Tau_StructWf_renameExact H0 rho Hrel).
  - cbn [Tm_rename]. eapply tm_struct_check_let.
    + exact (IHTm_StructCheck1 _ _ _ _ rho Hrel).
    + exact (Tau_StructWf_renameExact H0 rho Hrel).
    + rewrite Ty_weaken_rename.
      exact (IHTm_StructCheck2 _ _ _ _ (Renaming_ext rho)
        (Path_RelHom_scoped Hrel)).
  - cbn [Tm_rename]. apply tm_struct_check_typed.
    + exact (IHTm_StructCheck _ _ _ _ rho Hrel).
    + exact (Tau_StructWf_renameExact H0 rho Hrel).
  - eapply tm_struct_check_sub.
    + exact (IHTm_StructCheck _ _ _ _ rho Hrel).
    + exact (Tau_StructSub_renameExact H0 rho Hrel).
    + exact (Tau_StructWf_renameExact H1 rho Hrel).
Qed.

(** Structural well-formedness is stable under a structural variable
    environment and compatible relation morphism. *)
Theorem Tau_StructWf_rename {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {k : Kind} {d : Tau n k}
    (H : Tau_StructWf G R d) :
    forall {m : nat} {f : FinFun.t n m} {D : Ctx m}
      {E : Path m -> Path m -> Prop},
      Path_StructRenaming G f D E -> Path_RelHom R E f ->
      Tau_StructWf D E (Tau_rename d f).
Proof.
  induction H; intros m f D E rho Hrel;
    cbn [Path_rename Ty_rename Tau_rename].
  - apply tau_struct_wf_bot.
  - apply tau_struct_wf_top.
  - eapply tau_struct_wf_path.
    exact (Path_StructCheck_rename H rho Hrel).
  - eapply tau_struct_wf_sel.
    exact (Path_StructCheck_rename H rho Hrel).
  - apply tau_struct_wf_fun.
    + exact (IHTau_StructWf1 _ _ _ _ rho Hrel).
    + exact (IHTau_StructWf2 _ _ _ _ (Path_StructRenaming_ext rho)
        (Path_RelHom_scoped Hrel)).
  - apply tau_struct_wf_pair.
    + exact (IHTau_StructWf1 _ _ _ _ rho Hrel).
    + exact (IHTau_StructWf2 _ _ _ _ (Path_StructRenaming_ext rho)
        (Path_RelHom_scoped Hrel)).
  - apply tau_struct_wf_bounds.
    + exact (IHTau_StructWf1 _ _ _ _ rho Hrel).
    + exact (IHTau_StructWf2 _ _ _ _ rho Hrel).
    + exact (Tau_StructSub_rename H1 rho Hrel).
Qed.

(** Structural term checking is stable under structural renaming. *)
Theorem Tm_StructCheck_rename {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {t : Tm n} {T : Ty n}
    (H : Tm_StructCheck G R t T) :
    forall {m : nat} {f : FinFun.t n m} {D : Ctx m}
      {E : Path m -> Path m -> Prop},
      Path_StructRenaming G f D E -> Path_RelHom R E f ->
      Tm_StructCheck D E (Tm_rename t f) (Ty_rename T f).
Proof.
  induction H; intros m f D E rho Hrel.
  - cbn [Tm_rename Ty_rename Path_rename].
    eapply tm_struct_check_path.
    exact (Path_StructCheck_rename H rho Hrel).
  - cbn [Tm_rename Ty_rename]. apply tm_struct_check_abs.
    + exact (IHTm_StructCheck _ _ _ _ (Path_StructRenaming_ext rho)
        (Path_RelHom_scoped Hrel)).
    + exact (Tau_StructWf_rename H0 rho Hrel).
  - cbn [Tm_rename Ty_rename]. rewrite Ty_open_rename.
    eapply tm_struct_check_app.
    + exact (IHTm_StructCheck1 _ _ _ _ rho Hrel).
    + exact (IHTm_StructCheck2 _ _ _ _ rho Hrel).
  - destruct (Ctx_Binds_exists D (f y)) as [Sy Hy].
    destruct (Ctx_Binds_exists D (f z)) as [Sz Hz].
    cbn [Tm_rename Def_rename Ty_rename Tau_rename Path_rename].
    rewrite <- Path_weaken_rename.
    eapply tm_struct_check_pair; eassumption.
  - destruct (Ctx_Binds_exists D (f y)) as [Sy Hy].
    cbn [Tm_rename Def_rename Ty_rename Tau_rename Path_rename].
    rewrite <- Tau_weaken_rename.
    eapply tm_struct_check_tpair.
    + exact Hy.
    + exact (Tau_StructWf_rename H0 rho Hrel).
  - cbn [Tm_rename]. eapply tm_struct_check_let.
    + exact (IHTm_StructCheck1 _ _ _ _ rho Hrel).
    + exact (Tau_StructWf_rename H0 rho Hrel).
    + rewrite Ty_weaken_rename.
      exact (IHTm_StructCheck2 _ _ _ _ (Path_StructRenaming_ext rho)
        (Path_RelHom_scoped Hrel)).
  - cbn [Tm_rename]. apply tm_struct_check_typed.
    + exact (IHTm_StructCheck _ _ _ _ rho Hrel).
    + exact (Tau_StructWf_rename H0 rho Hrel).
  - eapply tm_struct_check_sub.
    + exact (IHTm_StructCheck _ _ _ _ rho Hrel).
    + exact (Tau_StructSub_rename H0 rho Hrel).
    + exact (Tau_StructWf_rename H1 rho Hrel).
Qed.

(** The information retained by structurally typing a path term: a precise
    path classification, the complete singleton-to-result subtyping chain,
    and well-formedness of the observed result. *)
Inductive Tm_StructPathPackage {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (p : Path n) (T : Ty n) : Prop :=
| tm_struct_path_package_intro (precise : Ty n) :
    Path_StructCheck G R p (tau_ty precise) ->
    Tau_StructSub G R (tau_ty (ty_single p)) (tau_ty T) ->
    Tau_StructWf G R (tau_ty T) ->
    Tm_StructPathPackage G R p T.

Arguments tm_struct_path_package_intro {n G R p T} precise _ _ _.

(** A first-order view of the path constructor, used to obtain ordinary
    constructor injectivity without dependent inversion of [Tm]. *)
Definition tm_path_payload {n : nat} (t : Tm n) : option (Path n) :=
  match t in Tm n' return option (Path n') with
  | tm_path p => Some p
  | tm_abs _ _ => None
  | tm_pair _ _ _ => None
  | tm_app _ _ => None
  | tm_let _ _ => None
  | tm_typed _ _ => None
  end.

(** Inversion of a structurally checked path term gathers all trailing
    subsumption into the singleton-to-result chain. *)
Theorem Tm_StructCheck_path_inversion {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {t : Tm n} {T : Ty n}
    (H : Tm_StructCheck G R t T) :
    forall p : Path n, t = tm_path p -> Tm_StructPathPackage G R p T.
Proof.
  induction H; intros target_path Heq.
  - pose proof (f_equal tm_path_payload Heq) as Eshape.
    cbn [tm_path_payload] in Eshape. injection Eshape as Ep.
    subst target_path.
    eapply tm_struct_path_package_intro.
    + exact H.
    + apply tau_struct_sub_refl.
    + eapply tau_struct_wf_path. exact H.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - destruct (IHTm_StructCheck target_path Heq) as [U Hp Hbase Hwf].
    eapply tm_struct_path_package_intro.
    + exact Hp.
    + eapply tau_struct_sub_trans; [exact Hbase | exact H0].
    + exact H1.
Qed.

(** Exact context lookup suffices to open structural well-formedness. *)
Theorem Tau_StructWf_open_var_exact {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {S0 : Ty n} {x : Fin.t n}
    {k : Kind} {d : Tau (S n) k}
    (H : Tau_StructWf (ctx_snoc G S0) (Path_ScopedLift R) d)
    (HR : Path_IsEquivCongr R) (Hx : Ctx_Binds G x S0) :
    Tau_StructWf G R (Tau_rename d (FinFun.openAt x)).
Proof.
  exact (Tau_StructWf_renameExact H (Renaming_open Hx)
    (Path_RelHom_openAt HR x)).
Qed.

(** Exact context lookup suffices to open structural term checking. *)
Theorem Tm_StructCheck_open_var_exact {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {S0 : Ty n} {x : Fin.t n}
    {t : Tm (S n)} {T : Ty (S n)}
    (H : Tm_StructCheck (ctx_snoc G S0) (Path_ScopedLift R) t T)
    (HR : Path_IsEquivCongr R) (Hx : Ctx_Binds G x S0) :
    Tm_StructCheck G R (Tm_open t x)
      (Ty_rename T (FinFun.openAt x)).
Proof.
  unfold Tm_open.
  exact (Tm_StructCheck_renameExact H (Renaming_open Hx)
    (Path_RelHom_openAt HR x)).
Qed.

(** Structural checking of the replacement variable suffices to open
    well-formedness. *)
Theorem Tau_StructWf_open_var {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {S0 : Ty n} {x : Fin.t n}
    {k : Kind} {d : Tau (S n) k}
    (H : Tau_StructWf (ctx_snoc G S0) (Path_ScopedLift R) d)
    (HR : Path_IsEquivCongr R)
    (Hx : Path_StructCheck G R (path_var x) (tau_ty S0)) :
    Tau_StructWf G R (Tau_rename d (FinFun.openAt x)).
Proof.
  exact (Tau_StructWf_rename H (Path_StructRenaming_openAt Hx)
    (Path_RelHom_openAt HR x)).
Qed.

(** Structural checking of the replacement variable suffices to open a
    term derivation. *)
Theorem Tm_StructCheck_open_var {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {S0 : Ty n} {x : Fin.t n}
    {t : Tm (S n)} {T : Ty (S n)}
    (H : Tm_StructCheck (ctx_snoc G S0) (Path_ScopedLift R) t T)
    (HR : Path_IsEquivCongr R)
    (Hx : Path_StructCheck G R (path_var x) (tau_ty S0)) :
    Tm_StructCheck G R (Tm_open t x)
      (Ty_rename T (FinFun.openAt x)).
Proof.
  unfold Tm_open.
  exact (Tm_StructCheck_rename H (Path_StructRenaming_openAt Hx)
    (Path_RelHom_openAt HR x)).
Qed.

(** Singleton promotion supplies the operational opening premise for
    structural well-formedness. *)
Theorem Tau_StructWf_open_var_of_singleton {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {S0 U : Ty n} {x : Fin.t n}
    {k : Kind} {d : Tau (S n) k}
    (H : Tau_StructWf (ctx_snoc G S0) (Path_ScopedLift R) d)
    (HR : Path_IsEquivCongr R)
    (Hx : Path_StructCheck G R (path_var x) (tau_ty U))
    (Hsub : Tau_StructSub G R
      (tau_ty (ty_single (path_var x))) (tau_ty S0)) :
    Tau_StructWf G R (Tau_rename d (FinFun.openAt x)).
Proof.
  apply (Tau_StructWf_open_var H HR).
  exact (path_struct_check_promote Hx Hsub).
Qed.

(** A path inversion package supplies the operational opening premise for a
    term derivation. *)
Theorem Tm_StructCheck_open_var_of_path_package {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {S0 : Ty n} {x : Fin.t n}
    {t : Tm (S n)} {T : Ty (S n)}
    (H : Tm_StructCheck (ctx_snoc G S0) (Path_ScopedLift R) t T)
    (HR : Path_IsEquivCongr R)
    (Hx : Tm_StructPathPackage G R (path_var x) S0) :
    Tm_StructCheck G R (Tm_open t x)
      (Ty_rename T (FinFun.openAt x)).
Proof.
  destruct Hx as [U Hcheck Hsub Hwf].
  apply (Tm_StructCheck_open_var H HR).
  exact (path_struct_check_promote Hcheck Hsub).
Qed.

(** Convenient opening form from the checked path term itself. *)
Theorem Tm_StructCheck_open_var_of_path_term {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {S0 : Ty n} {x : Fin.t n}
    {t : Tm (S n)} {T : Ty (S n)}
    (H : Tm_StructCheck (ctx_snoc G S0) (Path_ScopedLift R) t T)
    (HR : Path_IsEquivCongr R)
    (Hx : Tm_StructCheck G R (tm_path (path_var x)) S0) :
    Tm_StructCheck G R (Tm_open t x)
      (Ty_rename T (FinFun.openAt x)).
Proof.
  apply (Tm_StructCheck_open_var_of_path_package H HR).
  exact (Tm_StructCheck_path_inversion Hx eq_refl).
Qed.

Print Assumptions Tau_StructWf_of_source.
Print Assumptions Tm_StructCheck_of_source.
Print Assumptions Tm_StructCheck_renameExact.
Print Assumptions Tm_StructCheck_rename.
Print Assumptions Tm_StructCheck_path_inversion.
Print Assumptions Tau_StructWf_open_var_of_singleton.
Print Assumptions Tm_StructCheck_open_var_of_path_term.
