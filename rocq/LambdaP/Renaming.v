From PathDependent.LambdaP Require Import FinFun Syntax Context Typing.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Local Coercion FinFun.apply : FinFun.t >-> Funclass.

(** A finite-variable renaming that respects the types recorded by two
    contexts. *)
Definition Renaming {n m : nat} (G : Ctx n) (f : FinFun.t n m)
    (D : Ctx m) : Prop :=
  forall (x : Fin.t n) (T : Ty n),
    Ctx_Binds G x T -> Ctx_Binds D (f x) (Ty_rename T f).

Theorem Renaming_id {n : nat} (G : Ctx n) :
    Renaming G (FinFun.id n) G.
Proof.
  intros x T H. rewrite FinFun.id_apply, Ty_rename_id. exact H.
Qed.

Theorem Renaming_comp {n m l : nat} {G : Ctx n} {D : Ctx m}
    {E : Ctx l} {f : FinFun.t n m} {g : FinFun.t m l}
    (rho : Renaming G f D) (theta : Renaming D g E) :
    Renaming G (FinFun.comp f g) E.
Proof.
  intros x T H. rewrite FinFun.comp_apply, <- Ty_rename_rename.
  now apply theta, rho.
Qed.

Theorem Renaming_ext {n m : nat} {G : Ctx n} {D : Ctx m}
    {f : FinFun.t n m} {T : Ty n} (rho : Renaming G f D) :
    Renaming (ctx_snoc G T) (FinFun.ext f)
      (ctx_snoc D (Ty_rename T f)).
Proof.
  intros x U H.
  refine (@Fin.cases' n x
    (fun x => Ctx_Binds (ctx_snoc G T) x U ->
      Ctx_Binds (ctx_snoc D (Ty_rename T f)) (FinFun.ext f x)
        (Ty_rename U (FinFun.ext f))) _ _ H).
  - intros H0.
    assert (U = Ty_weaken T) as ->.
    { exact (Ctx_Binds_unique H0 (binds_here G T)). }
    rewrite FinFun.ext_zero, <- Ty_weaken_rename.
    apply binds_here.
  - intros y Hy.
    assert (U = Ty_weaken (Ctx_lookup G y)) as ->.
    { exact (Ctx_Binds_unique Hy
        (binds_there G T (Ctx_lookup G y) y (Ctx_lookup_binds G y))). }
    rewrite FinFun.ext_succ, <- Ty_weaken_rename.
    apply binds_there. apply rho. apply Ctx_lookup_binds.
Qed.

Theorem Renaming_weaken {n : nat} {G : Ctx n} {S0 : Ty n} :
    Renaming G (FinFun.weaken n) (ctx_snoc G S0).
Proof.
  intros x T H. rewrite FinFun.weaken_apply.
  change (Ctx_Binds (ctx_snoc G S0) (Fin.succ x) (Ty_weaken T)).
  now apply binds_there.
Qed.

(** Precise path typing is preserved by a context-respecting renaming. *)
Theorem Path_Ty_rename {n : nat} {k : Kind} {G : Ctx n}
    {p : Path n} {d : Tau n k} (H : Path_Ty G p d) :
    forall {m : nat} {f : FinFun.t n m} {D : Ctx m},
      Renaming G f D -> Path_Ty D (Path_rename p f) (Tau_rename d f).
Proof.
  induction H; intros m f D rho;
    cbn [Path_rename Ty_rename Tau_rename].
  - apply path_ty_var. now apply rho.
  - eapply path_ty_fst. now apply IHPath_Ty.
  - rewrite Tau_open_rename. eapply path_ty_sel_r. now apply IHPath_Ty.
  - eapply path_ty_sel_l.
    + now apply IHPath_Ty1.
    + now apply IHPath_Ty2.
    + assumption.
Qed.

(** Subtyping is preserved by a context-respecting renaming. *)
Theorem Tau_Sub_rename {n : nat} {k : Kind} {G : Ctx n}
    {d1 d2 : Tau n k} (H : Tau_Sub G d1 d2) :
    forall {m : nat} {f : FinFun.t n m} {D : Ctx m},
      Renaming G f D -> Tau_Sub D (Tau_rename d1 f) (Tau_rename d2 f).
Proof.
  induction H; intros m f D rho;
    cbn [Path_rename Ty_rename Tau_rename].
  - apply sub_refl.
  - eapply sub_trans.
    + now apply IHTau_Sub1.
    + now apply IHTau_Sub2.
  - apply sub_bot.
  - apply sub_top.
  - apply sub_widen. exact (Path_Ty_rename H rho).
  - apply sub_symm. exact (Path_Ty_rename H rho).
  - eapply sub_sel_hi.
    + exact (Path_Ty_rename H rho).
    + now apply IHTau_Sub.
  - eapply sub_sel_lo.
    + exact (Path_Ty_rename H rho).
    + now apply IHTau_Sub.
  - apply sub_fun.
    + now apply IHTau_Sub1.
    + apply IHTau_Sub2. now apply Renaming_ext.
  - apply sub_pair_fst. now apply IHTau_Sub.
  - assert (Hopen : Tau_Sub D
        (Tau_open (Tau_rename d (FinFun.ext f)) (Path_rename p f))
        (Tau_open (Tau_rename d' (FinFun.ext f)) (Path_rename p f))).
    { rewrite <- !Tau_open_rename. now apply IHTau_Sub2. }
    eapply sub_pair_single_member.
    + exact (Path_Ty_rename H rho).
    + apply IHTau_Sub1.
      exact (@Renaming_ext n m G D f (ty_single p) rho).
    + exact Hopen.
  - apply sub_bounds.
    + now apply IHTau_Sub1.
    + now apply IHTau_Sub2.
    + now apply IHTau_Sub3.
Qed.

(** Well-formed generalized types are preserved by renaming. *)
Theorem Tau_Wf_rename {n : nat} {k : Kind} {G : Ctx n}
    {d : Tau n k} (H : Tau_Wf G d) :
    forall {m : nat} {f : FinFun.t n m} {D : Ctx m},
      Renaming G f D -> Tau_Wf D (Tau_rename d f).
Proof.
  induction H; intros m f D rho;
    cbn [Path_rename Ty_rename Tau_rename].
  - apply wf_bot.
  - apply wf_top.
  - apply wf_path with (T := Ty_rename T f).
    exact (Path_Ty_rename H rho).
  - eapply wf_sel. exact (Path_Ty_rename H rho).
  - apply wf_fun.
    + now apply IHTau_Wf1.
    + apply IHTau_Wf2. now apply Renaming_ext.
  - apply wf_pair.
    + now apply IHTau_Wf1.
    + apply IHTau_Wf2. now apply Renaming_ext.
  - apply wf_bounds.
    + now apply IHTau_Wf1.
    + now apply IHTau_Wf2.
    + exact (Tau_Sub_rename H1 rho).
Qed.

(** Term typing is preserved by a context-respecting renaming. *)
Theorem Tm_Ty_rename {n : nat} {G : Ctx n} {t : Tm n} {T : Ty n}
    (H : Tm_Ty G t T) :
    forall {m : nat} {f : FinFun.t n m} {D : Ctx m},
      Renaming G f D -> Tm_Ty D (Tm_rename t f) (Ty_rename T f).
Proof.
  induction H; intros m f D rho;
    cbn [Tm_rename Def_rename Path_rename Ty_rename Tau_rename].
  - apply tm_ty_path with (T := Ty_rename T f).
    exact (Path_Ty_rename H rho).
  - apply tm_ty_abs.
    + apply IHTm_Ty. now apply Renaming_ext.
    + exact (Tau_Wf_rename H0 rho).
  - rewrite Ty_open_rename.
    apply tm_ty_app with (S := Ty_rename S f).
    + now apply IHTm_Ty1.
    + now apply IHTm_Ty2.
  - rewrite <- Path_weaken_rename.
    apply tm_ty_pair with (S := Ty_rename S f) (T := Ty_rename T f).
    + now apply rho.
    + now apply rho.
  - rewrite <- Tau_weaken_rename.
    apply tm_ty_tpair with (S := Ty_rename S f).
    + now apply rho.
    + exact (Tau_Wf_rename H0 rho).
  - apply tm_ty_let with (S := Ty_rename S f).
    + now apply IHTm_Ty1.
    + exact (Tau_Wf_rename H0 rho).
    + rewrite Ty_weaken_rename. apply IHTm_Ty2.
      now apply Renaming_ext.
  - apply tm_ty_typed.
    + now apply IHTm_Ty.
    + exact (Tau_Wf_rename H0 rho).
  - eapply tm_ty_sub.
    + now apply IHTm_Ty.
    + exact (Tau_Sub_rename H0 rho).
    + exact (Tau_Wf_rename H1 rho).
Qed.

(** Weakening corollaries used by store typing and allocation. *)
Theorem Path_Ty_weaken {n : nat} {k : Kind} {G : Ctx n}
    {p : Path n} {d : Tau n k} {S0 : Ty n} (H : Path_Ty G p d) :
    Path_Ty (ctx_snoc G S0) (Path_weaken p) (Tau_weaken d).
Proof.
  unfold Path_weaken, Tau_weaken.
  apply (Path_Ty_rename H). exact (@Renaming_weaken n G S0).
Qed.

Theorem Tau_Sub_weaken {n : nat} {k : Kind} {G : Ctx n}
    {d1 d2 : Tau n k} {S0 : Ty n} (H : Tau_Sub G d1 d2) :
    Tau_Sub (ctx_snoc G S0) (Tau_weaken d1) (Tau_weaken d2).
Proof.
  unfold Tau_weaken.
  apply (Tau_Sub_rename H). exact (@Renaming_weaken n G S0).
Qed.

Theorem Tau_Wf_weaken {n : nat} {k : Kind} {G : Ctx n}
    {d : Tau n k} {S0 : Ty n} (H : Tau_Wf G d) :
    Tau_Wf (ctx_snoc G S0) (Tau_weaken d).
Proof.
  unfold Tau_weaken.
  apply (Tau_Wf_rename H). exact (@Renaming_weaken n G S0).
Qed.

Theorem Tm_Ty_weaken {n : nat} {G : Ctx n} {t : Tm n} {T S0 : Ty n}
    (H : Tm_Ty G t T) :
    Tm_Ty (ctx_snoc G S0) (Tm_weaken t) (Ty_weaken T).
Proof.
  unfold Tm_weaken, Ty_weaken.
  apply (Tm_Ty_rename H). exact (@Renaming_weaken n G S0).
Qed.
