From PathDependent.LambdaP Require Import FinFun Syntax Context Typing
  Renaming ScopedRuntimeEq Opening StructuralRuntimeTyping
  StructuralTermTyping PathPreservation.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Local Coercion FinFun.apply : FinFun.t >-> Funclass.

(** A path substitution maps an abstract source relation into a target
    relation. *)
Definition Path_SubstRelHom {n m : nat}
    (R : Path n -> Path n -> Prop) (E : Path m -> Path m -> Prop)
    (rho : PathSubst n m) : Prop :=
  forall p q, R p q -> E (Path_subst p rho) (Path_subst q rho).

(** Identity substitution preserves a path relation. *)
Theorem Path_SubstRelHom_id {n : nat}
    {R : Path n -> Path n -> Prop} :
    Path_SubstRelHom R R (PathSubst_id n).
Proof.
  intros p q Hpq. rewrite !Path_subst_id. exact Hpq.
Qed.

(** Relation-respecting substitutions are closed under composition. *)
Theorem Path_SubstRelHom_comp {n m l : nat}
    {R : Path n -> Path n -> Prop} {E : Path m -> Path m -> Prop}
    {F : Path l -> Path l -> Prop} {rho : PathSubst n m}
    {theta : PathSubst m l}
    (Hrho : Path_SubstRelHom R E rho)
    (Htheta : Path_SubstRelHom E F theta) :
    Path_SubstRelHom R F (PathSubst_comp rho theta).
Proof.
  intros p q Hpq. rewrite <- !Path_subst_comp.
  exact (Htheta _ _ (Hrho _ _ Hpq)).
Qed.

(** A relation-respecting path substitution lifts through a binder. *)
Theorem Path_SubstRelHom_scoped {n m : nat}
    {R : Path n -> Path n -> Prop} {E : Path m -> Path m -> Prop}
    {rho : PathSubst n m} (H : Path_SubstRelHom R E rho) :
    Path_SubstRelHom (Path_ScopedLift R) (Path_ScopedLift E)
      (PathSubst_lift rho).
Proof.
  intros p q Hpq. induction Hpq; cbn [Path_subst].
  - rewrite !PathSubst_lift_zero. apply path_scoped_lift_bound.
  - rewrite !Path_weaken_subst_lift.
    apply path_scoped_lift_old. apply H. assumption.
  - now apply path_scoped_lift_symm.
  - eapply path_scoped_lift_trans; eassumption.
  - now apply path_scoped_lift_fst.
  - now apply path_scoped_lift_sel.
Qed.

(** Structural conversion is natural with respect to path substitution. *)
Theorem Tau_StructConv_subst {n m : nat} {k : Kind}
    {R : Path n -> Path n -> Prop} {E : Path m -> Path m -> Prop}
    {rho : PathSubst n m} {d1 d2 : Tau n k}
    (H : Tau_StructConv R d1 d2)
    (Hrel : Path_SubstRelHom R E rho) :
    Tau_StructConv E (Tau_subst d1 rho) (Tau_subst d2 rho).
Proof.
  induction H.
  - apply tau_struct_conv_refl.
  - now apply tau_struct_conv_symm.
  - eapply tau_struct_conv_trans; eassumption.
  - rewrite !Tau_open_subst. apply tau_struct_conv_replace.
    exact (Hrel _ _ H).
Qed.

(** A structural context substitution maps each source variable to a target
    path checked at the correspondingly substituted context type. *)
Definition Path_StructSubstitution {n m : nat} (G : Ctx n)
    (rho : PathSubst n m) (D : Ctx m)
    (E : Path m -> Path m -> Prop) : Prop :=
  forall (x : Fin.t n) (T : Ty n), Ctx_Binds G x T ->
    Path_StructCheck D E (rho x) (tau_ty (Ty_subst T rho)).

(** Identity is a structural context substitution. *)
Theorem Path_StructSubstitution_id {n : nat} {G : Ctx n}
    {E : Path n -> Path n -> Prop} :
    Path_StructSubstitution G (PathSubst_id n) G E.
Proof.
  intros x T Hx. rewrite PathSubst_id_apply, Ty_subst_id.
  apply path_struct_check_var. exact Hx.
Qed.

(** Structural context substitutions extend through a dependent binder. *)
Theorem Path_StructSubstitution_lift {n m : nat} {G : Ctx n}
    {rho : PathSubst n m} {D : Ctx m}
    {E : Path m -> Path m -> Prop} {S0 : Ty n}
    (H : Path_StructSubstitution G rho D E) :
    Path_StructSubstitution (ctx_snoc G S0) (PathSubst_lift rho)
      (ctx_snoc D (Ty_subst S0 rho)) (Path_ScopedLift E).
Proof.
  intros x T Hx.
  refine (@Fin.cases' n x
    (fun x => Ctx_Binds (ctx_snoc G S0) x T ->
      Path_StructCheck (ctx_snoc D (Ty_subst S0 rho))
        (Path_ScopedLift E) (PathSubst_lift rho x)
        (tau_ty (Ty_subst T (PathSubst_lift rho)))) _ _ Hx).
  - intro H0.
    assert (T = Ty_weaken S0) as ->.
    { exact (Ctx_Binds_unique H0 (binds_here G S0)). }
    rewrite PathSubst_lift_zero, Ty_weaken_subst_lift.
    apply path_struct_check_var. apply binds_here.
  - intros y Hy.
    assert (T = Ty_weaken (Ctx_lookup G y)) as ->.
    { exact (Ctx_Binds_unique Hy
        (binds_there G S0 (Ctx_lookup G y) y (Ctx_lookup_binds G y))). }
    rewrite PathSubst_lift_succ, Ty_weaken_subst_lift.
    pose proof (Path_StructCheck_renameExact
      (H y (Ctx_lookup G y) (Ctx_lookup_binds G y))
      (@Renaming_weaken m D (Ty_subst S0 rho))
      (@Path_RelHom_weaken m E)) as Hweak.
    exact Hweak.
Qed.

Definition Path_SubstMotive {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) {k : Kind}
    (p : Path n) (d : Tau n k) (_ : Path_StructCheck G R p d) : Prop :=
  forall (m : nat) (rho : PathSubst n m) (D : Ctx m)
    (E : Path m -> Path m -> Prop),
    Path_StructSubstitution G rho D E -> Path_SubstRelHom R E rho ->
    Path_StructCheck D E (Path_subst p rho) (Tau_subst d rho).

Definition Struct_SubstMotive {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) {k : Kind}
    (d1 d2 : Tau n k) (_ : Tau_StructSub G R d1 d2) : Prop :=
  forall (m : nat) (rho : PathSubst n m) (D : Ctx m)
    (E : Path m -> Path m -> Prop),
    Path_StructSubstitution G rho D E -> Path_SubstRelHom R E rho ->
    Tau_StructSub D E (Tau_subst d1 rho) (Tau_subst d2 rho).

Lemma Path_Sub_subst_mut :
    (forall n G R k p d (H : Path_StructCheck G R p d),
      @Path_SubstMotive n G R k p d H) /\
    (forall n G R k d1 d2 (H : Tau_StructSub G R d1 d2),
      @Struct_SubstMotive n G R k d1 d2 H).
Proof.
  apply PathStruct_mutind;
    unfold Path_SubstMotive, Struct_SubstMotive.
  - intros n G R x T Hb m rho D E Hctx Hrel.
    cbn [Path_subst Tau_subst]. exact (Hctx x T Hb).
  - intros n k G R p d1 d2 Hp IHp Hs IHs m rho D E Hctx Hrel.
    eapply path_struct_check_sub.
    + exact (IHp _ _ _ _ Hctx Hrel).
    + exact (IHs _ _ _ _ Hctx Hrel).
  - intros n G R p U T Hp IHp Hs IHs m rho D E Hctx Hrel.
    cbn [Path_subst Ty_subst Tau_subst].
    eapply path_struct_check_promote.
    + exact (IHp _ _ _ _ Hctx Hrel).
    + exact (IHs _ _ _ _ Hctx Hrel).
  - intros n k G R p S0 a d Hp IHp m rho D E Hctx Hrel.
    cbn [Path_subst Ty_subst Tau_subst].
    eapply path_struct_check_fst. exact (IHp _ _ _ _ Hctx Hrel).
  - intros n k G R p S0 a d Hp IHp m rho D E Hctx Hrel.
    cbn [Path_subst Ty_subst Tau_subst]. rewrite Tau_open_subst.
    eapply path_struct_check_sel_r. exact (IHp _ _ _ _ Hctx Hrel).
  - intros n k k' G R p S0 a b d d' Hp IHp Htail IHtail Hne
      m rho D E Hctx Hrel.
    cbn [Path_subst Ty_subst Tau_subst].
    eapply path_struct_check_sel_l.
    + exact (IHp _ _ _ _ Hctx Hrel).
    + exact (IHtail _ _ _ _ Hctx Hrel).
    + exact Hne.
  - intros n k G R d m rho D E Hctx Hrel.
    apply tau_struct_sub_refl.
  - intros n k G R d1 d2 d3 H1 IH1 H2 IH2
      m rho D E Hctx Hrel.
    eapply tau_struct_sub_trans.
    + exact (IH1 _ _ _ _ Hctx Hrel).
    + exact (IH2 _ _ _ _ Hctx Hrel).
  - intros n k G R d1 d2 Hconv m rho D E Hctx Hrel.
    apply tau_struct_sub_conv.
    exact (@Tau_StructConv_subst n m k R E rho d1 d2 Hconv Hrel).
  - intros n G R T m rho D E Hctx Hrel.
    cbn [Ty_subst Tau_subst]. apply tau_struct_sub_bot.
  - intros n G R T m rho D E Hctx Hrel.
    cbn [Ty_subst Tau_subst]. apply tau_struct_sub_top.
  - intros n G R p T Hp IHp m rho D E Hctx Hrel.
    cbn [Path_subst Ty_subst Tau_subst].
    apply tau_struct_sub_widen. exact (IHp _ _ _ _ Hctx Hrel).
  - intros n G R p q Hp IHp m rho D E Hctx Hrel.
    cbn [Path_subst Ty_subst Tau_subst].
    apply tau_struct_sub_symm. exact (IHp _ _ _ _ Hctx Hrel).
  - intros n G R p A S0 T Hp IHp Hs IHs m rho D E Hctx Hrel.
    cbn [Path_subst Ty_subst Tau_subst].
    eapply tau_struct_sub_sel_hi.
    + exact (IHp _ _ _ _ Hctx Hrel).
    + exact (IHs _ _ _ _ Hctx Hrel).
  - intros n G R p A S0 T Hp IHp Hs IHs m rho D E Hctx Hrel.
    cbn [Path_subst Ty_subst Tau_subst].
    eapply tau_struct_sub_sel_lo.
    + exact (IHp _ _ _ _ Hctx Hrel).
    + exact (IHs _ _ _ _ Hctx Hrel).
  - intros n G R S0 S' T T' Hdom IHdom Hcod IHcod
      m rho D E Hctx Hrel.
    cbn [Ty_subst Tau_subst]. eapply tau_struct_sub_fun.
    + exact (IHdom _ _ _ _ Hctx Hrel).
    + exact (IHcod _ _ _ _ (Path_StructSubstitution_lift Hctx)
        (Path_SubstRelHom_scoped Hrel)).
  - intros n k G R S0 S' a d Hfst IHfst m rho D E Hctx Hrel.
    cbn [Ty_subst Tau_subst]. apply tau_struct_sub_pair_fst.
    exact (IHfst _ _ _ _ Hctx Hrel).
  - intros n k G R p P a d d' Hp IHp Hsnd IHsnd Hopen IHopen
      m rho D E Hctx Hrel.
    pose proof (IHopen _ _ _ _ Hctx Hrel) as Hopen'.
    rewrite !Tau_open_subst in Hopen'.
    cbn [Path_subst Ty_subst Tau_subst].
    eapply tau_struct_sub_pair_single_member.
    + exact (IHp _ _ _ _ Hctx Hrel).
    + exact (IHsnd _ _ _ _ (Path_StructSubstitution_lift Hctx)
        (Path_SubstRelHom_scoped Hrel)).
    + exact Hopen'.
  - intros n G R S0 S' T T' Hlo IHlo Hhi IHhi Hnon IHnon
      m rho D E Hctx Hrel.
    cbn [Tau_subst]. eapply tau_struct_sub_bounds.
    + exact (IHlo _ _ _ _ Hctx Hrel).
    + exact (IHhi _ _ _ _ Hctx Hrel).
    + exact (IHnon _ _ _ _ Hctx Hrel).
Qed.

(** Structural path checking is stable under structural path substitution. *)
Theorem Path_StructCheck_subst {n m : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {k : Kind}
    {p : Path n} {d : Tau n k} (H : Path_StructCheck G R p d)
    {rho : PathSubst n m} {D : Ctx m}
    {E : Path m -> Path m -> Prop}
    (Hctx : Path_StructSubstitution G rho D E)
    (Hrel : Path_SubstRelHom R E rho) :
    Path_StructCheck D E (Path_subst p rho) (Tau_subst d rho).
Proof.
  exact (proj1 Path_Sub_subst_mut _ _ _ _ _ _ H _ _ _ _ Hctx Hrel).
Qed.

(** Structural generalized subtyping is stable under the same structural
    path substitution. *)
Theorem Tau_StructSub_subst {n m : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {k : Kind}
    {d1 d2 : Tau n k} (H : Tau_StructSub G R d1 d2)
    {rho : PathSubst n m} {D : Ctx m}
    {E : Path m -> Path m -> Prop}
    (Hctx : Path_StructSubstitution G rho D E)
    (Hrel : Path_SubstRelHom R E rho) :
    Tau_StructSub D E (Tau_subst d1 rho) (Tau_subst d2 rho).
Proof.
  exact (proj2 Path_Sub_subst_mut _ _ _ _ _ _ H _ _ _ _ Hctx Hrel).
Qed.

(** Structural well-formedness is stable under structural path
    substitution. *)
Theorem Tau_StructWf_subst {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {k : Kind} {d : Tau n k}
    (H : Tau_StructWf G R d) :
    forall {m : nat} {rho : PathSubst n m} {D : Ctx m}
      {E : Path m -> Path m -> Prop},
      Path_StructSubstitution G rho D E ->
      Path_SubstRelHom R E rho ->
      Tau_StructWf D E (Tau_subst d rho).
Proof.
  induction H; intros m rho D E Hctx Hrel;
    cbn [Path_subst Ty_subst Tau_subst].
  - apply tau_struct_wf_bot.
  - apply tau_struct_wf_top.
  - eapply tau_struct_wf_path.
    exact (Path_StructCheck_subst H Hctx Hrel).
  - eapply tau_struct_wf_sel.
    exact (Path_StructCheck_subst H Hctx Hrel).
  - apply tau_struct_wf_fun.
    + exact (IHTau_StructWf1 _ _ _ _ Hctx Hrel).
    + exact (IHTau_StructWf2 _ _ _ _
        (Path_StructSubstitution_lift Hctx)
        (Path_SubstRelHom_scoped Hrel)).
  - apply tau_struct_wf_pair.
    + exact (IHTau_StructWf1 _ _ _ _ Hctx Hrel).
    + exact (IHTau_StructWf2 _ _ _ _
        (Path_StructSubstitution_lift Hctx)
        (Path_SubstRelHom_scoped Hrel)).
  - apply tau_struct_wf_bounds.
    + exact (IHTau_StructWf1 _ _ _ _ Hctx Hrel).
    + exact (IHTau_StructWf2 _ _ _ _ Hctx Hrel).
    + exact (Tau_StructSub_subst H1 Hctx Hrel).
Qed.

(** Structural context substitutions are closed under composition. *)
Theorem Path_StructSubstitution_comp {n m l : nat}
    {G : Ctx n} {D : Ctx m} {X : Ctx l}
    {rho : PathSubst n m} {theta : PathSubst m l}
    {E : Path m -> Path m -> Prop} {F : Path l -> Path l -> Prop}
    (Hrho : Path_StructSubstitution G rho D E)
    (Htheta : Path_StructSubstitution D theta X F)
    (Hrel : Path_SubstRelHom E F theta) :
    Path_StructSubstitution G (PathSubst_comp rho theta) X F.
Proof.
  intros x T Hx.
  pose proof (Path_StructCheck_subst (Hrho x T Hx) Htheta Hrel) as Hsub.
  rewrite PathSubst_comp_apply, <- Ty_subst_comp.
  exact Hsub.
Qed.

(** Replacing the newest context variable by an arbitrary path checked at
    the binder type is a structural context substitution. *)
Theorem Path_StructSubstitution_openAt {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {q : Path n} {S0 : Ty n}
    (Hq : Path_StructCheck G R q (tau_ty S0)) :
    Path_StructSubstitution (ctx_snoc G S0) (PathSubst_openAt q) G R.
Proof.
  intros x T Hx.
  refine (@Fin.cases' n x
    (fun x => Ctx_Binds (ctx_snoc G S0) x T ->
      Path_StructCheck G R (PathSubst_openAt q x)
        (tau_ty (Ty_subst T (PathSubst_openAt q)))) _ _ Hx).
  - intro H0.
    assert (T = Ty_weaken S0) as ->.
    { exact (Ctx_Binds_unique H0 (binds_here G S0)). }
    rewrite PathSubst_openAt_zero.
    change (Path_StructCheck G R q
      (tau_ty (Ty_open (Ty_weaken S0) q))).
    rewrite Ty_weaken_open. exact Hq.
  - intros y Hy.
    assert (T = Ty_weaken (Ctx_lookup G y)) as ->.
    { exact (Ctx_Binds_unique Hy
        (binds_there G S0 (Ctx_lookup G y) y (Ctx_lookup_binds G y))). }
    rewrite PathSubst_openAt_succ.
    change (Path_StructCheck G R (path_var y)
      (tau_ty (Ty_open (Ty_weaken (Ctx_lookup G y)) q))).
    rewrite Ty_weaken_open. apply path_struct_check_var.
    apply Ctx_lookup_binds.
Qed.

(** Opening a scoped relation at one path maps it back to the ambient
    relation. *)
Theorem Path_SubstRelHom_openAt {n : nat}
    {R : Path n -> Path n -> Prop} (HR : Path_IsEquivCongr R)
    (q : Path n) :
    Path_SubstRelHom (Path_ScopedLift R) R (PathSubst_openAt q).
Proof.
  intros p r Hpr. change (R (Path_open p q) (Path_open r q)).
  exact (Path_ScopedLift_open_paths HR Hpr (path_equiv_refl HR q)).
Qed.

(** Standard dependent opening for structural well-formedness at an
    arbitrary checked path. *)
Theorem Tau_StructWf_open_path {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {S0 : Ty n} {q : Path n}
    {k : Kind} {d : Tau (S n) k}
    (H : Tau_StructWf (ctx_snoc G S0) (Path_ScopedLift R) d)
    (HR : Path_IsEquivCongr R)
    (Hq : Path_StructCheck G R q (tau_ty S0)) :
    Tau_StructWf G R (Tau_open d q).
Proof.
  unfold Tau_open.
  exact (Tau_StructWf_subst H (Path_StructSubstitution_openAt Hq)
    (Path_SubstRelHom_openAt HR q)).
Qed.

Print Assumptions Path_SubstRelHom_scoped.
Print Assumptions Tau_StructConv_subst.
Print Assumptions Path_StructSubstitution_lift.
Print Assumptions Path_StructCheck_subst.
Print Assumptions Tau_StructSub_subst.
Print Assumptions Tau_StructWf_subst.
Print Assumptions Path_StructSubstitution_comp.
Print Assumptions Tau_StructWf_open_path.
