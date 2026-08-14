From Equations Require Import Equations.
From PathDependent.LambdaP Require Import FinFun Syntax Context Typing
  Renaming ScopedRuntimeEq Opening StructuralRuntimeTyping
  StructuralTermTyping StructuralPathSubstitution.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Local Coercion FinFun.apply : FinFun.t >-> Funclass.

(** Exchange the two newest variables and leave all older variables fixed. *)
Definition PathSubst_swap01 (n : nat) : PathSubst (S (S n)) (S (S n)) :=
  Env.tabulate (S (S n)) (fun x =>
    Fin.cases (path_var (Fin.succ Fin.zero))
      (fun y => Fin.cases (path_var Fin.zero)
        (fun z => path_var (Fin.succ (Fin.succ z))) y) x).

Theorem PathSubst_swap01_zero {n : nat} :
    PathSubst_swap01 n Fin.zero = path_var (Fin.succ Fin.zero).
Proof.
  unfold PathSubst_swap01, PathSubst_apply.
  rewrite Env.lookup_tabulate. reflexivity.
Qed.

Theorem PathSubst_swap01_one {n : nat} :
    PathSubst_swap01 n (Fin.succ Fin.zero) = path_var Fin.zero.
Proof.
  unfold PathSubst_swap01, PathSubst_apply.
  rewrite Env.lookup_tabulate. reflexivity.
Qed.

Theorem PathSubst_swap01_succ_succ {n : nat} (x : Fin.t n) :
    PathSubst_swap01 n (Fin.succ (Fin.succ x)) =
      path_var (Fin.succ (Fin.succ x)).
Proof.
  unfold PathSubst_swap01, PathSubst_apply.
  rewrite Env.lookup_tabulate. reflexivity.
Qed.

(** Swapping the component binder with the outer replacement variable and
    then opening is exactly capture-avoiding lifted opening. *)
Theorem Tau_swap01_open_weaken {n : nat} {k : Kind}
    (template : Tau (S (S n)) k) (p : Path n) :
    Tau_open (Tau_subst template (PathSubst_swap01 n)) (Path_weaken p) =
      Tau_subst template (PathSubst_lift (PathSubst_openAt p)).
Proof.
  unfold Tau_open. rewrite Tau_subst_comp.
  f_equal. apply PathSubst_funext. intro x.
  refine (@Fin.cases' (S n) x
    (fun x =>
      PathSubst_comp (PathSubst_swap01 n)
        (PathSubst_openAt (Path_weaken p)) x =
      PathSubst_lift (PathSubst_openAt p) x) _ _).
  - rewrite PathSubst_comp_apply, PathSubst_swap01_zero.
    cbn [Path_subst]. rewrite PathSubst_openAt_succ,
      PathSubst_lift_zero. reflexivity.
  - intros y. refine (@Fin.cases' n y
      (fun y =>
        PathSubst_comp (PathSubst_swap01 n)
          (PathSubst_openAt (Path_weaken p)) (Fin.succ y) =
        PathSubst_lift (PathSubst_openAt p) (Fin.succ y)) _ _).
    + rewrite PathSubst_comp_apply, PathSubst_swap01_one.
      cbn [Path_subst]. rewrite PathSubst_openAt_zero,
        PathSubst_lift_succ, PathSubst_openAt_zero. reflexivity.
    + intros z.
      rewrite PathSubst_comp_apply, PathSubst_swap01_succ_succ.
      cbn [Path_subst]. rewrite PathSubst_openAt_succ,
        PathSubst_lift_succ, PathSubst_openAt_succ.
      unfold Path_weaken. cbn [Path_rename].
      rewrite FinFun.weaken_apply. reflexivity.
Qed.

(** Outer-constructor tags used to rule out impossible transitivity
    intermediates without indexed inversion. *)
Inductive Tau_ConvTag : Type :=
| conv_tag_top
| conv_tag_bot
| conv_tag_fun
| conv_tag_pair (a : Name) (k : Kind)
| conv_tag_single
| conv_tag_tsel
| conv_tag_interval.

Definition Ty_convTag {n : nat} (T : Ty n) : Tau_ConvTag :=
  match T with
  | ty_top => conv_tag_top
  | ty_bot => conv_tag_bot
  | ty_fun _ _ => conv_tag_fun
  | @ty_pair _ k _ a _ => conv_tag_pair a k
  | ty_single _ => conv_tag_single
  | ty_tsel _ _ => conv_tag_tsel
  end.

Definition Tau_convTag {n : nat} {k : Kind} (d : Tau n k) : Tau_ConvTag :=
  match d with
  | tau_ty T => Ty_convTag T
  | tau_intv _ _ => conv_tag_interval
  end.

Lemma TyTau_convTag_subst :
    (forall (n : nat) (T : Ty n) (m : nat) (rho : PathSubst n m),
      Ty_convTag (Ty_subst T rho) = Ty_convTag T) /\
    (forall (n : nat) (k : Kind) (d : Tau n k) (m : nat)
      (rho : PathSubst n m),
      Tau_convTag (Tau_subst d rho) = Tau_convTag d).
Proof.
  apply TyTau_mutind; intros;
    cbn [Ty_subst Tau_subst Ty_convTag Tau_convTag];
    try reflexivity; try assumption.
  exact (H m rho).
Qed.

Theorem Ty_convTag_open {n : nat} (T : Ty (S n)) (p : Path n) :
    Ty_convTag (Ty_open T p) = Ty_convTag T.
Proof. unfold Ty_open. exact (proj1 TyTau_convTag_subst _ T _ _). Qed.

Theorem Tau_convTag_open {n : nat} {k : Kind}
    (d : Tau (S n) k) (p : Path n) :
    Tau_convTag (Tau_open d p) = Tau_convTag d.
Proof.
  unfold Tau_open. exact (proj2 TyTau_convTag_subst _ _ d _ _).
Qed.

Theorem Tau_StructConv_convTag_eq {n : nat} {k : Kind}
    {R : Path n -> Path n -> Prop} {d1 d2 : Tau n k}
    (H : Tau_StructConv R d1 d2) : Tau_convTag d1 = Tau_convTag d2.
Proof.
  induction H.
  - reflexivity.
  - symmetry. exact IHTau_StructConv.
  - etransitivity; eassumption.
  - rewrite !Tau_convTag_open. reflexivity.
Qed.

(** Function conversion exposes domain conversion and scoped codomain
    conversion. *)
Lemma Tau_StructConv_fun_parts_aux {n : nat}
    {R : Path n -> Path n -> Prop} {d1 d2 : Tau n star}
    (H : Tau_StructConv R d1 d2) :
    forall (S1 : Ty n) (U1 : Ty (S n)),
      d1 = tau_ty (ty_fun S1 U1) ->
    forall (S2 : Ty n) (U2 : Ty (S n)),
      d2 = tau_ty (ty_fun S2 U2) ->
      Tau_StructConv R (tau_ty S1) (tau_ty S2) /\
      Tau_StructConv (Path_ScopedLift R) (tau_ty U1) (tau_ty U2).
Proof.
  induction H.
  - intros S1 U1 H1 S2 U2 H2.
    dependent elimination H1. dependent elimination H2.
    split; apply tau_struct_conv_refl.
  - intros S1 U1 H1 S2 U2 H2.
    destruct (IHTau_StructConv S2 U2 H2 S1 U1 H1) as [Hdom Hcod].
    split; now apply tau_struct_conv_symm.
  - intros S1 U1 Hstart S3 U3 Hend.
    pose proof (Tau_StructConv_convTag_eq H) as Htag.
    rewrite Hstart in Htag. cbn [Tau_convTag Ty_convTag] in Htag.
    dependent elimination d2. dependent elimination t;
      try discriminate Htag.
    destruct (IHTau_StructConv1 S1 U1 Hstart t t0 eq_refl)
      as [Hdom1 Hcod1].
    destruct (IHTau_StructConv2 t t0 eq_refl S3 U3 Hend)
      as [Hdom2 Hcod2].
    split; eapply tau_struct_conv_trans; eassumption.
  - intros S1 U1 H1 S2 U2 H2.
    dependent elimination template. dependent elimination t;
      try discriminate H1.
    cbn [Tau_open Tau_subst Ty_subst] in H1, H2.
    dependent elimination H1. dependent elimination H2.
    split.
    + exact (tau_struct_conv_replace (tau_ty t) H).
    + pose proof (tau_struct_conv_replace
        (R := Path_ScopedLift R)
        (Tau_subst (tau_ty t0) (PathSubst_swap01 n))
        (path_scoped_lift_old H)) as Hcod.
      rewrite !Tau_swap01_open_weaken in Hcod. exact Hcod.
Qed.

(** Runtime conversion between function types decomposes componentwise. *)
Theorem Tau_StructConv_fun_parts {n : nat}
    {R : Path n -> Path n -> Prop}
    {S1 S2 : Ty n} {U1 U2 : Ty (S n)}
    (H : Tau_StructConv R
      (tau_ty (ty_fun S1 U1)) (tau_ty (ty_fun S2 U2))) :
    Tau_StructConv R (tau_ty S1) (tau_ty S2) /\
    Tau_StructConv (Path_ScopedLift R) (tau_ty U1) (tau_ty U2).
Proof.
  exact (@Tau_StructConv_fun_parts_aux n R _ _ H
    S1 U1 eq_refl S2 U2 eq_refl).
Qed.

(** Pair conversion preserves the member label and kind. *)
Lemma Tau_StructConv_pair_parts_aux {n : nat}
    {R : Path n -> Path n -> Prop} {d1 d2 : Tau n star}
    (H : Tau_StructConv R d1 d2) :
    forall (S1 : Ty n) (a1 : Name) (k1 : Kind)
      (m1 : Tau (S n) k1), d1 = tau_ty (ty_pair S1 a1 m1) ->
    forall (S2 : Ty n) (a2 : Name) (k2 : Kind)
      (m2 : Tau (S n) k2), d2 = tau_ty (ty_pair S2 a2 m2) ->
      a1 = a2 /\ k1 = k2.
Proof.
  induction H.
  - intros S1 a1 k1 m1 H1 S2 a2 k2 m2 H2.
    dependent elimination H1. dependent elimination H2.
    split; reflexivity.
  - intros S1 a1 k1 m1 H1 S2 a2 k2 m2 H2.
    destruct (IHTau_StructConv S2 a2 k2 m2 H2
      S1 a1 k1 m1 H1) as [Ha Hk].
    split; symmetry; assumption.
  - intros S1 a1 k1 m1 Hstart S3 a3 k3 m3 Hend.
    pose proof (Tau_StructConv_convTag_eq H) as Htag.
    rewrite Hstart in Htag. cbn [Tau_convTag Ty_convTag] in Htag.
    dependent elimination d2. dependent elimination t;
      try discriminate Htag.
    destruct (IHTau_StructConv1 S1 a1 k1 m1 Hstart
      t1 n4 k t2 eq_refl) as [Ha1 Hk1].
    destruct (IHTau_StructConv2 t1 n4 k t2 eq_refl
      S3 a3 k3 m3 Hend) as [Ha2 Hk2].
    split; etransitivity; eassumption.
  - intros S1 a1 k1 m1 H1 S2 a2 k2 m2 H2.
    dependent elimination template. dependent elimination t;
      try discriminate H1.
    cbn [Tau_open Tau_subst Ty_subst] in H1, H2.
    dependent elimination H1. dependent elimination H2.
    split; reflexivity.
Qed.

Theorem Tau_StructConv_pair_label_kind {n : nat}
    {R : Path n -> Path n -> Prop} {S1 S2 : Ty n}
    {a1 a2 : Name} {k1 k2 : Kind}
    {m1 : Tau (S n) k1} {m2 : Tau (S n) k2}
    (H : Tau_StructConv R
      (tau_ty (ty_pair S1 a1 m1)) (tau_ty (ty_pair S2 a2 m2))) :
    a1 = a2 /\ k1 = k2.
Proof.
  exact (@Tau_StructConv_pair_parts_aux n R _ _ H
    S1 a1 k1 m1 eq_refl S2 a2 k2 m2 eq_refl).
Qed.

(** First-order projections for pair injectivity. *)
Definition Tau_star_type {n : nat} (d : Tau n star) : Ty n :=
  match d with tau_ty T => T end.

Definition Ty_pair_first_opt {n : nat} (T : Ty n) : option (Ty n) :=
  match T with
  | ty_pair S0 _ _ => Some S0
  | _ => None
  end.

Definition Ty_pair_member_opt {n : nat} (T : Ty n) :
    option { k : Kind & Tau (S n) k } :=
  match T in Ty n' return option { k : Kind & Tau (S n') k } with
  | @ty_pair _ k _ _ d => Some (existT (fun k => Tau _ k) k d)
  | _ => None
  end.

Lemma ty_pair_eq_components {n : nat} {k : Kind}
    {S1 S2 : Ty n} {a : Name} {m1 m2 : Tau (S n) k}
    (Epair : ty_pair S1 a m1 = ty_pair S2 a m2) :
    S1 = S2 /\ m1 = m2.
Proof.
  pose proof (f_equal (@Ty_pair_first_opt n) Epair) as Efirst.
  cbn [Ty_pair_first_opt] in Efirst. injection Efirst as Efirst.
  pose proof (f_equal (@Ty_pair_member_opt n) Epair) as Emember.
  cbn [Ty_pair_member_opt] in Emember. injection Emember as Emember.
  split.
  - exact Efirst.
  - exact (@Eqdep_dec.inj_pair2_eq_dec Kind Kind_eq_dec
      (fun k => Tau (S n) k) k m1 m2 Emember).
Qed.

(** With a common label and member kind exposed, pair conversion decomposes
    into first-component and scoped member conversion. *)
Lemma Tau_StructConv_pair_components_aux {n : nat}
    {R : Path n -> Path n -> Prop} {d1 d2 : Tau n star}
    (H : Tau_StructConv R d1 d2) :
    forall (S1 : Ty n) (a : Name) (k : Kind)
      (m1 : Tau (S n) k), d1 = tau_ty (ty_pair S1 a m1) ->
    forall (S2 : Ty n) (m2 : Tau (S n) k),
      d2 = tau_ty (ty_pair S2 a m2) ->
      Tau_StructConv R (tau_ty S1) (tau_ty S2) /\
      Tau_StructConv (Path_ScopedLift R) m1 m2.
Proof.
  induction H.
  - intros S1 a k m1 H1 S2 m2 H2.
    pose proof (f_equal Tau_star_type H1) as E1.
    pose proof (f_equal Tau_star_type H2) as E2.
    cbn [Tau_star_type] in E1, E2.
    assert (Epair : ty_pair S1 a m1 = ty_pair S2 a m2).
    { transitivity (Tau_star_type d).
      - symmetry. exact E1.
      - exact E2. }
    destruct (ty_pair_eq_components Epair) as [Efirst Emember].
    destruct Efirst. destruct Emember.
    split; apply tau_struct_conv_refl.
  - intros S1 a k m1 H1 S2 m2 H2.
    destruct (IHTau_StructConv S2 a k m2 H2 S1 m1 H1)
      as [Hfirst Hmember].
    split; now apply tau_struct_conv_symm.
  - intros S1 a k0 m1 Hstart S3 m3 Hend.
    pose proof (Tau_StructConv_convTag_eq H) as Htag.
    rewrite Hstart in Htag. cbn [Tau_convTag Ty_convTag] in Htag.
    dependent elimination d2. dependent elimination t;
      try discriminate Htag.
    injection Htag as Ha Hk. destruct Ha. destruct Hk.
    destruct (IHTau_StructConv1 S1 a k0 m1 Hstart
      t1 t2 eq_refl) as [Hfirst1 Hmember1].
    destruct (IHTau_StructConv2 t1 a k0 t2 eq_refl
      S3 m3 Hend) as [Hfirst2 Hmember2].
    split; eapply tau_struct_conv_trans; eassumption.
  - intros S1 a k0 m1 H1 S2 m2 H2.
    dependent elimination template. dependent elimination t;
      try discriminate H1.
    pose proof (f_equal Tau_star_type H1) as E1.
    pose proof (f_equal Tau_star_type H2) as E2.
    cbn [Tau_star_type Tau_open Tau_subst Ty_subst] in E1, E2.
    pose proof (f_equal Ty_convTag E1) as Etag.
    cbn [Ty_convTag] in Etag. injection Etag as Ea Ek.
    destruct Ea. destruct Ek.
    destruct (ty_pair_eq_components E1) as [Efirst1 Emember1].
    destruct (ty_pair_eq_components E2) as [Efirst2 Emember2].
    destruct Efirst1. destruct Efirst2.
    destruct Emember1. destruct Emember2.
    split.
    + exact (tau_struct_conv_replace (tau_ty t1) H).
    + pose proof (tau_struct_conv_replace
        (R := Path_ScopedLift R)
        (Tau_subst t2 (PathSubst_swap01 n))
        (path_scoped_lift_old H)) as Hmember.
      rewrite !Tau_swap01_open_weaken in Hmember. exact Hmember.
Qed.

Theorem Tau_StructConv_pair_components {n : nat}
    {R : Path n -> Path n -> Prop} {S1 S2 : Ty n}
    {a : Name} {k : Kind} {m1 m2 : Tau (S n) k}
    (H : Tau_StructConv R
      (tau_ty (ty_pair S1 a m1)) (tau_ty (ty_pair S2 a m2))) :
    Tau_StructConv R (tau_ty S1) (tau_ty S2) /\
    Tau_StructConv (Path_ScopedLift R) m1 m2.
Proof.
  exact (@Tau_StructConv_pair_components_aux n R _ _ H
    S1 a k m1 eq_refl S2 m2 eq_refl).
Qed.

(** Singleton conversion is generated by the underlying path relation. *)
Lemma Tau_StructConv_single_paths_aux {n : nat}
    {R : Path n -> Path n -> Prop} (HR : Path_IsEquivCongr R)
    {d1 d2 : Tau n star} (H : Tau_StructConv R d1 d2) :
    forall p : Path n, d1 = tau_ty (ty_single p) ->
    forall q : Path n, d2 = tau_ty (ty_single q) -> R p q.
Proof.
  induction H.
  - intros p H1 q H2. dependent elimination H1.
    dependent elimination H2. apply (path_equiv_refl HR).
  - intros p H1 q H2. apply (path_equiv_symm HR).
    exact (IHTau_StructConv q H2 p H1).
  - intros p Hstart r Hend.
    pose proof (Tau_StructConv_convTag_eq H) as Htag.
    rewrite Hstart in Htag. cbn [Tau_convTag Ty_convTag] in Htag.
    dependent elimination d2. dependent elimination t;
      try discriminate Htag.
    eapply (path_equiv_trans HR).
    + exact (IHTau_StructConv1 p Hstart p0 eq_refl).
    + exact (IHTau_StructConv2 p0 eq_refl r Hend).
  - intros r H1 s H2.
    dependent elimination template. dependent elimination t;
      try discriminate H1.
    cbn [Tau_open Tau_subst Ty_subst] in H1, H2.
    dependent elimination H1. dependent elimination H2.
    exact (Path_IsEquivCongr_open_context HR H p0).
Qed.

Theorem Tau_StructConv_single_paths {n : nat}
    {R : Path n -> Path n -> Prop} (HR : Path_IsEquivCongr R)
    {p q : Path n}
    (H : Tau_StructConv R
      (tau_ty (ty_single p)) (tau_ty (ty_single q))) : R p q.
Proof.
  exact (@Tau_StructConv_single_paths_aux n R HR _ _ H
    p eq_refl q eq_refl).
Qed.

(** Type-selection conversion preserves the label and converts its receiver
    path. *)
Lemma Tau_StructConv_tsel_parts_aux {n : nat}
    {R : Path n -> Path n -> Prop} (HR : Path_IsEquivCongr R)
    {d1 d2 : Tau n star} (H : Tau_StructConv R d1 d2) :
    forall (p : Path n) (A : Name), d1 = tau_ty (ty_tsel p A) ->
    forall (q : Path n) (B : Name), d2 = tau_ty (ty_tsel q B) ->
      A = B /\ R p q.
Proof.
  induction H.
  - intros p A H1 q B H2. dependent elimination H1.
    dependent elimination H2. split; [reflexivity | apply (path_equiv_refl HR)].
  - intros p A H1 q B H2.
    destruct (IHTau_StructConv q B H2 p A H1) as [Hlabel Hpath].
    split; [symmetry; exact Hlabel | now apply (path_equiv_symm HR)].
  - intros p A Hstart r C Hend.
    pose proof (Tau_StructConv_convTag_eq H) as Htag.
    rewrite Hstart in Htag. cbn [Tau_convTag Ty_convTag] in Htag.
    dependent elimination d2. dependent elimination t;
      try discriminate Htag.
    destruct (IHTau_StructConv1 p A Hstart p1 n7 eq_refl)
      as [Hab Hpq].
    destruct (IHTau_StructConv2 p1 n7 eq_refl r C Hend)
      as [Hbc Hqr].
    split.
    + etransitivity; eassumption.
    + eapply (path_equiv_trans HR); eassumption.
  - intros r A H1 s B H2.
    dependent elimination template. dependent elimination t;
      try discriminate H1.
    cbn [Tau_open Tau_subst Ty_subst] in H1, H2.
    dependent elimination H1. dependent elimination H2.
    split.
    + reflexivity.
    + exact (Path_IsEquivCongr_open_context HR H p1).
Qed.

Theorem Tau_StructConv_tsel_parts {n : nat}
    {R : Path n -> Path n -> Prop} (HR : Path_IsEquivCongr R)
    {p q : Path n} {A B : Name}
    (H : Tau_StructConv R
      (tau_ty (ty_tsel p A)) (tau_ty (ty_tsel q B))) :
    A = B /\ R p q.
Proof.
  exact (@Tau_StructConv_tsel_parts_aux n R HR _ _ H
    p A eq_refl q B eq_refl).
Qed.

(** Nullary conversion cannot change its outer constructor. *)
Lemma Ty_convTag_top_eq {n : nat} (T : Ty n)
    (H : Ty_convTag T = conv_tag_top) : T = ty_top.
Proof.
  dependent elimination T; cbn [Ty_convTag] in H;
    try discriminate H; reflexivity.
Qed.

Lemma Ty_convTag_bot_eq {n : nat} (T : Ty n)
    (H : Ty_convTag T = conv_tag_bot) : T = ty_bot.
Proof.
  dependent elimination T; cbn [Ty_convTag] in H;
    try discriminate H; reflexivity.
Qed.

Theorem Tau_StructConv_top_target_eq {n : nat}
    {R : Path n -> Path n -> Prop} {T : Ty n}
    (H : Tau_StructConv R (tau_ty ty_top) (tau_ty T)) : T = ty_top.
Proof.
  pose proof (Tau_StructConv_convTag_eq H) as Htag.
  cbn [Tau_convTag Ty_convTag] in Htag.
  apply Ty_convTag_top_eq. symmetry. exact Htag.
Qed.

Theorem Tau_StructConv_top_source_eq {n : nat}
    {R : Path n -> Path n -> Prop} {T : Ty n}
    (H : Tau_StructConv R (tau_ty T) (tau_ty ty_top)) : T = ty_top.
Proof.
  exact (@Tau_StructConv_top_target_eq n R T
    (tau_struct_conv_symm H)).
Qed.

Theorem Tau_StructConv_bot_target_eq {n : nat}
    {R : Path n -> Path n -> Prop} {T : Ty n}
    (H : Tau_StructConv R (tau_ty ty_bot) (tau_ty T)) : T = ty_bot.
Proof.
  pose proof (Tau_StructConv_convTag_eq H) as Htag.
  cbn [Tau_convTag Ty_convTag] in Htag.
  apply Ty_convTag_bot_eq. symmetry. exact Htag.
Qed.

Theorem Tau_StructConv_bot_source_eq {n : nat}
    {R : Path n -> Path n -> Prop} {T : Ty n}
    (H : Tau_StructConv R (tau_ty T) (tau_ty ty_bot)) : T = ty_bot.
Proof.
  exact (@Tau_StructConv_bot_target_eq n R T
    (tau_struct_conv_symm H)).
Qed.

(** Interval conversion acts componentwise in the same direction. *)
Lemma Tau_StructConv_interval_components_aux {n : nat}
    {R : Path n -> Path n -> Prop} {d1 d2 : Tau n iota}
    (H : Tau_StructConv R d1 d2) :
    forall L1 U1 : Ty n, d1 = tau_intv L1 U1 ->
    forall L2 U2 : Ty n, d2 = tau_intv L2 U2 ->
      Tau_StructConv R (tau_ty L1) (tau_ty L2) /\
      Tau_StructConv R (tau_ty U1) (tau_ty U2).
Proof.
  induction H.
  - intros L1 U1 H1 L2 U2 H2.
    dependent elimination H1. dependent elimination H2.
    split; apply tau_struct_conv_refl.
  - intros L1 U1 H1 L2 U2 H2.
    destruct (IHTau_StructConv L2 U2 H2 L1 U1 H1) as [Hlo Hhi].
    split; now apply tau_struct_conv_symm.
  - intros L1 U1 Hstart L3 U3 Hend.
    dependent elimination d2.
    destruct (IHTau_StructConv1 L1 U1 Hstart t0 t1 eq_refl)
      as [Hlo1 Hhi1].
    destruct (IHTau_StructConv2 t0 t1 eq_refl L3 U3 Hend)
      as [Hlo2 Hhi2].
    split; eapply tau_struct_conv_trans; eassumption.
  - intros L1 U1 H1 L2 U2 H2.
    dependent elimination template.
    cbn [Tau_open Tau_subst Ty_subst] in H1, H2.
    dependent elimination H1. dependent elimination H2.
    split.
    + exact (tau_struct_conv_replace (tau_ty t0) H).
    + exact (tau_struct_conv_replace (tau_ty t1) H).
Qed.

Theorem Tau_StructConv_interval_components {n : nat}
    {R : Path n -> Path n -> Prop} {L1 U1 L2 U2 : Ty n}
    (H : Tau_StructConv R
      (tau_intv L1 U1) (tau_intv L2 U2)) :
    Tau_StructConv R (tau_ty L1) (tau_ty L2) /\
    Tau_StructConv R (tau_ty U1) (tau_ty U2).
Proof.
  exact (@Tau_StructConv_interval_components_aux n R _ _ H
    L1 U1 eq_refl L2 U2 eq_refl).
Qed.

Print Assumptions Tau_swap01_open_weaken.
Print Assumptions Tau_StructConv_fun_parts.
Print Assumptions Tau_StructConv_pair_label_kind.
Print Assumptions Tau_StructConv_pair_components.
Print Assumptions Tau_StructConv_single_paths.
Print Assumptions Tau_StructConv_tsel_parts.
Print Assumptions Tau_StructConv_top_target_eq.
Print Assumptions Tau_StructConv_interval_components.
