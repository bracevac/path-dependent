From PathDependent.LambdaP Require Import FinFun Syntax Context Typing.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** First-order projections keep constructor injectivity proofs independent
    of proof irrelevance for the intrinsic scope indices. *)
Local Definition tm_path_projection {n : nat} (t : Tm n) : option (Path n) :=
  match t with
  | tm_path p => Some p
  | _ => None
  end.

Local Definition tm_app_left_projection {n : nat} (t : Tm n) :
    option (Path n) :=
  match t with
  | tm_app p _ => Some p
  | _ => None
  end.

Local Definition tm_app_right_projection {n : nat} (t : Tm n) :
    option (Path n) :=
  match t with
  | tm_app _ q => Some q
  | _ => None
  end.

Local Lemma tm_path_injective {n : nat} (p q : Path n) :
    tm_path p = tm_path q -> p = q.
Proof.
  intro H.
  pose proof (f_equal (@tm_path_projection n) H) as Hp.
  cbn in Hp. now injection Hp.
Qed.

Local Lemma tm_app_injective {n : nat} (p q p' q' : Path n) :
    tm_app p q = tm_app p' q' -> p = p' /\ q = q'.
Proof.
  intro H. split.
  - pose proof (f_equal (@tm_app_left_projection n) H) as Hp.
    cbn in Hp. now injection Hp.
  - pose proof (f_equal (@tm_app_right_projection n) H) as Hq.
    cbn in Hq. now injection Hq.
Qed.

(** A typing derivation for a path term consists of its precise path
    classification followed by zero or more subsumption steps. *)
Theorem Tm_Ty_path_inversion
    {n : nat} {G : Ctx n} {t : Tm n} {T : Ty n}
    (H : Tm_Ty G t T) :
    forall (p : Path n), t = tm_path p ->
      exists U,
        Path_Ty G p (tau_ty U) /\
        Tau_Sub G (tau_ty (ty_single p)) (tau_ty T) /\
        Tau_Wf G (tau_ty T).
Proof.
  induction H as
      [n G p T Hp
      |n G S t T Ht IH Hwf
      |n G p q S T Hp IHp Hq IHq
      |n G y z S T a Hy Hz
      |n G y S T A Hy Hwf
      |n G s S T t Hs IHs Hwf Ht IHt
      |n G t T Ht IH Hwf
      |n G t S T Ht IH Hsub Hwf];
      intros p0 Heq.
  - apply tm_path_injective in Heq. subst p0.
    exists T. repeat split.
    + exact Hp.
    + exact (sub_refl G (tau_ty (ty_single p))).
    + exact (wf_path G p T Hp).
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - destruct (IH p0 Heq) as [U [Hp [Hbase Hbase_wf]]].
    exists U. repeat split.
    + exact Hp.
    + eapply sub_trans; [exact Hbase | exact Hsub].
    + exact Hwf.
Qed.

(** Any typing of a path term factors through subtyping from the path's
    principal singleton. *)
Theorem Tm_Ty_path_subtyping
    {n : nat} {G : Ctx n} {p : Path n} {T : Ty n}
    (H : Tm_Ty G (tm_path p) T) :
    Tau_Sub G (tau_ty (ty_single p)) (tau_ty T).
Proof.
  destruct (@Tm_Ty_path_inversion n G (tm_path p) T H p eq_refl)
    as [U [Hp [Hsub Hwf]]].
  exact Hsub.
Qed.

(** Trailing subsumption does not obscure the two premises of an
    application typing derivation. *)
Theorem Tm_Ty_app_inversion_of_eq
    {n : nat} {G : Ctx n} {u : Tm n} {R : Ty n}
    (H : Tm_Ty G u R) :
    forall (p q : Path n), u = tm_app p q ->
      exists (S : Ty n) (T : Ty (Datatypes.S n)),
        Tm_Ty G (tm_path p) (ty_fun S T) /\
        Tm_Ty G (tm_path q) S.
Proof.
  induction H as
      [n G p T Hp
      |n G S t T Ht IH Hwf
      |n G p q S T Hp IHp Hq IHq
      |n G y z S T a Hy Hz
      |n G y S T A Hy Hwf
      |n G s S T t Hs IHs Hwf Ht IHt
      |n G t T Ht IH Hwf
      |n G t S T Ht IH Hsub Hwf];
      intros p0 q0 Heq.
  - discriminate Heq.
  - discriminate Heq.
  - destruct (tm_app_injective Heq) as [Heqp Heqq]. subst p0 q0.
    exists S, T. now split.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - exact (IH p0 q0 Heq).
Qed.

(** Public application inversion. *)
Theorem Tm_Ty_app_inversion
    {n : nat} {G : Ctx n} {p q : Path n} {R : Ty n}
    (H : Tm_Ty G (tm_app p q) R) :
    exists (S : Ty n) (T : Ty (Datatypes.S n)),
      Tm_Ty G (tm_path p) (ty_fun S T) /\
      Tm_Ty G (tm_path q) S.
Proof.
  exact (@Tm_Ty_app_inversion_of_eq n G (tm_app p q) R H p q eq_refl).
Qed.

Print Assumptions Tm_Ty_path_inversion.
Print Assumptions Tm_Ty_app_inversion.
