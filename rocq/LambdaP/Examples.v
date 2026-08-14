From PathDependent.LambdaP Require Import FinFun Syntax Context Typing.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Module Examples.

(** The exact type member [{x}..{x}], where [x] is the pair binder. *)
Definition exactSelfMember (n : nat) : Tau (S n) iota :=
  tau_intv (ty_single (path_var Fin.zero))
    (ty_single (path_var Fin.zero)).

(** The proper abstract interval [Bot..{x}]. *)
Definition abstractSelfMember (n : nat) : Tau (S n) iota :=
  tau_intv ty_bot (ty_single (path_var Fin.zero)).

Theorem pair_single_member_widen_exact_interval
    {n : nat} {G : Ctx n} {p : Path n} {P : Ty n} {a : Name}
    {L T U : Ty (S n)}
    (hp : Path_Ty G p (tau_ty P))
    (hlo : Tau_Sub (ctx_snoc G (ty_single p)) (tau_ty L) (tau_ty T))
    (hhi : Tau_Sub (ctx_snoc G (ty_single p)) (tau_ty T) (tau_ty U))
    (hloOpen : Tau_Sub G (tau_ty (Ty_open L p)) (tau_ty (Ty_open T p)))
    (hhiOpen : Tau_Sub G (tau_ty (Ty_open T p)) (tau_ty (Ty_open U p))) :
    Tau_Sub G
      (tau_ty (ty_pair (ty_single p) a (tau_intv T T)))
      (tau_ty (ty_pair (ty_single p) a (tau_intv L U))).
Proof.
  eapply sub_pair_single_member; [exact hp| |].
  - exact (sub_bounds _ _ _ _ _ hlo hhi (sub_refl _ _)).
  - exact (sub_bounds _ _ _ _ _ hloOpen hhiOpen (sub_refl _ _)).
Qed.

Theorem pair_rules_widen_exact_interval
    {n : nat} {G : Ctx n} {p : Path n} {P : Ty n} {a : Name}
    {L T U : Ty (S n)}
    (hp : Path_Ty G p (tau_ty P))
    (hlo : Tau_Sub (ctx_snoc G (ty_single p)) (tau_ty L) (tau_ty T))
    (hhi : Tau_Sub (ctx_snoc G (ty_single p)) (tau_ty T) (tau_ty U))
    (hloOpen : Tau_Sub G (tau_ty (Ty_open L p)) (tau_ty (Ty_open T p)))
    (hhiOpen : Tau_Sub G (tau_ty (Ty_open T p)) (tau_ty (Ty_open U p))) :
    Tau_Sub G
      (tau_ty (ty_pair (ty_single p) a (tau_intv T T)))
      (tau_ty (ty_pair P a (tau_intv L U))).
Proof.
  eapply sub_trans.
  - exact (pair_single_member_widen_exact_interval hp hlo hhi
      hloOpen hhiOpen).
  - apply sub_pair_fst. now apply sub_widen.
Qed.

Theorem exact_self_member_to_abstract_self_member
    {n : nat} {G : Ctx n} {p : Path n} {P : Ty n} {a : Name}
    (hp : Path_Ty G p (tau_ty P)) :
    Tau_Sub G
      (tau_ty (ty_pair (ty_single p) a (exactSelfMember n)))
      (tau_ty (ty_pair (ty_single p) a (abstractSelfMember n))).
Proof.
  unfold exactSelfMember, abstractSelfMember.
  eapply sub_pair_single_member; [exact hp| |].
  - apply sub_bounds.
    + apply sub_bot.
    + apply sub_refl.
    + apply sub_refl.
  - apply sub_bounds.
    + apply sub_bot.
    + apply sub_refl.
    + apply sub_refl.
Qed.

Theorem exact_self_member_to_widened_abstract_pair
    {n : nat} {G : Ctx n} {p : Path n} {P : Ty n} {a : Name}
    (hp : Path_Ty G p (tau_ty P)) :
    Tau_Sub G
      (tau_ty (ty_pair (ty_single p) a (exactSelfMember n)))
      (tau_ty (ty_pair P a (abstractSelfMember n))).
Proof.
  eapply sub_trans.
  - exact (@exact_self_member_to_abstract_self_member n G p P a hp).
  - apply sub_pair_fst. now apply sub_widen.
Qed.

Definition storedExactMember {n : nat} (p : Path n) : Tau (S n) iota :=
  Tau_weaken (tau_intv (ty_single p) (ty_single p)).

Theorem typed_type_pair_at_dependent_abstract_type
    {n : nat} {G : Ctx n} {y : Fin.t n} {P : Ty n} {A : Name}
    (hy : Ctx_Binds G y P)
    (hP : Tau_Wf G (tau_ty P)) :
    Tm_Ty G
      (tm_pair y A (def_type (ty_single (path_var y))))
      (ty_pair P A (abstractSelfMember n)).
Proof.
  set (p := path_var y : Path n).
  assert (hp : Path_Ty G p (tau_ty P)).
  { unfold p. now apply path_ty_var. }
  assert (hnew : Path_Ty (ctx_snoc G (ty_single p))
      (path_var Fin.zero) (tau_ty (Ty_weaken (ty_single p)))).
  { exact (path_ty_var _ _ _ (binds_here G (ty_single p))). }
  assert (hmember : Tau_Sub G
      (tau_ty (ty_pair (ty_single p) A (storedExactMember p)))
      (tau_ty (ty_pair (ty_single p) A (abstractSelfMember n)))).
  { eapply sub_pair_single_member; [exact hp| |].
    - unfold storedExactMember, abstractSelfMember.
      cbn.
      apply sub_bounds.
      + apply sub_bot.
      + now apply sub_symm.
      + apply sub_refl.
    - unfold storedExactMember, abstractSelfMember.
      rewrite !Tau_weaken_open.
      cbn.
      apply sub_bounds.
      + apply sub_bot.
      + apply sub_refl.
      + apply sub_refl. }
  assert (hsub : Tau_Sub G
      (tau_ty (ty_pair (ty_single p) A (storedExactMember p)))
      (tau_ty (ty_pair P A (abstractSelfMember n)))).
  { eapply sub_trans; [exact hmember|].
    apply sub_pair_fst. now apply sub_widen. }
  assert (hnewP : Path_Ty (ctx_snoc G P) (path_var Fin.zero)
      (tau_ty (Ty_weaken P))).
  { exact (path_ty_var _ _ _ (binds_here G P)). }
  assert (htarget : Tau_Wf G
      (tau_ty (ty_pair P A (abstractSelfMember n)))).
  { apply wf_pair.
    - exact hP.
    - unfold abstractSelfMember. apply wf_bounds.
      + apply wf_bot.
      + exact (wf_path _ _ (Ty_weaken P) hnewP).
      + apply sub_bot. }
  eapply tm_ty_sub; [|exact hsub|exact htarget].
  change (Tm_Ty G
    (tm_pair y A (def_type (ty_single (path_var y))))
    (ty_pair (ty_single p) A (storedExactMember p))).
  apply tm_ty_tpair with (S := P).
  - exact hy.
  - exact (wf_path _ _ P hp).
Qed.

End Examples.
