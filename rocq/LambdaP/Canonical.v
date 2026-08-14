From Stdlib Require Import Arith.PeanoNat Logic.Eqdep_dec.
From Equations Require Import Equations.
From PathDependent.LambdaP Require Import FinFun Syntax Context Typing
  PreciseStore PathFunctionality.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Derive NoConfusion for Ty.
Derive NoConfusion for Tau.

(** The concrete head of a value type. *)
Inductive Ty_Head : Type :=
| head_arrow
| head_pair (a : Name).

Definition Ty_Head_eq_dec (h1 h2 : Ty_Head) : {h1 = h2} + {h1 <> h2}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Derive NoConfusion for Ty_Head.

(** A concrete value head admitted by a generalized type. *)
Inductive Tau_MayHead {n : nat} (G : Ctx n) :
    forall {k : Kind}, Tau n k -> Ty_Head -> Prop :=
| tau_may_head_top (h : Ty_Head) :
    Tau_MayHead G (tau_ty ty_top) h
| tau_may_head_arrow (S0 : Ty n) (T : Ty (S n)) :
    Tau_MayHead G (tau_ty (ty_fun S0 T)) head_arrow
| tau_may_head_pair {k : Kind}
    (S0 : Ty n) (a : Name) (d : Tau (S n) k) :
    Tau_MayHead G (tau_ty (ty_pair S0 a d)) (head_pair a)
| tau_may_head_single (p : Path n) (T : Ty n) (h : Ty_Head) :
    Path_Ty G p (tau_ty T) ->
    Tau_MayHead G (tau_ty T) h ->
    Tau_MayHead G (tau_ty (ty_single p)) h
| tau_may_head_tsel
    (p : Path n) (A : Name) (L U : Ty n) (h : Ty_Head) :
    Path_Ty G (path_sel p A) (tau_intv L U) ->
    Tau_MayHead G (tau_ty U) h ->
    Tau_MayHead G (tau_ty (ty_tsel p A)) h
| tau_may_head_interval (L U : Ty n) (h : Ty_Head) :
    Tau_MayHead G (tau_ty U) h ->
    Tau_MayHead G (tau_intv L U) h.

Arguments tau_may_head_top {n} G h.
Arguments tau_may_head_arrow {n} G S0 T.
Arguments tau_may_head_pair {n} G {k} S0 a d.
Arguments tau_may_head_single {n} G p T h _ _.
Arguments tau_may_head_tsel {n} G p A L U h _ _.
Arguments tau_may_head_interval {n} G L U h _.

(** First-order observations of fixed-kind generalized types. *)
Definition Tau_ty_projection {n : nat} (d : Tau n star) : Ty n :=
  match d with tau_ty T => T end.

Definition Tau_upper_projection {n : nat} (d : Tau n iota) : Ty n :=
  match d with tau_intv _ U => U end.

Definition Tau_to_upper {n : nat} {k : Kind}
    (d : Tau n k) : option (Ty n) :=
  match d with
  | tau_ty _ => None
  | tau_intv _ U => Some U
  end.

Definition PackedTau_to_upper {n : nat}
    (d : PackedTau n) : option (Ty n) :=
  match d with existT _ _ member => Tau_to_upper member end.

Lemma Tau_DEq_ty_eq {n : nat} {T U : Ty n}
    (H : Tau_DEq (tau_ty T) (tau_ty U)) : T = U.
Proof.
  pose proof (f_equal PackedTau_to_ty (Tau_DEq_pack_eq H)) as E.
  cbn in E. now injection E.
Qed.

Lemma Tau_DEq_upper_eq {n : nat} {L1 U1 L2 U2 : Ty n}
    (H : Tau_DEq (tau_intv L1 U1) (tau_intv L2 U2)) : U1 = U2.
Proof.
  pose proof (f_equal PackedTau_to_upper (Tau_DEq_pack_eq H)) as E.
  cbn in E. now injection E.
Qed.

Lemma PackedNat_same_index_inj {P : nat -> Type} {n : nat} {p q : P n}
    (E : existT P n p = existT P n q) : p = q.
Proof.
  exact (inj_pair2_eq_dec nat Nat.eq_dec P n p q E).
Qed.

Ltac unpack_path_equality :=
  lazymatch goal with
  | E : @existT nat ?P ?n ?p = @existT nat ?P ?n ?q |- _ =>
      let Ep := fresh "Epath" in
      assert (Ep : p = q) by exact (PackedNat_same_index_inj E);
      clear E;
      first [ is_var p; subst p | is_var q; subst q ]
  end.

Ltac align_singleton_path_types :=
  lazymatch goal with
  | H1 : Path_Ty ?G ?p (tau_ty ?T1),
    H2 : Path_Ty ?G ?p (tau_ty ?T2),
    HH : Tau_MayHead ?G (tau_ty ?T1) ?h
    |- Tau_MayHead ?G (tau_ty ?T2) ?h =>
      let E := fresh "Etype" in
      assert (E : T1 = T2) by
        (pose proof (Path_Ty_functional H1 H2) as D;
         exact (Tau_DEq_ty_eq D));
      subst T2; exact HH
  end.

Ltac align_selection_upper_bounds :=
  lazymatch goal with
  | H1 : Path_Ty ?G (path_sel ?p ?A) (tau_intv ?L1 ?U1),
    H2 : Path_Ty ?G (path_sel ?p ?A) (tau_intv ?L2 ?U2),
    HH : Tau_MayHead ?G (tau_ty ?U1) ?h
    |- Tau_MayHead ?G (tau_ty ?U2) ?h =>
      let E := fresh "Eupper" in
      assert (E : U1 = U2) by
        (pose proof (Path_Ty_functional H1 H2) as D;
         exact (Tau_DEq_upper_eq D));
      subst U2; exact HH
  end.

(** Subtyping preserves every admitted concrete head. *)
Theorem Tau_Sub_mayHead {n : nat} {k : Kind} {G : Ctx n}
    {d1 d2 : Tau n k} {h : Ty_Head}
    (Hs : Tau_Sub G d1 d2) (Hh : Tau_MayHead G d1 h) :
    Tau_MayHead G d2 h.
Proof.
  induction Hs.
  - exact Hh.
  - apply IHHs2. now apply IHHs1.
  - inversion Hh.
  - apply tau_may_head_top.
  - inversion Hh. unpack_path_equality. align_singleton_path_types.
  - eapply tau_may_head_single; eassumption.
  - inversion Hh. unpack_path_equality. align_selection_upper_bounds.
  - eapply tau_may_head_tsel; [eassumption | now apply IHHs].
  - inversion Hh. apply tau_may_head_arrow.
  - inversion Hh. apply tau_may_head_pair.
  - inversion Hh. apply tau_may_head_pair.
  - inversion Hh.
    unpack_path_equality. unpack_path_equality.
    apply tau_may_head_interval. now apply IHHs2.
Qed.

Theorem Tau_Sub_pair_not_fun {n : nat} {G : Ctx n}
    {k : Kind} {S0 U : Ty n} {a : Name}
    {d : Tau (S n) k} {V : Ty (S n)}
    (Hs : Tau_Sub G (tau_ty (ty_pair S0 a d))
      (tau_ty (ty_fun U V))) : False.
Proof.
  pose proof (Tau_Sub_mayHead Hs
    (tau_may_head_pair G S0 a d)) as Hh.
  inversion Hh.
Qed.

Theorem Tau_Sub_fun_not_pair {n : nat} {G : Ctx n}
    {k : Kind} {S0 : Ty n} {T : Ty (S n)}
    {U : Ty n} {a : Name} {d : Tau (S n) k}
    (Hs : Tau_Sub G (tau_ty (ty_fun S0 T))
      (tau_ty (ty_pair U a d))) : False.
Proof.
  pose proof (Tau_Sub_mayHead Hs
    (tau_may_head_arrow G S0 T)) as Hh.
  inversion Hh.
Qed.

Theorem Tau_Sub_pair_label {n : nat} {G : Ctx n}
    {k1 k2 : Kind} {S0 U : Ty n} {a b : Name}
    {d1 : Tau (S n) k1} {d2 : Tau (S n) k2}
    (Hs : Tau_Sub G (tau_ty (ty_pair S0 b d1))
      (tau_ty (ty_pair U a d2))) : b = a.
Proof.
  pose proof (Tau_Sub_mayHead Hs
    (tau_may_head_pair G S0 b d1)) as Hh.
  inversion Hh. reflexivity.
Qed.

Theorem Tm_PreciseTy_fun_canonical {n : nat} {G : Ctx n}
    {v : Tm n} {P S0 : Ty n} {T : Ty (S n)}
    (Hp : Tm_PreciseTy G v P)
    (Hs : Tau_Sub G (tau_ty P) (tau_ty (ty_fun S0 T))) :
    exists (A : Ty n) (body : Tm (S n)) (B : Ty (S n)),
      v = tm_abs A body /\
      P = ty_fun A B /\
      Tm_Ty (ctx_snoc G A) body B /\
      Tau_Wf G (tau_ty A).
Proof.
  dependent elimination Hp.
  - eexists _, _, _. repeat split; eauto.
  - exfalso. eapply Tau_Sub_pair_not_fun. exact Hs.
  - exfalso. eapply Tau_Sub_pair_not_fun. exact Hs.
Qed.

Theorem Tm_PreciseTy_pair_canonical {n : nat} {G : Ctx n}
    {k : Kind} {v : Tm n} {P S0 : Ty n} {a : Name}
    {d : Tau (S n) k}
    (Hp : Tm_PreciseTy G v P)
    (Hs : Tau_Sub G (tau_ty P) (tau_ty (ty_pair S0 a d))) :
    (exists (y z : Fin.t n),
      v = tm_pair y a (def_val z) /\
      P = ty_pair (ty_single (path_var y)) a
        (tau_ty (ty_single (Path_weaken (path_var z))))) \/
    (exists (y : Fin.t n) (U : Ty n),
      v = tm_pair y a (def_type U) /\
      P = ty_pair (ty_single (path_var y)) a
        (Tau_weaken (tau_intv U U))).
Proof.
  dependent elimination Hp.
  - exfalso. eapply Tau_Sub_fun_not_pair. exact Hs.
  - left.
    pose proof (Tau_Sub_pair_label Hs) as E. subst a.
    eexists _, _. split; reflexivity.
  - right.
    pose proof (Tau_Sub_pair_label Hs) as E. subst a.
    eexists _, _. split; reflexivity.
Qed.

Print Assumptions Tau_Sub_mayHead.
Print Assumptions Tm_PreciseTy_fun_canonical.
Print Assumptions Tm_PreciseTy_pair_canonical.
