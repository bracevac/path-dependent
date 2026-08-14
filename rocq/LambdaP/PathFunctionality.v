From Stdlib Require Import Logic.JMeq.
From Equations Require Import Equations.
From PathDependent.LambdaP Require Import FinFun Syntax Context Typing.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Derive NoConfusion for Path.
Derive NoConfusion for Kind.

(** Dependent equality of generalized types, including equality of their kind
    indices. *)
Inductive Tau_DEq {n : nat} {k : Kind} (d : Tau n k) :
    forall k' : Kind, Tau n k' -> Prop :=
| tau_deq_refl : Tau_DEq d d.

Arguments tau_deq_refl {n k d}.

Theorem Tau_DEq_kind_eq {n : nat} {k1 k2 : Kind}
    {d1 : Tau n k1} {d2 : Tau n k2} (H : Tau_DEq d1 d2) : k1 = k2.
Proof. destruct H. reflexivity. Qed.

Theorem Tau_DEq_jmeq {n : nat} {k1 k2 : Kind}
    {d1 : Tau n k1} {d2 : Tau n k2} (H : Tau_DEq d1 d2) : JMeq d1 d2.
Proof. destruct H. reflexivity. Qed.

Definition PackedTau (n : nat) : Type := { k : Kind & Tau n k }.

Theorem Tau_DEq_pack_eq {n : nat} {k1 k2 : Kind}
    {d1 : Tau n k1} {d2 : Tau n k2} (H : Tau_DEq d1 d2) :
    existT (Tau n) k1 d1 = existT (Tau n) k2 d2.
Proof. destruct H. reflexivity. Qed.

Definition Tau_to_ty {n : nat} {k : Kind} (d : Tau n k) : option (Ty n) :=
  match d with
  | tau_ty T => Some T
  | tau_intv _ _ => None
  end.

Definition PackedTau_to_ty {n : nat} (d : PackedTau n) : option (Ty n) :=
  match d with existT _ _ member => Tau_to_ty member end.

Definition option_value {A : Type} (default : A) (o : option A) : A :=
  match o with Some x => x | None => default end.

Definition Ty_pair_first {n : nat} (T : Ty n) : option (Ty n) :=
  match T with
  | ty_pair S0 _ _ => Some S0
  | _ => None
  end.

Definition Ty_pair_label {n : nat} (T : Ty n) : option Name :=
  match T with
  | ty_pair _ a _ => Some a
  | _ => None
  end.

Definition Ty_pair_member {n : nat} (T : Ty n) : option (PackedTau (S n)) :=
  match T in Ty n' return option (PackedTau (S n')) with
  | @ty_pair n' k _ _ d => Some (existT (Tau (S n')) k d)
  | _ => None
  end.

Lemma Tau_DEq_pair_first {n : nat} {k1 k2 : Kind}
    {S1 S2 : Ty n} {a1 a2 : Name}
    {d1 : Tau (S n) k1} {d2 : Tau (S n) k2}
    (H : Tau_DEq (tau_ty (ty_pair S1 a1 d1))
      (tau_ty (ty_pair S2 a2 d2))) : S1 = S2.
Proof.
  pose proof (f_equal PackedTau_to_ty (Tau_DEq_pack_eq H)) as E.
  pose proof (f_equal (option_value (ty_pair S1 a1 d1)) E) as ET.
  cbn in ET.
  pose proof (f_equal Ty_pair_first ET) as E'. cbn in E'. now injection E'.
Qed.

Lemma Tau_DEq_pair_label {n : nat} {k1 k2 : Kind}
    {S1 S2 : Ty n} {a1 a2 : Name}
    {d1 : Tau (S n) k1} {d2 : Tau (S n) k2}
    (H : Tau_DEq (tau_ty (ty_pair S1 a1 d1))
      (tau_ty (ty_pair S2 a2 d2))) : a1 = a2.
Proof.
  pose proof (f_equal PackedTau_to_ty (Tau_DEq_pack_eq H)) as E.
  pose proof (f_equal (option_value (ty_pair S1 a1 d1)) E) as ET.
  cbn in ET.
  pose proof (f_equal Ty_pair_label ET) as E'. cbn in E'. now injection E'.
Qed.

Lemma Tau_DEq_pair_member {n : nat} {k1 k2 : Kind}
    {S1 S2 : Ty n} {a1 a2 : Name}
    {d1 : Tau (S n) k1} {d2 : Tau (S n) k2}
    (H : Tau_DEq (tau_ty (ty_pair S1 a1 d1))
      (tau_ty (ty_pair S2 a2 d2))) : Tau_DEq d1 d2.
Proof.
  pose proof (f_equal PackedTau_to_ty (Tau_DEq_pack_eq H)) as E.
  pose proof (f_equal (option_value (ty_pair S1 a1 d1)) E) as ET.
  cbn in ET.
  pose proof (f_equal Ty_pair_member ET) as E'. cbn in E'.
  assert (existT (Tau (S n)) k1 d1 = existT (Tau (S n)) k2 d2) as Ep
    by now injection E'.
  dependent elimination Ep. constructor.
Qed.

Lemma Tau_DEq_open {n : nat} {k1 k2 : Kind}
    {d1 : Tau (S n) k1} {d2 : Tau (S n) k2}
    (H : Tau_DEq d1 d2) (p : Path n) :
    Tau_DEq (Tau_open d1 p) (Tau_open d2 p).
Proof. destruct H. constructor. Qed.

(** Precise path typing is functional. *)
Theorem Path_Ty_functional {n : nat} {G : Ctx n} {p : Path n}
    {k1 k2 : Kind} {d1 : Tau n k1} {d2 : Tau n k2}
    (H1 : Path_Ty G p d1) (H2 : Path_Ty G p d2) : Tau_DEq d1 d2.
Proof.
  induction H1 in k2, d2, H2 |- *.
  - dependent elimination H2.
    assert (T = T0) as ->.
    { lazymatch goal with
      | Hleft : Ctx_Binds ?G ?x T,
        Hright : Ctx_Binds ?G ?x T0 |- _ =>
          exact (Ctx_Binds_unique Hleft Hright)
      end. }
    apply tau_deq_refl.
  - dependent elimination H2.
    pose proof (IHPath_Ty _ _ p1) as E.
    assert (S = S0) as -> by exact (Tau_DEq_pair_first E).
    apply tau_deq_refl.
  - dependent elimination H2.
    + pose proof (IHPath_Ty _ _ p3) as E.
      exact (Tau_DEq_open (Tau_DEq_pair_member E) (path_fst p2)).
    + pose proof (IHPath_Ty _ _ p5) as E.
      exfalso. apply n4. exact (Tau_DEq_pair_label E).
  - dependent elimination H2.
    + pose proof (IHPath_Ty1 _ _ p3) as E.
      exfalso. apply H. symmetry. exact (Tau_DEq_pair_label E).
    + exact (IHPath_Ty2 _ _ p6).
Qed.

Theorem Path_Ty_kind_unique {n : nat} {G : Ctx n} {p : Path n}
    {k1 k2 : Kind} {d1 : Tau n k1} {d2 : Tau n k2}
    (H1 : Path_Ty G p d1) (H2 : Path_Ty G p d2) : k1 = k2.
Proof. exact (Tau_DEq_kind_eq (Path_Ty_functional H1 H2)). Qed.

Theorem Path_Ty_signature_unique {n : nat} {G : Ctx n} {p : Path n}
    {k1 k2 : Kind} {d1 : Tau n k1} {d2 : Tau n k2}
    (H1 : Path_Ty G p d1) (H2 : Path_Ty G p d2) : JMeq d1 d2.
Proof. exact (Tau_DEq_jmeq (Path_Ty_functional H1 H2)). Qed.

(** Constructor-specific inversion principles. *)
Theorem Path_Ty_invert_var {n : nat} {G : Ctx n} {x : Fin.t n}
    {k : Kind} {d : Tau n k} (H : Path_Ty G (path_var x) d) :
    exists T, Ctx_Binds G x T /\ Tau_DEq d (tau_ty T).
Proof.
  dependent elimination H. exists T. split; [assumption|constructor].
Qed.

Theorem Path_Ty_invert_fst {n : nat} {G : Ctx n} {p : Path n}
    {k : Kind} {d : Tau n k} (H : Path_Ty G (path_fst p) d) :
    exists (S0 : Ty n) (a : Name) (k' : Kind)
      (member : Tau (S n) k'),
      Path_Ty G p (tau_ty (ty_pair S0 a member)) /\
      Tau_DEq d (tau_ty S0).
Proof.
  dependent elimination H.
  exists S0, a, k0, d0. split; [assumption|constructor].
Qed.

Theorem Path_Ty_invert_sel {n : nat} {G : Ctx n} {p : Path n}
    {a : Name} {k : Kind} {d : Tau n k}
    (H : Path_Ty G (path_sel p a) d) :
    (exists (S0 : Ty n) (k' : Kind) (member : Tau (S n) k'),
      Path_Ty G p (tau_ty (ty_pair S0 a member)) /\
      Tau_DEq d (Tau_open member (path_fst p))) \/
    (exists (S0 : Ty n) (b : Name) (k' : Kind)
      (member : Tau (S n) k'),
      Path_Ty G p (tau_ty (ty_pair S0 b member)) /\
      Path_Ty G (path_sel (path_fst p) a) d /\ a <> b).
Proof.
  dependent elimination H.
  - left. exists S1, k1, d1. split; [exact p3|constructor].
  - right. exists S2, b, k', d'. repeat split;
      [exact p5 | exact p6 | exact n4].
Qed.
