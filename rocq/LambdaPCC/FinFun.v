From Equations Require Import Equations.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Intrinsically bounded de Bruijn indices.  Finite maps below are
    first-order vectors rather than functions, so their equality is
    structural and needs no functional-extensionality axiom. *)
Inductive Fin : nat -> Type :=
| FZ {n : nat} : Fin (S n)
| FS {n : nat} : Fin n -> Fin (S n).

Arguments FZ {n}.
Arguments FS {n} _.

Fixpoint fin_value {n : nat} (x : Fin n) : nat :=
  match x with
  | FZ => 0
  | FS y => S (fin_value y)
  end.

Lemma fin_value_lt {n : nat} (x : Fin n) : fin_value x < n.
Proof. induction x; cbn [fin_value]; lia. Qed.

Definition fin_elim0 {P : Fin 0 -> Type} (x : Fin 0) : P x :=
  match x with end.

Equations fin_case {n : nat} {P : Fin (S n) -> Type}
    (zero : P FZ) (succ : forall i : Fin n, P (FS i))
    (i : Fin (S n)) : P i :=
fin_case zero succ FZ := zero;
fin_case zero succ (FS i) := succ i.

(** Length-indexed vectors used as total finite maps. *)
Inductive Vec (A : Type) : nat -> Type :=
| VNil : Vec A 0
| VCons {n : nat} : A -> Vec A n -> Vec A (S n).

Arguments VNil {A}.
Arguments VCons {A n} _ _.

Fixpoint vec_lookup {A : Type} {n : nat}
    (xs : Vec A n) (i : Fin n) : A :=
  match xs in Vec _ n return Fin n -> A with
  | VNil => fun i => fin_elim0 i
  | VCons x rest =>
      fun i => fin_case x (fun j => vec_lookup rest j) i
  end i.

Fixpoint vec_map {A B : Type} {n : nat}
    (f : A -> B) (xs : Vec A n) : Vec B n :=
  match xs with
  | VNil => VNil
  | VCons x rest => VCons (f x) (vec_map f rest)
  end.

Lemma vec_lookup_map {A B : Type} {n : nat}
    (f : A -> B) (xs : Vec A n) (i : Fin n) :
    vec_lookup (vec_map f xs) i = f (vec_lookup xs i).
Proof.
  revert i.
  induction xs as [|n x xs IH]; intro i.
  - exact (@fin_elim0
      (fun i => vec_lookup (vec_map f VNil) i = f (vec_lookup VNil i)) i).
  - refine (fin_case (P := fun i =>
        vec_lookup (vec_map f (VCons x xs)) i =
          f (vec_lookup (VCons x xs) i)) _ _ i).
    + change (f x = f x). reflexivity.
    + intro j.
      change (vec_lookup (vec_map f xs) j = f (vec_lookup xs j)).
      apply IH.
Qed.

Equations vec_unique0 {A : Type} (xs : Vec A 0) : xs = VNil :=
vec_unique0 VNil := eq_refl.

Equations vec_head {A : Type} {n : nat} (xs : Vec A (S n)) : A :=
vec_head (VCons x rest) := x.

Equations vec_tail {A : Type} {n : nat} (xs : Vec A (S n)) : Vec A n :=
vec_tail (VCons x rest) := rest.

Equations vec_eta {A : Type} {n : nat} (xs : Vec A (S n)) :
    VCons (vec_head xs) (vec_tail xs) = xs :=
vec_eta (VCons x rest) := eq_refl.

Lemma vec_lookup_zero {A : Type} {n : nat} (xs : Vec A (S n)) :
    vec_lookup xs FZ = vec_head xs.
Proof.
  rewrite <- (vec_eta xs). unfold vec_lookup. simp fin_case. reflexivity.
Qed.

Lemma vec_lookup_succ {A : Type} {n : nat}
    (xs : Vec A (S n)) (i : Fin n) :
    vec_lookup xs (FS i) = vec_lookup (vec_tail xs) i.
Proof.
  rewrite <- (vec_eta xs). unfold vec_lookup. simp fin_case. reflexivity.
Qed.

Lemma vec_ext {A : Type} {n : nat} (xs ys : Vec A n) :
    (forall i, vec_lookup xs i = vec_lookup ys i) -> xs = ys.
Proof.
  revert xs ys.
  induction n as [|n IH]; intros xs ys H.
  - exact (eq_trans (vec_unique0 xs) (eq_sym (vec_unique0 ys))).
  - assert (Hhead : vec_head xs = vec_head ys).
    { rewrite <- (vec_lookup_zero xs), <- (vec_lookup_zero ys). apply H. }
    assert (Htail : vec_tail xs = vec_tail ys).
    { apply IH. intro i.
      rewrite <- (vec_lookup_succ xs i), <- (vec_lookup_succ ys i).
      apply H. }
    refine (eq_trans (eq_sym (vec_eta xs)) _).
    refine (eq_trans (f_equal2 (fun head tail => VCons head tail)
      Hhead Htail) _).
    apply vec_eta.
Qed.

(** A renaming between scopes represented as a first-order finite table. *)
Definition FinFun (n m : nat) : Type := Vec (Fin m) n.

Definition apply {n m : nat} (f : FinFun n m) (i : Fin n) : Fin m :=
  vec_lookup f i.

Lemma finfun_ext {n m : nat} (f g : FinFun n m) :
    (forall i, apply f i = apply g i) -> f = g.
Proof. apply vec_ext. Qed.

Fixpoint id (n : nat) : FinFun n n :=
  match n as n return FinFun n n with
  | 0 => VNil
  | S n => VCons FZ (vec_map FS (id n))
  end.

Definition comp {n m k : nat}
    (f : FinFun n m) (g : FinFun m k) : FinFun n k :=
  vec_map (apply g) f.

Definition weaken (n : nat) : FinFun n (S n) :=
  vec_map FS (id n).

Definition openAt {n : nat} (x : Fin n) : FinFun (S n) n :=
  VCons x (id n).

Definition ext {n m : nat} (f : FinFun n m) : FinFun (S n) (S m) :=
  VCons FZ (vec_map FS f).

Lemma id_apply {n : nat} (i : Fin n) : apply (id n) i = i.
Proof.
  induction i as [n|n i IH].
  - reflexivity.
  - cbn [id apply vec_lookup].
    simp fin_case.
    rewrite vec_lookup_map. f_equal. exact IH.
Qed.

Lemma comp_apply {n m k : nat}
    (f : FinFun n m) (g : FinFun m k) (i : Fin n) :
    apply (comp f g) i = apply g (apply f i).
Proof. unfold comp, apply. apply vec_lookup_map. Qed.

Lemma weaken_apply {n : nat} (i : Fin n) :
    apply (weaken n) i = FS i.
Proof.
  unfold weaken, apply. rewrite vec_lookup_map.
  change (FS (apply (id n) i) = FS i).
  rewrite id_apply. reflexivity.
Qed.

Lemma openAt_zero {n : nat} (x : Fin n) : apply (openAt x) FZ = x.
Proof.
  unfold openAt, apply, vec_lookup. simp fin_case.
  reflexivity.
Qed.

Lemma openAt_succ {n : nat} (x i : Fin n) :
    apply (openAt x) (FS i) = i.
Proof.
  unfold openAt, apply, vec_lookup. simp fin_case.
  change (apply (id n) i = i). apply id_apply.
Qed.

Lemma ext_zero {n m : nat} (f : FinFun n m) : apply (ext f) FZ = FZ.
Proof. unfold ext, apply, vec_lookup. simp fin_case. reflexivity. Qed.

Lemma ext_succ {n m : nat} (f : FinFun n m) (i : Fin n) :
    apply (ext f) (FS i) = FS (apply f i).
Proof.
  unfold ext, apply at 1. unfold vec_lookup. simp fin_case.
  rewrite vec_lookup_map. reflexivity.
Qed.

Lemma ext_id {n : nat} : ext (id n) = id (S n).
Proof. reflexivity. Qed.

Lemma comp_weaken {n m : nat} (f : FinFun n m) :
    comp f (weaken m) = comp (weaken n) (ext f).
Proof.
  apply finfun_ext. intro i.
  repeat rewrite comp_apply.
  repeat rewrite weaken_apply.
  rewrite ext_succ. reflexivity.
Qed.

Lemma ext_comp {n m k : nat} (f : FinFun n m) (g : FinFun m k) :
    comp (ext f) (ext g) = ext (comp f g).
Proof.
  apply finfun_ext. intro i.
  refine (fin_case (P := fun i =>
      apply (comp (ext f) (ext g)) i = apply (ext (comp f g)) i)
      _ _ i).
  - repeat rewrite comp_apply. repeat rewrite ext_zero. reflexivity.
  - intro j. repeat rewrite comp_apply. repeat rewrite ext_succ.
    rewrite comp_apply. reflexivity.
Qed.

Create Rewrite HintDb finfun.
#[export] Hint Rewrite @id_apply @comp_apply @weaken_apply
  @openAt_zero @openAt_succ @ext_zero @ext_succ : finfun.

Print Assumptions ext_comp.
