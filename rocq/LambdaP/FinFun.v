From Stdlib Require Import Arith.PeanoNat.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Intrinsically bounded de Bruijn indices.  We use an inductive finite
    ordinal rather than a sigma type, so equality never depends on proof
    irrelevance. *)
Module Fin.

Inductive t : nat -> Type :=
| zero {n} : t (S n)
| succ {n} : t n -> t (S n).

Arguments zero {n}.
Arguments succ {n} _.

Definition elim0 {A : Type} (x : t 0) : A :=
  match x with end.

Definition cases' {n : nat} (x : t (S n)) :
    forall (P : t (S n) -> Type)
      (P0 : P zero) (PS : forall y : t n, P (succ y)), P x :=
  match x with
  | @zero k => fun P P0 PS => P0
  | @succ k y => fun P P0 PS => PS y
  end.

Definition cases {n : nat} {A : Type}
    (z : A) (s : t n -> A) (x : t (S n)) : A :=
  @cases' n x (fun _ => A) z s.

Definition succ_inj {n : nat} (x y : t n)
    (H : succ x = succ y) : x = y :=
  match H in _ = a return
    match a as a' in t m return
      match m with
      | 0 => Prop
      | S n' => t n' -> Prop
      end
    with
    | zero => fun _ => True
    | succ y' => fun x' => x' = y'
    end x
  with
  | eq_refl => eq_refl
  end.

Fixpoint to_nat {n : nat} (x : t n) : nat :=
  match x with
  | zero => 0
  | succ y => S (to_nat y)
  end.

Theorem to_nat_inj {n : nat} (x y : t n) :
    to_nat x = to_nat y -> x = y.
Proof.
  induction x as [n|n x IH].
  - refine (@cases' n y
      (fun y => to_nat zero = to_nat y -> zero = y) _ _).
    + intros _. reflexivity.
    + intros y' H. discriminate H.
  - refine (@cases' n y
      (fun y => to_nat (succ x) = to_nat y -> succ x = y) _ _).
    + intros H. discriminate H.
    + intros y' H.
      apply f_equal. apply IH. now apply Nat.succ_inj in H.
Qed.

Definition eq_dec {n : nat} (x y : t n) : {x = y} + {x <> y}.
Proof.
  destruct (Nat.eq_dec (to_nat x) (to_nat y)) as [H|H].
  - left. now apply to_nat_inj.
  - right. intro E. apply H. now subst y.
Defined.

End Fin.

(** A first-order, length-indexed environment.  This is the representation
    used for both renamings and path substitutions. *)
Module Env.

Inductive t (A : Type) : nat -> Type :=
| nil : t A 0
| cons {n} : A -> t A n -> t A (S n).

Arguments nil {A}.
Arguments cons {A n} _ _.

(** Dependent eliminators specialized to empty and non-empty environments.
    These are kernel pattern matches, so they do not require uniqueness of
    identity proofs. *)
Definition case0 {A : Type} (P : t A 0 -> Type)
    (H : P nil) (e : t A 0) : P e :=
  match e with
  | nil => H
  | cons _ _ => fun devil => False_rect IDProp devil
  end.

Definition caseS' {A : Type} {n : nat} (e : t A (S n)) :
    forall (P : t A (S n) -> Type)
      (H : forall a rest, P (cons a rest)), P e :=
  match e with
  | cons a rest => fun P H => H a rest
  | nil => fun devil => False_rect IDProp devil
  end.

Fixpoint lookup {A : Type} {n : nat} (e : t A n) : Fin.t n -> A :=
  match e in t _ n' return Fin.t n' -> A with
  | nil => fun x => Fin.elim0 x
  | cons a rest => fun x => Fin.cases a (fun y => lookup rest y) x
  end.

Fixpoint map {A B : Type} {n : nat} (f : A -> B) (e : t A n) : t B n :=
  match e with
  | nil => nil
  | cons a rest => cons (f a) (map f rest)
  end.

Fixpoint tabulate {A : Type} (n : nat) : (Fin.t n -> A) -> t A n :=
  match n return (Fin.t n -> A) -> t A n with
  | 0 => fun _ => nil
  | S n' => fun f => cons (f Fin.zero)
      (@tabulate A n' (fun x => f (Fin.succ x)))
  end.

Arguments tabulate {A} n _.

Theorem lookup_map {A B : Type} {n : nat} (f : A -> B)
    (e : t A n) (x : Fin.t n) :
    lookup (map f e) x = f (lookup e x).
Proof.
  induction e as [|n a rest IH].
  - exact (Fin.elim0 x).
  - refine (@Fin.cases' n x
      (fun x => lookup (map f (cons a rest)) x =
        f (lookup (cons a rest) x)) _ _).
    + reflexivity.
    + intros y. simpl. apply IH.
Qed.

Theorem lookup_tabulate {A : Type} {n : nat}
    (f : Fin.t n -> A) (x : Fin.t n) :
    lookup (tabulate n f) x = f x.
Proof.
  induction n as [|n IH].
  - exact (Fin.elim0 x).
  - refine (@Fin.cases' n x
      (fun x => lookup (tabulate (S n) f) x = f x) _ _).
    + reflexivity.
    + intros y. simpl. apply IH.
Qed.

(** Extensional equality is provable for first-order environments, without
    function extensionality. *)
Theorem ext {A : Type} {n : nat} (e1 e2 : t A n)
    (H : forall x, lookup e1 x = lookup e2 x) : e1 = e2.
Proof.
  revert H. revert e2.
  induction e1 as [|n a rest IH].
  - intros e2 H.
    exact (@case0 A
      (fun e => (forall x, lookup nil x = lookup e x) -> nil = e)
      (fun _ => eq_refl) e2 H).
  - intros e2 H.
    refine (@caseS' A n e2
      (fun e =>
        (forall x, lookup (cons a rest) x = lookup e x) ->
        cons a rest = e) _ H).
    intros b rest' Heq.
    assert (Hab : a = b) by exact (Heq Fin.zero).
    destruct Hab.
    f_equal. apply IH. intro x. exact (Heq (Fin.succ x)).
Qed.

End Env.

(** Finite renamings represented as first-order environments. *)
Module FinFun.

Definition t (n m : nat) : Type := Env.t (Fin.t m) n.

Definition apply {n m : nat} (f : t n m) : Fin.t n -> Fin.t m :=
  Env.lookup f.

Coercion apply : t >-> Funclass.

Definition id (n : nat) : t n n :=
  Env.tabulate n (fun i => i).

Definition comp {n m k : nat} (f : t n m) (g : t m k) : t n k :=
  Env.tabulate n (fun i => g (f i)).

Definition weaken (n : nat) : t n (S n) :=
  Env.tabulate n (fun i => Fin.succ i).

Definition openAt {n : nat} (x : Fin.t n) : t (S n) n :=
  Env.tabulate (S n) (fun i => Fin.cases x (fun j => j) i).

Definition ext {n m : nat} (f : t n m) : t (S n) (S m) :=
  Env.tabulate (S n)
    (fun i => Fin.cases Fin.zero (fun j => Fin.succ (f j)) i).

Theorem id_apply {n : nat} (i : Fin.t n) : id n i = i.
Proof. apply Env.lookup_tabulate. Qed.

Theorem comp_apply {n m k : nat} (f : t n m) (g : t m k)
    (i : Fin.t n) : comp f g i = g (f i).
Proof.
  exact (@Env.lookup_tabulate (Fin.t k) n (fun j => g (f j)) i).
Qed.

Theorem weaken_apply {n : nat} (i : Fin.t n) :
    weaken n i = Fin.succ i.
Proof. apply Env.lookup_tabulate. Qed.

Theorem openAt_zero {n : nat} (x : Fin.t n) :
    openAt x Fin.zero = x.
Proof. unfold openAt, apply. rewrite Env.lookup_tabulate. reflexivity. Qed.

Theorem openAt_succ {n : nat} (x i : Fin.t n) :
    openAt x (Fin.succ i) = i.
Proof. unfold openAt, apply. rewrite Env.lookup_tabulate. reflexivity. Qed.

Theorem ext_zero {n m : nat} (f : t n m) :
    ext f Fin.zero = Fin.zero.
Proof. unfold ext, apply. rewrite Env.lookup_tabulate. reflexivity. Qed.

Theorem ext_succ {n m : nat} (f : t n m) (i : Fin.t n) :
    ext f (Fin.succ i) = Fin.succ (f i).
Proof. unfold ext, apply. rewrite Env.lookup_tabulate. reflexivity. Qed.

Theorem funext {n m : nat} {f g : t n m}
    (H : forall i, f i = g i) : f = g.
Proof. apply Env.ext. exact H. Qed.

Theorem weaken_injective {n : nat} :
    forall i j : Fin.t n, weaken n i = weaken n j -> i = j.
Proof.
  intros i j H. rewrite !weaken_apply in H. now apply Fin.succ_inj in H.
Qed.

Theorem id_comp {n m : nat} (f : t n m) : comp (id n) f = f.
Proof.
  apply funext. intro i. rewrite comp_apply, id_apply. reflexivity.
Qed.

Theorem comp_id {n m : nat} (f : t n m) : comp f (id m) = f.
Proof.
  apply funext. intro i. rewrite comp_apply, id_apply. reflexivity.
Qed.

Theorem comp_assoc {n m k l : nat}
    (f : t n m) (g : t m k) (h : t k l) :
    comp (comp f g) h = comp f (comp g h).
Proof.
  apply funext. intro i. rewrite !comp_apply. reflexivity.
Qed.

Theorem ext_id {n : nat} : ext (id n) = id (S n).
Proof.
  apply funext. intro i.
  refine (@Fin.cases' n i
    (fun i => ext (id n) i = id (S n) i) _ _).
  - rewrite ext_zero, id_apply. reflexivity.
  - intros j. rewrite ext_succ, !id_apply. reflexivity.
Qed.

Theorem comp_weaken {n m : nat} (f : t n m) :
    comp f (weaken m) = comp (weaken n) (ext f).
Proof.
  apply funext. intro i. rewrite !comp_apply, !weaken_apply, ext_succ.
  reflexivity.
Qed.

Theorem ext_comp {n m k : nat} (f : t n m) (g : t m k) :
    comp (ext f) (ext g) = ext (comp f g).
Proof.
  apply funext. intro i.
  refine (@Fin.cases' n i
    (fun i => comp (ext f) (ext g) i = ext (comp f g) i) _ _).
  - rewrite comp_apply, !ext_zero. reflexivity.
  - intros j. rewrite comp_apply, !ext_succ, comp_apply. reflexivity.
Qed.

Theorem openAt_comp {n m : nat} (f : t n m) (x : Fin.t n) :
    comp (openAt x) f = comp (ext f) (openAt (f x)).
Proof.
  apply funext. intro i.
  refine (@Fin.cases' n i
    (fun i => comp (openAt x) f i =
      comp (ext f) (openAt (f x)) i) _ _).
  - rewrite !comp_apply, !openAt_zero, ext_zero. reflexivity.
  - intros j.
    rewrite !comp_apply, !openAt_succ, ext_succ, openAt_succ.
    reflexivity.
Qed.

Theorem openAt_weaken {n : nat} (x : Fin.t n) :
    comp (weaken n) (openAt x) = id n.
Proof.
  apply funext. intro i. rewrite comp_apply, weaken_apply, openAt_succ,
    id_apply. reflexivity.
Qed.

End FinFun.
