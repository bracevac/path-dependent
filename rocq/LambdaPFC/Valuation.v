From Equations Require Import Equations.
From PathDependent.LambdaPFC Require Import FinFun Syntax.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

Definition Valuation (n m : nat) : Type := FinFun n m.

(** Extend a valuation with the newest source variable. *)
Definition valuation_snoc {n m : nat} (rho : Valuation n m) (y : Fin m) :
    Valuation (S n) m := VCons y rho.

(** Shift all target locations through one allocation. *)
Definition valuation_weaken {n m : nat} (rho : Valuation n m) :
    Valuation n (S m) := comp rho (weaken m).

Lemma valuation_snoc_zero {n m : nat} (rho : Valuation n m) (y : Fin m) :
    apply (valuation_snoc rho y) FZ = y.
Proof. unfold valuation_snoc, apply. rewrite vec_lookup_zero. simp vec_head. reflexivity. Qed.

Lemma valuation_snoc_succ {n m : nat} (rho : Valuation n m)
    (y : Fin m) (x : Fin n) :
    apply (valuation_snoc rho y) (FS x) = apply rho x.
Proof. unfold valuation_snoc, apply. rewrite vec_lookup_succ. simp vec_tail. reflexivity. Qed.

Lemma valuation_ext_comp_openAt {n m : nat}
    (rho : Valuation n m) (y : Fin m) :
    comp (ext rho) (openAt y) = valuation_snoc rho y.
Proof.
  apply finfun_ext. intro x.
  refine (fin_case (P := fun x =>
    apply (comp (ext rho) (openAt y)) x =
      apply (valuation_snoc rho y) x) _ _ x).
  - rewrite comp_apply, ext_zero, openAt_zero, valuation_snoc_zero.
    reflexivity.
  - intro i. rewrite comp_apply, ext_succ, openAt_succ,
      valuation_snoc_succ. reflexivity.
Qed.

Lemma ty_rename_ext_openAt {n m : nat}
    (T : Ty (S n)) (rho : Valuation n m) (y : Fin m) :
    ty_rename (ty_rename T (ext rho)) (openAt y) =
      ty_rename T (valuation_snoc rho y).
Proof. rewrite ty_rename_rename, valuation_ext_comp_openAt. reflexivity. Qed.

Lemma tau_rename_ext_openAt {n m : nat} {k : Kind}
    (d : Tau (S n) k) (rho : Valuation n m) (y : Fin m) :
    tau_rename (tau_rename d (ext rho)) (openAt y) =
      tau_rename d (valuation_snoc rho y).
Proof. rewrite tau_rename_rename, valuation_ext_comp_openAt. reflexivity. Qed.

Lemma tm_rename_ext_openAt {n m : nat}
    (t : Tm (S n)) (rho : Valuation n m) (y : Fin m) :
    tm_rename (tm_rename t (ext rho)) (openAt y) =
      tm_rename t (valuation_snoc rho y).
Proof. rewrite tm_rename_rename, valuation_ext_comp_openAt. reflexivity. Qed.

Print Assumptions tm_rename_ext_openAt.
