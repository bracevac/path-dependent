From PathDependent.LambdaPCC Require Import FinFun Syntax.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Finite semantic valuations map source variables to target locations. *)
Definition Valuation (n m : nat) : Type := FinFun n m.

(** Extend a valuation by assigning the newest source variable to [y]. *)
Definition valuation_snoc {n m : nat} (rho : Valuation n m) (y : Fin m) :
    Valuation (S n) m := VCons y rho.

(** Weaken all target locations through a fresh target allocation. *)
Definition valuation_weaken {n m : nat} (rho : Valuation n m) :
    Valuation n (S m) := comp rho (weaken m).

Lemma valuation_snoc_zero {n m : nat} (rho : Valuation n m) (y : Fin m) :
    apply (valuation_snoc rho y) FZ = y.
Proof. reflexivity. Qed.

Lemma valuation_snoc_succ {n m : nat} (rho : Valuation n m)
    (y : Fin m) (x : Fin n) :
    apply (valuation_snoc rho y) (FS x) = apply rho x.
Proof. reflexivity. Qed.

(** Lifting and then opening the fresh target binder is semantic snoc. *)
Lemma valuation_ext_comp_openAt {n m : nat} (rho : Valuation n m)
    (y : Fin m) :
    comp (ext rho) (openAt y) = valuation_snoc rho y.
Proof.
  apply finfun_ext. intro x.
  refine (fin_case (P := fun x =>
      apply (comp (ext rho) (openAt y)) x =
        apply (valuation_snoc rho y) x) _ _ x).
  - rewrite comp_apply, ext_zero, openAt_zero. reflexivity.
  - intro i. rewrite comp_apply, ext_succ, openAt_succ. reflexivity.
Qed.

(** Renaming through semantic binder extension. *)
Lemma capture_rename_ext_openAt {n m : nat} (C : CaptureSet (S n))
    (rho : Valuation n m) (y : Fin m) :
    capture_rename (capture_rename C (ext rho)) (openAt y) =
      capture_rename C (valuation_snoc rho y).
Proof.
  rewrite capture_rename_rename, valuation_ext_comp_openAt. reflexivity.
Qed.

Lemma ty_rename_ext_openAt {n m : nat} (T : Ty (S n))
    (rho : Valuation n m) (y : Fin m) :
    ty_rename (ty_rename T (ext rho)) (openAt y) =
      ty_rename T (valuation_snoc rho y).
Proof.
  rewrite ty_rename_rename, valuation_ext_comp_openAt. reflexivity.
Qed.

Lemma shape_rename_ext_openAt {n m : nat} (shape : Shape (S n))
    (rho : Valuation n m) (y : Fin m) :
    shape_rename (shape_rename shape (ext rho)) (openAt y) =
      shape_rename shape (valuation_snoc rho y).
Proof.
  rewrite shape_rename_rename, valuation_ext_comp_openAt. reflexivity.
Qed.

Lemma tau_rename_ext_openAt {n m : nat} {k : Kind} (d : Tau (S n) k)
    (rho : Valuation n m) (y : Fin m) :
    tau_rename (tau_rename d (ext rho)) (openAt y) =
      tau_rename d (valuation_snoc rho y).
Proof.
  rewrite tau_rename_rename, valuation_ext_comp_openAt. reflexivity.
Qed.

Lemma tm_rename_ext_openAt {n m : nat} (term : Tm (S n))
    (rho : Valuation n m) (y : Fin m) :
    tm_rename (tm_rename term (ext rho)) (openAt y) =
      tm_rename term (valuation_snoc rho y).
Proof.
  rewrite tm_rename_rename, valuation_ext_comp_openAt. reflexivity.
Qed.

Print Assumptions valuation_ext_comp_openAt.
Print Assumptions tm_rename_ext_openAt.
