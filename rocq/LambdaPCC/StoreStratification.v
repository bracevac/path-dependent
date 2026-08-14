From Stdlib Require Import Lia.
From Equations Require Import Equations.
From PathDependent.LambdaPCC Require Import FinFun Syntax Context Typing Runtime.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Remaining allocation depth of a generalized runtime referent. *)
Definition referent_stratum {n : nat} (referent : Referent n) : nat :=
  match referent with
  | RLoc x => n - fin_value x
  | RType _ => 0
  | RCapture _ => 0
  end.

Lemma referent_stratum_weaken {n : nat} (referent : Referent n) :
    referent_stratum (referent_weaken referent) = referent_stratum referent.
Proof.
  destruct referent as [x|shape|C];
    cbn [referent_weaken referent_stratum fin_value].
  - pose proof (fin_value_lt x). lia.
  - reflexivity.
  - reflexivity.
Qed.

Lemma referent_stratum_loc_succ {n : nat} (x : Fin n) :
    referent_stratum (RLoc (FS x) : Referent (S n)) =
      referent_stratum (RLoc x : Referent n).
Proof.
  cbn [referent_stratum fin_value]. pose proof (fin_value_lt x). lia.
Qed.

(** A definition stored in a fresh cell denotes an older referent. *)
Lemma def_referent_weaken_stratum_lt {n : nat} {k : Kind} (d : Def n k) :
    referent_stratum (referent_weaken (def_referent d)) <
      referent_stratum (RLoc FZ : Referent (S n)).
Proof.
  destruct d as [n x|n shape|n C];
    cbn [def_referent referent_weaken referent_stratum fin_value].
  - pose proof (fin_value_lt x). lia.
  - lia.
  - lia.
Qed.

Local Lemma store_binds_pair_strata_lt_aux {n : nat} {sigma : Store n}
    {x : Fin n} {term : Tm n} (binding : StoreBinds sigma x term) :
    forall {y : Fin n} {a : Name} {k : Kind} {d : Def n k},
      term = TmPair y a d ->
      referent_stratum (RLoc y) < referent_stratum (RLoc x) /\
      referent_stratum (def_referent d) < referent_stratum (RLoc x).
Proof.
  induction binding as
    [n sigma v value
    |n sigma x v u u_value binding IH];
    intros y a k d equation.
  - inversion value; subst.
    + unfold tm_weaken in equation. rewrite tm_rename_equation_2 in equation.
      discriminate equation.
    + unfold tm_weaken in equation. rewrite tm_rename_equation_3 in equation.
      pose proof (f_equal tm_pair_first equation) as Hfirst.
      pose proof (f_equal tm_pair_referent equation) as Hreferent.
      cbn [tm_pair_first tm_pair_referent] in Hfirst, Hreferent.
      pose proof (some_injective Hfirst) as Hy.
      pose proof (some_injective Hreferent) as Hr.
      rewrite weaken_apply in Hy. subst y.
      split.
      * cbn [referent_stratum fin_value]. lia.
      * rewrite <- Hr, def_referent_weaken.
        apply def_referent_weaken_stratum_lt.
  - destruct v as [n p|n A body|n kind first label definition|n p q|n s body];
      unfold tm_weaken in equation;
      simp tm_rename in equation;
      try discriminate equation.
    pose proof (IH first label kind definition eq_refl)
      as [Hfirst_old Hreferent_old].
    pose proof (f_equal tm_pair_first equation) as Hfirst.
    pose proof (f_equal tm_pair_referent equation) as Hreferent.
    cbn [tm_pair_first tm_pair_referent] in Hfirst, Hreferent.
    pose proof (some_injective Hfirst) as Hy.
    pose proof (some_injective Hreferent) as Hr.
    rewrite weaken_apply in Hy. subst y.
    split.
    + rewrite referent_stratum_loc_succ, referent_stratum_loc_succ.
      exact Hfirst_old.
    + rewrite <- Hr, def_referent_weaken, referent_stratum_weaken,
        referent_stratum_loc_succ.
      exact Hreferent_old.
Qed.

Lemma store_binds_pair_first_stratum_lt {n : nat} {sigma : Store n}
    {x y : Fin n} {a : Name} {k : Kind} {d : Def n k}
    (binding : StoreBinds sigma x (TmPair y a d)) :
    referent_stratum (RLoc y) < referent_stratum (RLoc x).
Proof. exact (proj1 (store_binds_pair_strata_lt_aux binding eq_refl)). Qed.

Lemma store_binds_pair_referent_stratum_lt {n : nat} {sigma : Store n}
    {x y : Fin n} {a : Name} {k : Kind} {d : Def n k}
    (binding : StoreBinds sigma x (TmPair y a d)) :
    referent_stratum (def_referent d) < referent_stratum (RLoc x).
Proof. exact (proj2 (store_binds_pair_strata_lt_aux binding eq_refl)). Qed.

Print Assumptions store_binds_pair_first_stratum_lt.
Print Assumptions store_binds_pair_referent_stratum_lt.
