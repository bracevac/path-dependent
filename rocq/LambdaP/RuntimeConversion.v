From Equations Require Import Equations.
From PathDependent.LambdaP Require Import FinFun Syntax Context Typing
  Renaming Store PathReduction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Substituting pointwise reduction-equivalent paths into a path preserves
    reduction. *)
Theorem Path_reduce_subst_congr {l n : nat} {s : Store n} {r : Path l}
    {rho1 rho2 : PathSubst l n} {z : Fin.t n}
    (Hrho : forall (x : Fin.t l) (y : Fin.t n),
      Path_reduce (rho1 x) s y <-> Path_reduce (rho2 x) s y)
    (Hred : Path_reduce (Path_subst r rho1) s z) :
    Path_reduce (Path_subst r rho2) s z.
Proof.
  induction r as [x|r IH|r IH a] in z, Hred |- *; cbn in Hred |- *.
  - exact (proj1 (Hrho x z) Hred).
  - dependent elimination Hred.
    eapply path_reduce_fst; [eapply IH; eassumption | eassumption].
  - dependent elimination Hred.
    + eapply path_reduce_sel_hit; [eapply IH; eassumption | eassumption].
    + eapply path_reduce_sel_miss;
        [eapply IH; eassumption | eassumption | eassumption | eassumption].
Qed.

(** Pointwise equality of reduction graphs is preserved by path
    substitution. *)
Theorem Path_reduce_subst_iff {l n : nat} {s : Store n} {r : Path l}
    {rho1 rho2 : PathSubst l n} {z : Fin.t n}
    (Hrho : forall (x : Fin.t l) (y : Fin.t n),
      Path_reduce (rho1 x) s y <-> Path_reduce (rho2 x) s y) :
    Path_reduce (Path_subst r rho1) s z <->
      Path_reduce (Path_subst r rho2) s z.
Proof.
  split.
  - apply Path_reduce_subst_congr. exact Hrho.
  - apply Path_reduce_subst_congr.
    intros x y. symmetry. apply Hrho.
Qed.

(** Replacing the distinguished hole of an arbitrary path template by paths
    with the same reduction graph preserves the reduction graph. *)
Theorem Path_reduce_open_iff {n : nat} {s : Store n}
    {p q : Path n} {z : Fin.t n}
    (Hpq : forall y : Fin.t n,
      Path_reduce p s y <-> Path_reduce q s y)
    (r : Path (S n)) :
    Path_reduce (Path_open r p) s z <->
      Path_reduce (Path_open r q) s z.
Proof.
  unfold Path_open. apply Path_reduce_subst_iff.
  intros x y.
  refine (@Fin.cases' n x
    (fun x => Path_reduce (PathSubst_openAt p x) s y <->
      Path_reduce (PathSubst_openAt q x) s y) _ _).
  - rewrite !PathSubst_openAt_zero. exact (Hpq y).
  - intros i. rewrite !PathSubst_openAt_succ. reflexivity.
Qed.

(** Runtime equality is the least equivalence containing paths which resolve
    to a common store location and closed under arbitrary one-hole path
    contexts. *)
Inductive Path_RuntimeEq {n : nat} (s : Store n) :
    Path n -> Path n -> Prop :=
| path_runtime_eq_refl (p : Path n) : Path_RuntimeEq s p p
| path_runtime_eq_symm {p q : Path n} :
    Path_RuntimeEq s p q -> Path_RuntimeEq s q p
| path_runtime_eq_trans {p q r : Path n} :
    Path_RuntimeEq s p q -> Path_RuntimeEq s q r ->
    Path_RuntimeEq s p r
| path_runtime_eq_coresolve {p q : Path n} {x : Fin.t n} :
    Path_reduce p s x -> Path_reduce q s x -> Path_RuntimeEq s p q
| path_runtime_eq_congr {p q : Path n} :
    Path_RuntimeEq s p q -> forall r : Path (S n),
      Path_RuntimeEq s (Path_open r p) (Path_open r q).

Arguments path_runtime_eq_refl {n s} p.
Arguments path_runtime_eq_symm {n s p q} _.
Arguments path_runtime_eq_trans {n s p q r} _ _.
Arguments path_runtime_eq_coresolve {n s p q x} _ _.
Arguments path_runtime_eq_congr {n s p q} _ r.

(** Paths resolving to the same location have the same reduction graph. *)
Theorem Path_reduce_cotarget_iff {n : nat} {s : Store n}
    {p q : Path n} {x : Fin.t n}
    (Hp : Path_reduce p s x) (Hq : Path_reduce q s x) (z : Fin.t n) :
    Path_reduce p s z <-> Path_reduce q s z.
Proof.
  split; intro Hz.
  - assert (z = x) as -> by
      (eapply Path_reduce_deterministic; [exact Hz | exact Hp]).
    exact Hq.
  - assert (z = x) as -> by
      (eapply Path_reduce_deterministic; [exact Hz | exact Hq]).
    exact Hp.
Qed.

(** Runtime equality preserves the complete reduction graph of a path. *)
Theorem Path_RuntimeEq_reduce_iff {n : nat} {s : Store n}
    {p q : Path n} (H : Path_RuntimeEq s p q) (z : Fin.t n) :
    Path_reduce p s z <-> Path_reduce q s z.
Proof.
  induction H in z |- *.
  - reflexivity.
  - symmetry. apply IHPath_RuntimeEq.
  - transitivity (Path_reduce q s z).
    + apply IHPath_RuntimeEq1.
    + apply IHPath_RuntimeEq2.
  - eapply Path_reduce_cotarget_iff; eassumption.
  - apply Path_reduce_open_iff. intro y. apply IHPath_RuntimeEq.
Qed.

(** A reducing path is runtime-equal to the variable naming its result. *)
Theorem Path_RuntimeEq_of_reduce {n : nat} {s : Store n}
    {p : Path n} {x : Fin.t n} (H : Path_reduce p s x) :
    Path_RuntimeEq s p (path_var x).
Proof. eapply path_runtime_eq_coresolve; [exact H | apply path_reduce_var]. Qed.

Lemma Tm_weaken_pair {n : nat} {k : Kind} (y : Fin.t n)
    (a : Name) (d : Def n k) :
    Tm_weaken (tm_pair y a d) =
      tm_pair (Fin.succ y) a (Def_rename d (FinFun.weaken n)).
Proof.
  unfold Tm_weaken. cbn [Tm_rename]. now rewrite FinFun.weaken_apply.
Qed.

Lemma Tm_weaken_pair_val {n : nat} (y z : Fin.t n) (a : Name) :
    Tm_weaken (tm_pair y a (def_val z)) =
      tm_pair (Fin.succ y) a (def_val (Fin.succ z)).
Proof.
  unfold Tm_weaken. cbn [Tm_rename Def_rename].
  now rewrite !FinFun.weaken_apply.
Qed.

(** Path reduction is stable when a fresh value is appended to the store. *)
Theorem Path_reduce_weaken {n : nat} {s : Store n}
    {p : Path n} {x : Fin.t n}
    (H : Path_reduce p s x) (v : Tm n) (Hv : Tm_IsValue v) :
    Path_reduce (Path_weaken p) (store_val s v Hv) (Fin.succ x).
Proof.
  induction H; unfold Path_weaken in *; cbn [Path_rename] in *;
    rewrite ?FinFun.weaken_apply in *.
  - apply path_reduce_var.
  - eapply path_reduce_fst.
    + exact (IHPath_reduce v Hv).
    + rewrite <- Tm_weaken_pair.
      eapply store_binds_there. exact H0.
  - eapply path_reduce_sel_hit.
    + exact (IHPath_reduce v Hv).
    + rewrite <- Tm_weaken_pair_val.
      eapply store_binds_there. exact H0.
  - eapply path_reduce_sel_miss.
    + exact (IHPath_reduce1 v Hv).
    + rewrite <- Tm_weaken_pair.
      eapply store_binds_there. exact H0.
    + assumption.
    + exact (IHPath_reduce2 v Hv).
Qed.

(** Runtime equality is stable when a fresh value is appended to the store. *)
Theorem Path_RuntimeEq_weaken {n : nat} {s : Store n} {p q : Path n}
    (H : Path_RuntimeEq s p q) (v : Tm n) (Hv : Tm_IsValue v) :
    Path_RuntimeEq (store_val s v Hv) (Path_weaken p) (Path_weaken q).
Proof.
  induction H.
  - apply path_runtime_eq_refl.
  - now apply path_runtime_eq_symm.
  - eapply path_runtime_eq_trans; eassumption.
  - eapply path_runtime_eq_coresolve;
      eapply Path_reduce_weaken; eassumption.
  - unfold Path_weaken. rewrite !Path_open_rename.
    now apply path_runtime_eq_congr.
Qed.

(** Store-indexed conversion of generalized types. *)
Inductive Tau_RuntimeConv {n : nat} {k : Kind} (s : Store n) :
    Tau n k -> Tau n k -> Prop :=
| tau_runtime_conv_refl (d : Tau n k) : Tau_RuntimeConv s d d
| tau_runtime_conv_symm {d1 d2 : Tau n k} :
    Tau_RuntimeConv s d1 d2 -> Tau_RuntimeConv s d2 d1
| tau_runtime_conv_trans {d1 d2 d3 : Tau n k} :
    Tau_RuntimeConv s d1 d2 -> Tau_RuntimeConv s d2 d3 ->
    Tau_RuntimeConv s d1 d3
| tau_runtime_conv_replace (d : Tau (S n) k) {p q : Path n} :
    Path_RuntimeEq s p q ->
    Tau_RuntimeConv s (Tau_open d p) (Tau_open d q).

Arguments tau_runtime_conv_refl {n k s} d.
Arguments tau_runtime_conv_symm {n k s d1 d2} _.
Arguments tau_runtime_conv_trans {n k s d1 d2 d3} _ _.
Arguments tau_runtime_conv_replace {n k s} d {p q} _.

(** A common runtime result licenses replacement in any generalized-type
    template. *)
Theorem Tau_RuntimeConv_replace_of_reduce {n : nat} {s : Store n}
    {p q : Path n} {x : Fin.t n} {k : Kind} {d : Tau (S n) k}
    (Hp : Path_reduce p s x) (Hq : Path_reduce q s x) :
    Tau_RuntimeConv s (Tau_open d p) (Tau_open d q).
Proof.
  apply tau_runtime_conv_replace.
  eapply path_runtime_eq_coresolve; [exact Hp | exact Hq].
Qed.

(** Runtime conversion is stable under extension of the store. *)
Theorem Tau_RuntimeConv_weaken {n : nat} {s : Store n} {k : Kind}
    {d1 d2 : Tau n k} (H : Tau_RuntimeConv s d1 d2)
    (v : Tm n) (Hv : Tm_IsValue v) :
    Tau_RuntimeConv (store_val s v Hv) (Tau_weaken d1) (Tau_weaken d2).
Proof.
  induction H.
  - apply tau_runtime_conv_refl.
  - now apply tau_runtime_conv_symm.
  - eapply tau_runtime_conv_trans; eassumption.
  - unfold Tau_weaken. rewrite !Tau_open_rename.
    apply tau_runtime_conv_replace. now apply Path_RuntimeEq_weaken.
Qed.

(** Reflexive-transitive closure of source subtyping and runtime
    conversion. *)
Inductive Tau_RuntimeSub {n : nat} {k : Kind}
    (G : Ctx n) (s : Store n) : Tau n k -> Tau n k -> Prop :=
| tau_runtime_sub_refl (d : Tau n k) : Tau_RuntimeSub G s d d
| tau_runtime_sub_source {d1 d2 : Tau n k} :
    Tau_Sub G d1 d2 -> Tau_RuntimeSub G s d1 d2
| tau_runtime_sub_conv {d1 d2 : Tau n k} :
    Tau_RuntimeConv s d1 d2 -> Tau_RuntimeSub G s d1 d2
| tau_runtime_sub_trans {d1 d2 d3 : Tau n k} :
    Tau_RuntimeSub G s d1 d2 -> Tau_RuntimeSub G s d2 d3 ->
    Tau_RuntimeSub G s d1 d3.

Arguments tau_runtime_sub_refl {n k G s} d.
Arguments tau_runtime_sub_source {n k G s d1 d2} _.
Arguments tau_runtime_sub_conv {n k G s d1 d2} _.
Arguments tau_runtime_sub_trans {n k G s d1 d2 d3} _ _.

Theorem Tau_RuntimeSub_of_source {n : nat} {k : Kind}
    {G : Ctx n} {s : Store n} {d1 d2 : Tau n k}
    (H : Tau_Sub G d1 d2) : Tau_RuntimeSub G s d1 d2.
Proof. now apply tau_runtime_sub_source. Qed.

Theorem Tau_RuntimeSub_of_conv {n : nat} {k : Kind}
    {G : Ctx n} {s : Store n} {d1 d2 : Tau n k}
    (H : Tau_RuntimeConv s d1 d2) : Tau_RuntimeSub G s d1 d2.
Proof. now apply tau_runtime_sub_conv. Qed.

Theorem Tau_RuntimeSub_comp {n : nat} {k : Kind}
    {G : Ctx n} {s : Store n} {d1 d2 d3 : Tau n k}
    (H1 : Tau_RuntimeSub G s d1 d2)
    (H2 : Tau_RuntimeSub G s d2 d3) : Tau_RuntimeSub G s d1 d3.
Proof. eapply tau_runtime_sub_trans; [exact H1 | exact H2]. Qed.

(** Replace runtime-equal paths inside an arbitrary generalized-type
    template. *)
Theorem Tau_RuntimeSub_replace {n : nat} {G : Ctx n} {s : Store n}
    {p q : Path n} {k : Kind} {d : Tau (S n) k}
    (H : Path_RuntimeEq s p q) :
    Tau_RuntimeSub G s (Tau_open d p) (Tau_open d q).
Proof. apply tau_runtime_sub_conv. now apply tau_runtime_conv_replace. Qed.

(** A common runtime result licenses replacement inside mixed subtyping. *)
Theorem Tau_RuntimeSub_replace_of_reduce {n : nat}
    {G : Ctx n} {s : Store n} {p q : Path n} {x : Fin.t n}
    {k : Kind} {d : Tau (S n) k}
    (Hp : Path_reduce p s x) (Hq : Path_reduce q s x) :
    Tau_RuntimeSub G s (Tau_open d p) (Tau_open d q).
Proof.
  apply Tau_RuntimeSub_replace.
  eapply path_runtime_eq_coresolve; [exact Hp | exact Hq].
Qed.

(** Mixed runtime subtyping weakens with a context/store extension. *)
Theorem Tau_RuntimeSub_weaken {n : nat} {G : Ctx n} {s : Store n}
    {k : Kind} {d1 d2 : Tau n k}
    (H : Tau_RuntimeSub G s d1 d2)
    (S0 : Ty n) (v : Tm n) (Hv : Tm_IsValue v) :
    Tau_RuntimeSub (ctx_snoc G S0) (store_val s v Hv)
      (Tau_weaken d1) (Tau_weaken d2).
Proof.
  induction H.
  - apply tau_runtime_sub_refl.
  - apply tau_runtime_sub_source. now apply Tau_Sub_weaken.
  - apply tau_runtime_sub_conv. now apply Tau_RuntimeConv_weaken.
  - eapply tau_runtime_sub_trans; eassumption.
Qed.

Print Assumptions Path_reduce_subst_congr.
Print Assumptions Path_RuntimeEq_reduce_iff.
Print Assumptions Path_RuntimeEq_weaken.
Print Assumptions Tau_RuntimeConv_weaken.
Print Assumptions Tau_RuntimeSub_weaken.
