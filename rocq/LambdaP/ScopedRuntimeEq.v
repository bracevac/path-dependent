From Equations Require Import Equations.
From PathDependent.LambdaP Require Import FinFun Syntax Store
  RuntimeConversion.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** The elementary interface required of a path equivalence. *)
Record Path_IsEquivCongr {n : nat}
    (E : Path n -> Path n -> Prop) : Prop := {
  path_equiv_refl : forall p, E p p;
  path_equiv_symm : forall p q, E p q -> E q p;
  path_equiv_trans : forall p q r, E p q -> E q r -> E p r;
  path_equiv_fst : forall p q, E p q -> E (path_fst p) (path_fst q);
  path_equiv_sel : forall p q, E p q -> forall a,
    E (path_sel p a) (path_sel q a)
}.

Arguments path_equiv_refl {n E} _ p.
Arguments path_equiv_symm {n E} _ {p q} _.
Arguments path_equiv_trans {n E} _ {p q r} _ _.
Arguments path_equiv_fst {n E} _ {p q} _.
Arguments path_equiv_sel {n E} _ {p q} _ a.

(** Pointwise-equivalent substitutions give equivalent instances of one
    path template. *)
Theorem Path_IsEquivCongr_subst {n m : nat}
    {E : Path m -> Path m -> Prop} {rho1 rho2 : PathSubst n m}
    (HE : Path_IsEquivCongr E)
    (Hrho : forall x, E (rho1 x) (rho2 x)) (p : Path n) :
    E (Path_subst p rho1) (Path_subst p rho2).
Proof.
  induction p; cbn [Path_subst].
  - apply Hrho.
  - now apply (path_equiv_fst HE).
  - now apply (path_equiv_sel HE).
Qed.

(** Equivalent paths remain equivalent in an arbitrary one-hole path
    context. *)
Theorem Path_IsEquivCongr_open_context {n : nat}
    {E : Path n -> Path n -> Prop} (HE : Path_IsEquivCongr E)
    {p q : Path n} (H : E p q) (r : Path (S n)) :
    E (Path_open r p) (Path_open r q).
Proof.
  unfold Path_open. apply Path_IsEquivCongr_subst with (HE := HE).
  intro x.
  refine (@Fin.cases' n x
    (fun x => E (PathSubst_openAt p x) (PathSubst_openAt q x)) _ _).
  - rewrite !PathSubst_openAt_zero. exact H.
  - intro y. rewrite !PathSubst_openAt_succ.
    apply (path_equiv_refl HE).
Qed.

(** Least congruence lifting an ambient path equivalence through one
    binder. *)
Inductive Path_ScopedLift {n : nat}
    (E : Path n -> Path n -> Prop) :
    Path (S n) -> Path (S n) -> Prop :=
| path_scoped_lift_bound :
    Path_ScopedLift E (path_var Fin.zero) (path_var Fin.zero)
| path_scoped_lift_old {p q : Path n} :
    E p q -> Path_ScopedLift E (Path_weaken p) (Path_weaken q)
| path_scoped_lift_symm {p q : Path (S n)} :
    Path_ScopedLift E p q -> Path_ScopedLift E q p
| path_scoped_lift_trans {p q r : Path (S n)} :
    Path_ScopedLift E p q -> Path_ScopedLift E q r ->
    Path_ScopedLift E p r
| path_scoped_lift_fst {p q : Path (S n)} :
    Path_ScopedLift E p q ->
    Path_ScopedLift E (path_fst p) (path_fst q)
| path_scoped_lift_sel {p q : Path (S n)} {a : Name} :
    Path_ScopedLift E p q ->
    Path_ScopedLift E (path_sel p a) (path_sel q a).

Arguments path_scoped_lift_bound {n E}.
Arguments path_scoped_lift_old {n E p q} _.
Arguments path_scoped_lift_symm {n E p q} _.
Arguments path_scoped_lift_trans {n E p q r} _ _.
Arguments path_scoped_lift_fst {n E p q} _.
Arguments path_scoped_lift_sel {n E p q a} _.

(** A morphism of ambient path relations lifts together with an extended
    renaming. *)
Theorem Path_ScopedLift_rename {n m : nat}
    {E1 : Path n -> Path n -> Prop}
    {E2 : Path m -> Path m -> Prop} {f : FinFun.t n m}
    (Hmap : forall p q, E1 p q ->
      E2 (Path_rename p f) (Path_rename q f))
    {p q : Path (S n)} (H : Path_ScopedLift E1 p q) :
    Path_ScopedLift E2
      (Path_rename p (FinFun.ext f))
      (Path_rename q (FinFun.ext f)).
Proof.
  induction H; cbn [Path_rename].
  - rewrite FinFun.ext_zero. apply path_scoped_lift_bound.
  - rewrite <- !Path_weaken_rename.
    apply path_scoped_lift_old. now apply Hmap.
  - now apply path_scoped_lift_symm.
  - eapply path_scoped_lift_trans; eassumption.
  - now apply path_scoped_lift_fst.
  - now apply path_scoped_lift_sel.
Qed.

(** Reflexivity is derived structurally. *)
Theorem Path_ScopedLift_refl {n : nat}
    {E : Path n -> Path n -> Prop}
    (HE : Path_IsEquivCongr E) (p : Path (S n)) :
    Path_ScopedLift E p p.
Proof.
  induction p.
  - refine (@Fin.cases' n t
      (fun x => Path_ScopedLift E (path_var x) (path_var x)) _ _).
    + apply path_scoped_lift_bound.
    + intro y. change (Path_ScopedLift E
        (path_var (Fin.succ y)) (path_var (Fin.succ y))).
      replace (path_var (Fin.succ y)) with
        (Path_weaken (path_var y)).
      * apply path_scoped_lift_old. apply (path_equiv_refl HE).
      * unfold Path_weaken. cbn [Path_rename].
        now rewrite FinFun.weaken_apply.
  - now apply path_scoped_lift_fst.
  - now apply path_scoped_lift_sel.
Qed.

(** The scoped lift is itself an equivalence and path congruence. *)
Theorem Path_ScopedLift_isEquivCongr {n : nat}
    {E : Path n -> Path n -> Prop} (HE : Path_IsEquivCongr E) :
    Path_IsEquivCongr (Path_ScopedLift E).
Proof.
  constructor.
  - apply Path_ScopedLift_refl. exact HE.
  - intros. now apply path_scoped_lift_symm.
  - intros p q r H1 H2.
    eapply path_scoped_lift_trans; [exact H1 | exact H2].
  - intros. now apply path_scoped_lift_fst.
  - intros. now apply path_scoped_lift_sel.
Qed.

(** Substituting opening substitutions into lifted-equivalent templates is
    sound when the actual paths are ambient-equivalent. *)
Theorem Path_ScopedLift_subst_openAt {n : nat}
    {E : Path n -> Path n -> Prop} (HE : Path_IsEquivCongr E)
    {p q : Path (S n)} (H : Path_ScopedLift E p q) :
    forall {r s : Path n}, E r s ->
      E (Path_subst p (PathSubst_openAt r))
        (Path_subst q (PathSubst_openAt s)).
Proof.
  induction H; intros r0 s0 Hrs; cbn [Path_subst].
  - rewrite !PathSubst_openAt_zero. exact Hrs.
  - change (E (Path_open (Path_weaken p) r0)
      (Path_open (Path_weaken q) s0)).
    rewrite !Path_weaken_open. exact H.
  - apply (path_equiv_symm HE).
    apply IHPath_ScopedLift. now apply (path_equiv_symm HE).
  - eapply (path_equiv_trans HE).
    + exact (IHPath_ScopedLift1 r0 s0 Hrs).
    + apply IHPath_ScopedLift2. apply (path_equiv_refl HE).
  - apply (path_equiv_fst HE). now apply IHPath_ScopedLift.
  - apply (path_equiv_sel HE). now apply IHPath_ScopedLift.
Qed.

(** Opening form of [Path_ScopedLift_subst_openAt]. *)
Theorem Path_ScopedLift_open_paths {n : nat}
    {E : Path n -> Path n -> Prop} (HE : Path_IsEquivCongr E)
    {p q : Path (S n)} (H : Path_ScopedLift E p q)
    {r s : Path n} (Hrs : E r s) :
    E (Path_open p r) (Path_open q s).
Proof. unfold Path_open. now apply (Path_ScopedLift_subst_openAt HE H). Qed.

Lemma Path_weaken_ne_bound {n : nat} (p : Path n) :
    Path_weaken p <> path_var (@Fin.zero n).
Proof.
  destruct p; unfold Path_weaken; cbn [Path_rename]; intro E.
  - rewrite FinFun.weaken_apply in E. discriminate E.
  - discriminate E.
  - discriminate E.
Qed.

(** The fresh variable cannot become equivalent to a distinct path. *)
Theorem Path_ScopedLift_bound_only {n : nat}
    {E : Path n -> Path n -> Prop} {p q : Path (S n)}
    (H : Path_ScopedLift E p q) :
    (p = path_var Fin.zero -> q = path_var Fin.zero) /\
    (q = path_var Fin.zero -> p = path_var Fin.zero).
Proof.
  induction H.
  - split; intro; reflexivity.
  - split; intro Heq.
    + exfalso. exact (@Path_weaken_ne_bound n p Heq).
    + exfalso. exact (@Path_weaken_ne_bound n q Heq).
  - exact (conj (proj2 IHPath_ScopedLift) (proj1 IHPath_ScopedLift)).
  - split.
    + intro Hp. apply (proj1 IHPath_ScopedLift2).
      now apply (proj1 IHPath_ScopedLift1).
    + intro Hr. apply (proj2 IHPath_ScopedLift1).
      now apply (proj2 IHPath_ScopedLift2).
  - split; intro Heq; discriminate Heq.
  - split; intro Heq; discriminate Heq.
Qed.

Theorem Path_ScopedLift_bound_left {n : nat}
    {E : Path n -> Path n -> Prop} {q : Path (S n)}
    (H : Path_ScopedLift E (path_var Fin.zero) q) :
    q = path_var Fin.zero.
Proof. exact (proj1 (Path_ScopedLift_bound_only H) eq_refl). Qed.

Theorem Path_ScopedLift_bound_right {n : nat}
    {E : Path n -> Path n -> Prop} {p : Path (S n)}
    (H : Path_ScopedLift E p (path_var Fin.zero)) :
    p = path_var Fin.zero.
Proof. exact (proj2 (Path_ScopedLift_bound_only H) eq_refl). Qed.

(** Store-indexed runtime equality supplies the generic interface. *)
Theorem Path_RuntimeEq_isEquivCongr {n : nat} (s : Store n) :
    Path_IsEquivCongr (Path_RuntimeEq s).
Proof.
  constructor.
  - intro p. apply path_runtime_eq_refl.
  - intros p q H. now apply path_runtime_eq_symm.
  - intros p q r H1 H2.
    eapply path_runtime_eq_trans; [exact H1 | exact H2].
  - intros p q H.
    pose proof (path_runtime_eq_congr H
      (path_fst (path_var Fin.zero))) as Hcongr.
    unfold Path_open in Hcongr. cbn [Path_subst] in Hcongr.
    rewrite !PathSubst_openAt_zero in Hcongr. exact Hcongr.
  - intros p q H a.
    pose proof (path_runtime_eq_congr H
      (path_sel (path_var Fin.zero) a)) as Hcongr.
    unfold Path_open in Hcongr. cbn [Path_subst] in Hcongr.
    rewrite !PathSubst_openAt_zero in Hcongr. exact Hcongr.
Qed.

(** Runtime equality lifted through a binder without extending the store. *)
Definition Path_ScopedRuntimeEq {n : nat} (s : Store n) :
    Path (S n) -> Path (S n) -> Prop :=
  Path_ScopedLift (Path_RuntimeEq s).

(** Opening scoped runtime-equivalent templates by runtime-equivalent actual
    paths is sound in an exact store. *)
Theorem Path_ScopedRuntimeEq_open {n : nat} {s : Store n}
    {p q : Path (S n)} (H : Path_ScopedRuntimeEq s p q)
    {r t : Path n} (Hrt : Path_RuntimeEq s r t) :
    Path_RuntimeEq s (Path_open p r) (Path_open q t).
Proof.
  exact (Path_ScopedLift_open_paths
    (Path_RuntimeEq_isEquivCongr s) H Hrt).
Qed.

Print Assumptions Path_ScopedLift_open_paths.
Print Assumptions Path_ScopedLift_bound_only.
Print Assumptions Path_ScopedRuntimeEq_open.
