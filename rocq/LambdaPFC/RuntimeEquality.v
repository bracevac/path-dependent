From Equations Require Import Equations.
From Stdlib Require Import Program.Equality.
From PathDependent.LambdaPFC Require Import
  FinFun Syntax Context Typing Runtime.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Finite proof-relevant runtime path equality. *)
Inductive PathRuntimeEq {n : nat} (sigma : Store n) :
    Path n -> Path n -> Type :=
| PREq_refl (p : Path n) : PathRuntimeEq sigma p p
| PREq_symm {p q : Path n} :
    PathRuntimeEq sigma p q -> PathRuntimeEq sigma q p
| PREq_trans {p q r : Path n} :
    PathRuntimeEq sigma p q -> PathRuntimeEq sigma q r ->
    PathRuntimeEq sigma p r
| PREq_coresolve {p q : Path n} {referent : PathReferent n} :
    PathResolve p sigma referent -> PathResolve q sigma referent ->
    PathRuntimeEq sigma p q
| PREq_fst {p q : Path n} :
    PathRuntimeEq sigma p q -> PathRuntimeEq sigma (PFst p) (PFst q)
| PREq_sel {p q : Path n} :
    PathRuntimeEq sigma p q -> forall a : Name,
      PathRuntimeEq sigma (PSel p a) (PSel q a).

Arguments PREq_refl {n sigma} p.
Arguments PREq_symm {n sigma p q} _.
Arguments PREq_trans {n sigma p q r} _ _.
Arguments PREq_coresolve {n sigma p q referent} _ _.
Arguments PREq_fst {n sigma p q} _.
Arguments PREq_sel {n sigma p q} _ a.

(** Runtime equality preserves the generalized resolution graph. *)
Lemma path_runtime_eq_resolve_iff {n : nat} {sigma : Store n}
    {p q : Path n} (evidence : PathRuntimeEq sigma p q)
    (referent : PathReferent n) :
    PathResolve p sigma referent <-> PathResolve q sigma referent.
Proof.
  revert referent.
  induction evidence; intro target.
  - tauto.
  - specialize (IHevidence target). tauto.
  - specialize (IHevidence1 target).
    specialize (IHevidence2 target). tauto.
  - split; intro resolution.
    + pose proof (path_resolve_deterministic p0 resolution) as equality.
      destruct equality. exact p1.
    + pose proof (path_resolve_deterministic p1 resolution) as equality.
      destruct equality. exact p0.
  - split; intro resolution.
    + dependent elimination resolution.
      exact (Resolve_fst (proj1 (IHevidence (RefLoc x0)) p1) s).
    + dependent elimination resolution.
      exact (Resolve_fst (proj2 (IHevidence (RefLoc x0)) p1) s).
  - split; intro resolution.
    + dependent elimination resolution.
      * exact (Resolve_sel (proj1 (IHevidence (RefLoc x1)) p3) s0).
      * exact (Resolve_sel_miss (proj1 (IHevidence (RefLoc x2)) p5)
          s1 n4 p6).
    + dependent elimination resolution.
      * exact (Resolve_sel (proj2 (IHevidence (RefLoc x1)) p3) s0).
      * exact (Resolve_sel_miss (proj2 (IHevidence (RefLoc x2)) p5)
          s1 n4 p6).
Qed.

(** Runtime equality survives allocation. *)
Definition path_runtime_eq_weaken {n : nat} {sigma : Store n}
    {p q : Path n} (evidence : PathRuntimeEq sigma p q)
    (v : Tm n) (value : Tm_IsValue v) :
    PathRuntimeEq (StoreVal sigma v value) (path_weaken p) (path_weaken q).
Proof.
  induction evidence.
  - exact (PREq_refl (path_weaken p)).
  - exact (PREq_symm IHevidence).
  - exact (PREq_trans IHevidence1 IHevidence2).
  - exact (PREq_coresolve (path_resolve_weaken p0 (v := v) value)
      (path_resolve_weaken p1 (v := v) value)).
  - unfold path_weaken in *. simp path_rename in *.
    exact (PREq_fst IHevidence).
  - unfold path_weaken in *. simp path_rename in *.
    exact (PREq_sel IHevidence a).
Defined.

(** Operations required of a proof-relevant path equality. *)
Record PathEqCongruence {n : nat} (R : Path n -> Path n -> Type) : Type := {
  eq_refl : forall p, R p p;
  eq_symm : forall p q, R p q -> R q p;
  eq_trans : forall p q r, R p q -> R q r -> R p r;
  eq_fst : forall p q, R p q -> R (PFst p) (PFst q);
  eq_sel : forall p q, R p q -> forall a, R (PSel p a) (PSel q a)
}.

Arguments eq_refl {n R} _ _.
Arguments eq_symm {n R} _ {p q} _.
Arguments eq_trans {n R} _ {p q r} _ _.
Arguments eq_fst {n R} _ {p q} _.
Arguments eq_sel {n R} _ {p q} _ _.

Definition path_runtime_eq_congruence {n : nat} (sigma : Store n) :
    PathEqCongruence (PathRuntimeEq sigma) :=
  {| eq_refl := fun p => PREq_refl p;
     eq_symm := fun _ _ e => PREq_symm e;
     eq_trans := fun _ _ _ e1 e2 => PREq_trans e1 e2;
     eq_fst := fun _ _ e => PREq_fst e;
     eq_sel := fun _ _ e a => PREq_sel e a |}.

(** Least path congruence below a binder. *)
Inductive PathScopedLift {n : nat} (R : Path n -> Path n -> Type) :
    Path (S n) -> Path (S n) -> Type :=
| SL_bound : PathScopedLift R (PVar FZ) (PVar FZ)
| SL_old {p q : Path n} :
    R p q -> PathScopedLift R (path_weaken p) (path_weaken q)
| SL_symm {p q : Path (S n)} :
    PathScopedLift R p q -> PathScopedLift R q p
| SL_trans {p q r : Path (S n)} :
    PathScopedLift R p q -> PathScopedLift R q r -> PathScopedLift R p r
| SL_fst {p q : Path (S n)} :
    PathScopedLift R p q -> PathScopedLift R (PFst p) (PFst q)
| SL_sel {p q : Path (S n)} {a : Name} :
    PathScopedLift R p q -> PathScopedLift R (PSel p a) (PSel q a).

Arguments SL_bound {n R}.
Arguments SL_old {n R p q} _.
Arguments SL_symm {n R p q} _.
Arguments SL_trans {n R p q r} _ _.
Arguments SL_fst {n R p q} _.
Arguments SL_sel {n R p q a} _.

Definition path_scoped_lift_refl_old {n : nat}
    {R : Path n -> Path n -> Type} (operations : PathEqCongruence R)
    (x : Fin n) : PathScopedLift R (PVar (FS x)) (PVar (FS x)).
Proof.
  assert (H : path_weaken (PVar x) = PVar (FS x)).
  { unfold path_weaken. simp path_rename. rewrite weaken_apply. reflexivity. }
  rewrite <- H.
  exact (SL_old (eq_refl operations (PVar x))).
Defined.

Equations path_scoped_lift_refl {n : nat}
    {R : Path n -> Path n -> Type} (operations : PathEqCongruence R)
    (p : Path (S n)) : PathScopedLift R p p :=
path_scoped_lift_refl operations (PVar FZ) := SL_bound;
path_scoped_lift_refl operations (PVar (FS x)) :=
  path_scoped_lift_refl_old operations x;
path_scoped_lift_refl operations (PFst p) :=
  SL_fst (path_scoped_lift_refl operations p);
path_scoped_lift_refl operations (PSel p a) :=
  SL_sel (path_scoped_lift_refl operations p).

Definition path_scoped_lift_congruence {n : nat}
    {R : Path n -> Path n -> Type} (operations : PathEqCongruence R) :
    PathEqCongruence (PathScopedLift R) :=
  {| eq_refl := path_scoped_lift_refl operations;
     eq_symm := fun _ _ e => SL_symm e;
     eq_trans := fun _ _ _ e1 e2 => SL_trans e1 e2;
     eq_fst := fun _ _ e => SL_fst e;
     eq_sel := fun _ _ e _ => SL_sel e |}.

Definition PathSubstHom {n m : nat}
    (R : Path n -> Path n -> Type) (E : Path m -> Path m -> Type)
    (rho : PathSubst n m) : Type :=
  forall p q, R p q -> E (path_subst p rho) (path_subst q rho).

Definition path_scoped_lift_subst {n m : nat}
    {R : Path n -> Path n -> Type} {E : Path m -> Path m -> Type}
    {rho : PathSubst n m} {p q : Path (S n)}
    (map_old : PathSubstHom R E rho)
    (evidence : PathScopedLift R p q) :
    PathScopedLift E
      (path_subst p (path_subst_lift rho))
      (path_subst q (path_subst_lift rho)).
Proof.
  induction evidence.
  - simp path_subst. rewrite path_subst_lift_zero. exact SL_bound.
  - rewrite !path_weaken_subst_lift. exact (SL_old (map_old _ _ r)).
  - exact (SL_symm IHevidence).
  - exact (SL_trans IHevidence1 IHevidence2).
  - simp path_subst. exact (SL_fst IHevidence).
  - simp path_subst. exact (SL_sel IHevidence).
Defined.

Definition path_scoped_lift_open {n : nat}
    {R : Path n -> Path n -> Type} {p q : Path (S n)} {r s : Path n}
    (operations : PathEqCongruence R)
    (evidence : PathScopedLift R p q) (arguments : R r s) :
    R (path_open p r) (path_open q s).
Proof.
  revert r s arguments.
  induction evidence; intros r0 s0 arguments.
  - unfold path_open. simp path_subst.
    rewrite !path_subst_openAt_zero. exact arguments.
  - rewrite !path_weaken_open. exact r.
  - apply (eq_symm operations). apply IHevidence.
    apply (eq_symm operations). exact arguments.
  - eapply (eq_trans operations).
    + exact (IHevidence1 r0 s0 arguments).
    + exact (IHevidence2 s0 s0 (eq_refl operations s0)).
  - unfold path_open in *. simp path_subst in *.
    exact (eq_fst operations (IHevidence r0 s0 arguments)).
  - unfold path_open in *. simp path_subst in *.
    exact (eq_sel operations (IHevidence r0 s0 arguments) a).
Defined.

(** Finite conversion evidence generated by replacement of related paths. *)
Inductive TauRuntimeConv :
    forall {n : nat}, (Path n -> Path n -> Type) ->
    forall {k : Kind}, Tau n k -> Tau n k -> Type :=
| TRC_refl {n : nat} {R : Path n -> Path n -> Type}
    {k : Kind} {d : Tau n k} : TauRuntimeConv R d d
| TRC_replace {n : nat} {R : Path n -> Path n -> Type}
    {k : Kind} (context : Tau (S n) k) {p q : Path n} :
    R p q -> TauRuntimeConv R (tau_open context p) (tau_open context q)
| TRC_fun {n : nat} {R : Path n -> Path n -> Type}
    {S S' : Ty n} {T T' : Ty (Datatypes.S n)} :
    TauRuntimeConv R (TauTy S) (TauTy S') ->
    TauRuntimeConv (PathScopedLift R) (TauTy T) (TauTy T') ->
    TauRuntimeConv R (TauTy (TyFun S T)) (TauTy (TyFun S' T'))
| TRC_pair {n : nat} {R : Path n -> Path n -> Type}
    {k : Kind} {S S' : Ty n} {d d' : Tau (Datatypes.S n) k} {a : Name} :
    TauRuntimeConv R (TauTy S) (TauTy S') ->
    TauRuntimeConv (PathScopedLift R) d d' ->
    TauRuntimeConv R (TauTy (TyPair S a d)) (TauTy (TyPair S' a d'))
| TRC_single {n : nat} {R : Path n -> Path n -> Type} {p q : Path n} :
    R p q -> TauRuntimeConv R (TauTy (TySingle p)) (TauTy (TySingle q))
| TRC_selection {n : nat} {R : Path n -> Path n -> Type}
    {p q : Path n} {a : Name} :
    R p q -> TauRuntimeConv R (TauTy (TyTSel p a)) (TauTy (TyTSel q a))
| TRC_interval {n : nat} {R : Path n -> Path n -> Type}
    {L L' U U' : Ty n} :
    TauRuntimeConv R (TauTy L) (TauTy L') ->
    TauRuntimeConv R (TauTy U) (TauTy U') ->
    TauRuntimeConv R (TauIntv L U) (TauIntv L' U').

Arguments TRC_refl {n R k d}.
Arguments TRC_replace {n R k} context {p q} _.
Arguments TRC_fun {n R S S' T T'} _ _.
Arguments TRC_pair {n R k S S' d d' a} _ _.
Arguments TRC_single {n R p q} _.
Arguments TRC_selection {n R p q a} _.
Arguments TRC_interval {n R L L' U U'} _ _.

(** Conversion is natural under simultaneous substitution and relation maps. *)
Fixpoint tau_runtime_conv_subst {n : nat}
    {R : Path n -> Path n -> Type} {k : Kind} {d1 d2 : Tau n k}
    (conversion : TauRuntimeConv R d1 d2) {struct conversion} :
    forall {m : nat} {E : Path m -> Path m -> Type}
      (rho : PathSubst n m), PathSubstHom R E rho ->
      TauRuntimeConv E (tau_subst d1 rho) (tau_subst d2 rho).
Proof.
  intros m E rho map_paths.
  destruct conversion.
  - exact TRC_refl.
  - rewrite !tau_open_subst.
    exact (TRC_replace (tau_subst context (path_subst_lift rho))
      (map_paths _ _ r)).
  - exact (TRC_fun
      (@tau_runtime_conv_subst n R KStar _ _ conversion1
        m E rho map_paths)
      (@tau_runtime_conv_subst (Datatypes.S n) (PathScopedLift R) KStar _ _
        conversion2 (Datatypes.S m) (PathScopedLift E) (path_subst_lift rho)
        (fun p q evidence => path_scoped_lift_subst map_paths evidence))).
  - exact (TRC_pair
      (@tau_runtime_conv_subst n R KStar _ _ conversion1
        m E rho map_paths)
      (@tau_runtime_conv_subst (Datatypes.S n) (PathScopedLift R) k _ _
        conversion2 (Datatypes.S m) (PathScopedLift E) (path_subst_lift rho)
        (fun p q evidence => path_scoped_lift_subst map_paths evidence))).
  - exact (TRC_single (map_paths _ _ r)).
  - exact (TRC_selection (map_paths _ _ r)).
  - exact (TRC_interval
      (@tau_runtime_conv_subst n R KStar _ _ conversion1
        m E rho map_paths)
      (@tau_runtime_conv_subst n R KStar _ _ conversion2
        m E rho map_paths)).
Defined.

Arguments tau_runtime_conv_subst {n R k d1 d2} conversion
  {m E} rho map_paths.

(** Renaming is the variable-only instance of conversion substitution. *)
Definition tau_runtime_conv_rename {n m : nat}
    {R : Path n -> Path n -> Type} {E : Path m -> Path m -> Type}
    {k : Kind} {d1 d2 : Tau n k} (f : FinFun n m)
    (map_paths : forall p q, R p q ->
      E (path_rename p f) (path_rename q f))
    (conversion : TauRuntimeConv R d1 d2) :
    TauRuntimeConv E (tau_rename d1 f) (tau_rename d2 f).
Proof.
  assert (map_subst : PathSubstHom R E (finfun_as_subst f)).
  { intros p q evidence. rewrite !path_subst_as_subst.
    exact (map_paths p q evidence). }
  pose proof (tau_runtime_conv_subst conversion
    (finfun_as_subst f) map_subst) as result.
  rewrite !tau_subst_as_subst in result. exact result.
Defined.

(** Opening a scoped conversion at one path. *)
Definition tau_runtime_conv_open_same {n : nat}
    {R : Path n -> Path n -> Type} {k : Kind}
    {d1 d2 : Tau (S n) k} (operations : PathEqCongruence R)
    (conversion : TauRuntimeConv (PathScopedLift R) d1 d2)
    (argument : Path n) :
    TauRuntimeConv R (tau_open d1 argument) (tau_open d2 argument) :=
  tau_runtime_conv_subst conversion (path_subst_openAt argument)
    (fun p q evidence => path_scoped_lift_open operations evidence
      (eq_refl operations argument)).

(** Runtime conversion survives allocation. *)
Definition tau_runtime_conv_weaken {n : nat} {sigma : Store n}
    {k : Kind} {d1 d2 : Tau n k}
    (conversion : TauRuntimeConv (PathRuntimeEq sigma) d1 d2)
    (v : Tm n) (value : Tm_IsValue v) :
    TauRuntimeConv (PathRuntimeEq (StoreVal sigma v value))
      (tau_weaken d1) (tau_weaken d2).
Proof.
  unfold tau_weaken.
  exact (tau_runtime_conv_rename (f := weaken n)
    (fun p q evidence => path_runtime_eq_weaken evidence (v := v) value)
    conversion).
Defined.

(** Structural normal form for runtime conversion. *)
Inductive TauRuntimeCongruent :
    forall {n : nat}, (Path n -> Path n -> Type) ->
    forall {k : Kind}, Tau n k -> Tau n k -> Type :=
| TRG_top {n : nat} {R : Path n -> Path n -> Type} :
    TauRuntimeCongruent R (TauTy TyTop) (TauTy TyTop)
| TRG_bot {n : nat} {R : Path n -> Path n -> Type} :
    TauRuntimeCongruent R (TauTy TyBot) (TauTy TyBot)
| TRG_fun {n : nat} {R : Path n -> Path n -> Type}
    {S S' : Ty n} {T T' : Ty (Datatypes.S n)} :
    TauRuntimeCongruent R (TauTy S) (TauTy S') ->
    TauRuntimeCongruent (PathScopedLift R) (TauTy T) (TauTy T') ->
    TauRuntimeCongruent R (TauTy (TyFun S T)) (TauTy (TyFun S' T'))
| TRG_pair {n : nat} {R : Path n -> Path n -> Type}
    {k : Kind} {S S' : Ty n} {d d' : Tau (Datatypes.S n) k}
    {a : Name} :
    TauRuntimeCongruent R (TauTy S) (TauTy S') ->
    TauRuntimeCongruent (PathScopedLift R) d d' ->
    TauRuntimeCongruent R (TauTy (TyPair S a d))
      (TauTy (TyPair S' a d'))
| TRG_single {n : nat} {R : Path n -> Path n -> Type}
    {p q : Path n} :
    R p q -> TauRuntimeCongruent R (TauTy (TySingle p))
      (TauTy (TySingle q))
| TRG_selection {n : nat} {R : Path n -> Path n -> Type}
    {p q : Path n} {a : Name} :
    R p q -> TauRuntimeCongruent R (TauTy (TyTSel p a))
      (TauTy (TyTSel q a))
| TRG_interval {n : nat} {R : Path n -> Path n -> Type}
    {L L' U U' : Ty n} :
    TauRuntimeCongruent R (TauTy L) (TauTy L') ->
    TauRuntimeCongruent R (TauTy U) (TauTy U') ->
    TauRuntimeCongruent R (TauIntv L U) (TauIntv L' U').

Arguments TRG_top {n R}.
Arguments TRG_bot {n R}.
Arguments TRG_fun {n R S S' T T'} _ _.
Arguments TRG_pair {n R k S S' d d' a} _ _.
Arguments TRG_single {n R p q} _.
Arguments TRG_selection {n R p q a} _.
Arguments TRG_interval {n R L L' U U'} _ _.

(** Pointwise related substitutions remain related below one binder. *)
Definition path_scoped_lift_pointwise {l n : nat}
    {R : Path n -> Path n -> Type}
    {rho1 rho2 : PathSubst l n}
    (related : forall x, R (subst_apply rho1 x) (subst_apply rho2 x))
    (x : Fin (S l)) :
    PathScopedLift R
      (subst_apply (path_subst_lift rho1) x)
      (subst_apply (path_subst_lift rho2) x).
Proof.
  refine (fin_case (P := fun x => PathScopedLift R
      (subst_apply (path_subst_lift rho1) x)
      (subst_apply (path_subst_lift rho2) x)) _ _ x).
  - rewrite !path_subst_lift_zero. exact SL_bound.
  - intro i. rewrite !path_subst_lift_succ. exact (SL_old (related i)).
Defined.

(** Reflexivity of structural conversion. *)
Fixpoint ty_runtime_congruent_refl {n : nat}
    {R : Path n -> Path n -> Type} (operations : PathEqCongruence R)
    (T : Ty n) {struct T} :
    TauRuntimeCongruent R (TauTy T) (TauTy T)
with tau_runtime_congruent_refl {n : nat}
    {R : Path n -> Path n -> Type} (operations : PathEqCongruence R)
    {k : Kind} (d : Tau n k) {struct d} :
    TauRuntimeCongruent R d d.
Proof.
  - dependent destruction T.
    + exact TRG_top.
    + exact TRG_bot.
    + exact (TRG_fun
        (ty_runtime_congruent_refl n R operations T1)
        (ty_runtime_congruent_refl (S n) (PathScopedLift R)
          (path_scoped_lift_congruence operations) T2)).
    + exact (TRG_pair
        (ty_runtime_congruent_refl n R operations T)
        (tau_runtime_congruent_refl (S n) (PathScopedLift R)
          (path_scoped_lift_congruence operations) k t)).
    + exact (TRG_single (eq_refl operations p)).
    + exact (TRG_selection (eq_refl operations p)).
  - dependent destruction d.
    + exact (ty_runtime_congruent_refl n R operations t).
    + exact (TRG_interval
        (ty_runtime_congruent_refl n R operations t)
        (ty_runtime_congruent_refl n R operations t0)).
Defined.

Arguments ty_runtime_congruent_refl {n R} operations T.
Arguments tau_runtime_congruent_refl {n R} operations {k} d.

(** Symmetry of structural conversion. *)
Fixpoint tau_runtime_congruent_symm {n : nat}
    {R : Path n -> Path n -> Type} {k : Kind} {d1 d2 : Tau n k}
    (operations : PathEqCongruence R)
    (evidence : TauRuntimeCongruent R d1 d2) {struct evidence} :
    TauRuntimeCongruent R d2 d1.
Proof.
  destruct evidence.
  - exact TRG_top.
  - exact TRG_bot.
  - exact (TRG_fun
      (@tau_runtime_congruent_symm n R KStar _ _ operations evidence1)
      (@tau_runtime_congruent_symm (Datatypes.S n) (PathScopedLift R)
        KStar _ _ (path_scoped_lift_congruence operations) evidence2)).
  - exact (TRG_pair
      (@tau_runtime_congruent_symm n R KStar _ _ operations evidence1)
      (@tau_runtime_congruent_symm (Datatypes.S n) (PathScopedLift R)
        k _ _ (path_scoped_lift_congruence operations) evidence2)).
  - exact (TRG_single (eq_symm operations r)).
  - exact (TRG_selection (eq_symm operations r)).
  - exact (TRG_interval
      (@tau_runtime_congruent_symm n R KStar _ _ operations evidence1)
      (@tau_runtime_congruent_symm n R KStar _ _ operations evidence2)).
Defined.

Arguments tau_runtime_congruent_symm {n R k d1 d2} operations evidence.

(** Substitution maps every compound path congruentially. *)
Fixpoint path_subst_related {l n : nat}
    {R : Path n -> Path n -> Type} (operations : PathEqCongruence R)
    (rho1 rho2 : PathSubst l n)
    (related : forall x, R (subst_apply rho1 x) (subst_apply rho2 x))
    (p : Path l) {struct p} :
    R (path_subst p rho1) (path_subst p rho2).
Proof.
  destruct p.
  - exact (related f).
  - exact (eq_fst operations
      (path_subst_related n0 n R operations rho1 rho2 related p)).
  - exact (eq_sel operations
      (path_subst_related n0 n R operations rho1 rho2 related p) n1).
Defined.

Arguments path_subst_related {l n R} operations rho1 rho2 related p.

(** Pointwise related substitutions induce structural conversion. *)
Fixpoint ty_runtime_congruent_of_subst {l n : nat}
    {R : Path n -> Path n -> Type} (operations : PathEqCongruence R)
    (rho1 rho2 : PathSubst l n)
    (related : forall x, R (subst_apply rho1 x) (subst_apply rho2 x))
    (T : Ty l) {struct T} :
    TauRuntimeCongruent R (TauTy (ty_subst T rho1))
      (TauTy (ty_subst T rho2))
with tau_runtime_congruent_of_subst {l n : nat}
    {R : Path n -> Path n -> Type} (operations : PathEqCongruence R)
    (rho1 rho2 : PathSubst l n)
    (related : forall x, R (subst_apply rho1 x) (subst_apply rho2 x))
    {k : Kind} (d : Tau l k) {struct d} :
    TauRuntimeCongruent R (tau_subst d rho1) (tau_subst d rho2).
Proof.
  - dependent destruction T.
    + exact TRG_top.
    + exact TRG_bot.
    + exact (TRG_fun
        (ty_runtime_congruent_of_subst n0 n R operations
          rho1 rho2 related T1)
        (ty_runtime_congruent_of_subst (S n0) (S n) (PathScopedLift R)
          (path_scoped_lift_congruence operations)
          (path_subst_lift rho1) (path_subst_lift rho2)
          (path_scoped_lift_pointwise related) T2)).
    + exact (TRG_pair
        (ty_runtime_congruent_of_subst n0 n R operations
          rho1 rho2 related T)
        (tau_runtime_congruent_of_subst (S n0) (S n) (PathScopedLift R)
          (path_scoped_lift_congruence operations)
          (path_subst_lift rho1) (path_subst_lift rho2)
          (path_scoped_lift_pointwise related) k t)).
    + exact (TRG_single
        (path_subst_related operations rho1 rho2 related p)).
    + exact (TRG_selection
        (path_subst_related operations rho1 rho2 related p)).
  - dependent destruction d.
    + exact (ty_runtime_congruent_of_subst n0 n R operations
        rho1 rho2 related t).
    + exact (TRG_interval
        (ty_runtime_congruent_of_subst n0 n R operations
          rho1 rho2 related t)
        (ty_runtime_congruent_of_subst n0 n R operations
          rho1 rho2 related t0)).
Defined.

Arguments ty_runtime_congruent_of_subst {l n R} operations
  rho1 rho2 related T.
Arguments tau_runtime_congruent_of_subst {l n R} operations
  rho1 rho2 related {k} d.

(** Re-encode structural conversion as ordinary conversion evidence. *)
Fixpoint tau_runtime_congruent_to_runtime_conv {n : nat}
    {R : Path n -> Path n -> Type} {k : Kind} {d1 d2 : Tau n k}
    (evidence : TauRuntimeCongruent R d1 d2) {struct evidence} :
    TauRuntimeConv R d1 d2.
Proof.
  destruct evidence.
  - exact TRC_refl.
  - exact TRC_refl.
  - exact (TRC_fun
      (@tau_runtime_congruent_to_runtime_conv n R KStar _ _ evidence1)
      (@tau_runtime_congruent_to_runtime_conv (Datatypes.S n)
        (PathScopedLift R) KStar _ _ evidence2)).
  - exact (TRC_pair
      (@tau_runtime_congruent_to_runtime_conv n R KStar _ _ evidence1)
      (@tau_runtime_congruent_to_runtime_conv (Datatypes.S n)
        (PathScopedLift R) k _ _ evidence2)).
  - exact (TRC_single r).
  - exact (TRC_selection r).
  - exact (TRC_interval
      (@tau_runtime_congruent_to_runtime_conv n R KStar _ _ evidence1)
      (@tau_runtime_congruent_to_runtime_conv n R KStar _ _ evidence2)).
Defined.

Arguments tau_runtime_congruent_to_runtime_conv {n R k d1 d2} evidence.

Definition path_subst_openAt_related {n : nat}
    {R : Path n -> Path n -> Type} (operations : PathEqCongruence R)
    {p q : Path n} (evidence : R p q) (x : Fin (S n)) :
    R (subst_apply (path_subst_openAt p) x)
      (subst_apply (path_subst_openAt q) x).
Proof.
  refine (fin_case (P := fun x =>
      R (subst_apply (path_subst_openAt p) x)
        (subst_apply (path_subst_openAt q) x)) _ _ x).
  - rewrite !path_subst_openAt_zero. exact evidence.
  - intro i. rewrite !path_subst_openAt_succ.
    exact (eq_refl operations (PVar i)).
Defined.

(** Normalize arbitrary conversion evidence to structural form. *)
Fixpoint tau_runtime_conv_runtime_congruent {n : nat}
    {R : Path n -> Path n -> Type} (operations : PathEqCongruence R)
    {k : Kind} {d1 d2 : Tau n k}
    (conversion : TauRuntimeConv R d1 d2) {struct conversion} :
    TauRuntimeCongruent R d1 d2.
Proof.
  destruct conversion.
  - exact (tau_runtime_congruent_refl operations d).
  - exact (tau_runtime_congruent_of_subst operations
      (path_subst_openAt p) (path_subst_openAt q)
      (path_subst_openAt_related operations r) context).
  - exact (TRG_fun
      (@tau_runtime_conv_runtime_congruent n R operations KStar _ _
        conversion1)
      (@tau_runtime_conv_runtime_congruent (Datatypes.S n)
        (PathScopedLift R) (path_scoped_lift_congruence operations)
        KStar _ _ conversion2)).
  - exact (TRG_pair
      (@tau_runtime_conv_runtime_congruent n R operations KStar _ _
        conversion1)
      (@tau_runtime_conv_runtime_congruent (Datatypes.S n)
        (PathScopedLift R) (path_scoped_lift_congruence operations)
        k _ _ conversion2)).
  - exact (TRG_single r).
  - exact (TRG_selection r).
  - exact (TRG_interval
      (@tau_runtime_conv_runtime_congruent n R operations KStar _ _
        conversion1)
      (@tau_runtime_conv_runtime_congruent n R operations KStar _ _
        conversion2)).
Defined.

Arguments tau_runtime_conv_runtime_congruent {n R} operations
  {k d1 d2} conversion.

Print Assumptions path_runtime_eq_resolve_iff.
Print Assumptions tau_runtime_conv_runtime_congruent.
