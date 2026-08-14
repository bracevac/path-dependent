From Stdlib Require Import Arith.PeanoNat.
From PathDependent.LambdaP Require Import FinFun.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Local Coercion FinFun.apply : FinFun.t >-> Funclass.

Definition Name : Type := nat.

Inductive Kind : Type :=
| star
| iota.

Definition Kind_eq_dec (x y : Kind) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Inductive Path (n : nat) : Type :=
| path_var : Fin.t n -> Path n
| path_fst : Path n -> Path n
| path_sel : Path n -> Name -> Path n.

Arguments path_var {n} _.
Arguments path_fst {n} _.
Arguments path_sel {n} _ _.

Fixpoint Path_eq_dec {n : nat} (p q : Path n) : {p = q} + {p <> q}.
Proof.
  decide equality; try apply Nat.eq_dec; try apply Fin.eq_dec.
Defined.

Inductive Ty : nat -> Type :=
| ty_top {n} : Ty n
| ty_bot {n} : Ty n
| ty_fun {n} : Ty n -> Ty (S n) -> Ty n
| ty_pair {n k} : Ty n -> Name -> Tau (S n) k -> Ty n
| ty_single {n} : Path n -> Ty n
| ty_tsel {n} : Path n -> Name -> Ty n
with Tau : nat -> Kind -> Type :=
| tau_ty {n} : Ty n -> Tau n star
| tau_intv {n} : Ty n -> Ty n -> Tau n iota.

Arguments ty_top {n}.
Arguments ty_bot {n}.
Arguments ty_fun {n} _ _.
Arguments ty_pair {n k} _ _ _.
Arguments ty_single {n} _.
Arguments ty_tsel {n} _ _.
Arguments tau_ty {n} _.
Arguments tau_intv {n} _ _.

Inductive Def : nat -> Kind -> Type :=
| def_val {n} : Fin.t n -> Def n star
| def_type {n} : Ty n -> Def n iota.

Arguments def_val {n} _.
Arguments def_type {n} _.

Inductive Tm : nat -> Type :=
| tm_path {n} : Path n -> Tm n
| tm_abs {n} : Ty n -> Tm (S n) -> Tm n
| tm_pair {n k} : Fin.t n -> Name -> Def n k -> Tm n
| tm_app {n} : Path n -> Path n -> Tm n
| tm_let {n} : Tm n -> Tm (S n) -> Tm n
| tm_typed {n} : Tm n -> Ty n -> Tm n.

Arguments tm_path {n} _.
Arguments tm_abs {n} _ _.
Arguments tm_pair {n k} _ _ _.
Arguments tm_app {n} _ _.
Arguments tm_let {n} _ _.
Arguments tm_typed {n} _ _.

(** The four coercions present in the Lean surface. *)
Coercion ty_single : Path >-> Ty.
Coercion tm_path : Path >-> Tm.
Coercion tau_ty : Ty >-> Tau.
Coercion def_type : Ty >-> Def.

Definition Interval (n : nat) : Type := (Ty n * Ty n)%type.

Definition Tau_interval {n : nat} (d : Tau n iota) : Interval n :=
  match d with
  | tau_intv s t => (s, t)
  end.

Inductive Path_IsVar {n : nat} : Path n -> Prop :=
| is_var (x : Fin.t n) : Path_IsVar (path_var x).

Inductive Tm_IsValue {n : nat} : Tm n -> Prop :=
| value_abs (T : Ty n) (t : Tm (S n)) : Tm_IsValue (tm_abs T t)
| value_pair (k : Kind) (y : Fin.t n) (a : Name) (d : Def n k) :
    Tm_IsValue (tm_pair y a d).

(** Renaming. *)
Fixpoint Path_rename {n m : nat} (p : Path n) (f : FinFun.t n m) : Path m :=
  match p with
  | path_var x => path_var (f x)
  | path_fst p => path_fst (Path_rename p f)
  | path_sel p a => path_sel (Path_rename p f) a
  end.

Fixpoint Ty_rename {n : nat} (T : Ty n) :
    forall m, FinFun.t n m -> Ty m :=
  match T in Ty n' return forall m, FinFun.t n' m -> Ty m with
  | ty_top => fun m _ => @ty_top m
  | ty_bot => fun m _ => @ty_bot m
  | ty_fun s t => fun m f =>
      ty_fun (@Ty_rename _ s m f)
        (@Ty_rename _ t (S m) (FinFun.ext f))
  | ty_pair s a d => fun m f =>
      ty_pair (@Ty_rename _ s m f) a
        (@Tau_rename _ _ d (S m) (FinFun.ext f))
  | ty_single p => fun m f => ty_single (Path_rename p f)
  | ty_tsel p A => fun m f => ty_tsel (Path_rename p f) A
  end
with Tau_rename {n k} (d : Tau n k) :
    forall m, FinFun.t n m -> Tau m k :=
  match d in Tau n' k' return forall m, FinFun.t n' m -> Tau m k' with
  | tau_ty t => fun m f => tau_ty (@Ty_rename _ t m f)
  | tau_intv s t => fun m f =>
      tau_intv (@Ty_rename _ s m f) (@Ty_rename _ t m f)
  end.

Arguments Ty_rename {n} T {m} f.
Arguments Tau_rename {n k} d {m} f.

Definition Def_rename {n k} (d : Def n k) :
    forall m, FinFun.t n m -> Def m k :=
  match d in Def n' k' return forall m, FinFun.t n' m -> Def m k' with
  | def_val x => fun m f => def_val (f x)
  | def_type t => fun m f => def_type (Ty_rename t f)
  end.

Arguments Def_rename {n k} d {m} f.

Fixpoint Tm_rename {n : nat} (t : Tm n) :
    forall m, FinFun.t n m -> Tm m :=
  match t in Tm n' return forall m, FinFun.t n' m -> Tm m with
  | tm_path p => fun m f => tm_path (Path_rename p f)
  | tm_abs ty body => fun m f =>
      tm_abs (Ty_rename ty f) (Tm_rename body (FinFun.ext f))
  | tm_pair y a d => fun m f => tm_pair (f y) a (Def_rename d f)
  | tm_app p q => fun m f => tm_app (Path_rename p f) (Path_rename q f)
  | tm_let t u => fun m f =>
      tm_let (Tm_rename t f) (Tm_rename u (FinFun.ext f))
  | tm_typed t ty => fun m f =>
      tm_typed (Tm_rename t f) (Ty_rename ty f)
  end.

Arguments Tm_rename {n} t {m} f.

Definition Path_weaken {n : nat} (p : Path n) : Path (S n) :=
  Path_rename p (FinFun.weaken n).

Definition Ty_weaken {n : nat} (T : Ty n) : Ty (S n) :=
  Ty_rename T (FinFun.weaken n).

Definition Tau_weaken {n k} (d : Tau n k) : Tau (S n) k :=
  Tau_rename d (FinFun.weaken n).

Definition Tm_weaken {n : nat} (t : Tm n) : Tm (S n) :=
  Tm_rename t (FinFun.weaken n).

Definition Def_weaken {n k} (d : Def n k) : Def (S n) k :=
  Def_rename d (FinFun.weaken n).

(** First-order simultaneous substitutions. *)
Definition PathSubst (n m : nat) : Type := Env.t (Path m) n.

Definition PathSubst_apply {n m : nat} (s : PathSubst n m) :
    Fin.t n -> Path m := Env.lookup s.

Coercion PathSubst_apply : PathSubst >-> Funclass.

Definition FinFun_asSubst {n m : nat} (f : FinFun.t n m) : PathSubst n m :=
  Env.tabulate n (fun x => path_var (f x)).

Definition PathSubst_id (n : nat) : PathSubst n n :=
  Env.tabulate n (fun x => path_var x).

Definition PathSubst_lift {n m : nat} (s : PathSubst n m) :
    PathSubst (S n) (S m) :=
  Env.tabulate (S n)
    (fun x => Fin.cases (path_var Fin.zero)
      (fun i => Path_weaken (s i)) x).

Definition PathSubst_openAt {n : nat} (p : Path n) : PathSubst (S n) n :=
  Env.tabulate (S n)
    (fun x => Fin.cases p (fun i => path_var i) x).

Definition PathSubst_compRename {n m l : nat}
    (s : PathSubst n m) (f : FinFun.t m l) : PathSubst n l :=
  Env.tabulate n (fun x => Path_rename (s x) f).

Definition FinFun_compSubst {n m l : nat}
    (f : FinFun.t n m) (s : PathSubst m l) : PathSubst n l :=
  Env.tabulate n (fun x => s (f x)).

Fixpoint Path_subst {n m : nat} (p : Path n) (s : PathSubst n m) : Path m :=
  match p with
  | path_var x => s x
  | path_fst p => path_fst (Path_subst p s)
  | path_sel p a => path_sel (Path_subst p s) a
  end.

Definition PathSubst_comp {n m l : nat}
    (s : PathSubst n m) (t : PathSubst m l) : PathSubst n l :=
  Env.tabulate n (fun x => Path_subst (s x) t).

Fixpoint Ty_subst {n : nat} (T : Ty n) :
    forall m, PathSubst n m -> Ty m :=
  match T in Ty n' return forall m, PathSubst n' m -> Ty m with
  | ty_top => fun m _ => @ty_top m
  | ty_bot => fun m _ => @ty_bot m
  | ty_fun dom cod => fun m s =>
      ty_fun (@Ty_subst _ dom m s)
        (@Ty_subst _ cod (S m) (PathSubst_lift s))
  | ty_pair fst_ty a d => fun m s =>
      ty_pair (@Ty_subst _ fst_ty m s) a
        (@Tau_subst _ _ d (S m) (PathSubst_lift s))
  | ty_single p => fun m s => ty_single (Path_subst p s)
  | ty_tsel p A => fun m s => ty_tsel (Path_subst p s) A
  end
with Tau_subst {n k} (d : Tau n k) :
    forall m, PathSubst n m -> Tau m k :=
  match d in Tau n' k' return forall m, PathSubst n' m -> Tau m k' with
  | tau_ty t => fun m s => tau_ty (@Ty_subst _ t m s)
  | tau_intv lo hi => fun m s =>
      tau_intv (@Ty_subst _ lo m s) (@Ty_subst _ hi m s)
  end.

Arguments Ty_subst {n} T {m} s.
Arguments Tau_subst {n k} d {m} s.

Definition Path_open {n : nat} (q : Path (S n)) (p : Path n) : Path n :=
  Path_subst q (PathSubst_openAt p).

Definition Ty_open {n : nat} (T : Ty (S n)) (p : Path n) : Ty n :=
  Ty_subst T (PathSubst_openAt p).

Definition Tau_open {n k} (d : Tau (S n) k) (p : Path n) : Tau n k :=
  Tau_subst d (PathSubst_openAt p).

Definition Tm_open {n : nat} (t : Tm (S n)) (x : Fin.t n) : Tm n :=
  Tm_rename t (FinFun.openAt x).

Definition Def_open {n k} (d : Def (S n) k) (x : Fin.t n) : Def n k :=
  Def_rename d (FinFun.openAt x).

(** Mutual induction principles used by the syntax algebra. *)
Scheme Ty_mut := Induction for Ty Sort Prop
with Tau_mut := Induction for Tau Sort Prop.
Combined Scheme TyTau_mutind from Ty_mut, Tau_mut.

(** Algebra of renaming. *)
Theorem Path_rename_id {n : nat} (p : Path n) :
    Path_rename p (FinFun.id n) = p.
Proof.
  induction p; cbn; f_equal; auto using FinFun.id_apply.
Qed.

Theorem Path_rename_rename {n m l : nat} (p : Path n)
    (f : FinFun.t n m) (g : FinFun.t m l) :
    Path_rename (Path_rename p f) g = Path_rename p (FinFun.comp f g).
Proof.
  induction p; cbn; f_equal; auto using FinFun.comp_apply.
Qed.

Lemma TyTau_rename_id :
    (forall (n : nat) (T : Ty n), Ty_rename T (FinFun.id n) = T) /\
    (forall (n : nat) (k : Kind) (d : Tau n k),
      Tau_rename d (FinFun.id n) = d).
Proof.
  apply TyTau_mutind; intros; cbn.
  - reflexivity.
  - reflexivity.
  - change (ty_fun (Ty_rename t (FinFun.id n))
      (Ty_rename t0 (FinFun.ext (FinFun.id n))) = ty_fun t t0).
    rewrite H, FinFun.ext_id, H0. reflexivity.
  - change (ty_pair (Ty_rename t (FinFun.id n)) n0
      (Tau_rename t0 (FinFun.ext (FinFun.id n))) = ty_pair t n0 t0).
    rewrite H, FinFun.ext_id, H0. reflexivity.
  - now rewrite Path_rename_id.
  - now rewrite Path_rename_id.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Theorem Ty_rename_id {n : nat} (T : Ty n) :
    Ty_rename T (FinFun.id n) = T.
Proof. exact (proj1 TyTau_rename_id n T). Qed.

Theorem Tau_rename_id {n : nat} {k : Kind} (d : Tau n k) :
    Tau_rename d (FinFun.id n) = d.
Proof. exact (proj2 TyTau_rename_id n k d). Qed.

Theorem Def_rename_id {n : nat} {k : Kind} (d : Def n k) :
    Def_rename d (FinFun.id n) = d.
Proof.
  destruct d.
  - change (def_val (FinFun.id n t) = def_val t).
    now rewrite FinFun.id_apply.
  - change (def_type (Ty_rename t (FinFun.id n)) = def_type t).
    now rewrite Ty_rename_id.
Qed.

Theorem Tm_rename_id {n : nat} (t : Tm n) :
    Tm_rename t (FinFun.id n) = t.
Proof.
  induction t; cbn.
  - now rewrite Path_rename_id.
  - change (tm_abs (Ty_rename t (FinFun.id n))
      (Tm_rename t0 (FinFun.ext (FinFun.id n))) = tm_abs t t0).
    rewrite Ty_rename_id, FinFun.ext_id, IHt. reflexivity.
  - rewrite FinFun.id_apply, Def_rename_id. reflexivity.
  - now rewrite !Path_rename_id.
  - change (tm_let (Tm_rename t1 (FinFun.id n))
      (Tm_rename t2 (FinFun.ext (FinFun.id n))) = tm_let t1 t2).
    rewrite IHt1, FinFun.ext_id, IHt2. reflexivity.
  - now rewrite IHt, Ty_rename_id.
Qed.

Lemma TyTau_rename_rename :
    (forall (n : nat) (T : Ty n) (m l : nat)
      (f : FinFun.t n m) (g : FinFun.t m l),
      Ty_rename (Ty_rename T f) g = Ty_rename T (FinFun.comp f g)) /\
    (forall (n : nat) (k : Kind) (d : Tau n k) (m l : nat)
      (f : FinFun.t n m) (g : FinFun.t m l),
      Tau_rename (Tau_rename d f) g = Tau_rename d (FinFun.comp f g)).
Proof.
  apply TyTau_mutind; intros; cbn.
  - reflexivity.
  - reflexivity.
  - change (ty_fun (Ty_rename (Ty_rename t f) g)
      (Ty_rename (Ty_rename t0 (FinFun.ext f)) (FinFun.ext g)) =
      ty_fun (Ty_rename t (FinFun.comp f g))
        (Ty_rename t0 (FinFun.ext (FinFun.comp f g)))).
    rewrite H, H0, FinFun.ext_comp. reflexivity.
  - change (ty_pair (Ty_rename (Ty_rename t f) g) n0
      (Tau_rename (Tau_rename t0 (FinFun.ext f)) (FinFun.ext g)) =
      ty_pair (Ty_rename t (FinFun.comp f g)) n0
        (Tau_rename t0 (FinFun.ext (FinFun.comp f g)))).
    rewrite H, H0, FinFun.ext_comp. reflexivity.
  - now rewrite Path_rename_rename.
  - now rewrite Path_rename_rename.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Theorem Ty_rename_rename {n m l : nat} (T : Ty n)
    (f : FinFun.t n m) (g : FinFun.t m l) :
    Ty_rename (Ty_rename T f) g = Ty_rename T (FinFun.comp f g).
Proof. exact (proj1 TyTau_rename_rename n T m l f g). Qed.

Theorem Tau_rename_rename {n m l : nat} {k : Kind} (d : Tau n k)
    (f : FinFun.t n m) (g : FinFun.t m l) :
    Tau_rename (Tau_rename d f) g = Tau_rename d (FinFun.comp f g).
Proof. exact (proj2 TyTau_rename_rename n k d m l f g). Qed.

Theorem Def_rename_rename {n m l : nat} {k : Kind} (d : Def n k)
    (f : FinFun.t n m) (g : FinFun.t m l) :
    Def_rename (Def_rename d f) g = Def_rename d (FinFun.comp f g).
Proof.
  destruct d; cbn.
  - now rewrite FinFun.comp_apply.
  - now rewrite Ty_rename_rename.
Qed.

Theorem Tm_rename_rename {n m l : nat} (t : Tm n)
    (f : FinFun.t n m) (g : FinFun.t m l) :
    Tm_rename (Tm_rename t f) g = Tm_rename t (FinFun.comp f g).
Proof.
  revert m l f g. induction t; intros m l f g; cbn.
  - now rewrite Path_rename_rename.
  - change (tm_abs (Ty_rename (Ty_rename t f) g)
      (Tm_rename (Tm_rename t0 (FinFun.ext f)) (FinFun.ext g)) =
      tm_abs (Ty_rename t (FinFun.comp f g))
        (Tm_rename t0 (FinFun.ext (FinFun.comp f g)))).
    rewrite Ty_rename_rename, IHt, FinFun.ext_comp. reflexivity.
  - rewrite FinFun.comp_apply, Def_rename_rename. reflexivity.
  - now rewrite !Path_rename_rename.
  - change (tm_let (Tm_rename (Tm_rename t1 f) g)
      (Tm_rename (Tm_rename t2 (FinFun.ext f)) (FinFun.ext g)) =
      tm_let (Tm_rename t1 (FinFun.comp f g))
        (Tm_rename t2 (FinFun.ext (FinFun.comp f g)))).
    rewrite IHt1, IHt2, FinFun.ext_comp. reflexivity.
  - now rewrite IHt, Ty_rename_rename.
Qed.

Theorem Path_weaken_rename {n m : nat} (p : Path n) (f : FinFun.t n m) :
    Path_weaken (Path_rename p f) =
      Path_rename (Path_weaken p) (FinFun.ext f).
Proof.
  unfold Path_weaken. rewrite !Path_rename_rename, FinFun.comp_weaken.
  reflexivity.
Qed.

Theorem Ty_weaken_rename {n m : nat} (T : Ty n) (f : FinFun.t n m) :
    Ty_weaken (Ty_rename T f) = Ty_rename (Ty_weaken T) (FinFun.ext f).
Proof.
  unfold Ty_weaken. rewrite !Ty_rename_rename, FinFun.comp_weaken.
  reflexivity.
Qed.

Theorem Tau_weaken_rename {n m : nat} {k : Kind}
    (d : Tau n k) (f : FinFun.t n m) :
    Tau_weaken (Tau_rename d f) = Tau_rename (Tau_weaken d) (FinFun.ext f).
Proof.
  unfold Tau_weaken. rewrite !Tau_rename_rename, FinFun.comp_weaken.
  reflexivity.
Qed.

Theorem Def_weaken_rename {n m : nat} {k : Kind}
    (d : Def n k) (f : FinFun.t n m) :
    Def_weaken (Def_rename d f) = Def_rename (Def_weaken d) (FinFun.ext f).
Proof.
  unfold Def_weaken. rewrite !Def_rename_rename, FinFun.comp_weaken.
  reflexivity.
Qed.

Theorem Tm_weaken_rename {n m : nat} (t : Tm n) (f : FinFun.t n m) :
    Tm_weaken (Tm_rename t f) = Tm_rename (Tm_weaken t) (FinFun.ext f).
Proof.
  unfold Tm_weaken. rewrite !Tm_rename_rename, FinFun.comp_weaken.
  reflexivity.
Qed.

(** Pointwise observations and algebra for first-order substitutions. *)
Theorem PathSubst_funext {n m : nat} {s t : PathSubst n m}
    (H : forall x, s x = t x) : s = t.
Proof. apply Env.ext. exact H. Qed.

Theorem PathSubst_lift_zero {n m : nat} (s : PathSubst n m) :
    PathSubst_lift s Fin.zero = path_var Fin.zero.
Proof.
  unfold PathSubst_lift, PathSubst_apply.
  rewrite Env.lookup_tabulate. reflexivity.
Qed.

Theorem PathSubst_lift_succ {n m : nat} (s : PathSubst n m)
    (x : Fin.t n) :
    PathSubst_lift s (Fin.succ x) = Path_weaken (s x).
Proof.
  unfold PathSubst_lift, PathSubst_apply.
  rewrite Env.lookup_tabulate. reflexivity.
Qed.

Theorem PathSubst_openAt_zero {n : nat} (p : Path n) :
    PathSubst_openAt p Fin.zero = p.
Proof.
  unfold PathSubst_openAt, PathSubst_apply.
  rewrite Env.lookup_tabulate. reflexivity.
Qed.

Theorem PathSubst_openAt_succ {n : nat} (p : Path n) (x : Fin.t n) :
    PathSubst_openAt p (Fin.succ x) = path_var x.
Proof.
  unfold PathSubst_openAt, PathSubst_apply.
  rewrite Env.lookup_tabulate. reflexivity.
Qed.

Theorem PathSubst_comp_apply {n m l : nat}
    (s : PathSubst n m) (t : PathSubst m l) (x : Fin.t n) :
    PathSubst_comp s t x = Path_subst (s x) t.
Proof. exact (@Env.lookup_tabulate (Path l) n (fun x => Path_subst (s x) t) x). Qed.

Theorem PathSubst_compRename_apply {n m l : nat}
    (s : PathSubst n m) (f : FinFun.t m l) (x : Fin.t n) :
    PathSubst_compRename s f x = Path_rename (s x) f.
Proof. exact (@Env.lookup_tabulate (Path l) n (fun x => Path_rename (s x) f) x). Qed.

Theorem FinFun_compSubst_apply {n m l : nat}
    (f : FinFun.t n m) (s : PathSubst m l) (x : Fin.t n) :
    FinFun_compSubst f s x = s (f x).
Proof. exact (@Env.lookup_tabulate (Path l) n (fun x => s (f x)) x). Qed.

Theorem PathSubst_id_apply {n : nat} (x : Fin.t n) :
    PathSubst_id n x = path_var x.
Proof. exact (@Env.lookup_tabulate (Path n) n (fun x => path_var x) x). Qed.

Theorem PathSubst_lift_id {n : nat} :
    PathSubst_lift (PathSubst_id n) = PathSubst_id (S n).
Proof.
  apply PathSubst_funext. intro x.
  refine (@Fin.cases' n x
    (fun x => PathSubst_lift (PathSubst_id n) x =
      PathSubst_id (S n) x) _ _).
  - rewrite PathSubst_lift_zero.
    unfold PathSubst_id, PathSubst_apply. rewrite Env.lookup_tabulate.
    reflexivity.
  - intros y. rewrite PathSubst_lift_succ.
    unfold PathSubst_id, PathSubst_apply, Path_weaken.
    rewrite !Env.lookup_tabulate. cbn. now rewrite FinFun.weaken_apply.
Qed.

Theorem PathSubst_compRename_lift {n m l : nat}
    (s : PathSubst n m) (f : FinFun.t m l) :
    PathSubst_lift (PathSubst_compRename s f) =
      PathSubst_compRename (PathSubst_lift s) (FinFun.ext f).
Proof.
  apply PathSubst_funext. intro x.
  refine (@Fin.cases' n x
    (fun x => PathSubst_lift (PathSubst_compRename s f) x =
      PathSubst_compRename (PathSubst_lift s) (FinFun.ext f) x) _ _).
  - rewrite PathSubst_lift_zero, PathSubst_compRename_apply,
      PathSubst_lift_zero. reflexivity.
  - intros y. rewrite PathSubst_lift_succ.
    rewrite PathSubst_compRename_apply.
    rewrite PathSubst_compRename_apply.
    rewrite PathSubst_lift_succ.
    apply Path_weaken_rename.
Qed.

Theorem PathSubst_compSubst_lift {n m l : nat}
    (g : FinFun.t n m) (s : PathSubst m l) :
    PathSubst_lift (FinFun_compSubst g s) =
      FinFun_compSubst (FinFun.ext g) (PathSubst_lift s).
Proof.
  apply PathSubst_funext. intro x.
  refine (@Fin.cases' n x
    (fun x => PathSubst_lift (FinFun_compSubst g s) x =
      FinFun_compSubst (FinFun.ext g) (PathSubst_lift s) x) _ _).
  - rewrite PathSubst_lift_zero, FinFun_compSubst_apply,
      FinFun.ext_zero, PathSubst_lift_zero. reflexivity.
  - intros y. rewrite PathSubst_lift_succ, FinFun_compSubst_apply,
      FinFun_compSubst_apply, FinFun.ext_succ, PathSubst_lift_succ.
    reflexivity.
Qed.

Theorem PathSubst_openAt_rename {n m : nat}
    (p : Path n) (f : FinFun.t n m) :
    PathSubst_compRename (PathSubst_openAt p) f =
      FinFun_compSubst (FinFun.ext f)
        (PathSubst_openAt (Path_rename p f)).
Proof.
  apply PathSubst_funext. intro x.
  refine (@Fin.cases' n x
    (fun x => PathSubst_compRename (PathSubst_openAt p) f x =
      FinFun_compSubst (FinFun.ext f)
        (PathSubst_openAt (Path_rename p f)) x) _ _).
  - rewrite PathSubst_compRename_apply, PathSubst_openAt_zero.
    rewrite FinFun_compSubst_apply, FinFun.ext_zero,
      PathSubst_openAt_zero. reflexivity.
  - intros y. rewrite PathSubst_compRename_apply, PathSubst_openAt_succ.
    rewrite FinFun_compSubst_apply, FinFun.ext_succ,
      PathSubst_openAt_succ. reflexivity.
Qed.

Theorem PathSubst_openAt_weaken {n : nat} (p : Path n) :
    FinFun_compSubst (FinFun.weaken n) (PathSubst_openAt p) =
      PathSubst_id n.
Proof.
  apply PathSubst_funext. intro x.
  rewrite FinFun_compSubst_apply, FinFun.weaken_apply,
    PathSubst_openAt_succ, PathSubst_id_apply. reflexivity.
Qed.

Theorem Path_subst_id {n : nat} (p : Path n) :
    Path_subst p (PathSubst_id n) = p.
Proof.
  induction p; cbn; f_equal; auto.
  unfold PathSubst_id, PathSubst_apply. apply Env.lookup_tabulate.
Qed.

Theorem Path_subst_rename {n m l : nat} (p : Path n)
    (s : PathSubst n m) (f : FinFun.t m l) :
    Path_rename (Path_subst p s) f =
      Path_subst p (PathSubst_compRename s f).
Proof.
  induction p; cbn; f_equal; auto using PathSubst_compRename_apply.
Qed.

Theorem Path_rename_subst {n m l : nat} (p : Path n)
    (g : FinFun.t n m) (s : PathSubst m l) :
    Path_subst (Path_rename p g) s =
      Path_subst p (FinFun_compSubst g s).
Proof.
  induction p; cbn; f_equal; auto.
  symmetry. apply FinFun_compSubst_apply.
Qed.

Lemma TyTau_subst_id :
    (forall (n : nat) (T : Ty n), Ty_subst T (PathSubst_id n) = T) /\
    (forall (n : nat) (k : Kind) (d : Tau n k),
      Tau_subst d (PathSubst_id n) = d).
Proof.
  apply TyTau_mutind; intros; cbn.
  - reflexivity.
  - reflexivity.
  - change (ty_fun (Ty_subst t (PathSubst_id n))
      (Ty_subst t0 (PathSubst_lift (PathSubst_id n))) = ty_fun t t0).
    rewrite H, PathSubst_lift_id, H0. reflexivity.
  - change (ty_pair (Ty_subst t (PathSubst_id n)) n0
      (Tau_subst t0 (PathSubst_lift (PathSubst_id n))) = ty_pair t n0 t0).
    rewrite H, PathSubst_lift_id, H0. reflexivity.
  - now rewrite Path_subst_id.
  - now rewrite Path_subst_id.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Theorem Ty_subst_id {n : nat} (T : Ty n) :
    Ty_subst T (PathSubst_id n) = T.
Proof. exact (proj1 TyTau_subst_id n T). Qed.

Theorem Tau_subst_id {n : nat} {k : Kind} (d : Tau n k) :
    Tau_subst d (PathSubst_id n) = d.
Proof. exact (proj2 TyTau_subst_id n k d). Qed.

Lemma TyTau_subst_rename :
    (forall (n : nat) (T : Ty n) (m l : nat)
      (s : PathSubst n m) (f : FinFun.t m l),
      Ty_rename (Ty_subst T s) f =
        Ty_subst T (PathSubst_compRename s f)) /\
    (forall (n : nat) (k : Kind) (d : Tau n k) (m l : nat)
      (s : PathSubst n m) (f : FinFun.t m l),
      Tau_rename (Tau_subst d s) f =
        Tau_subst d (PathSubst_compRename s f)).
Proof.
  apply TyTau_mutind; intros; cbn.
  - reflexivity.
  - reflexivity.
  - change (ty_fun (Ty_rename (Ty_subst t s) f)
      (Ty_rename (Ty_subst t0 (PathSubst_lift s)) (FinFun.ext f)) =
      ty_fun (Ty_subst t (PathSubst_compRename s f))
        (Ty_subst t0 (PathSubst_lift (PathSubst_compRename s f)))).
    rewrite H, H0, PathSubst_compRename_lift. reflexivity.
  - change (ty_pair (Ty_rename (Ty_subst t s) f) n0
      (Tau_rename (Tau_subst t0 (PathSubst_lift s)) (FinFun.ext f)) =
      ty_pair (Ty_subst t (PathSubst_compRename s f)) n0
        (Tau_subst t0 (PathSubst_lift (PathSubst_compRename s f)))).
    rewrite H, H0, PathSubst_compRename_lift. reflexivity.
  - now rewrite Path_subst_rename.
  - now rewrite Path_subst_rename.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Theorem Ty_subst_rename {n m l : nat} (T : Ty n)
    (s : PathSubst n m) (f : FinFun.t m l) :
    Ty_rename (Ty_subst T s) f = Ty_subst T (PathSubst_compRename s f).
Proof. exact (proj1 TyTau_subst_rename n T m l s f). Qed.

Theorem Tau_subst_rename {n m l : nat} {k : Kind} (d : Tau n k)
    (s : PathSubst n m) (f : FinFun.t m l) :
    Tau_rename (Tau_subst d s) f = Tau_subst d (PathSubst_compRename s f).
Proof. exact (proj2 TyTau_subst_rename n k d m l s f). Qed.

Lemma TyTau_rename_subst :
    (forall (n : nat) (T : Ty n) (m l : nat)
      (g : FinFun.t n m) (s : PathSubst m l),
      Ty_subst (Ty_rename T g) s = Ty_subst T (FinFun_compSubst g s)) /\
    (forall (n : nat) (k : Kind) (d : Tau n k) (m l : nat)
      (g : FinFun.t n m) (s : PathSubst m l),
      Tau_subst (Tau_rename d g) s =
        Tau_subst d (FinFun_compSubst g s)).
Proof.
  apply TyTau_mutind; intros; cbn.
  - reflexivity.
  - reflexivity.
  - change (ty_fun (Ty_subst (Ty_rename t g) s)
      (Ty_subst (Ty_rename t0 (FinFun.ext g)) (PathSubst_lift s)) =
      ty_fun (Ty_subst t (FinFun_compSubst g s))
        (Ty_subst t0 (PathSubst_lift (FinFun_compSubst g s)))).
    rewrite H, H0, PathSubst_compSubst_lift. reflexivity.
  - change (ty_pair (Ty_subst (Ty_rename t g) s) n0
      (Tau_subst (Tau_rename t0 (FinFun.ext g)) (PathSubst_lift s)) =
      ty_pair (Ty_subst t (FinFun_compSubst g s)) n0
        (Tau_subst t0 (PathSubst_lift (FinFun_compSubst g s)))).
    rewrite H, H0, PathSubst_compSubst_lift. reflexivity.
  - now rewrite Path_rename_subst.
  - now rewrite Path_rename_subst.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Theorem Ty_rename_subst {n m l : nat} (T : Ty n)
    (g : FinFun.t n m) (s : PathSubst m l) :
    Ty_subst (Ty_rename T g) s = Ty_subst T (FinFun_compSubst g s).
Proof. exact (proj1 TyTau_rename_subst n T m l g s). Qed.

Theorem Tau_rename_subst {n m l : nat} {k : Kind} (d : Tau n k)
    (g : FinFun.t n m) (s : PathSubst m l) :
    Tau_subst (Tau_rename d g) s = Tau_subst d (FinFun_compSubst g s).
Proof. exact (proj2 TyTau_rename_subst n k d m l g s). Qed.

(** Renamings regarded as substitutions. *)
Theorem FinFun_asSubst_apply {n m : nat} (f : FinFun.t n m)
    (x : Fin.t n) : FinFun_asSubst f x = path_var (f x).
Proof. exact (@Env.lookup_tabulate (Path m) n (fun x => path_var (f x)) x). Qed.

Theorem FinFun_asSubst_id {n : nat} :
    FinFun_asSubst (FinFun.id n) = PathSubst_id n.
Proof.
  apply PathSubst_funext. intro x.
  rewrite FinFun_asSubst_apply, FinFun.id_apply, PathSubst_id_apply.
  reflexivity.
Qed.

Theorem FinFun_asSubst_ext {n m : nat} (f : FinFun.t n m) :
    FinFun_asSubst (FinFun.ext f) = PathSubst_lift (FinFun_asSubst f).
Proof.
  apply PathSubst_funext. intro x.
  refine (@Fin.cases' n x
    (fun x => FinFun_asSubst (FinFun.ext f) x =
      PathSubst_lift (FinFun_asSubst f) x) _ _).
  - rewrite FinFun_asSubst_apply, FinFun.ext_zero, PathSubst_lift_zero.
    reflexivity.
  - intros y.
    rewrite FinFun_asSubst_apply, FinFun.ext_succ, PathSubst_lift_succ,
      FinFun_asSubst_apply. unfold Path_weaken. cbn.
    now rewrite FinFun.weaken_apply.
Qed.

Theorem FinFun_openAt_asSubst {n : nat} (x : Fin.t n) :
    FinFun_asSubst (FinFun.openAt x) = PathSubst_openAt (path_var x).
Proof.
  apply PathSubst_funext. intro y.
  refine (@Fin.cases' n y
    (fun y => FinFun_asSubst (FinFun.openAt x) y =
      PathSubst_openAt (path_var x) y) _ _).
  - rewrite FinFun_asSubst_apply, FinFun.openAt_zero,
      PathSubst_openAt_zero. reflexivity.
  - intros z. rewrite FinFun_asSubst_apply, FinFun.openAt_succ,
      PathSubst_openAt_succ. reflexivity.
Qed.

Theorem Path_subst_asSubst {n m : nat} (p : Path n) (f : FinFun.t n m) :
    Path_subst p (FinFun_asSubst f) = Path_rename p f.
Proof.
  induction p; cbn; f_equal; auto using FinFun_asSubst_apply.
Qed.

Lemma TyTau_subst_asSubst :
    (forall (n : nat) (T : Ty n) (m : nat) (f : FinFun.t n m),
      Ty_subst T (FinFun_asSubst f) = Ty_rename T f) /\
    (forall (n : nat) (k : Kind) (d : Tau n k)
      (m : nat) (f : FinFun.t n m),
      Tau_subst d (FinFun_asSubst f) = Tau_rename d f).
Proof.
  apply TyTau_mutind; intros; cbn.
  - reflexivity.
  - reflexivity.
  - change (ty_fun (Ty_subst t (FinFun_asSubst f))
      (Ty_subst t0 (PathSubst_lift (FinFun_asSubst f))) =
      ty_fun (Ty_rename t f) (Ty_rename t0 (FinFun.ext f))).
    rewrite H, <- FinFun_asSubst_ext, H0. reflexivity.
  - change (ty_pair (Ty_subst t (FinFun_asSubst f)) n0
      (Tau_subst t0 (PathSubst_lift (FinFun_asSubst f))) =
      ty_pair (Ty_rename t f) n0 (Tau_rename t0 (FinFun.ext f))).
    rewrite H, <- FinFun_asSubst_ext, H0. reflexivity.
  - now rewrite Path_subst_asSubst.
  - now rewrite Path_subst_asSubst.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Theorem Ty_subst_asSubst {n m : nat} (T : Ty n) (f : FinFun.t n m) :
    Ty_subst T (FinFun_asSubst f) = Ty_rename T f.
Proof. exact (proj1 TyTau_subst_asSubst n T m f). Qed.

Theorem Tau_subst_asSubst {n m : nat} {k : Kind}
    (d : Tau n k) (f : FinFun.t n m) :
    Tau_subst d (FinFun_asSubst f) = Tau_rename d f.
Proof. exact (proj2 TyTau_subst_asSubst n k d m f). Qed.

Lemma PathSubst_weaken_lift {n m : nat} (s : PathSubst n m) :
    FinFun_compSubst (FinFun.weaken n) (PathSubst_lift s) =
      PathSubst_compRename s (FinFun.weaken m).
Proof.
  apply PathSubst_funext. intro x.
  rewrite FinFun_compSubst_apply, FinFun.weaken_apply,
    PathSubst_lift_succ, PathSubst_compRename_apply.
  reflexivity.
Qed.

Theorem Path_weaken_subst_lift {n m : nat} (p : Path n)
    (s : PathSubst n m) :
    Path_subst (Path_weaken p) (PathSubst_lift s) =
      Path_weaken (Path_subst p s).
Proof.
  unfold Path_weaken. rewrite Path_rename_subst, Path_subst_rename,
    PathSubst_weaken_lift. reflexivity.
Qed.

Theorem Ty_weaken_subst_lift {n m : nat} (T : Ty n)
    (s : PathSubst n m) :
    Ty_subst (Ty_weaken T) (PathSubst_lift s) =
      Ty_weaken (Ty_subst T s).
Proof.
  unfold Ty_weaken. rewrite Ty_rename_subst, Ty_subst_rename,
    PathSubst_weaken_lift. reflexivity.
Qed.

Theorem Tau_weaken_subst_lift {n m : nat} {k : Kind} (d : Tau n k)
    (s : PathSubst n m) :
    Tau_subst (Tau_weaken d) (PathSubst_lift s) =
      Tau_weaken (Tau_subst d s).
Proof.
  unfold Tau_weaken. rewrite Tau_rename_subst, Tau_subst_rename,
    PathSubst_weaken_lift. reflexivity.
Qed.

Theorem PathSubst_comp_lift {n m l : nat}
    (s : PathSubst n m) (t : PathSubst m l) :
    PathSubst_lift (PathSubst_comp s t) =
      PathSubst_comp (PathSubst_lift s) (PathSubst_lift t).
Proof.
  apply PathSubst_funext. intro x.
  refine (@Fin.cases' n x
    (fun x => PathSubst_lift (PathSubst_comp s t) x =
      PathSubst_comp (PathSubst_lift s) (PathSubst_lift t) x) _ _).
  - rewrite PathSubst_lift_zero, PathSubst_comp_apply,
      PathSubst_lift_zero. reflexivity.
  - intros y. rewrite PathSubst_lift_succ, PathSubst_comp_apply.
    rewrite PathSubst_comp_apply, PathSubst_lift_succ.
    symmetry. apply Path_weaken_subst_lift.
Qed.

Theorem Path_subst_comp {n m l : nat} (p : Path n)
    (s : PathSubst n m) (t : PathSubst m l) :
    Path_subst (Path_subst p s) t =
      Path_subst p (PathSubst_comp s t).
Proof.
  induction p; cbn; f_equal; auto using PathSubst_comp_apply.
Qed.

Lemma TyTau_subst_comp :
    (forall (n : nat) (T : Ty n) (m l : nat)
      (s : PathSubst n m) (t : PathSubst m l),
      Ty_subst (Ty_subst T s) t = Ty_subst T (PathSubst_comp s t)) /\
    (forall (n : nat) (k : Kind) (d : Tau n k) (m l : nat)
      (s : PathSubst n m) (t : PathSubst m l),
      Tau_subst (Tau_subst d s) t = Tau_subst d (PathSubst_comp s t)).
Proof.
  apply TyTau_mutind; intros; cbn.
  - reflexivity.
  - reflexivity.
  - change (ty_fun (Ty_subst (Ty_subst t s) t1)
      (Ty_subst (Ty_subst t0 (PathSubst_lift s)) (PathSubst_lift t1)) =
      ty_fun (Ty_subst t (PathSubst_comp s t1))
        (Ty_subst t0 (PathSubst_lift (PathSubst_comp s t1)))).
    rewrite H, H0, PathSubst_comp_lift. reflexivity.
  - change (ty_pair (Ty_subst (Ty_subst t s) t1) n0
      (Tau_subst (Tau_subst t0 (PathSubst_lift s)) (PathSubst_lift t1)) =
      ty_pair (Ty_subst t (PathSubst_comp s t1)) n0
        (Tau_subst t0 (PathSubst_lift (PathSubst_comp s t1)))).
    rewrite H, H0, PathSubst_comp_lift. reflexivity.
  - now rewrite Path_subst_comp.
  - now rewrite Path_subst_comp.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Theorem Ty_subst_comp {n m l : nat} (T : Ty n)
    (s : PathSubst n m) (t : PathSubst m l) :
    Ty_subst (Ty_subst T s) t = Ty_subst T (PathSubst_comp s t).
Proof. exact (proj1 TyTau_subst_comp n T m l s t). Qed.

Theorem Tau_subst_comp {n m l : nat} {k : Kind} (d : Tau n k)
    (s : PathSubst n m) (t : PathSubst m l) :
    Tau_subst (Tau_subst d s) t = Tau_subst d (PathSubst_comp s t).
Proof. exact (proj2 TyTau_subst_comp n k d m l s t). Qed.

Theorem PathSubst_id_comp {n m : nat} (s : PathSubst n m) :
    PathSubst_comp (PathSubst_id n) s = s.
Proof.
  apply PathSubst_funext. intro x.
  rewrite PathSubst_comp_apply, PathSubst_id_apply. reflexivity.
Qed.

Theorem PathSubst_comp_id {n m : nat} (s : PathSubst n m) :
    PathSubst_comp s (PathSubst_id m) = s.
Proof.
  apply PathSubst_funext. intro x.
  rewrite PathSubst_comp_apply, Path_subst_id. reflexivity.
Qed.

Theorem PathSubst_comp_assoc {n m l r : nat}
    (s : PathSubst n m) (t : PathSubst m l) (u : PathSubst l r) :
    PathSubst_comp (PathSubst_comp s t) u =
      PathSubst_comp s (PathSubst_comp t u).
Proof.
  apply PathSubst_funext. intro x. rewrite !PathSubst_comp_apply.
  apply Path_subst_comp.
Qed.

Theorem PathSubst_comp_asSubst {n m l : nat}
    (s : PathSubst n m) (f : FinFun.t m l) :
    PathSubst_comp s (FinFun_asSubst f) = PathSubst_compRename s f.
Proof.
  apply PathSubst_funext. intro x.
  rewrite PathSubst_comp_apply, PathSubst_compRename_apply,
    Path_subst_asSubst. reflexivity.
Qed.

Theorem FinFun_asSubst_comp {n m l : nat}
    (f : FinFun.t n m) (g : FinFun.t m l) :
    FinFun_asSubst (FinFun.comp f g) =
      PathSubst_comp (FinFun_asSubst f) (FinFun_asSubst g).
Proof.
  apply PathSubst_funext. intro x.
  rewrite FinFun_asSubst_apply, FinFun.comp_apply,
    PathSubst_comp_apply, FinFun_asSubst_apply. cbn.
  symmetry. apply FinFun_asSubst_apply.
Qed.

Theorem FinFun_asSubst_compSubst {n m l : nat}
    (f : FinFun.t n m) (s : PathSubst m l) :
    PathSubst_comp (FinFun_asSubst f) s = FinFun_compSubst f s.
Proof.
  apply PathSubst_funext. intro x.
  rewrite PathSubst_comp_apply, FinFun_asSubst_apply,
    FinFun_compSubst_apply. reflexivity.
Qed.

(** Opening cancels weakening; stated early for substitution composition. *)
Theorem Path_weaken_open {n : nat} (p q : Path n) :
    Path_open (Path_weaken p) q = p.
Proof.
  unfold Path_open, Path_weaken. rewrite Path_rename_subst,
    PathSubst_openAt_weaken, Path_subst_id. reflexivity.
Qed.

Theorem PathSubst_openAt_comp {n m : nat} (p : Path n)
    (s : PathSubst n m) :
    PathSubst_comp (PathSubst_openAt p) s =
      PathSubst_comp (PathSubst_lift s)
        (PathSubst_openAt (Path_subst p s)).
Proof.
  apply PathSubst_funext. intro x.
  refine (@Fin.cases' n x
    (fun x => PathSubst_comp (PathSubst_openAt p) s x =
      PathSubst_comp (PathSubst_lift s)
        (PathSubst_openAt (Path_subst p s)) x) _ _).
  - rewrite !PathSubst_comp_apply, PathSubst_openAt_zero,
      PathSubst_lift_zero. reflexivity.
  - intros y. rewrite !PathSubst_comp_apply, PathSubst_openAt_succ,
      PathSubst_lift_succ. change (s y =
        Path_open (Path_weaken (s y)) (Path_subst p s)).
    symmetry. apply Path_weaken_open.
Qed.

Theorem Path_open_subst {n m : nat} (p : Path (S n)) (q : Path n)
    (s : PathSubst n m) :
    Path_subst (Path_open p q) s =
      Path_open (Path_subst p (PathSubst_lift s)) (Path_subst q s).
Proof.
  unfold Path_open. rewrite !Path_subst_comp, PathSubst_openAt_comp.
  reflexivity.
Qed.

Theorem Ty_open_subst {n m : nat} (T : Ty (S n)) (p : Path n)
    (s : PathSubst n m) :
    Ty_subst (Ty_open T p) s =
      Ty_open (Ty_subst T (PathSubst_lift s)) (Path_subst p s).
Proof.
  unfold Ty_open. rewrite !Ty_subst_comp, PathSubst_openAt_comp.
  reflexivity.
Qed.

Theorem Tau_open_subst {n m : nat} {k : Kind}
    (d : Tau (S n) k) (p : Path n) (s : PathSubst n m) :
    Tau_subst (Tau_open d p) s =
      Tau_open (Tau_subst d (PathSubst_lift s)) (Path_subst p s).
Proof.
  unfold Tau_open. rewrite !Tau_subst_comp, PathSubst_openAt_comp.
  reflexivity.
Qed.

Theorem Path_rename_openAt_eq_open_var {n : nat}
    (p : Path (S n)) (x : Fin.t n) :
    Path_rename p (FinFun.openAt x) = Path_open p (path_var x).
Proof.
  unfold Path_open. rewrite <- Path_subst_asSubst,
    FinFun_openAt_asSubst. reflexivity.
Qed.

Theorem Ty_rename_openAt_eq_open_var {n : nat}
    (T : Ty (S n)) (x : Fin.t n) :
    Ty_rename T (FinFun.openAt x) = Ty_open T (path_var x).
Proof.
  unfold Ty_open. rewrite <- Ty_subst_asSubst,
    FinFun_openAt_asSubst. reflexivity.
Qed.

Theorem Tau_rename_openAt_eq_open_var {n : nat} {k : Kind}
    (d : Tau (S n) k) (x : Fin.t n) :
    Tau_rename d (FinFun.openAt x) = Tau_open d (path_var x).
Proof.
  unfold Tau_open. rewrite <- Tau_subst_asSubst,
    FinFun_openAt_asSubst. reflexivity.
Qed.

Theorem Path_open_rename {n m : nat} (p : Path (S n))
    (q : Path n) (f : FinFun.t n m) :
    Path_rename (Path_open p q) f =
      Path_open (Path_rename p (FinFun.ext f)) (Path_rename q f).
Proof.
  unfold Path_open. rewrite Path_subst_rename, Path_rename_subst,
    PathSubst_openAt_rename. reflexivity.
Qed.

Theorem Ty_open_rename {n m : nat} (T : Ty (S n))
    (p : Path n) (f : FinFun.t n m) :
    Ty_rename (Ty_open T p) f =
      Ty_open (Ty_rename T (FinFun.ext f)) (Path_rename p f).
Proof.
  unfold Ty_open. rewrite Ty_subst_rename, Ty_rename_subst,
    PathSubst_openAt_rename. reflexivity.
Qed.

Theorem Tau_open_rename {n m : nat} {k : Kind} (d : Tau (S n) k)
    (p : Path n) (f : FinFun.t n m) :
    Tau_rename (Tau_open d p) f =
      Tau_open (Tau_rename d (FinFun.ext f)) (Path_rename p f).
Proof.
  unfold Tau_open. rewrite Tau_subst_rename, Tau_rename_subst,
    PathSubst_openAt_rename. reflexivity.
Qed.

Theorem Ty_weaken_open {n : nat} (T : Ty n) (p : Path n) :
    Ty_open (Ty_weaken T) p = T.
Proof.
  unfold Ty_open, Ty_weaken. rewrite Ty_rename_subst,
    PathSubst_openAt_weaken, Ty_subst_id. reflexivity.
Qed.

Theorem Tau_weaken_open {n : nat} {k : Kind}
    (d : Tau n k) (p : Path n) : Tau_open (Tau_weaken d) p = d.
Proof.
  unfold Tau_open, Tau_weaken. rewrite Tau_rename_subst,
    PathSubst_openAt_weaken, Tau_subst_id. reflexivity.
Qed.

Theorem Tm_open_rename {n m : nat} (t : Tm (S n))
    (x : Fin.t n) (f : FinFun.t n m) :
    Tm_rename (Tm_open t x) f =
      Tm_open (Tm_rename t (FinFun.ext f)) (f x).
Proof.
  unfold Tm_open. rewrite !Tm_rename_rename, FinFun.openAt_comp.
  reflexivity.
Qed.

Theorem Def_open_rename {n m : nat} {k : Kind} (d : Def (S n) k)
    (x : Fin.t n) (f : FinFun.t n m) :
    Def_rename (Def_open d x) f =
      Def_open (Def_rename d (FinFun.ext f)) (f x).
Proof.
  unfold Def_open. rewrite !Def_rename_rename, FinFun.openAt_comp.
  reflexivity.
Qed.

Theorem Tm_weaken_open {n : nat} (t : Tm n) (x : Fin.t n) :
    Tm_open (Tm_weaken t) x = t.
Proof.
  unfold Tm_open, Tm_weaken. rewrite Tm_rename_rename,
    FinFun.openAt_weaken, Tm_rename_id. reflexivity.
Qed.

Theorem Def_weaken_open {n : nat} {k : Kind}
    (d : Def n k) (x : Fin.t n) : Def_open (Def_weaken d) x = d.
Proof.
  unfold Def_open, Def_weaken. rewrite Def_rename_rename,
    FinFun.openAt_weaken, Def_rename_id. reflexivity.
Qed.

Theorem Tm_IsValue_rename {n m : nat} {t : Tm n}
    (H : Tm_IsValue t) (f : FinFun.t n m) :
    Tm_IsValue (Tm_rename t f).
Proof. destruct H; cbn; constructor. Qed.

Theorem Tm_IsValue_weaken {n : nat} {t : Tm n}
    (H : Tm_IsValue t) : Tm_IsValue (Tm_weaken t).
Proof. unfold Tm_weaken. now apply Tm_IsValue_rename. Qed.
