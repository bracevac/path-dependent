From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PathDependent.LambdaPFC Require Import FinFun Syntax Context Typing.

Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Immutable, intrinsically scoped stores. *)
Inductive Store : nat -> Type :=
| StoreEmpty : Store 0
| StoreVal {n : nat} (sigma : Store n) (v : Tm n) :
    Tm_IsValue v -> Store (S n).

Arguments StoreVal {n} _ _ _.

Inductive StoreBinds : forall {n : nat}, Store n -> Fin n -> Tm n -> Prop :=
| StoreBinds_here {n : nat} {sigma : Store n} {v : Tm n}
    (value : Tm_IsValue v) :
    StoreBinds (StoreVal sigma v value) FZ (tm_weaken v)
| StoreBinds_there {n : nat} {sigma : Store n} {x : Fin n}
    {v u : Tm n} {u_value : Tm_IsValue u} :
    StoreBinds sigma x v ->
    StoreBinds (StoreVal sigma u u_value) (FS x) (tm_weaken v).

Equations store_lookup {n : nat} (sigma : Store n) (x : Fin n) : Tm n :=
store_lookup (StoreVal sigma v value) FZ := tm_weaken v;
store_lookup (StoreVal sigma v value) (FS x) := tm_weaken (store_lookup sigma x).

Lemma store_binds_lookup_eq {n : nat} {sigma : Store n}
    {x : Fin n} {v : Tm n} (binding : StoreBinds sigma x v) :
    store_lookup sigma x = v.
Proof.
  induction binding.
  - simp store_lookup. reflexivity.
  - simp store_lookup. apply f_equal. exact IHbinding.
Qed.

Lemma store_binds_unique {n : nat} {sigma : Store n} {x : Fin n}
    {v1 v2 : Tm n} (first : StoreBinds sigma x v1)
    (second : StoreBinds sigma x v2) : v1 = v2.
Proof.
  exact (eq_trans (eq_sym (store_binds_lookup_eq first))
    (store_binds_lookup_eq second)).
Qed.

(** Runtime referents are locations or stored type definitions. *)
Inductive PathReferent (n : nat) : Type :=
| RefLoc : Fin n -> PathReferent n
| RefType : Ty n -> PathReferent n.

Arguments RefLoc {n} _.
Arguments RefType {n} _.

Definition referent_weaken {n : nat} (r : PathReferent n) :
    PathReferent (S n) :=
  match r with
  | RefLoc x => RefLoc (FS x)
  | RefType T => RefType (ty_weaken T)
  end.

Definition def_referent {n : nat} {k : Kind} (d : Def n k) : PathReferent n :=
  match d with
  | DefVal x => RefLoc x
  | DefType T => RefType T
  end.

Lemma def_referent_weaken {n : nat} {k : Kind} (d : Def n k) :
    def_referent (def_rename d (weaken n)) = referent_weaken (def_referent d).
Proof.
  destruct d as [n x|n T].
  - rewrite def_rename_equation_1. cbn [def_referent referent_weaken].
    f_equal. apply weaken_apply.
  - rewrite def_rename_equation_2. cbn [def_referent referent_weaken].
    reflexivity.
Qed.

(** Generalized path resolution. *)
Inductive PathResolve : forall {n : nat},
    Path n -> Store n -> PathReferent n -> Prop :=
| Resolve_var {n : nat} {sigma : Store n} (x : Fin n) :
    PathResolve (PVar x) sigma (RefLoc x)
| Resolve_fst {n : nat} {sigma : Store n} {p : Path n}
    {x y : Fin n} {a : Name} {k : Kind} {d : Def n k} :
    PathResolve p sigma (RefLoc x) ->
    StoreBinds sigma x (TmPair y a d) ->
    PathResolve (PFst p) sigma (RefLoc y)
| Resolve_sel {n : nat} {sigma : Store n} {p : Path n}
    {x y : Fin n} {a : Name} {k : Kind} {d : Def n k} :
    PathResolve p sigma (RefLoc x) ->
    StoreBinds sigma x (TmPair y a d) ->
    PathResolve (PSel p a) sigma (def_referent d)
| Resolve_sel_miss {n : nat} {sigma : Store n} {p : Path n}
    {x y : Fin n} {a b : Name} {k : Kind} {d : Def n k}
    {referent : PathReferent n} :
    PathResolve p sigma (RefLoc x) ->
    StoreBinds sigma x (TmPair y b d) ->
    a <> b ->
    PathResolve (PSel (PVar y) a) sigma referent ->
    PathResolve (PSel p a) sigma referent.

(** Projections used to compare dependent pair bindings without assuming
    uniqueness of identity proofs. *)
Definition tm_pair_first {n : nat} (t : Tm n) : option (Fin n) :=
  match t with
  | TmPair y _ _ => Some y
  | _ => None
  end.

Definition tm_pair_label {n : nat} (t : Tm n) : option Name :=
  match t with
  | TmPair _ a _ => Some a
  | _ => None
  end.

Definition tm_pair_referent {n : nat} (t : Tm n) : option (PathReferent n) :=
  match t with
  | TmPair _ _ d => Some (def_referent d)
  | _ => None
  end.

Lemma some_injective {A : Type} (x y : A) : Some x = Some y -> x = y.
Proof. intro equality. injection equality. trivial. Qed.

(** Generalized path resolution is deterministic. *)
Lemma path_resolve_deterministic {n : nat} {sigma : Store n}
    {p : Path n} {r1 r2 : PathReferent n}
    (first : PathResolve p sigma r1) (second : PathResolve p sigma r2) :
    r1 = r2.
Proof.
  revert r2 second.
  induction first; intros r2 second; dependent elimination second.
  - reflexivity.
  - pose proof (IHfirst _ p1) as Hloc. inversion Hloc; subst x1.
    pose proof (store_binds_unique H s) as Heq.
    pose proof (f_equal tm_pair_first Heq) as Hfirst.
    cbn [tm_pair_first] in Hfirst. inversion Hfirst. reflexivity.
  - pose proof (IHfirst _ p3) as Hloc. inversion Hloc; subst x2.
    pose proof (store_binds_unique H s0) as Heq.
    pose proof (f_equal tm_pair_referent Heq) as Hreferent.
    cbn [tm_pair_referent] in Hreferent.
    inversion Hreferent. reflexivity.
  - pose proof (IHfirst _ p5) as Hloc. inversion Hloc; subst x3.
    pose proof (store_binds_unique H s1) as Heq.
    pose proof (f_equal tm_pair_label Heq) as Hlabel.
    cbn [tm_pair_label] in Hlabel.
    exfalso. exact (n4 (some_injective Hlabel)).
  - pose proof (IHfirst1 _ p3) as Hloc. inversion Hloc; subst x2.
    pose proof (store_binds_unique H s0) as Heq.
    pose proof (f_equal tm_pair_label Heq) as Hlabel.
    cbn [tm_pair_label] in Hlabel.
    exfalso. apply H0. apply eq_sym. exact (some_injective Hlabel).
  - pose proof (IHfirst1 _ p5) as Hloc. inversion Hloc; subst x3.
    pose proof (store_binds_unique H s1) as Heq.
    pose proof (f_equal tm_pair_first Heq) as Hfirst.
    cbn [tm_pair_first] in Hfirst.
    pose proof (some_injective Hfirst) as Hy. subst y2.
    exact (IHfirst2 _ p6).
Qed.

(** Selection depends only on the location referent of its prefix. *)
Lemma path_resolve_sel_congr {n : nat} {sigma : Store n}
    {p q : Path n} {a : Name} {referent : PathReferent n} {x : Fin n}
    (selected : PathResolve (PSel p a) sigma referent)
    (left : PathResolve p sigma (RefLoc x))
    (right : PathResolve q sigma (RefLoc x)) :
    PathResolve (PSel q a) sigma referent.
Proof.
  dependent elimination selected.
  - pose proof (path_resolve_deterministic left p3) as Hloc.
    inversion Hloc; subst x2. exact (Resolve_sel right s0).
  - pose proof (path_resolve_deterministic left p5) as Hloc.
    inversion Hloc; subst x3.
    exact (Resolve_sel_miss right s1 n4 p6).
Qed.

(** Resolution survives allocation. *)
Lemma path_resolve_weaken {n : nat} {p : Path n} {sigma : Store n}
    {referent : PathReferent n} (resolution : PathResolve p sigma referent)
    (v : Tm n) (value : Tm_IsValue v) :
    PathResolve (path_weaken p) (StoreVal sigma v value)
      (referent_weaken referent).
Proof.
  induction resolution.
  - unfold path_weaken. simp path_rename. rewrite weaken_apply.
    exact (Resolve_var (FS x)).
  - unfold path_weaken in *. simp path_rename in *.
    cbn [referent_weaken]. rewrite <- weaken_apply.
    exact (Resolve_fst (IHresolution v value) (StoreBinds_there H)).
  - unfold path_weaken in *. simp path_rename in *.
    rewrite <- def_referent_weaken.
    exact (Resolve_sel (IHresolution v value) (StoreBinds_there H)).
  - unfold path_weaken in *. simp path_rename in *.
    exact (Resolve_sel_miss (IHresolution1 v value)
      (StoreBinds_there H) H0 (IHresolution2 v value)).
Qed.

(** CK continuations and machine states. *)
Definition TmCont (n : nat) : Type := list (Tm (S n)).

Definition cont_rename {n m : nat} (cont : TmCont n) (f : FinFun n m) :
    TmCont m := map (fun body => tm_rename body (ext f)) cont.

Definition cont_weaken {n : nat} (cont : TmCont n) : TmCont (S n) :=
  cont_rename cont (weaken n).

Record State (n : nat) : Type := StateMk {
  state_store : Store n;
  state_cont : TmCont n;
  state_term : Tm n
}.

Arguments StateMk {n} _ _ _.

Inductive StateIsFinal : forall {n : nat}, State n -> Prop :=
| Final_location {n : nat} (sigma : Store n) (x : Fin n) :
    StateIsFinal (StateMk sigma [] (TmPath (PVar x)))
| Final_value {n : nat} (sigma : Store n) (v : Tm n) :
    Tm_IsValue v -> StateIsFinal (StateMk sigma [] v).

Definition state_initial (t : Tm 0) : State 0 := StateMk StoreEmpty [] t.

Inductive StateStep : forall {n m : nat}, State n -> State m -> Prop :=
| Step_app {n : nat} {sigma : Store n} {cont : TmCont n}
    {p q : Path n} {f y : Fin n} {A : Ty n} {body : Tm (S n)} :
    PathResolve p sigma (RefLoc f) ->
    PathResolve q sigma (RefLoc y) ->
    StoreBinds sigma f (TmAbs A body) ->
    StateStep (StateMk sigma cont (TmApp p q))
      (StateMk sigma cont (tm_open body y))
| Step_path {n : nat} {sigma : Store n} {cont : TmCont n}
    {p : Path n} {x : Fin n} :
    PathResolve p sigma (RefLoc x) ->
    ~ Path_IsVar p ->
    StateStep (StateMk sigma cont (TmPath p))
      (StateMk sigma cont (TmPath (PVar x)))
| Step_let_push {n : nat} {sigma : Store n} {cont : TmCont n}
    {bound : Tm n} {body : Tm (S n)} :
    StateStep (StateMk sigma cont (TmLet bound body))
      (StateMk sigma (body :: cont) bound)
| Step_return {n : nat} {sigma : Store n} {cont : TmCont n}
    {body : Tm (S n)} {x : Fin n} :
    StateStep (StateMk sigma (body :: cont) (TmPath (PVar x)))
      (StateMk sigma cont (tm_open body x))
| Step_allocate {n : nat} {sigma : Store n} {cont : TmCont n}
    {body : Tm (S n)} {v : Tm n} (value : Tm_IsValue v) :
    StateStep (StateMk sigma (body :: cont) v)
      (StateMk (StoreVal sigma v value) (cont_weaken cont) body).

Inductive StateSteps : forall {n m : nat}, State n -> State m -> Prop :=
| Steps_refl {n : nat} (source : State n) : StateSteps source source
| Steps_tail {n l m : nat} {source : State n} {middle : State l}
    {target : State m} :
    StateStep source middle -> StateSteps middle target ->
    StateSteps source target.

Inductive StateProgress {n : nat} (state : State n) : Prop :=
| Progress_final : StateIsFinal state -> StateProgress state
| Progress_step {m : nat} {target : State m} :
    StateStep state target -> StateProgress state.

Lemma state_progress_path_var {n : nat} (sigma : Store n)
    (cont : TmCont n) (x : Fin n) :
    StateProgress (StateMk sigma cont (TmPath (PVar x))).
Proof.
  destruct cont as [|body cont].
  - apply Progress_final. apply Final_location.
  - eapply Progress_step. apply Step_return.
Qed.

Lemma state_progress_value {n : nat} (sigma : Store n)
    (cont : TmCont n) (v : Tm n) (value : Tm_IsValue v) :
    StateProgress (StateMk sigma cont v).
Proof.
  destruct cont as [|body cont].
  - apply Progress_final. apply Final_value. exact value.
  - eapply Progress_step. exact (Step_allocate value).
Qed.

Print Assumptions path_resolve_deterministic.
Print Assumptions state_progress_value.
