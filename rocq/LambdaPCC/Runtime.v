From Equations Require Import Equations.
From Stdlib Require Import Lists.List.
From PathDependent.LambdaPCC Require Import FinFun Syntax Context Typing.

Import ListNotations.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Immutable stores indexed by their exact scope. *)
Inductive Store : nat -> Type :=
| StoreEmpty : Store 0
| StoreVal {n : nat} (sigma : Store n) (v : Tm n) :
    Tm_IsValue v -> Store (S n).

Arguments StoreVal {n} _ _ _.

Inductive StoreBinds : forall {n : nat}, Store n -> Fin n -> Tm n -> Prop :=
| SB_here {n : nat} (sigma : Store n) (v : Tm n)
    (is_value : Tm_IsValue v) :
    StoreBinds (StoreVal sigma v is_value) FZ (tm_weaken v)
| SB_there {n : nat} (sigma : Store n) (x : Fin n)
    (v u : Tm n) (is_value : Tm_IsValue u) :
    StoreBinds sigma x v ->
    StoreBinds (StoreVal sigma u is_value) (FS x) (tm_weaken v).

Equations store_lookup {n : nat} (sigma : Store n) (x : Fin n) : Tm n :=
store_lookup StoreEmpty x := fin_elim0 x;
store_lookup (StoreVal sigma v is_value) FZ := tm_weaken v;
store_lookup (StoreVal sigma v is_value) (FS x) :=
  tm_weaken (store_lookup sigma x).

Lemma store_binds_lookup_eq {n : nat} {sigma : Store n}
    {x : Fin n} {v : Tm n} (binding : StoreBinds sigma x v) :
    store_lookup sigma x = v.
Proof.
  induction binding as
    [n sigma v is_value|n sigma x v u is_value binding IH].
  - simp store_lookup. reflexivity.
  - simp store_lookup. now rewrite IH.
Qed.

Lemma store_binds_unique {n : nat} {sigma : Store n} {x : Fin n}
    {v1 v2 : Tm n} (first : StoreBinds sigma x v1)
    (second : StoreBinds sigma x v2) : v1 = v2.
Proof.
  exact (eq_trans (eq_sym (store_binds_lookup_eq first))
    (store_binds_lookup_eq second)).
Qed.

(** Generalized runtime referents. *)
Inductive Referent (n : nat) : Type :=
| RLoc : Fin n -> Referent n
| RType : Shape n -> Referent n
| RCapture : CaptureSet n -> Referent n.

Arguments RLoc {n} _.
Arguments RType {n} _.
Arguments RCapture {n} _.

Equations referent_weaken {n : nat} (referent : Referent n) :
    Referent (S n) :=
referent_weaken (RLoc x) := RLoc (FS x);
referent_weaken (RType shape) := RType (shape_weaken shape);
referent_weaken (RCapture C) := RCapture (capture_weaken C).

Equations def_referent {n : nat} {k : Kind} (d : Def n k) : Referent n :=
def_referent (DefVal x) := RLoc x;
def_referent (DefType shape) := RType shape;
def_referent (DefCapture C) := RCapture C.

Lemma def_referent_weaken {n : nat} {k : Kind} (d : Def n k) :
    def_referent (def_rename d (weaken n)) =
      referent_weaken (def_referent d).
Proof.
  destruct d as [n x|n shape|n C];
    simp def_rename def_referent referent_weaken.
  - now rewrite weaken_apply.
  - reflexivity.
  - reflexivity.
Qed.

(** Follow a path to a location, shape definition, or capture-set
    definition. *)
Inductive PathResolve {n : nat} (sigma : Store n) :
    Path n -> Referent n -> Prop :=
| PR_var (x : Fin n) : PathResolve sigma (PVar x) (RLoc x)
| PR_fst {k : Kind} (p : Path n) (x y : Fin n)
    (a : Name) (d : Def n k) :
    PathResolve sigma p (RLoc x) ->
    StoreBinds sigma x (TmPair y a d) ->
    PathResolve sigma (PFst p) (RLoc y)
| PR_sel {k : Kind} (p : Path n) (x y : Fin n)
    (a : Name) (d : Def n k) :
    PathResolve sigma p (RLoc x) ->
    StoreBinds sigma x (TmPair y a d) ->
    PathResolve sigma (PSel p a) (def_referent d)
| PR_sel_miss {stored_kind : Kind} (p : Path n) (x y : Fin n)
    (a b : Name) (d : Def n stored_kind) (referent : Referent n) :
    PathResolve sigma p (RLoc x) ->
    StoreBinds sigma x (TmPair y b d) ->
    a <> b ->
    PathResolve sigma (PSel (PVar y) a) referent ->
    PathResolve sigma (PSel p a) referent.

Arguments PathResolve {n} sigma _ _.

(** First-order observations of dependent pair terms.  They let the
    determinism proof compare the data carried by existentially kinded
    definitions without assuming uniqueness of identity proofs. *)
Definition tm_pair_first {n : nat} (term : Tm n) : option (Fin n) :=
  match term with
  | TmPair y _ _ => Some y
  | _ => None
  end.

Definition tm_pair_label {n : nat} (term : Tm n) : option Name :=
  match term with
  | TmPair _ a _ => Some a
  | _ => None
  end.

Definition tm_pair_referent {n : nat} (term : Tm n) :
    option (Referent n) :=
  match term with
  | TmPair _ _ d => Some (def_referent d)
  | _ => None
  end.

Lemma some_injective {A : Type} (x y : A) : Some x = Some y -> x = y.
Proof. intro equality. injection equality. trivial. Qed.

Lemma path_resolve_deterministic {n : nat} {sigma : Store n}
    {p : Path n} {r1 r2 : Referent n}
    (first : PathResolve sigma p r1)
    (second : PathResolve sigma p r2) : r1 = r2.
Proof.
  revert r2 second.
  induction first as
    [x
    |k p x y a d prefix IHprefix binding
    |k p x y a d prefix IHprefix binding
    |stored_kind p x y a b d referent prefix IHprefix binding distinct tail
      IHtail];
    intros r2 second; try clear prefix; dependent elimination second.
  - reflexivity.
  - pose proof (IHprefix _ p1) as Hloc. inversion Hloc; subst x1.
    pose proof (store_binds_unique binding s) as Heq.
    pose proof (f_equal tm_pair_first Heq) as Hfirst.
    cbn [tm_pair_first] in Hfirst.
    pose proof (some_injective Hfirst) as Hy. subst y0. reflexivity.
  - pose proof (IHprefix _ p3) as Hloc. inversion Hloc; subst x2.
    pose proof (store_binds_unique binding s0) as Heq.
    pose proof (f_equal tm_pair_referent Heq) as Hreferent.
    cbn [tm_pair_referent] in Hreferent.
    exact (some_injective Hreferent).
  - pose proof (IHprefix _ p5) as Hloc. inversion Hloc; subst x3.
    pose proof (store_binds_unique binding s1) as Heq.
    pose proof (f_equal tm_pair_label Heq) as Hlabel.
    cbn [tm_pair_label] in Hlabel.
    match goal with
    | other_distinct : ?left <> ?right |- _ =>
        exfalso; exact (other_distinct (some_injective Hlabel))
    end.
  - pose proof (IHprefix _ p3) as Hloc. inversion Hloc; subst x2.
    pose proof (store_binds_unique binding s0) as Heq.
    pose proof (f_equal tm_pair_label Heq) as Hlabel.
    cbn [tm_pair_label] in Hlabel.
    exfalso. apply distinct. apply eq_sym.
    exact (some_injective Hlabel).
  - pose proof (IHprefix _ p5) as Hloc. inversion Hloc; subst x3.
    pose proof (store_binds_unique binding s1) as Heq.
    pose proof (f_equal tm_pair_first Heq) as Hfirst.
    cbn [tm_pair_first] in Hfirst.
    pose proof (some_injective Hfirst) as Hy. subst y2.
    exact (IHtail _ p6).
Qed.

Lemma path_resolve_sel_congr {n : nat} {sigma : Store n}
    {p q : Path n} {a : Name} {referent : Referent n} {x : Fin n}
    (selection : PathResolve sigma (PSel p a) referent)
    (left : PathResolve sigma p (RLoc x))
    (right : PathResolve sigma q (RLoc x)) :
    PathResolve sigma (PSel q a) referent.
Proof.
  dependent elimination selection.
  - pose proof (path_resolve_deterministic left p3) as Hloc.
    inversion Hloc; subst x2. eapply PR_sel; eassumption.
  - pose proof (path_resolve_deterministic left p5) as Hloc.
    inversion Hloc; subst x3.
    eapply PR_sel_miss; eassumption.
Qed.

Lemma path_resolve_weaken {n : nat} {sigma : Store n}
    {p : Path n} {referent : Referent n}
    (resolution : PathResolve sigma p referent)
    (v : Tm n) (is_value : Tm_IsValue v) :
    PathResolve (StoreVal sigma v is_value)
      (path_weaken p) (referent_weaken referent).
Proof.
  induction resolution as
    [x
    |k p x y a d prefix IHprefix binding
    |k p x y a d prefix IHprefix binding
    |stored_kind p x y a b d referent prefix IHprefix binding distinct
      tail IHtail].
  - unfold path_weaken. simp path_rename. rewrite weaken_apply.
    simp referent_weaken. apply PR_var.
  - change (PathResolve (StoreVal sigma v is_value)
      (PFst (path_weaken p)) (RLoc (FS y))).
    eapply PR_fst.
    + exact IHprefix.
    + pose proof (@SB_there n sigma x (TmPair y a d)
        v is_value binding) as weakened_binding.
      unfold tm_weaken in weakened_binding.
      cbn [tm_rename] in weakened_binding.
      rewrite weaken_apply in weakened_binding. exact weakened_binding.
  - change (PathResolve (StoreVal sigma v is_value)
      (PSel (path_weaken p) a) (referent_weaken (def_referent d))).
    rewrite <- def_referent_weaken.
    eapply PR_sel.
    + exact IHprefix.
    + pose proof (@SB_there n sigma x (TmPair y a d)
        v is_value binding) as weakened_binding.
      unfold tm_weaken in weakened_binding.
      cbn [tm_rename] in weakened_binding.
      rewrite weaken_apply in weakened_binding. exact weakened_binding.
  - change (PathResolve (StoreVal sigma v is_value)
      (PSel (path_weaken p) a) (referent_weaken referent)).
    eapply PR_sel_miss.
    + exact IHprefix.
    + pose proof (@SB_there n sigma x (TmPair y b d)
        v is_value binding) as weakened_binding.
      unfold tm_weaken in weakened_binding.
      cbn [tm_rename] in weakened_binding.
      rewrite weaken_apply in weakened_binding. exact weakened_binding.
    + exact distinct.
    + unfold path_weaken in IHtail.
      cbn [path_rename] in IHtail.
      rewrite weaken_apply in IHtail.
      exact IHtail.
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

Definition state_initial (term : Tm 0) : State 0 :=
  StateMk StoreEmpty [] term.

(** A single transition of the intrinsically scoped CK machine. *)
Inductive StateStep : forall {n m : nat}, State n -> State m -> Prop :=
| Step_app {n : nat} {sigma : Store n} {cont : TmCont n}
    {p q : Path n} {f y : Fin n} {A : Ty n} {body : Tm (S n)} :
    PathResolve sigma p (RLoc f) ->
    PathResolve sigma q (RLoc y) ->
    StoreBinds sigma f (TmAbs A body) ->
    StateStep (StateMk sigma cont (TmApp p q))
      (StateMk sigma cont (tm_open body y))
| Step_path {n : nat} {sigma : Store n} {cont : TmCont n}
    {p : Path n} {x : Fin n} :
    PathResolve sigma p (RLoc x) ->
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
    {body : Tm (S n)} {v : Tm n} (is_value : Tm_IsValue v) :
    StateStep (StateMk sigma (body :: cont) v)
      (StateMk (StoreVal sigma v is_value) (cont_weaken cont) body).

(** Reflexive-transitive closure across allocation-induced scope changes. *)
Inductive StateSteps : forall {n m : nat}, State n -> State m -> Prop :=
| Steps_refl {n : nat} (source : State n) : StateSteps source source
| Steps_tail {n l m : nat} {source : State n} {middle : State l}
    {target : State m} :
    StateStep source middle ->
    StateSteps middle target ->
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
    (cont : TmCont n) (v : Tm n) (is_value : Tm_IsValue v) :
    StateProgress (StateMk sigma cont v).
Proof.
  destruct cont as [|body cont].
  - apply Progress_final. apply Final_value. exact is_value.
  - eapply Progress_step. exact (Step_allocate is_value).
Qed.

Print Assumptions path_resolve_deterministic.
Print Assumptions path_resolve_sel_congr.
Print Assumptions path_resolve_weaken.
Print Assumptions state_progress_value.
