From Stdlib Require Import Lists.List.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store Renaming Cont State PathReduction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** One transition of the intrinsically indexed CK machine. *)
Inductive State_Step : forall {n m : nat}, State n -> State m -> Prop :=
| state_step_app {n : nat} (s : Store n) (K : Tm_Cont n)
    (p q : Path n) (x y : Fin.t n) (T : Ty n) (t : Tm (S n)) :
    Path_reduce p s x ->
    Path_reduce q s y ->
    Store_Binds s x (tm_abs T t) ->
    State_Step
      (mk_state s K (tm_app p q))
      (mk_state s K (Tm_open t y))
| state_step_path {n : nat} (s : Store n) (K : Tm_Cont n)
    (p : Path n) (x : Fin.t n) :
    Path_reduce p s x ->
    ~ Path_IsVar p ->
    State_Step
      (mk_state s K (tm_path p))
      (mk_state s K (tm_path (path_var x)))
| state_step_let_push {n : nat} (s : Store n) (K : Tm_Cont n)
    (u : Tm n) (t : Tm (S n)) :
    State_Step
      (mk_state s K (tm_let u t))
      (mk_state s (cons (tm_frame_let t) K) u)
| state_step_rename {n : nat} (s : Store n) (K : Tm_Cont n)
    (t : Tm (S n)) (x : Fin.t n) :
    State_Step
      (mk_state s (cons (tm_frame_let t) K) (tm_path (path_var x)))
      (mk_state s K (Tm_open t x))
| state_step_lift {n : nat} (s : Store n) (K : Tm_Cont n)
    (t : Tm (S n)) (v : Tm n) (Hv : Tm_IsValue v) :
    State_Step
      (mk_state s (cons (tm_frame_let t) K) v)
      (mk_state (store_val s v Hv) (Tm_Cont_weaken K) t)
| state_step_ascribe {n : nat} (s : Store n) (K : Tm_Cont n)
    (t : Tm n) (T : Ty n) :
    State_Step
      (mk_state s K (tm_typed t T))
      (mk_state s K t).

Arguments state_step_app {n} s K p q x y T t _ _ _.
Arguments state_step_path {n} s K p x _ _.
Arguments state_step_let_push {n} s K u t.
Arguments state_step_rename {n} s K t x.
Arguments state_step_lift {n} s K t v Hv.
Arguments state_step_ascribe {n} s K t T.

Print Assumptions State_Step.
