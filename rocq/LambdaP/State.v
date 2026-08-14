From Stdlib Require Import Lists.List.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store Renaming Cont.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** A machine configuration at an exact store and scope size. *)
Record State (n : nat) : Type := mk_state {
  state_store : Store n;
  state_cont : Tm_Cont n;
  state_term : Tm n
}.

Arguments mk_state {n} _ _ _.
Arguments state_store {n} _.
Arguments state_cont {n} _.
Arguments state_term {n} _.

(** Typing of a complete machine configuration. *)
Inductive State_Ty : forall {n : nat},
    Ctx n -> State n -> Ty n -> Prop :=
| state_ty_ok {n : nat} (G : Ctx n) (s : Store n)
    (K : Tm_Cont n) (t : Tm n) (S0 T : Ty n) :
    Store_Ty G s ->
    Tm_Cont_Ty G S0 K T ->
    Tm_Ty G t S0 ->
    State_Ty G (mk_state s K t) T.

Arguments state_ty_ok {n} G s K t S0 T _ _ _.

(** Final configurations have an empty continuation and contain either a
    valid store location or a value. *)
Inductive State_IsFinal : forall {n : nat}, State n -> Prop :=
| state_final_var {n : nat} (s : Store n) (x : Fin.t n) (v : Tm n) :
    Store_Binds s x v ->
    State_IsFinal (mk_state s nil (tm_path (path_var x)))
| state_final_val {n : nat} (s : Store n) (v : Tm n) :
    Tm_IsValue v ->
    State_IsFinal (mk_state s nil v).

Arguments state_final_var {n} s x v _.
Arguments state_final_val {n} s v _.

Print Assumptions State_Ty.
Print Assumptions State_IsFinal.
