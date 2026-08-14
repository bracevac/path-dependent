From PathDependent.LambdaP Require Import FinFun Syntax Context Typing.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** A store of values, indexed by its exact scope size. *)
Inductive Store : nat -> Type :=
| store_empty : Store 0
| store_val {n : nat} (s : Store n) (t : Tm n) :
    Tm_IsValue t -> Store (S n).

Arguments store_val {n} s t _.

(** Intrinsically scoped store binding.  Older entries are weakened whenever
    the store grows. *)
Inductive Store_Binds : forall {n : nat},
    Store n -> Fin.t n -> Tm n -> Prop :=
| store_binds_here {n : nat} (s : Store n) (v : Tm n)
    (vv : Tm_IsValue v) :
    Store_Binds (store_val s v vv) Fin.zero (Tm_weaken v)
| store_binds_there {n : nat} (s : Store n) (u v : Tm n)
    (uv : Tm_IsValue u) (x : Fin.t n) :
    Store_Binds s x v ->
    Store_Binds (store_val s u uv) (Fin.succ x) (Tm_weaken v).

Arguments store_binds_here {n} s v vv.
Arguments store_binds_there {n} s u v uv x _.

(** Executable lookup corresponding to [Store_Binds]. *)
Fixpoint Store_lookup {n : nat} (s : Store n) : Fin.t n -> option (Tm n) :=
  match s in Store n' return Fin.t n' -> option (Tm n') with
  | store_empty => fun x => Fin.elim0 x
  | store_val s v _ => fun x =>
      Fin.cases (Some (Tm_weaken v))
        (fun y => option_map Tm_weaken (Store_lookup s y)) x
  end.

Theorem Store_Binds_isValue {n : nat} {s : Store n}
    {x : Fin.t n} {v : Tm n} (H : Store_Binds s x v) :
    Tm_IsValue v.
Proof.
  induction H.
  - now apply Tm_IsValue_weaken.
  - now apply Tm_IsValue_weaken.
Qed.

Theorem Store_Binds_lookup_eq {n : nat} {s : Store n}
    {x : Fin.t n} {v : Tm n} (H : Store_Binds s x v) :
    Store_lookup s x = Some v.
Proof.
  induction H.
  - reflexivity.
  - cbn. rewrite IHStore_Binds. reflexivity.
Qed.

(** A location has at most one stored term. *)
Theorem Store_Binds_unique {n : nat} {s : Store n} {x : Fin.t n}
    {v1 v2 : Tm n} (H1 : Store_Binds s x v1)
    (H2 : Store_Binds s x v2) : v1 = v2.
Proof.
  assert (Some v1 = Some v2) as H by
    exact (eq_trans (eq_sym (Store_Binds_lookup_eq H1))
      (Store_Binds_lookup_eq H2)).
  now injection H.
Qed.

(** A store is typed pointwise by a context with the same scope. *)
Inductive Store_Ty : forall {n : nat}, Ctx n -> Store n -> Prop :=
| store_ty_empty : Store_Ty ctx_nil store_empty
| store_ty_val {n : nat} (G : Ctx n) (s : Store n)
    (t : Tm n) (T : Ty n) (vt : Tm_IsValue t) :
    Store_Ty G s ->
    Tm_Ty G t T ->
    Store_Ty (ctx_snoc G T) (store_val s t vt).

Arguments store_ty_val {n} G s t T vt _ _.
