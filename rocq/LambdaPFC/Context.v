From Equations Require Import Equations.
From PathDependent.LambdaPFC Require Import FinFun Syntax.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** A context stores each type in the scope preceding its binder. *)
Inductive Ctx : nat -> Type :=
| CtxNil : Ctx 0
| CtxSnoc {n : nat} : Ctx n -> Ty n -> Ctx (S n).

Arguments CtxSnoc {n} _ _.

(** Lookup weakens the stored type through every newer binder. *)
Equations ctx_lookup {n : nat} (Gamma : Ctx n) (x : Fin n) : Ty n :=
ctx_lookup (CtxSnoc Gamma T) FZ := ty_weaken T;
ctx_lookup (CtxSnoc Gamma T) (FS x) := ty_weaken (ctx_lookup Gamma x).
