From PathDependent.LambdaP Require Import FinFun Syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Inductive Ctx : nat -> Type :=
| ctx_nil : Ctx 0
| ctx_snoc {n} : Ctx n -> Ty n -> Ctx (S n).

Arguments ctx_snoc {n} _ _.

Inductive Ctx_Binds : forall {n : nat}, Ctx n -> Fin.t n -> Ty n -> Prop :=
| binds_here {n : nat} (G : Ctx n) (T : Ty n) :
    Ctx_Binds (ctx_snoc G T) Fin.zero (Ty_weaken T)
| binds_there {n : nat} (G : Ctx n) (S T : Ty n) (x : Fin.t n) :
    Ctx_Binds G x T ->
    Ctx_Binds (ctx_snoc G S) (Fin.succ x) (Ty_weaken T).

Arguments binds_here {n} G T.
Arguments binds_there {n} G S T x _.

Fixpoint Ctx_lookup {n : nat} (G : Ctx n) : Fin.t n -> Ty n :=
  match G in Ctx n' return Fin.t n' -> Ty n' with
  | ctx_nil => fun x => Fin.elim0 x
  | ctx_snoc G T => fun x =>
      Fin.cases (Ty_weaken T) (fun i => Ty_weaken (Ctx_lookup G i)) x
  end.

Theorem Ctx_lookup_binds {n : nat} (G : Ctx n) (x : Fin.t n) :
    Ctx_Binds G x (Ctx_lookup G x).
Proof.
  induction G as [|n G IH T].
  - exact (Fin.elim0 x).
  - refine (@Fin.cases' n x
      (fun x => Ctx_Binds (ctx_snoc G T) x
        (Ctx_lookup (ctx_snoc G T) x)) _ _).
    + exact (binds_here G T).
    + intros y.
      exact (binds_there G T (Ctx_lookup G y) y (IH y)).
Qed.

Theorem Ctx_Binds_eq_lookup {n : nat} {G : Ctx n}
    {x : Fin.t n} {T : Ty n} (H : Ctx_Binds G x T) :
    T = Ctx_lookup G x.
Proof.
  induction H.
  - reflexivity.
  - cbn. now f_equal.
Qed.

Theorem Ctx_Binds_lookup_eq {n : nat} {G : Ctx n}
    {x : Fin.t n} {T : Ty n} (H : Ctx_Binds G x T) :
    Ctx_lookup G x = T.
Proof. symmetry. now apply Ctx_Binds_eq_lookup. Qed.

Theorem Ctx_Binds_unique {n : nat} {G : Ctx n} {x : Fin.t n}
    {T1 T2 : Ty n} (H1 : Ctx_Binds G x T1) (H2 : Ctx_Binds G x T2) :
    T1 = T2.
Proof.
  transitivity (Ctx_lookup G x).
  - now apply Ctx_Binds_eq_lookup.
  - symmetry. now apply Ctx_Binds_eq_lookup.
Qed.

Theorem Ctx_Binds_exists {n : nat} (G : Ctx n) (x : Fin.t n) :
    exists T, Ctx_Binds G x T.
Proof. exists (Ctx_lookup G x). now apply Ctx_lookup_binds. Qed.
