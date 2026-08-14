From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Renaming Store PreciseStore ValueInversion.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** A store typing enriched with the precise introduction type of every
    cell. [P] is precise; [T] is the public type recorded in the context. *)
Inductive Store_RefinedTy : forall {n : nat}, Ctx n -> Store n -> Prop :=
| store_refined_ty_empty : Store_RefinedTy ctx_nil store_empty
| store_refined_ty_val {n : nat} (G : Ctx n) (s : Store n)
    (v : Tm n) (P T : Ty n) (Hv : Tm_IsValue v) :
    Store_RefinedTy G s ->
    Tm_PreciseTy G v P ->
    Tm_Ty G v T ->
    Tau_Sub G (tau_ty P) (tau_ty T) ->
    Store_RefinedTy (ctx_snoc G T) (store_val s v Hv).

Arguments store_refined_ty_val {n} G s v P T Hv _ _ _ _.

(** Every public store typing admits the enriched proof data. *)
Theorem Store_Ty_toRefined {n : nat} {G : Ctx n} {s : Store n}
    (H : Store_Ty G s) : Store_RefinedTy G s.
Proof.
  induction H as
      [|n G s v T Hv Hs IH Ht].
  - apply store_refined_ty_empty.
  - destruct (Tm_Ty_value_inversion Ht Hv) as [P [Hp Hsub]].
    exact (store_refined_ty_val G s v P T Hv IH Hp Ht Hsub).
Qed.

(** Forgetting precise types recovers the public store typing. *)
Theorem Store_RefinedTy_toTy {n : nat} {G : Ctx n} {s : Store n}
    (H : Store_RefinedTy G s) : Store_Ty G s.
Proof.
  induction H.
  - apply store_ty_empty.
  - eapply store_ty_val; eassumption.
Qed.

(** Every aligned store/context location has a value, its public type, and
    its precise introduction type. *)
Theorem Store_RefinedTy_lookup_exists
    {n : nat} {G : Ctx n} {s : Store n}
    (H : Store_RefinedTy G s) (x : Fin.t n) :
    exists (v : Tm n) (T P : Ty n),
      Store_Binds s x v /\
      Ctx_Binds G x T /\
      Tm_PreciseTy G v P /\
      Tm_Ty G v T /\
      Tau_Sub G (tau_ty P) (tau_ty T).
Proof.
  induction H as
      [|n G s v P T Hv Hs IH Hp Ht Hsub].
  - exact (Fin.elim0 x).
  - refine (@Fin.cases' n x
      (fun x => exists (u : Tm (S n)) (U Q : Ty (S n)),
        Store_Binds (store_val s v Hv) x u /\
        Ctx_Binds (ctx_snoc G T) x U /\
        Tm_PreciseTy (ctx_snoc G T) u Q /\
        Tm_Ty (ctx_snoc G T) u U /\
        Tau_Sub (ctx_snoc G T) (tau_ty Q) (tau_ty U)) _ _).
    + exists (Tm_weaken v), (Ty_weaken T), (Ty_weaken P).
      repeat split.
      * apply store_binds_here.
      * apply binds_here.
      * now apply Tm_PreciseTy_weaken.
      * now apply Tm_Ty_weaken.
      * exact (@Tau_Sub_weaken n star G (tau_ty P) (tau_ty T) T Hsub).
    + intros y.
      destruct (IH y) as (u & U & Q & Hu & HU & Hq & Hut & HQU).
      exists (Tm_weaken u), (Ty_weaken U), (Ty_weaken Q).
      repeat split.
      * now apply store_binds_there.
      * now apply binds_there.
      * now apply Tm_PreciseTy_weaken.
      * now apply Tm_Ty_weaken.
      * exact (@Tau_Sub_weaken n star G (tau_ty Q) (tau_ty U) T HQU).
Qed.

(** Inverting a runtime lookup recovers the aligned public context type,
    precise introduction type, and refinement proof. *)
Theorem Store_RefinedTy_of_store_binds
    {n : nat} {G : Ctx n} {s : Store n} {x : Fin.t n} {v : Tm n}
    (H : Store_RefinedTy G s) (Hs : Store_Binds s x v) :
    exists (T P : Ty n),
      Ctx_Binds G x T /\
      Tm_PreciseTy G v P /\
      Tm_Ty G v T /\
      Tau_Sub G (tau_ty P) (tau_ty T).
Proof.
  destruct (Store_RefinedTy_lookup_exists H x)
    as (u & T & P & Hu & HT & Hp & Ht & Hsub).
  assert (u = v) as -> by exact (Store_Binds_unique Hu Hs).
  now exists T, P.
Qed.

(** Inverting a public context lookup recovers the aligned stored value and
    its precise refinement. *)
Theorem Store_RefinedTy_of_ctx_binds
    {n : nat} {G : Ctx n} {s : Store n} {x : Fin.t n} {T : Ty n}
    (H : Store_RefinedTy G s) (Hc : Ctx_Binds G x T) :
    exists (v : Tm n) (P : Ty n),
      Store_Binds s x v /\
      Tm_PreciseTy G v P /\
      Tm_Ty G v T /\
      Tau_Sub G (tau_ty P) (tau_ty T).
Proof.
  destruct (Store_RefinedTy_lookup_exists H x)
    as (v & U & P & Hv & HU & Hp & Ht & Hsub).
  assert (U = T) as -> by exact (Ctx_Binds_unique HU Hc).
  now exists v, P.
Qed.

(** Convenient inversion when both aligned lookup derivations are known. *)
Theorem Store_RefinedTy_lookup
    {n : nat} {G : Ctx n} {s : Store n} {x : Fin.t n}
    {v : Tm n} {T : Ty n}
    (H : Store_RefinedTy G s)
    (Hs : Store_Binds s x v) (Hc : Ctx_Binds G x T) :
    exists P,
      Tm_PreciseTy G v P /\
      Tm_Ty G v T /\
      Tau_Sub G (tau_ty P) (tau_ty T).
Proof.
  destruct (Store_RefinedTy_of_store_binds H Hs)
    as (U & P & HU & Hp & Ht & Hsub).
  assert (U = T) as -> by exact (Ctx_Binds_unique HU Hc).
  now exists P.
Qed.

Print Assumptions Store_Ty_toRefined.
Print Assumptions Store_RefinedTy_lookup_exists.
Print Assumptions Store_RefinedTy_lookup.
