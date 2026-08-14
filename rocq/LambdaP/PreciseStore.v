From PathDependent.LambdaP Require Import FinFun Syntax Context Typing
  Renaming Store.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** The type assigned directly by a value-introduction rule. *)
Inductive Tm_PreciseTy : forall {n : nat}, Ctx n -> Tm n -> Ty n -> Prop :=
| precise_ty_abs {n : nat} (G : Ctx n) (S0 : Ty n)
    (t : Tm (S n)) (T : Ty (S n)) :
    Tm_Ty (ctx_snoc G S0) t T ->
    Tau_Wf G (tau_ty S0) ->
    Tm_PreciseTy G (tm_abs S0 t) (ty_fun S0 T)
| precise_ty_pair {n : nat} (G : Ctx n) (y z : Fin.t n)
    (S0 T : Ty n) (a : Name) :
    Ctx_Binds G y S0 ->
    Ctx_Binds G z T ->
    Tm_PreciseTy G (tm_pair y a (def_val z))
      (ty_pair (ty_single (path_var y)) a
        (tau_ty (ty_single (Path_weaken (path_var z)))))
| precise_ty_tpair {n : nat} (G : Ctx n) (y : Fin.t n)
    (S0 T : Ty n) (A : Name) :
    Ctx_Binds G y S0 ->
    Tau_Wf G (tau_ty T) ->
    Tm_PreciseTy G (tm_pair y A (def_type T))
      (ty_pair (ty_single (path_var y)) A
        (Tau_weaken (tau_intv T T))).

Arguments precise_ty_abs {n} G S0 t T _ _.
Arguments precise_ty_pair {n} G y z S0 T a _ _.
Arguments precise_ty_tpair {n} G y S0 T A _ _.

Theorem Tm_PreciseTy_isValue {n : nat} {G : Ctx n}
    {v : Tm n} {T : Ty n} (H : Tm_PreciseTy G v T) : Tm_IsValue v.
Proof. destruct H; constructor. Qed.

Theorem Tm_PreciseTy_toTy {n : nat} {G : Ctx n}
    {v : Tm n} {T : Ty n} (H : Tm_PreciseTy G v T) : Tm_Ty G v T.
Proof.
  destruct H.
  - now apply tm_ty_abs.
  - eapply tm_ty_pair; eassumption.
  - eapply tm_ty_tpair; eassumption.
Qed.

Theorem Tm_PreciseTy_rename {n : nat} {G : Ctx n}
    {v : Tm n} {T : Ty n} (H : Tm_PreciseTy G v T) :
    forall {m : nat} {f : FinFun.t n m} {D : Ctx m},
      Renaming G f D ->
      Tm_PreciseTy D (Tm_rename v f) (Ty_rename T f).
Proof.
  destruct H; intros m f D rho;
    cbn [Tm_rename Def_rename Path_rename Ty_rename Tau_rename].
  - apply precise_ty_abs.
    + exact (Tm_Ty_rename H (Renaming_ext rho)).
    + exact (Tau_Wf_rename H0 rho).
  - rewrite <- Path_weaken_rename.
    apply precise_ty_pair with (S0 := Ty_rename S0 f)
      (T := Ty_rename T f).
    + now apply rho.
    + now apply rho.
  - rewrite <- Tau_weaken_rename.
    apply precise_ty_tpair with (S0 := Ty_rename S0 f).
    + now apply rho.
    + exact (Tau_Wf_rename H0 rho).
Qed.

Theorem Tm_PreciseTy_weaken {n : nat} {G : Ctx n}
    {v : Tm n} {T S0 : Ty n} (H : Tm_PreciseTy G v T) :
    Tm_PreciseTy (ctx_snoc G S0) (Tm_weaken v) (Ty_weaken T).
Proof.
  unfold Tm_weaken, Ty_weaken.
  exact (Tm_PreciseTy_rename H (@Renaming_weaken n G S0)).
Qed.

(** A store and context built in lockstep from exact value-introduction
    types. *)
Inductive Store_PreciseTy : forall {n : nat}, Ctx n -> Store n -> Prop :=
| store_precise_ty_empty : Store_PreciseTy ctx_nil store_empty
| store_precise_ty_val {n : nat} (G : Ctx n) (s : Store n)
    (v : Tm n) (T : Ty n) (vv : Tm_IsValue v) :
    Store_PreciseTy G s ->
    Tm_PreciseTy G v T ->
    Store_PreciseTy (ctx_snoc G T) (store_val s v vv).

Arguments store_precise_ty_val {n} G s v T vv _ _.

Theorem Store_PreciseTy_toTy {n : nat} {G : Ctx n} {s : Store n}
    (H : Store_PreciseTy G s) : Store_Ty G s.
Proof.
  induction H.
  - apply store_ty_empty.
  - eapply store_ty_val; [exact IHStore_PreciseTy|].
    now apply Tm_PreciseTy_toTy.
Qed.

(** Constructive joint lookup: a precise store supplies matching context and
    store bindings at every location. *)
Lemma Store_PreciseTy_lookup_pair {n : nat} {G : Ctx n} {s : Store n}
    (H : Store_PreciseTy G s) (x : Fin.t n) :
    exists (T : Ty n) (v : Tm n),
      Ctx_Binds G x T /\ Store_Binds s x v /\ Tm_PreciseTy G v T.
Proof.
  induction H.
  - exact (Fin.elim0 x).
  - refine (@Fin.cases' n x
      (fun x => exists (U : Ty (S n)) (u : Tm (S n)),
        Ctx_Binds (ctx_snoc G T) x U /\
        Store_Binds (store_val s v vv) x u /\
        Tm_PreciseTy (ctx_snoc G T) u U) _ _).
    + exists (Ty_weaken T), (Tm_weaken v). split.
      * apply binds_here.
      * split.
        -- apply store_binds_here.
        -- now apply Tm_PreciseTy_weaken.
    + intros y.
      destruct (IHStore_PreciseTy y) as (U & u & HU & Hu & Hp).
      exists (Ty_weaken U), (Tm_weaken u). split.
      * now apply binds_there.
      * split.
        -- now apply store_binds_there.
        -- now apply Tm_PreciseTy_weaken.
Qed.

Theorem Store_PreciseTy_of_store_binds {n : nat} {G : Ctx n}
    {s : Store n} {x : Fin.t n} {v : Tm n}
    (Hs : Store_PreciseTy G s) (Hb : Store_Binds s x v) :
    exists T, Ctx_Binds G x T /\ Tm_PreciseTy G v T.
Proof.
  destruct (Store_PreciseTy_lookup_pair Hs x)
    as (T & u & HT & Hu & Hp).
  assert (v = u) as -> by exact (Store_Binds_unique Hb Hu).
  now exists T.
Qed.

Theorem Store_PreciseTy_of_ctx_binds {n : nat} {G : Ctx n}
    {s : Store n} {x : Fin.t n} {T : Ty n}
    (Hs : Store_PreciseTy G s) (Hb : Ctx_Binds G x T) :
    exists v, Store_Binds s x v /\ Tm_PreciseTy G v T.
Proof.
  destruct (Store_PreciseTy_lookup_pair Hs x)
    as (U & v & HU & Hv & Hp).
  assert (T = U) as -> by exact (Ctx_Binds_unique Hb HU).
  now exists v.
Qed.

Theorem Store_PreciseTy_lookup {n : nat} {G : Ctx n}
    {s : Store n} {x : Fin.t n} {v : Tm n} {T : Ty n}
    (Hs : Store_PreciseTy G s) (Hstore : Store_Binds s x v)
    (Hctx : Ctx_Binds G x T) : Tm_PreciseTy G v T.
Proof.
  destruct (Store_PreciseTy_of_store_binds Hs Hstore)
    as (U & HU & Hv).
  assert (U = T) as -> by exact (Ctx_Binds_unique HU Hctx).
  exact Hv.
Qed.
