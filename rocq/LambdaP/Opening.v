From PathDependent.LambdaP Require Import FinFun Syntax Context Typing Renaming.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Local Coercion FinFun.apply : FinFun.t >-> Funclass.

(** Removing the newest context entry is a valid renaming when its image is
    an existing variable with exactly the stored binder type. *)
Theorem Renaming_open {n : nat} {G : Ctx n} {S0 : Ty n} {x : Fin.t n}
    (Hx : Ctx_Binds G x S0) :
    Renaming (ctx_snoc G S0) (FinFun.openAt x) G.
Proof.
  intros y T H.
  refine (@Fin.cases' n y
    (fun y => Ctx_Binds (ctx_snoc G S0) y T ->
      Ctx_Binds G (FinFun.openAt x y)
        (Ty_rename T (FinFun.openAt x))) _ _ H).
  - intros H0.
    assert (T = Ty_weaken S0) as ->.
    { exact (Ctx_Binds_unique H0 (binds_here G S0)). }
    rewrite FinFun.openAt_zero.
    unfold Ty_weaken. rewrite Ty_rename_rename,
      FinFun.openAt_weaken, Ty_rename_id. exact Hx.
  - intros z Hz.
    assert (T = Ty_weaken (Ctx_lookup G z)) as ->.
    { exact (Ctx_Binds_unique Hz
        (binds_there G S0 (Ctx_lookup G z) z (Ctx_lookup_binds G z))). }
    rewrite FinFun.openAt_succ.
    unfold Ty_weaken. rewrite Ty_rename_rename,
      FinFun.openAt_weaken, Ty_rename_id. apply Ctx_lookup_binds.
Qed.

Theorem Path_Ty_open_var {n : nat} {k : Kind} {G : Ctx n}
    {S0 : Ty n} {p : Path (S n)} {d : Tau (S n) k} {x : Fin.t n}
    (H : Path_Ty (ctx_snoc G S0) p d)
    (Hx : Ctx_Binds G x S0) :
    Path_Ty G (Path_rename p (FinFun.openAt x))
      (Tau_rename d (FinFun.openAt x)).
Proof. exact (Path_Ty_rename H (Renaming_open Hx)). Qed.

Theorem Tau_Sub_open_var {n : nat} {k : Kind} {G : Ctx n}
    {S0 : Ty n} {d1 d2 : Tau (S n) k} {x : Fin.t n}
    (H : Tau_Sub (ctx_snoc G S0) d1 d2)
    (Hx : Ctx_Binds G x S0) :
    Tau_Sub G (Tau_rename d1 (FinFun.openAt x))
      (Tau_rename d2 (FinFun.openAt x)).
Proof. exact (Tau_Sub_rename H (Renaming_open Hx)). Qed.

Theorem Tau_Wf_open_var {n : nat} {k : Kind} {G : Ctx n}
    {S0 : Ty n} {d : Tau (S n) k} {x : Fin.t n}
    (H : Tau_Wf (ctx_snoc G S0) d)
    (Hx : Ctx_Binds G x S0) :
    Tau_Wf G (Tau_rename d (FinFun.openAt x)).
Proof. exact (Tau_Wf_rename H (Renaming_open Hx)). Qed.

Theorem Tm_Ty_open_var {n : nat} {G : Ctx n} {S0 : Ty n}
    {t : Tm (S n)} {T : Ty (S n)} {x : Fin.t n}
    (H : Tm_Ty (ctx_snoc G S0) t T)
    (Hx : Ctx_Binds G x S0) :
    Tm_Ty G (Tm_open t x) (Ty_rename T (FinFun.openAt x)).
Proof. unfold Tm_open. exact (Tm_Ty_rename H (Renaming_open Hx)). Qed.

Theorem Tm_Ty_open_var_weaken {n : nat} {G : Ctx n} {S0 : Ty n}
    {t : Tm (S n)} {T : Ty n} {x : Fin.t n}
    (H : Tm_Ty (ctx_snoc G S0) t (Ty_weaken T))
    (Hx : Ctx_Binds G x S0) :
    Tm_Ty G (Tm_open t x) T.
Proof.
  pose proof (Tm_Ty_open_var H Hx) as Hopen.
  unfold Ty_weaken in Hopen.
  rewrite Ty_rename_rename, FinFun.openAt_weaken, Ty_rename_id in Hopen.
  exact Hopen.
Qed.
