From Stdlib Require Import Lists.List.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Renaming Store Cont State PathReduction Machine
  PreciseStore PathFunctionality TypingInversion Lookup PathPreservation.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Inductive State_Progress {n : nat} (s : State n) : Prop :=
| state_progress_final : State_IsFinal s -> State_Progress s
| state_progress_step {m : nat} (s' : State m) :
    State_Step s s' -> State_Progress s.

Arguments state_progress_final {n s} _.
Arguments state_progress_step {n s m} s' _.

Local Lemma Store_Ty_lookup_pair
    {n : nat} {G : Ctx n} {s : Store n}
    (Hs : Store_Ty G s) (x : Fin.t n) :
    exists (T : Ty n) (v : Tm n),
      Ctx_Binds G x T /\ Store_Binds s x v /\ Tm_Ty G v T.
Proof.
  induction Hs.
  - exact (Fin.elim0 x).
  - refine (@Fin.cases' n x
      (fun x => exists (U : Ty (S n)) (v : Tm (S n)),
        Ctx_Binds (ctx_snoc G T) x U /\
        Store_Binds (store_val s t vt) x v /\
        Tm_Ty (ctx_snoc G T) v U) _ _).
    + exists (Ty_weaken T), (Tm_weaken t). repeat split.
      * apply binds_here.
      * apply store_binds_here.
      * now apply Tm_Ty_weaken.
    + intros y.
      destruct (IHHs y) as (U & v & HU & Hv & Hvt).
      exists (Ty_weaken U), (Tm_weaken v). repeat split.
      * now apply binds_there.
      * now apply store_binds_there.
      * now apply Tm_Ty_weaken.
Qed.

Theorem Store_Ty_of_ctx_binds
    {n : nat} {G : Ctx n} {s : Store n} {x : Fin.t n} {T : Ty n}
    (Hs : Store_Ty G s) (Hb : Ctx_Binds G x T) :
    exists v, Store_Binds s x v /\ Tm_Ty G v T.
Proof.
  destruct (Store_Ty_lookup_pair Hs x) as (U & v & HU & Hv & Hvt).
  assert (U = T) as -> by exact (Ctx_Binds_unique HU Hb).
  now exists v.
Qed.

Theorem Store_Ty_lookup_exists
    {n : nat} {G : Ctx n} {s : Store n}
    (Hs : Store_Ty G s) (x : Fin.t n) :
    exists v, Store_Binds s x v.
Proof.
  destruct (Ctx_Binds_exists G x) as [T HT].
  destruct (Store_Ty_of_ctx_binds Hs HT) as [v [Hv Hvt]].
  now exists v.
Qed.

Theorem State_Progress_path_var
    {n : nat} {G : Ctx n} {s : Store n}
    (Hs : Store_Ty G s) (x : Fin.t n) (K : Tm_Cont n) :
    State_Progress (mk_state s K (tm_path (path_var x))).
Proof.
  destruct K as [|F K].
  - destruct (Store_Ty_lookup_exists Hs x) as [v Hv].
    apply state_progress_final. exact (state_final_var s x v Hv).
  - destruct F as [t].
    eapply state_progress_step. apply state_step_rename.
Qed.

Theorem State_Progress_value
    {n : nat} {v : Tm n} (Hv : Tm_IsValue v)
    (s : Store n) (K : Tm_Cont n) :
    State_Progress (mk_state s K v).
Proof.
  destruct K as [|F K].
  - apply state_progress_final. exact (state_final_val s v Hv).
  - destruct F as [t].
    eapply state_progress_step. exact (state_step_lift s K t v Hv).
Qed.

Theorem State_Progress_let_term
    {n : nat} (s : Store n) (K : Tm_Cont n)
    (u : Tm n) (t : Tm (S n)) :
    State_Progress (mk_state s K (tm_let u t)).
Proof. eapply state_progress_step. apply state_step_let_push. Qed.

Theorem State_Progress_typed
    {n : nat} (s : Store n) (K : Tm_Cont n)
    (t : Tm n) (T : Ty n) :
    State_Progress (mk_state s K (tm_typed t T)).
Proof. eapply state_progress_step. apply state_step_ascribe. Qed.

Theorem State_Progress_path
    {n : nat} {s : Store n} {p : Path n} {x : Fin.t n}
    {K : Tm_Cont n}
    (Hr : Path_reduce p s x) (Hnv : ~ Path_IsVar p) :
    State_Progress (mk_state s K (tm_path p)).
Proof. eapply state_progress_step. exact (state_step_path s K p x Hr Hnv). Qed.

Theorem State_Progress_app
    {n : nat} {s : Store n} {p q : Path n} {x y : Fin.t n}
    {A : Ty n} {body : Tm (S n)} {K : Tm_Cont n}
    (Hp : Path_reduce p s x) (Hq : Path_reduce q s y)
    (Hv : Store_Binds s x (tm_abs A body)) :
    State_Progress (mk_state s K (tm_app p q)).
Proof.
  eapply state_progress_step.
  exact (state_step_app s K p q x y A body Hp Hq Hv).
Qed.

Print Assumptions Store_Ty_of_ctx_binds.
Print Assumptions State_Progress_path_var.
Print Assumptions State_Progress_value.
Print Assumptions State_Progress_app.
