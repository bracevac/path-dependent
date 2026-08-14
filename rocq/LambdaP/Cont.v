From Stdlib Require Import Lists.List.
From PathDependent.LambdaP Require Import FinFun Syntax Context Typing Renaming.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** A single term evaluation frame. *)
Inductive Tm_Frame (n : nat) : Type :=
| tm_frame_let : Tm (S n) -> Tm_Frame n.

Arguments tm_frame_let {n} _.

(** Continuations are stacks of term frames. *)
Definition Tm_Cont (n : nat) : Type := list (Tm_Frame n).

Definition Tm_Frame_rename {n m : nat}
    (F : Tm_Frame n) (f : FinFun.t n m) : Tm_Frame m :=
  match F with
  | tm_frame_let t => tm_frame_let (Tm_rename t (FinFun.ext f))
  end.

Definition Tm_Cont_rename {n m : nat}
    (K : Tm_Cont n) (f : FinFun.t n m) : Tm_Cont m :=
  map (fun F => Tm_Frame_rename F f) K.

Definition Tm_Frame_weaken {n : nat} (F : Tm_Frame n) : Tm_Frame (S n) :=
  Tm_Frame_rename F (FinFun.weaken n).

Definition Tm_Cont_weaken {n : nat} (K : Tm_Cont n) : Tm_Cont (S n) :=
  Tm_Cont_rename K (FinFun.weaken n).

(** A frame consumes a term of type [S0] and resumes a computation of type
    [T]. *)
Inductive Tm_Frame_Ty : forall {n : nat},
    Ctx n -> Ty n -> Tm_Frame n -> Ty n -> Prop :=
| tm_frame_ty_let {n : nat} (G : Ctx n) (S0 T : Ty n)
    (t : Tm (S n)) :
    Tm_Ty (ctx_snoc G S0) t (Ty_weaken T) ->
    Tm_Frame_Ty G S0 (tm_frame_let t) T.

Arguments tm_frame_ty_let {n} G S0 T t _.

(** A continuation consumes its input type and eventually returns its output
    type. *)
Inductive Tm_Cont_Ty : forall {n : nat},
    Ctx n -> Ty n -> Tm_Cont n -> Ty n -> Prop :=
| tm_cont_ty_hole {n : nat} (G : Ctx n) (S0 T : Ty n) :
    Tau_Sub G (tau_ty S0) (tau_ty T) ->
    Tm_Cont_Ty G S0 nil T
| tm_cont_ty_cons {n : nat} (G : Ctx n) (S0 U T : Ty n)
    (F : Tm_Frame n) (K : Tm_Cont n) :
    Tm_Cont_Ty G S0 K T ->
    Tm_Frame_Ty G U F S0 ->
    Tm_Cont_Ty G U (cons F K) T.

Arguments tm_cont_ty_hole {n} G S0 T _.
Arguments tm_cont_ty_cons {n} G S0 U T F K _ _.

Theorem Tm_Frame_Ty_rename {n m : nat} {G : Ctx n} {D : Ctx m}
    {S0 T : Ty n} {F : Tm_Frame n} {f : FinFun.t n m}
    (H : Tm_Frame_Ty G S0 F T) (rho : Renaming G f D) :
    Tm_Frame_Ty D (Ty_rename S0 f) (Tm_Frame_rename F f)
      (Ty_rename T f).
Proof.
  destruct H as [n G S0 T t Ht]. cbn [Tm_Frame_rename].
  apply tm_frame_ty_let. rewrite Ty_weaken_rename.
  exact (Tm_Ty_rename Ht (Renaming_ext rho)).
Qed.

Theorem Tm_Cont_Ty_rename {n m : nat} {G : Ctx n} {D : Ctx m}
    {S0 T : Ty n} {K : Tm_Cont n} {f : FinFun.t n m}
    (H : Tm_Cont_Ty G S0 K T) (rho : Renaming G f D) :
    Tm_Cont_Ty D (Ty_rename S0 f) (Tm_Cont_rename K f)
      (Ty_rename T f).
Proof.
  induction H; cbn [Tm_Cont_rename].
  - apply tm_cont_ty_hole. exact (Tau_Sub_rename H rho).
  - eapply tm_cont_ty_cons.
    + exact (IHTm_Cont_Ty f rho).
    + exact (Tm_Frame_Ty_rename H0 rho).
Qed.

Theorem Tm_Frame_Ty_weaken {n : nat} {G : Ctx n} {S0 T U : Ty n}
    {F : Tm_Frame n} (H : Tm_Frame_Ty G S0 F T) :
    Tm_Frame_Ty (ctx_snoc G U) (Ty_weaken S0) (Tm_Frame_weaken F)
      (Ty_weaken T).
Proof.
  unfold Tm_Frame_weaken, Ty_weaken.
  exact (Tm_Frame_Ty_rename H (@Renaming_weaken n G U)).
Qed.

Theorem Tm_Cont_Ty_weaken {n : nat} {G : Ctx n} {S0 T U : Ty n}
    {K : Tm_Cont n} (H : Tm_Cont_Ty G S0 K T) :
    Tm_Cont_Ty (ctx_snoc G U) (Ty_weaken S0) (Tm_Cont_weaken K)
      (Ty_weaken T).
Proof.
  unfold Tm_Cont_weaken, Ty_weaken.
  exact (Tm_Cont_Ty_rename H (@Renaming_weaken n G U)).
Qed.
