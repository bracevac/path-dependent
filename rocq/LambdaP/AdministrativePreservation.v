From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Renaming Store Cont State PathReduction Machine.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Derive NoConfusion for State.
Derive NoConfusion for Tm_Frame.

(** A transition either preserves the context exactly or extends it with the
    type of a freshly allocated value. *)
Inductive Preserve : forall {n m : nat}, Ctx n -> State m -> Ty n -> Prop :=
| preserve_same {n : nat} (G : Ctx n) (s : State n) (T : Ty n) :
    State_Ty G s T -> Preserve G s T
| preserve_extend {n : nat} (G : Ctx n) (s : State (S n))
    (S0 T : Ty n) :
    State_Ty (ctx_snoc G S0) s (Ty_weaken T) -> Preserve G s T.

Arguments preserve_same {n} G s T _.
Arguments preserve_extend {n} G s S0 T _.

(** First-order term observations used by syntax-directed inversions. *)
Local Definition tm_let_bound_projection {n : nat} (u : Tm n) :
    option (Tm n) :=
  match u with
  | tm_let s _ => Some s
  | _ => None
  end.

Local Definition tm_let_body_projection {n : nat} (u : Tm n) :
    option (Tm (S n)) :=
  match u in Tm n' return option (Tm (S n')) with
  | tm_let _ t => Some t
  | _ => None
  end.

Local Definition tm_typed_term_projection {n : nat} (u : Tm n) :
    option (Tm n) :=
  match u with
  | tm_typed t _ => Some t
  | _ => None
  end.

Local Lemma tm_let_injective {n : nat}
    (s s' : Tm n) (t t' : Tm (S n)) :
    tm_let s t = tm_let s' t' -> s = s' /\ t = t'.
Proof.
  intro H. split.
  - pose proof (f_equal (@tm_let_bound_projection n) H) as Hs.
    cbn in Hs. now injection Hs.
  - pose proof (f_equal (@tm_let_body_projection n) H) as Ht.
    cbn in Ht. now injection Ht.
Qed.

Local Lemma tm_typed_term_injective {n : nat}
    (t t' : Tm n) (A A' : Ty n) :
    tm_typed t A = tm_typed t' A' -> t = t'.
Proof.
  intro H.
  pose proof (f_equal (@tm_typed_term_projection n) H) as Ht.
  cbn in Ht. now injection Ht.
Qed.

Theorem Tm_Ty_let_inv_of_eq
    {n : nat} {G : Ctx n} {u : Tm n} {T : Ty n}
    (H : Tm_Ty G u T) :
    forall (s : Tm n) (t : Tm (S n)), u = tm_let s t ->
      exists S0,
        Tm_Ty G s S0 /\
        Tau_Wf G (tau_ty T) /\
        Tm_Ty (ctx_snoc G S0) t (Ty_weaken T).
Proof.
  induction H as
      [n G p T Hp
      |n G S t T Ht IH Hwf
      |n G p q S T Hp IHp Hq IHq
      |n G y z S T a Hy Hz
      |n G y S T A0 Hy Hwf
      |n G s S T t Hs IHs Hwf Ht IHt
      |n G t T Ht IH Hwf
      |n G t S T Ht IH Hsub Hwf];
      intros s0 t0 Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - destruct (tm_let_injective Heq) as [Hs_eq Ht_eq].
    subst s0 t0. exists S. repeat split; assumption.
  - discriminate Heq.
  - destruct (IH s0 t0 Heq) as [U [Hs [Hwf_base Hb]]].
    exists U. repeat split.
    + exact Hs.
    + exact Hwf.
    + eapply tm_ty_sub.
      * exact Hb.
      * exact (@Tau_Sub_weaken n star G (tau_ty S) (tau_ty T) U Hsub).
      * exact (@Tau_Wf_weaken n star G (tau_ty T) U Hwf).
Qed.

Theorem Tm_Ty_let_inv
    {n : nat} {G : Ctx n} {s : Tm n} {t : Tm (S n)} {T : Ty n}
    (H : Tm_Ty G (tm_let s t) T) :
    exists S0,
      Tm_Ty G s S0 /\
      Tau_Wf G (tau_ty T) /\
      Tm_Ty (ctx_snoc G S0) t (Ty_weaken T).
Proof.
  exact (@Tm_Ty_let_inv_of_eq n G (tm_let s t) T H s t eq_refl).
Qed.

Theorem Tm_Ty_typed_inv_of_eq
    {n : nat} {G : Ctx n} {u : Tm n} {T : Ty n}
    (H : Tm_Ty G u T) :
    forall (t : Tm n) (A : Ty n), u = tm_typed t A ->
      Tm_Ty G t T /\ Tau_Wf G (tau_ty T).
Proof.
  induction H as
      [n G p T Hp
      |n G S t T Ht IH Hwf
      |n G p q S T Hp IHp Hq IHq
      |n G y z S T a Hy Hz
      |n G y S T A0 Hy Hwf
      |n G s S T t Hs IHs Hwf Ht IHt
      |n G t T Ht IH Hwf
      |n G t S T Ht IH Hsub Hwf];
      intros t0 Aann Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - apply tm_typed_term_injective in Heq. subst t0. now split.
  - destruct (IH t0 Aann Heq) as [Ht0 Hwf_base]. split.
    + eapply tm_ty_sub; eassumption.
    + exact Hwf.
Qed.

Theorem Tm_Ty_typed_inv
    {n : nat} {G : Ctx n} {t : Tm n} {A T : Ty n}
    (H : Tm_Ty G (tm_typed t A) T) :
    Tm_Ty G t T /\ Tau_Wf G (tau_ty T).
Proof.
  exact (@Tm_Ty_typed_inv_of_eq n G (tm_typed t A) T H t A eq_refl).
Qed.

Theorem Preserve_let_push
    {n : nat} {G : Ctx n} {s0 : Store n} {K : Tm_Cont n}
    {s : Tm n} {t : Tm (S n)} {T : Ty n}
    (H : State_Ty G (mk_state s0 K (tm_let s t)) T) :
    Preserve G (mk_state s0 (cons (tm_frame_let t) K) s) T.
Proof.
  dependent elimination H.
  lazymatch goal with
  | Hterm : Tm_Ty _ (tm_let _ _) _ |- _ =>
      destruct (Tm_Ty_let_inv Hterm) as [U [Hs [Hwf Hb]]]
  end.
  apply preserve_same.
  eapply state_ty_ok.
  - eassumption.
  - eapply tm_cont_ty_cons.
    + eassumption.
    + apply tm_frame_ty_let. exact Hb.
  - exact Hs.
Qed.

Theorem Preserve_lift
    {n : nat} {G : Ctx n} {s : Store n} {K : Tm_Cont n}
    {t : Tm (S n)} {v : Tm n} {T : Ty n}
    (Hv : Tm_IsValue v)
    (H : State_Ty G
      (mk_state s (cons (tm_frame_let t) K) v) T) :
    Preserve G
      (mk_state (store_val s v Hv) (Tm_Cont_weaken K) t) T.
Proof.
  dependent elimination H.
  lazymatch goal with
  | Hcont : Tm_Cont_Ty _ _ (cons _ _) _ |- _ =>
      dependent elimination Hcont
  end.
  lazymatch goal with
  | Hframe : Tm_Frame_Ty _ _ (tm_frame_let _) _ |- _ =>
      dependent elimination Hframe
  end.
  lazymatch goal with
  | Hterm : Tm_Ty ?G0 ?value ?U |- Preserve ?G0 ?destination ?T0 =>
      refine (@preserve_extend _ G0 destination U T0 _)
  end.
  eapply state_ty_ok.
  - eapply store_ty_val; eassumption.
  - lazymatch goal with
    | Hcont : Tm_Cont_Ty ?G0 ?Input ?K0 ?Output,
      Hterm : Tm_Ty ?G0 ?value ?Fresh |- _ =>
        exact (@Tm_Cont_Ty_weaken _ G0 Input Output Fresh K0 Hcont)
    end.
  - eassumption.
Qed.

Theorem Preserve_ascribe
    {n : nat} {G : Ctx n} {s : Store n} {K : Tm_Cont n}
    {t : Tm n} {A T : Ty n}
    (H : State_Ty G (mk_state s K (tm_typed t A)) T) :
    Preserve G (mk_state s K t) T.
Proof.
  dependent elimination H.
  apply preserve_same. eapply state_ty_ok; [eassumption | eassumption |].
  lazymatch goal with
  | Hterm : Tm_Ty _ (tm_typed _ _) _ |- _ =>
      exact (proj1 (Tm_Ty_typed_inv Hterm))
  end.
Qed.

Print Assumptions Tm_Ty_let_inv.
Print Assumptions Tm_Ty_typed_inv.
Print Assumptions Preserve_let_push.
Print Assumptions Preserve_lift.
Print Assumptions Preserve_ascribe.
