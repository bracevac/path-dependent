From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store Cont State Machine PathReduction
  RuntimeConversion ScopedRuntimeEq StructuralRuntimeTyping
  StructuralTermTyping StructuralMachineInvariant
  StructuralApplicationBoundary
  StructuralApplicationCompatibility StructuralPreciseStore
  StructuralPreservation StructuralPreciseCanonical.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Store-preserving path reduction. *)
Theorem PreciseStructPreserve_path {n : nat} {G : Ctx n}
    {s : Store n} {K : Tm_Cont n} {p : Path n} {x : Fin.t n}
    {T : Ty n} (Hr : Path_reduce p s x)
    (H : State_PreciseStructTy G (mk_state s K (tm_path p)) T) :
    PreciseStructPreserve G
      (mk_state s K (tm_path (path_var x))) T.
Proof.
  destruct H as [S0 Hstore Hcont Hterm].
  apply precise_struct_preserve_same.
  eapply state_precise_struct_ty_ok.
  - exact Hstore.
  - exact Hcont.
  - exact (Tm_StructCheck_reduce_path Hr Hterm).
Qed.

(** Store-preserving administrative let push. *)
Theorem PreciseStructPreserve_let_push {n : nat} {G : Ctx n}
    {s : Store n} {K : Tm_Cont n} {u : Tm n}
    {t : Tm (S n)} {T : Ty n}
    (H : State_PreciseStructTy G (mk_state s K (tm_let u t)) T) :
    PreciseStructPreserve G
      (mk_state s (cons (tm_frame_let t) K) u) T.
Proof.
  destruct H as [S0 Hstore Hcont Hterm].
  destruct (Tm_StructCheck_let_inv Hterm)
    as (U & Hu & Hwf & Hbody).
  apply precise_struct_preserve_same.
  eapply state_precise_struct_ty_ok.
  - exact Hstore.
  - eapply tm_cont_struct_ty_cons.
    + exact Hcont.
    + exact (tm_frame_struct_ty_let U S0 t Hbody).
  - exact Hu.
Qed.

(** Store-preserving removal of a checked ascription. *)
Theorem PreciseStructPreserve_ascribe {n : nat} {G : Ctx n}
    {s : Store n} {K : Tm_Cont n} {t : Tm n} {A T : Ty n}
    (H : State_PreciseStructTy G
      (mk_state s K (tm_typed t A)) T) :
    PreciseStructPreserve G (mk_state s K t) T.
Proof.
  destruct H as [S0 Hstore Hcont Hterm].
  apply precise_struct_preserve_same.
  eapply state_precise_struct_ty_ok.
  - exact Hstore.
  - exact Hcont.
  - exact (proj1 (Tm_StructCheck_typed_inv Hterm)).
Qed.

(** Store-preserving opening of a suspended let body. *)
Theorem PreciseStructPreserve_rename {n : nat} {G : Ctx n}
    {s : Store n} {K : Tm_Cont n} {t : Tm (S n)}
    {x : Fin.t n} {T : Ty n}
    (H : State_PreciseStructTy G
      (mk_state s (cons (tm_frame_let t) K)
        (tm_path (path_var x))) T) :
    PreciseStructPreserve G (mk_state s K (Tm_open t x)) T.
Proof.
  destruct H as [Input Hstore Hcont Harg].
  inversion Hcont as [|S0 U T0 F Ktail Hrest Hframe]; subst.
  inversion Hframe as [Input0 Result body Hbody]; subst.
  pose proof (Tm_StructCheck_open_var_of_path_term Hbody
    (Path_RuntimeEq_isEquivCongr s) Harg) as Hopened.
  unfold Ty_weaken in Hopened.
  rewrite Ty_rename_rename, FinFun.openAt_weaken, Ty_rename_id in Hopened.
  apply precise_struct_preserve_same.
  eapply state_precise_struct_ty_ok; eassumption.
Qed.

(** Beta reduction leaves the exact store unchanged, conditional on the
    observation-sized precise function pushback. *)
Theorem PreciseStructPreserve_app {n : nat} {G : Ctx n}
    {s : Store n} {K : Tm_Cont n} {p q : Path n}
    {x y : Fin.t n} {A : Ty n} {body : Tm (S n)} {T : Ty n}
    (Hpush : Store_StructPreciseFunctionPushback G s)
    (Hp : Path_reduce p s x) (Hq : Path_reduce q s y)
    (Hbind : Store_Binds s x (tm_abs A body))
    (H : State_PreciseStructTy G
      (mk_state s K (tm_app p q)) T) :
    PreciseStructPreserve G (mk_state s K (Tm_open body y)) T.
Proof.
  destruct H as [Input Hstore Hcont Happ].
  destruct (Tm_StructCheck_app_inversion Happ)
    as (S0 & U & Hfun & Harg & post).
  pose proof
    (Store_StructTy_open_application_of_preciseFunctionReflection
      (Store_StructPreciseTy_toStructTy Hstore)
      (Store_StructPreciseFunctionPushback_to_preciseFunctionReflection
        Hpush)
      Hp Hq Hbind Hfun Harg) as Hopened.
  apply precise_struct_preserve_same.
  eapply state_precise_struct_ty_ok.
  - exact Hstore.
  - exact Hcont.
  - exact (post (Tm_open body y) Hopened).
Qed.

(** Exact-store beta preservation through the smaller exact function
    pushback interface. *)
Theorem PreciseStructPreserve_app_of_exactPushback {n : nat}
    {G : Ctx n} {s : Store n} {K : Tm_Cont n} {p q : Path n}
    {x y : Fin.t n} {A : Ty n} {body : Tm (S n)} {T : Ty n}
    (Hpush : Store_StructExactFunctionPushback G s)
    (Hp : Path_reduce p s x) (Hq : Path_reduce q s y)
    (Hbind : Store_Binds s x (tm_abs A body))
    (H : State_PreciseStructTy G
      (mk_state s K (tm_app p q)) T) :
    PreciseStructPreserve G (mk_state s K (Tm_open body y)) T.
Proof.
  destruct H as [Input Hstore Hcont Happ].
  destruct (Tm_StructCheck_app_inversion Happ)
    as (S0 & U & Hfun & Harg & post).
  pose proof
    (Store_StructPreciseTy_open_application_of_exactPushback
      Hstore Hpush Hp Hq Hbind Hfun Harg) as Hopened.
  apply precise_struct_preserve_same.
  eapply state_precise_struct_ty_ok.
  - exact Hstore.
  - exact Hcont.
  - exact (post (Tm_open body y) Hopened).
Qed.

(** Every transition preserves the exact invariant, conditional on the
    observation-sized function pushback used by beta reduction. *)
Theorem State_Step_precise_preservation {n m : nat} {G : Ctx n}
    {source : State n} {target : State m} {T : Ty n}
    (Hpush : Store_StructPreciseFunctionPushback G
      (state_store source))
    (step : State_Step source target)
    (H : State_PreciseStructTy G source T) :
    PreciseStructPreserve G target T.
Proof.
  destruct step.
  - exact (PreciseStructPreserve_app Hpush H0 H1 H2 H).
  - exact (PreciseStructPreserve_path H0 H).
  - exact (PreciseStructPreserve_let_push H).
  - exact (PreciseStructPreserve_rename H).
  - exact (PreciseStructPreserve_lift Hv H).
  - exact (PreciseStructPreserve_ascribe H).
Qed.

(** Exact-store specialization, conditional only on exact function
    pushback. *)
Theorem State_Step_precise_preservation_of_exactPushback {n m : nat}
    {G : Ctx n} {source : State n} {target : State m} {T : Ty n}
    (Hpush : Store_StructExactFunctionPushback G (state_store source))
    (step : State_Step source target)
    (H : State_PreciseStructTy G source T) :
    PreciseStructPreserve G target T.
Proof.
  destruct step.
  - exact (PreciseStructPreserve_app_of_exactPushback
      Hpush H0 H1 H2 H).
  - exact (PreciseStructPreserve_path H0 H).
  - exact (PreciseStructPreserve_let_push H).
  - exact (PreciseStructPreserve_rename H).
  - exact (PreciseStructPreserve_lift Hv H).
  - exact (PreciseStructPreserve_ascribe H).
Qed.

Print Assumptions PreciseStructPreserve_path.
Print Assumptions PreciseStructPreserve_let_push.
Print Assumptions PreciseStructPreserve_ascribe.
Print Assumptions PreciseStructPreserve_rename.
Print Assumptions PreciseStructPreserve_app.
Print Assumptions PreciseStructPreserve_app_of_exactPushback.
Print Assumptions State_Step_precise_preservation.
Print Assumptions State_Step_precise_preservation_of_exactPushback.
