From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store Cont State Machine Progress
  StructuralMachineInvariant StructuralPreciseStore
  StructuralPreciseCanonical StructuralProgress.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Binding-oriented function reflection follows from the corresponding
    store-binding conclusion once the occupant is supplied. *)
Theorem Store_FunctionCheckReflection_to_funCheckReflection {n : nat}
    {G : Ctx n} {s : Store n}
    (H : Store_FunctionCheckReflection G s) :
    Store_FunCheckReflection G s.
Proof.
  intros x S0 U v Hbind Hfun.
  destruct (H x S0 U Hfun) as (A & body & Habs).
  pose proof (Store_Binds_unique Hbind Habs) as E. subst v.
  exists A, body. reflexivity.
Qed.

(** The two exact concrete-head facts form the operational package used by
    structural progress. *)
Theorem Store_HeadCheckReflection_to_structOperational {n : nat}
    {G : Ctx n} {s : Store n}
    (H : Store_HeadCheckReflection G s) :
    Store_StructOperational G s.
Proof.
  constructor.
  - exact (store_head_check_reflection_pair H).
  - exact (Store_FunctionCheckReflection_to_funCheckReflection
      (store_head_check_reflection_function H)).
Qed.

(** Exact-state progress factored through its concrete-head input. *)
Theorem State_PreciseStructTy_progress_of_headCheckReflection {n : nat}
    {G : Ctx n} {s : Store n} {K : Tm_Cont n} {t : Tm n}
    {T : Ty n} (Hhead : Store_HeadCheckReflection G s)
    (H : State_PreciseStructTy G (mk_state s K t) T) :
    State_Progress (mk_state s K t).
Proof.
  exact (State_StructTy_progress
    (Store_HeadCheckReflection_to_structOperational Hhead)
    (State_PreciseStructTy_toStructTy H)).
Qed.

(** Exact store typing plus singleton-head pushback discharges both
    reflection clauses used by structural progress. *)
Theorem Store_StructPreciseTy_structOperational_of_singletonHeadPushback
    {n : nat} {G : Ctx n} {s : Store n}
    (Hstore : Store_StructPreciseTy G s)
    (Hpush : Store_StructPreciseSingletonHeadPushback G s) :
    Store_StructOperational G s.
Proof.
  apply Store_HeadCheckReflection_to_structOperational.
  exact (Store_StructPreciseTy_headCheckReflection_of_singletonPushback
    Hstore Hpush).
Qed.

(** Full progress for a precise structural state, conditional on exact
    head inversion for proper singleton subtyping. *)
Theorem State_PreciseStructTy_progress {n : nat} {G : Ctx n}
    {s : Store n} {K : Tm_Cont n} {t : Tm n} {T : Ty n}
    (Hpush : Store_StructPreciseSingletonHeadPushback G s)
    (H : State_PreciseStructTy G (mk_state s K t) T) :
    State_Progress (mk_state s K t).
Proof.
  destruct H as [Input Hstore Hcont Hterm].
  eapply (@State_StructTy_progress n G s K t T).
  - exact
      (Store_StructPreciseTy_structOperational_of_singletonHeadPushback
        Hstore Hpush).
  - eapply state_struct_ty_ok.
    + exact (Store_StructPreciseTy_toStructTy Hstore).
    + exact Hcont.
    + exact Hterm.
Qed.

Print Assumptions Store_FunctionCheckReflection_to_funCheckReflection.
Print Assumptions Store_HeadCheckReflection_to_structOperational.
Print Assumptions State_PreciseStructTy_progress_of_headCheckReflection.
Print Assumptions
  Store_StructPreciseTy_structOperational_of_singletonHeadPushback.
Print Assumptions State_PreciseStructTy_progress.
