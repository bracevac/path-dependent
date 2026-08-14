From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store Cont State Machine Progress
  RuntimeConversion StructuralRuntimeTyping StructuralTermTyping
  StructuralMachineInvariant StructuralPreciseStore
  StructuralPreciseSafety CanonicalForms.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Initial machine configuration for a closed term. *)
Definition State_initial (t : Tm 0) : State 0 :=
  mk_state store_empty nil t.

(** Source typing embeds into the exact structural invariant at the empty
    store and continuation. *)
Theorem Tm_Ty_initial_preciseStructTy {t : Tm 0} {T : Ty 0}
    (Ht : Tm_Ty ctx_nil t T) :
    State_PreciseStructTy ctx_nil (State_initial t) T.
Proof.
  unfold State_initial.
  eapply state_precise_struct_ty_ok.
  - exact store_struct_precise_ty_empty.
  - apply tm_cont_struct_ty_hole.
    apply tau_struct_sub_refl.
  - exact (Tm_StructCheck_of_source Ht (Path_RuntimeEq store_empty)).
Qed.

(** A closed, well-typed source program is final or takes a preserving
    step. *)
Theorem Tm_Ty_closed_one_step_safety {t : Tm 0} {T : Ty 0}
    (Ht : Tm_Ty ctx_nil t T) :
    State_PreciseStructSafetyOutcome ctx_nil (State_initial t) T.
Proof.
  exact (State_PreciseStructTy_one_step_safety_of_laws
    Store_mappedPreciseStructSafetyLaws
    (Tm_Ty_initial_preciseStructTy Ht)).
Qed.

(** Initial-state progress. *)
Theorem Tm_Ty_closed_progress {t : Tm 0} {T : Ty 0}
    (Ht : Tm_Ty ctx_nil t T) : State_Progress (State_initial t).
Proof.
  exact (State_PreciseStructSafetyOutcome_progress
    (Tm_Ty_closed_one_step_safety Ht)).
Qed.

(** A single transition from a closed well-typed program has a precisely
    typed target at the same scope or one allocation extension. *)
Theorem Tm_Ty_closed_step_preservation {m : nat} {t : Tm 0}
    {T : Ty 0} {target : State m} (Ht : Tm_Ty ctx_nil t T)
    (Hstep : State_Step (State_initial t) target) :
    exists (D : Ctx m) (U : Ty m),
      State_PreciseStructExtension ctx_nil T D U /\
      State_PreciseStructTy D target U.
Proof.
  apply (State_PreciseSteps_preservation_of_laws
    Store_mappedPreciseStructSafetyLaws
    (state_precise_steps_tail (State_initial t) target target Hstep
      (state_precise_steps_refl target))).
  exact (Tm_Ty_initial_preciseStructTy Ht).
Qed.

(** Every finite execution preserves exact structural typing, with context
    growth made explicit. *)
Theorem Tm_Ty_closed_finite_preservation {m : nat} {t : Tm 0}
    {T : Ty 0} {target : State m} (Ht : Tm_Ty ctx_nil t T)
    (Hsteps : State_PreciseSteps (State_initial t) target) :
    exists (D : Ctx m) (U : Ty m),
      State_PreciseStructExtension ctx_nil T D U /\
      State_PreciseStructTy D target U.
Proof.
  exact (State_PreciseSteps_preservation_of_laws
    Store_mappedPreciseStructSafetyLaws Hsteps
    (Tm_Ty_initial_preciseStructTy Ht)).
Qed.

(** Preservation and progress at every finite execution endpoint. *)
Theorem Tm_Ty_closed_finite_safety {m : nat} {t : Tm 0}
    {T : Ty 0} {target : State m} (Ht : Tm_Ty ctx_nil t T)
    (Hsteps : State_PreciseSteps (State_initial t) target) :
    exists (D : Ctx m) (U : Ty m),
      State_PreciseStructExtension ctx_nil T D U /\
      State_PreciseStructTy D target U /\
      State_PreciseStructSafetyOutcome D target U.
Proof.
  exact (State_PreciseSteps_safety_of_laws
    Store_mappedPreciseStructSafetyLaws Hsteps
    (Tm_Ty_initial_preciseStructTy Ht)).
Qed.

(** No finite execution of a closed, well-typed source term ends stuck. *)
Theorem Tm_Ty_closed_type_safety {m : nat} {t : Tm 0}
    {T : Ty 0} {target : State m} (Ht : Tm_Ty ctx_nil t T)
    (Hsteps : State_PreciseSteps (State_initial t) target) :
    State_Progress target.
Proof.
  exact (State_PreciseSteps_nonstuck_of_laws
    Store_mappedPreciseStructSafetyLaws Hsteps
    (Tm_Ty_initial_preciseStructTy Ht)).
Qed.

Print Assumptions Tm_Ty_initial_preciseStructTy.
Print Assumptions Tm_Ty_closed_one_step_safety.
Print Assumptions Tm_Ty_closed_progress.
Print Assumptions Tm_Ty_closed_step_preservation.
Print Assumptions Tm_Ty_closed_finite_preservation.
Print Assumptions Tm_Ty_closed_finite_safety.
Print Assumptions Tm_Ty_closed_type_safety.
