From PathDependent.LambdaPCC Require Import
  FinFun Syntax Context Typing Runtime RuntimeEquality Valuation
  CaptureEvidence CaptureAction CaptureStatic CaptureCoercion
  CaptureTyping CaptureInterpretation CaptureAllocation
  CapturePreservation.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Initial joint type-and-use evidence for a closed source derivation. *)
Definition tm_ty_initial_evidence {term : Tm 0} {T : Ty 0}
    {C : CaptureSet 0} (code : TermTy CtxNil term T C) :
    CapStateEvidence CWV_empty (state_initial term) T C.
Proof.
  pose proof (cap_tm_ty_interpret code cap_environment_empty CWV_empty)
    as interpreted.
  rewrite tm_rename_id, ty_rename_id, capture_rename_id in interpreted.
  exact (CSE_ok CCE_hole interpreted).
Defined.

(** Joint semantic preservation iterated over a heterogeneous finite
    execution. *)
Theorem state_steps_preservation {n m : nat} {source : State n}
    {target : State m} {world : CapWorld (state_store source)}
    {valid : CapWorldValid world} {T : Ty n} {C : CaptureSet n}
    (steps : StateSteps source target)
    (evidence : CapStateEvidence valid source T C) :
    exists (target_world : CapWorld (state_store target))
      (target_valid : CapWorldValid target_world)
      (U : Ty m) (D : CaptureSet m),
      CapTyExtends T U /\ CapCaptureSetExtends C D /\
        inhabited (CapStateEvidence target_valid target U D).
Proof.
  revert world valid T C evidence.
  induction steps as
    [n0 source0
    |n0 l0 m0 source0 middle target0 step rest IH];
    intros world valid T C evidence.
  - exists world, valid, T, C. repeat split.
    + exact CapTyExtends_refl.
    + exact CapCaptureSetExtends_refl.
    + exact evidence.
  - destruct (cap_state_evidence_preservation evidence step)
      as (middle_world & middle_valid & U & D & type_extension &
        capture_extension & [middle_evidence]).
    destruct (IH middle_world middle_valid U D middle_evidence)
      as (target_world & target_valid & V & E & rest_type_extension &
        rest_capture_extension & [final_evidence]).
    exists target_world, target_valid, V, E. repeat split.
    + exact (cap_ty_extends_trans type_extension rest_type_extension).
    + exact (cap_capture_set_extends_trans
        capture_extension rest_capture_extension).
    + exact final_evidence.
Qed.

(** Initial progress for a closed, well-typed term under the joint
    invariant. *)
Theorem tm_ty_closed_progress {term : Tm 0} {T : Ty 0}
    {C : CaptureSet 0} (typing : TermTy CtxNil term T C) :
    StateProgress (state_initial term).
Proof.
  exact (cap_state_evidence_progress (tm_ty_initial_evidence typing)).
Qed.

(** Every finite endpoint retains joint type-and-use evidence modulo
    allocation weakening. *)
Theorem tm_ty_closed_finite_preservation {m : nat} {term : Tm 0}
    {T : Ty 0} {C : CaptureSet 0} {target : State m}
    (typing : TermTy CtxNil term T C)
    (steps : StateSteps (state_initial term) target) :
    exists (target_world : CapWorld (state_store target))
      (target_valid : CapWorldValid target_world)
      (U : Ty m) (D : CaptureSet m),
      CapTyExtends T U /\ CapCaptureSetExtends C D /\
        inhabited (CapStateEvidence target_valid target U D).
Proof.
  exact (state_steps_preservation steps (tm_ty_initial_evidence typing)).
Qed.

(** A finite execution of a closed, well-typed term cannot end stuck. *)
Theorem tm_ty_closed_type_safety {m : nat} {term : Tm 0}
    {T : Ty 0} {C : CaptureSet 0} {target : State m}
    (typing : TermTy CtxNil term T C)
    (steps : StateSteps (state_initial term) target) :
    StateProgress target.
Proof.
  destruct (tm_ty_closed_finite_preservation typing steps)
    as (target_world & target_valid & U & D & type_extension &
      capture_extension & [evidence]).
  exact (cap_state_evidence_progress evidence).
Qed.

Print Assumptions tm_ty_initial_evidence.
Print Assumptions state_steps_preservation.
Print Assumptions tm_ty_closed_progress.
Print Assumptions tm_ty_closed_finite_preservation.
Print Assumptions tm_ty_closed_type_safety.
