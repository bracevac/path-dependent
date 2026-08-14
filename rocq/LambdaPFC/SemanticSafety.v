From PathDependent.LambdaPFC Require Import
  FinFun Syntax Context Typing Runtime SemanticEvidence SemanticTyping
  SemanticFundamental SemanticProgress SemanticPreservation.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Initial-state evidence obtained from a source typing derivation. *)
Definition tm_ty_initial_evidence {term : Tm 0} {T : Ty 0}
    (code : TmTy CtxNil term T) :
    StateEvidence (state_initial term) T.
Proof.
  pose proof (tm_ty_interpret code environment_empty) as interpreted.
  rewrite tm_rename_id, ty_rename_id in interpreted.
  exact (StateEv_ok ContEv_hole interpreted).
Defined.

(** Semantic preservation iterated over a finite execution. *)
Theorem state_steps_preservation {n m : nat} {source : State n}
    {target : State m} {T : Ty n} (steps : StateSteps source target)
    (evidence : StateEvidence source T) :
    exists U : Ty m,
      TyExtends T U /\ inhabited (StateEvidence target U).
Proof.
  revert T evidence.
  induction steps as
    [n0 source0
    |n0 l0 m0 source0 middle target0 step rest IH];
    intros T evidence.
  - exists T. split.
    + exact TyExtends_refl.
    + exact (inhabits evidence).
  - destruct (state_evidence_preservation evidence step)
      as [U [extension [middle_evidence]]].
    destruct (IH U middle_evidence)
      as [V [rest_extension final_evidence]].
    exists V. split.
    + exact (ty_extends_trans extension rest_extension).
    + exact final_evidence.
Qed.

(** Initial progress for a closed, well-typed term. *)
Theorem tm_ty_closed_progress {term : Tm 0} {T : Ty 0}
    (typing : TmTy CtxNil term T) :
    StateProgress (state_initial term).
Proof.
  exact (state_evidence_progress (tm_ty_initial_evidence typing)).
Qed.

(** Every state reached by a finite execution retains semantic typing modulo
    allocation weakening. *)
Theorem tm_ty_closed_finite_preservation {m : nat} {term : Tm 0}
    {T : Ty 0} {target : State m} (typing : TmTy CtxNil term T)
    (steps : StateSteps (state_initial term) target) :
    exists U : Ty m,
      TyExtends T U /\ inhabited (StateEvidence target U).
Proof.
  exact (state_steps_preservation steps (tm_ty_initial_evidence typing)).
Qed.

(** A finite execution of a closed, well-typed term cannot end stuck. *)
Theorem tm_ty_closed_type_safety {m : nat} {term : Tm 0}
    {T : Ty 0} {target : State m} (typing : TmTy CtxNil term T)
    (steps : StateSteps (state_initial term) target) :
    StateProgress target.
Proof.
  destruct (tm_ty_closed_finite_preservation typing steps)
    as [U [extension [evidence]]].
  exact (state_evidence_progress evidence).
Qed.

Print Assumptions tm_ty_initial_evidence.
Print Assumptions state_steps_preservation.
Print Assumptions tm_ty_closed_progress.
Print Assumptions tm_ty_closed_finite_preservation.
Print Assumptions tm_ty_closed_type_safety.
