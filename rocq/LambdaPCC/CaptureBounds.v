From Equations Require Import Equations.
From Stdlib Require Import Lists.List.
From PathDependent.LambdaPCC Require Import
  FinFun Syntax Context Typing Runtime RuntimeEquality Valuation
  CaptureEvidence CaptureAction CaptureStatic CaptureCoercion CaptureTyping
  CaptureWeakening CaptureInterpretation CaptureAllocation
  CapturePreservation CaptureSafety.

Import ListNotations.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.
Unset Equations Derive Eliminator.

Derive NoConfusionHom for State.

(** The capture set assigned to a value at introduction is below the capture
    set of its assigned type. *)
Definition cap_value_capture_relation {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {v : Tm n} {T : Ty n}
    {Q : CaptureSet n} (value : CapValue world v T Q) :
    CapRelation world Q (ty_capture_set T).
Proof.
  destruct value.
  - exact (cap_ty_coercion_capture_relation c0).
  - exact (cap_ty_coercion_capture_relation c).
  - exact (cap_ty_coercion_capture_relation c).
  - exact (cap_ty_coercion_capture_relation c).
Defined.

(** The value returned by a final machine state, either directly or through
    the location in the final variable path. *)
Inductive CapStateReturns : forall {n : nat}, State n -> Tm n -> Prop :=
| CSR_value {n : nat} {sigma : Store n} {v : Tm n} :
    Tm_IsValue v -> CapStateReturns (StateMk sigma [] v) v
| CSR_location {n : nat} {sigma : Store n} {x : Fin n} {v : Tm n} :
    StoreBinds sigma x v ->
    CapStateReturns (StateMk sigma [] (TmPath (PVar x))) v.

(** A returned value together with its assigned capture-set bound. *)
Record CapFinalCapture {n : nat} {state : State n}
    {world : CapWorld (state_store state)} (valid : CapWorldValid world)
    (T : Ty n) : Type := {
  cap_final_value_term : Tm n;
  cap_final_value_type : Ty n;
  cap_final_assigned_capture_set : CaptureSet n;
  cap_final_returns : CapStateReturns state cap_final_value_term;
  cap_final_value : CapValue world cap_final_value_term
    cap_final_value_type cap_final_assigned_capture_set;
  cap_final_subcapture : CapRelation world cap_final_assigned_capture_set
    (ty_capture_set T)
}.

(** A final state has a returned value whose assigned capture set is below
    the capture set of the state's result type. *)
Theorem cap_state_evidence_returned_capture_bound {n : nat}
    {state : State n} {world : CapWorld (state_store state)}
    {valid : CapWorldValid world} {T : Ty n} {C : CaptureSet n}
    (evidence : CapStateEvidence valid state T C)
    (final : StateIsFinal state) :
    inhabited (CapFinalCapture valid T).
Proof.
  destruct final.
  - dependent elimination evidence.
    dependent elimination c.
    pose (entry := cap_world_valid_entry valid x).
    pose (view := cap_term_evidence_path_view c0).
    refine (inhabits {| cap_final_value_term := cap_entry_term entry;
      cap_final_value_type := cap_entry_assigned_type entry;
      cap_final_assigned_capture_set :=
        cap_entry_assigned_capture_set entry;
      cap_final_returns := CSR_location
        (cap_lookup_binds (cap_entry_lookup entry));
      cap_final_value := cap_entry_value entry;
      cap_final_subcapture := CR_trans
        (CR_fold (PR_var _ x) (cap_entry_lookup entry))
        (cap_ty_coercion_capture_relation (cap_path_view_suffix view)) |}).
  - dependent elimination evidence.
    dependent elimination c.
    match goal with
    | is_value : Tm_IsValue ?returned |- _ =>
        destruct (cap_term_evidence_nonempty_value_view c0 is_value)
          as [view];
        refine (inhabits {| cap_final_value_term := returned;
          cap_final_value_type := T;
          cap_final_assigned_capture_set :=
            cap_value_view_assigned_capture_set view;
          cap_final_returns := CSR_value is_value;
          cap_final_value := cap_value_view_value view;
          cap_final_subcapture :=
            cap_value_capture_relation (cap_value_view_value view) |})
    end.
Qed.

(** Application coverage for a step reached by a closed finite execution.
    The bound is the source use set transported through preceding
    allocations. *)
Theorem tm_ty_closed_finite_application_coverage
    {term : Tm 0} {T : Ty 0} {C : CaptureSet 0}
    (typing : TermTy CtxNil term T C)
    {n m : nat} {source : State n} {target : State m}
    (steps : StateSteps (state_initial term) source)
    (step : StateStep source target) {p q : Path n}
    (event : CapApplicationEvent step p q) :
    exists (world : CapWorld (state_store source))
      (valid : CapWorldValid world) (U : Ty n) (D : CaptureSet n),
      CapTyExtends T U /\ CapCaptureSetExtends C D /\
        inhabited
          (CapStateEvidence valid source U D *
            (CapRelation world (CSingleton p) D *
              CapRelation world (CSingleton q) D)).
Proof.
  destruct (tm_ty_closed_finite_preservation typing steps)
    as (world & valid & U & D & type_extension & capture_extension &
      [evidence]).
  destruct (cap_state_evidence_covers_application evidence event)
    as [[function_coverage argument_coverage]].
  exists world, valid, U, D.
  split; [exact type_extension|].
  split; [exact capture_extension|].
  exact (inhabits
    (evidence, (function_coverage, argument_coverage))).
Qed.

(** Assigned capture-set bound for the value returned by a closed finite
    execution. *)
Theorem tm_ty_closed_finite_returned_capture_bound
    {term : Tm 0} {T : Ty 0} {C : CaptureSet 0}
    (typing : TermTy CtxNil term T C)
    {n : nat} {target : State n}
    (steps : StateSteps (state_initial term) target)
    (final : StateIsFinal target) :
    exists (world : CapWorld (state_store target))
      (valid : CapWorldValid world) (U : Ty n) (D : CaptureSet n),
      CapTyExtends T U /\ CapCaptureSetExtends C D /\
        inhabited (CapFinalCapture valid U).
Proof.
  destruct (tm_ty_closed_finite_preservation typing steps)
    as (world & valid & U & D & type_extension & capture_extension &
      [evidence]).
  exists world, valid, U, D.
  split; [exact type_extension|].
  split; [exact capture_extension|].
  exact (cap_state_evidence_returned_capture_bound evidence final).
Qed.

Print Assumptions cap_value_capture_relation.
Print Assumptions CapStateReturns.
Print Assumptions CapFinalCapture.
Print Assumptions cap_state_evidence_returned_capture_bound.
Print Assumptions tm_ty_closed_finite_application_coverage.
Print Assumptions tm_ty_closed_finite_returned_capture_bound.
