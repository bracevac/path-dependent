From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PathDependent.LambdaPFC Require Import
  FinFun Syntax Runtime SemanticEvidence SemanticTyping SemanticAction.

Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** A typed path resolving to [x] makes [x] a possible inhabitant of its
    advertised type. *)
Definition term_evidence_path_possible_at {n : nat} {sigma : Store n}
    {p : Path n} {T : Ty n} {x : Fin n}
    (evidence : TermEvidence sigma (TmPath p) T)
    (resolution : PathResolve p sigma (RefLoc x)) :
    StorePossible sigma x T.
Proof.
  destruct (term_evidence_path_view evidence)
    as [location stored_resolution suffix].
  pose proof (path_resolve_deterministic resolution stored_resolution)
    as location_equality.
  dependent elimination location_equality.
  exact (coercion_action_possible suffix (Possible_single resolution)).
Defined.

(** Every runtime term carrying semantic evidence is final or takes one
    machine step, independently of continuation typing. *)
Theorem term_evidence_progress {n : nat} {sigma : Store n}
    {term : Tm n} {T : Ty n}
    (evidence : TermEvidence sigma term T) (cont : TmCont n) :
    StateProgress (StateMk sigma cont term).
Proof.
  destruct evidence.
  - destruct p as [scope f|scope p|scope p a].
    + pose proof (path_resolve_deterministic p0 (Resolve_var f))
        as location_equality.
      inversion location_equality. exact (state_progress_path_var sigma cont f).
    + eapply Progress_step. eapply Step_path.
      * exact p0.
      * intro variable. inversion variable.
    + eapply Progress_step. eapply Step_path.
      * exact p0.
      * intro variable. inversion variable.
  - exact (state_progress_value sigma cont (v := v)
      (value_evidence_is_value v0)).
  - destruct (term_evidence_path_view evidence1)
      as [function_location function_resolution function_suffix].
    destruct (term_evidence_path_view evidence2)
      as [argument_location argument_resolution argument_suffix].
    pose proof (term_evidence_path_possible_at evidence1
      function_resolution) as possible_function.
    dependent elimination possible_function.
    eapply Progress_step. eapply Step_app.
    + exact function_resolution.
    + exact argument_resolution.
    + exact s.
  - eapply Progress_step. apply Step_let_push.
Qed.

(** The complete machine invariant entails progress. *)
Theorem state_evidence_progress {n : nat} {state : State n} {T : Ty n}
    (evidence : StateEvidence state T) : StateProgress state.
Proof.
  destruct evidence. exact (term_evidence_progress t cont).
Qed.

Print Assumptions term_evidence_path_possible_at.
Print Assumptions term_evidence_progress.
Print Assumptions state_evidence_progress.
