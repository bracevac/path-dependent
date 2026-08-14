From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PathDependent.LambdaPCC Require Import
  FinFun Syntax Context Typing Runtime RuntimeEquality Valuation
  CaptureEvidence CaptureAction CaptureStatic CaptureCoercion CaptureTyping
  CaptureWeakening CaptureInterpretation CaptureAllocation.

Import ListNotations.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.
Unset Equations Derive Eliminator.

Derive NoConfusionHom for State.

(** Progress for a term carrying joint type-and-use evidence. *)
Theorem cap_term_evidence_progress {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {term : Tm n} {T : Ty n} {C : CaptureSet n}
    (evidence : CapTermEvidence valid term T C) (cont : TmCont n) :
    StateProgress (StateMk sigma cont term).
Proof.
  destruct evidence.
  - destruct p as [variable|receiver|receiver label].
    + exact (state_progress_path_var sigma cont f).
    + eapply Progress_step. eapply Step_path.
      * exact p0.
      * intro impossible. inversion impossible.
    + eapply Progress_step. eapply Step_path.
      * exact p0.
      * intro impossible. inversion impossible.
  - exact (state_progress_value sigma cont (cap_value_is_value c)).
  - pose (function_view := cap_term_evidence_path_view evidence1).
    pose (argument_view := cap_term_evidence_path_view evidence2).
    pose (possible_function := cap_term_evidence_path_location_at evidence1
      (cap_path_view_resolution function_view)).
    dependent elimination possible_function.
    eapply Progress_step. eapply Step_app.
    + exact (cap_path_view_resolution function_view).
    + exact (cap_path_view_resolution argument_view).
    + exact (cap_lookup_binds c3).
  - eapply Progress_step. exact Step_let_push.
Qed.

(** Progress for the complete capture-aware machine invariant. *)
Theorem cap_state_evidence_progress {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {state : State n} {T : Ty n} {C : CaptureSet n}
    (evidence : CapStateEvidence valid state T C) : StateProgress state.
Proof.
  destruct evidence.
  exact (cap_term_evidence_progress c0 cont).
Qed.

(** Opening a closure's introduction-use set substitutes the concrete
    argument path for the formal root. *)
Lemma capture_open_body_use {n : nat} (Q : CaptureSet n) (y : Fin n) :
    capture_open
      (CUnion (capture_weaken Q) (CSingleton (PVar FZ))) (PVar y) =
    CUnion Q (CSingleton (PVar y)).
Proof.
  change (CUnion (capture_open (capture_weaken Q) (PVar y))
    (CSingleton (PVar y)) = CUnion Q (CSingleton (PVar y))).
  now rewrite capture_weaken_open.
Qed.

Local Definition tm_abs_body {n : nat} (term : Tm n) :
    option (Tm (S n)) :=
  match term with
  | TmAbs _ body => Some body
  | _ => None
  end.

(** Reduce a semantically typed application, folding the closure capture set
    through the function path and aliasing the formal argument with the
    concrete argument path. *)
Definition cap_term_evidence_beta {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {p q : Path n} {Cf Cp Cq E : CaptureSet n}
    {S0 T : Ty n} {U : Ty (S n)} {f y : Fin n}
    {A : Ty n} {body : Tm (S n)}
    (function : CapTermEvidence valid (TmPath p)
      (TyCapt Cf (ShFun S0 U)) Cp)
    (argument : CapTermEvidence valid (TmPath q) S0 Cq)
    (suffix : CapTyCoercion world (ty_open U q) T)
    (application_coverage : CapRelation world (CUnion Cp Cq) E)
    (function_resolution : PathResolve sigma p (RLoc f))
    (argument_resolution : PathResolve sigma q (RLoc y))
    (binding : StoreBinds sigma f (TmAbs A body)) :
    CapTermEvidence valid (tm_open body y) T E.
Proof.
  pose (function_view := cap_term_evidence_path_view function).
  pose (argument_view := cap_term_evidence_path_view argument).
  pose (possible_function := cap_term_evidence_path_location_at
    function function_resolution).
  pose (possible_argument := cap_term_evidence_path_location_at
    argument argument_resolution).
  pose (argument_variable_resolution := PR_var sigma y).
  pose (application_codomain := U).
  pose (application_world := world).
  dependent elimination possible_function.
  match goal with
  | lookup : CapLookup ?stored_world _ (TmAbs ?stored_domain ?stored_body) _,
    closure : CapBody ?stored_world ?stored_domain ?stored_body
      ?stored_result _,
    input : CapTyCoercion ?stored_world ?argument_type ?stored_domain,
    output : CapDeferredCoercion ?stored_world ?argument_type
      ?stored_result ?codomain |- _ =>
      pose (stored_lookup := lookup);
      pose (stored_closure := closure);
      pose (stored_input := input);
      pose (stored_output := output)
  end.
  pose proof (store_binds_unique (cap_lookup_binds stored_lookup) binding)
    as binding_equality.
  pose proof (f_equal tm_abs_body binding_equality) as body_equality.
  cbn [tm_abs_body] in body_equality.
  injection body_equality as body_equality. subst body.
  pose (applied := cap_body_apply (valid := valid) stored_closure
    (cap_ty_coercion_action_location stored_input possible_argument)).
  pose (instantiated := cap_term_evidence_cast_type applied
    (cap_deferred_coercion_instantiate stored_output possible_argument)).
  pose (paths := PREq_symm
    (PREq_coresolve argument_resolution argument_variable_resolution)).
  pose (relocate := @CTC_runtime _ _ application_world _ _
    (TRC_replace application_codomain paths)).
  pose (function_use := cap_relation_comp
    (CR_fold function_resolution stored_lookup)
    (cap_path_view_coverage function_view)).
  pose (argument_use := cap_relation_comp
    (CR_alias argument_resolution argument_variable_resolution)
    (cap_path_view_coverage argument_view)).
  pose (body_use := CR_union_elim
    (cap_relation_comp function_use CR_union_left)
    (cap_relation_comp argument_use CR_union_right)).
  apply (cap_term_evidence_cast_use
    (cap_term_evidence_cast_type instantiated
      (cap_ty_coercion_comp relocate suffix))).
  rewrite capture_open_body_use.
  exact (cap_relation_comp body_use application_coverage).
Defined.

(** An application event extracted from an application transition. *)
Inductive CapApplicationEvent :
    forall {n m : nat} {source : State n} {target : State m},
      StateStep source target -> Path n -> Path n -> Prop :=
| CSSAE_app {n : nat} {sigma : Store n} {p q : Path n}
    {f y : Fin n} {A : Ty n} {body : Tm (S n)} {cont : TmCont n}
    (function : PathResolve sigma p (RLoc f))
    (argument : PathResolve sigma q (RLoc y))
    (binding : StoreBinds sigma f (TmAbs A body)) :
    CapApplicationEvent
      (Step_app (cont := cont) function argument binding) p q.

(** Both paths inspected by an application transition are covered by the
    use set of its runtime term. *)
Theorem cap_term_evidence_covers_application {n m : nat}
    {sigma : Store n} {world : CapWorld sigma}
    {valid : CapWorldValid world} {cont : TmCont n} {term : Tm n}
    {target : State m} {T : Ty n} {C : CaptureSet n} {p q : Path n}
    (evidence : CapTermEvidence valid term T C)
    (step : StateStep (StateMk sigma cont term) target)
    (event : CapApplicationEvent step p q) :
    inhabited
      (CapRelation world (CSingleton p) C *
        CapRelation world (CSingleton q) C).
Proof.
  dependent elimination event.
  pose (view := cap_term_evidence_app_view evidence).
  pose (function_view := cap_term_evidence_path_view
    (cap_app_view_function view)).
  pose (argument_view := cap_term_evidence_path_view
    (cap_app_view_argument view)).
  exact (inhabits
    (cap_relation_comp (cap_path_view_coverage function_view)
      (cap_relation_comp CR_union_left (cap_app_view_coverage view)),
    cap_relation_comp (cap_path_view_coverage argument_view)
      (cap_relation_comp CR_union_right (cap_app_view_coverage view)))).
Qed.

(** Application operands are covered by the use set of the complete machine
    invariant, including its continuation. *)
Theorem cap_state_evidence_covers_application {n m : nat}
    {source : State n} {target : State m}
    {world : CapWorld (state_store source)} {valid : CapWorldValid world}
    {T : Ty n} {C : CaptureSet n} {p q : Path n}
    (evidence : CapStateEvidence valid source T C)
    (step : StateStep source target)
    (event : CapApplicationEvent step p q) :
    inhabited
      (CapRelation world (CSingleton p) C *
        CapRelation world (CSingleton q) C).
Proof.
  destruct source as [sigma cont runtime_term].
  dependent elimination evidence.
  destruct (cap_term_evidence_covers_application c0 event)
    as [[function_coverage argument_coverage]].
  exact (inhabits
    (cap_relation_comp function_coverage
      (cap_cont_evidence_input_coverage c),
    cap_relation_comp argument_coverage
      (cap_cont_evidence_input_coverage c))).
Qed.

(** A type transported through zero or more fresh store allocations. *)
Inductive CapTyExtends : forall {n m : nat}, Ty n -> Ty m -> Prop :=
| CapTyExtends_refl {n : nat} {T : Ty n} : CapTyExtends T T
| CapTyExtends_alloc {n m : nat} {S0 : Ty n} {T : Ty m} :
    CapTyExtends S0 T -> CapTyExtends S0 (ty_weaken T).

Arguments CapTyExtends_refl {n T}.
Arguments CapTyExtends_alloc {n m S0 T} _.

Theorem cap_ty_extends_trans {n m l : nat} {S0 : Ty n} {T : Ty m}
    {U : Ty l} (first : CapTyExtends S0 T) (second : CapTyExtends T U) :
    CapTyExtends S0 U.
Proof.
  induction second.
  - exact first.
  - exact (CapTyExtends_alloc (IHsecond first)).
Qed.

(** A capture set transported through zero or more allocations. *)
Inductive CapCaptureSetExtends :
    forall {n m : nat}, CaptureSet n -> CaptureSet m -> Prop :=
| CapCaptureSetExtends_refl {n : nat} {C : CaptureSet n} :
    CapCaptureSetExtends C C
| CapCaptureSetExtends_alloc {n m : nat} {C : CaptureSet n}
    {D : CaptureSet m} :
    CapCaptureSetExtends C D ->
    CapCaptureSetExtends C (capture_weaken D).

Arguments CapCaptureSetExtends_refl {n C}.
Arguments CapCaptureSetExtends_alloc {n m C D} _.

Theorem cap_capture_set_extends_trans {n m l : nat}
    {C : CaptureSet n} {D : CaptureSet m} {E : CaptureSet l}
    (first : CapCaptureSetExtends C D)
    (second : CapCaptureSetExtends D E) : CapCaptureSetExtends C E.
Proof.
  induction second.
  - exact first.
  - exact (CapCaptureSetExtends_alloc (IHsecond first)).
Qed.

(** One transition preserves joint state evidence.  Allocation extends the
    world and weakens both the final type and use set once. *)
Theorem cap_state_evidence_preservation {n m : nat}
    {source : State n} {target : State m}
    {world : CapWorld (state_store source)} {valid : CapWorldValid world}
    {T : Ty n} {C : CaptureSet n}
    (evidence : CapStateEvidence valid source T C)
    (step : StateStep source target) :
    exists (target_world : CapWorld (state_store target))
      (target_valid : CapWorldValid target_world)
      (U : Ty m) (D : CaptureSet m),
      CapTyExtends T U /\ CapCaptureSetExtends C D /\
        inhabited (CapStateEvidence target_valid target U D).
Proof.
  destruct source as [sigma cont term].
  pose (source_store := sigma).
  pose (source_world := world).
  pose (source_valid := valid).
  pose (final_type := T).
  pose (final_use := C).
  dependent elimination evidence.
  dependent elimination step.
  - match goal with
    | function_resolution : PathResolve _ ?function_path (RLoc ?function_loc),
      argument_resolution : PathResolve _ ?argument_path (RLoc ?argument_loc),
      binding : StoreBinds _ ?function_loc (TmAbs _ _) |- _ =>
        pose (step_function_resolution := function_resolution);
        pose (step_argument_resolution := argument_resolution);
        pose (step_function_binding := binding)
    end.
    pose (view := cap_term_evidence_app_view c0).
    pose (reduced := cap_term_evidence_beta
      (cap_app_view_function view) (cap_app_view_argument view)
      (cap_app_view_suffix view) (cap_app_view_coverage view)
      step_function_resolution step_argument_resolution
      step_function_binding).
    exists source_world, source_valid, final_type, final_use.
    split; [exact CapTyExtends_refl|].
    split; [exact CapCaptureSetExtends_refl|].
    exact (inhabits (CSE_ok c reduced)).
  - match goal with
    | resolution : PathResolve _ ?runtime_path (RLoc ?location) |- _ =>
        pose (step_path := runtime_path);
        pose (step_location := location);
        pose (step_resolution := resolution)
    end.
    pose (view := cap_term_evidence_path_view c0).
    pose (paths := PREq_coresolve
      (PR_var source_store step_location) step_resolution).
    pose (back := @CTC_runtime _ source_store source_world _ _
      (TRC_capt (CRC_singleton paths) (SRC_single paths))).
    pose (uses := cap_relation_comp
      (CR_alias step_resolution (PR_var source_store step_location))
      (cap_path_view_coverage view)).
    exists source_world, source_valid, final_type, final_use.
    split; [exact CapTyExtends_refl|].
    split; [exact CapCaptureSetExtends_refl|].
    exact (inhabits (CSE_ok c
      (CTE_path (PR_var source_store step_location)
        (cap_ty_coercion_comp back (cap_path_view_suffix view)) uses))).
  - pose (view := cap_term_evidence_let_view c0).
    pose (current_coverage := cap_relation_comp
      (cap_let_view_coverage view) (cap_cont_evidence_input_coverage c)).
    exists source_world, source_valid, final_type, final_use.
    split; [exact CapTyExtends_refl|].
    split; [exact CapCaptureSetExtends_refl|].
    exact (inhabits (CSE_ok
      (CCE_cons c (cap_let_view_closure view) (cap_let_view_suffix view)
        current_coverage (cap_let_view_coverage view))
      (cap_let_view_bound view))).
  - match goal with
    | return_term : CapTermEvidence _ (TmPath (PVar ?location)) _ _ |- _ =>
        pose (return_location := location)
    end.
    dependent elimination c.
    pose (argument := cap_term_evidence_path_location_at c0
      (PR_var source_store return_location)).
    pose (resumed := cap_body_apply (valid := source_valid) c1 argument).
    rewrite ty_weaken_open, capture_weaken_open in resumed.
    exists source_world, source_valid, final_type, final_use.
    split; [exact CapTyExtends_refl|].
    split; [exact CapCaptureSetExtends_refl|].
    exact (inhabits (CSE_ok c
      (cap_term_evidence_cast_use
        (cap_term_evidence_cast_type resumed c2) c4))).
  - dependent elimination c.
    destruct (cap_term_evidence_nonempty_value_view c0 is_value)
      as [value_view].
    pose (value := cap_value_view_value value_view).
    pose (summary := cap_value_to_exact value).
    pose (target_world := CapWorld_val source_world summary
      (is_value := is_value)).
    pose (target_valid := cap_world_valid_extend
      (exact := summary) (is_value := is_value) source_valid value).
    pose (resumed := cap_body_allocate (valid := source_valid)
      c1 value is_value).
    pose (target_term := cap_term_evidence_cast_use
      (cap_term_evidence_cast_type resumed
        (cap_ty_coercion_weaken c2 summary is_value))
      (cap_relation_weaken c4 summary is_value)).
    exists target_world, target_valid, (ty_weaken final_type),
      (capture_weaken final_use).
    split; [exact (CapTyExtends_alloc CapTyExtends_refl)|].
    split; [exact (CapCaptureSetExtends_alloc
      CapCaptureSetExtends_refl)|].
    exact (inhabits (CSE_ok
      (cap_cont_evidence_weaken c value is_value) target_term)).
Qed.

Print Assumptions cap_term_evidence_progress.
Print Assumptions cap_state_evidence_progress.
Print Assumptions cap_term_evidence_beta.
Print Assumptions cap_term_evidence_covers_application.
Print Assumptions cap_state_evidence_covers_application.
Print Assumptions cap_ty_extends_trans.
Print Assumptions cap_capture_set_extends_trans.
Print Assumptions cap_state_evidence_preservation.
