From Equations Require Import Equations.
From PathDependent.LambdaPCC Require Import
  FinFun Syntax Context Typing Runtime RuntimeEquality Valuation
  CaptureEvidence CaptureAction CaptureStatic CaptureCoercion CaptureTyping
  CaptureWeakening CaptureInterpretation.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.
Unset Equations Derive Eliminator.

(** Recover the source allocation summary stored by a suspended body. *)
Definition cap_body_to_exact {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {S0 : Ty n} {term : Tm (S n)}
    {T : Ty (S n)} {C : CaptureSet (S n)}
    (body : CapBody world S0 term T C) :
    CapExactBody sigma S0 term T C.
Proof.
  destruct body. exact (CEB_source t).
Defined.

(** Recover the introduction capture summary stored by value evidence. *)
Definition cap_value_to_exact {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {v : Tm n} {T : Ty n}
    {Q : CaptureSet n} (value : CapValue world v T Q) :
    CapExactValue sigma v Q.
Proof.
  destruct value.
  - exact (CEV_abs (cap_body_to_exact c)).
  - exact CEV_pair.
  - exact CEV_type_pair.
  - exact CEV_capture_pair.
Defined.

(** Joint lookup and value evidence for one location of a valid world. *)
Record CapWorldEntry {n : nat} {sigma : Store n} {world : CapWorld sigma}
    (valid : CapWorldValid world) (x : Fin n) : Type := {
  cap_entry_term : Tm n;
  cap_entry_assigned_capture_set : CaptureSet n;
  cap_entry_assigned_type : Ty n;
  cap_entry_lookup :
    CapLookup world x cap_entry_term cap_entry_assigned_capture_set;
  cap_entry_value : CapValue world cap_entry_term cap_entry_assigned_type
    cap_entry_assigned_capture_set
}.

(** Validity supplies a joint entry at every world location. *)
Fixpoint cap_world_valid_entry {n : nat} {sigma : Store n}
    {world : CapWorld sigma} (valid : CapWorldValid world)
    (x : Fin n) {struct valid} : CapWorldEntry valid x.
Proof.
  destruct valid.
  - exact (fin_elim0 x).
  - refine (fin_case (P := fun x => CapWorldEntry (CWV_val valid c) x)
      _ _ x).
    + exact {| cap_entry_term := tm_weaken v;
        cap_entry_assigned_capture_set := capture_weaken Q;
        cap_entry_assigned_type := ty_weaken T;
        cap_entry_lookup := CapLookup_here;
        cap_entry_value := cap_value_weaken c exact is_value |}.
    + intro y.
      pose (old := @cap_world_valid_entry _ _ _ valid y).
      exact {| cap_entry_term := tm_weaken (cap_entry_term old);
        cap_entry_assigned_capture_set :=
          capture_weaken (cap_entry_assigned_capture_set old);
        cap_entry_assigned_type := ty_weaken (cap_entry_assigned_type old);
        cap_entry_lookup :=
          cap_lookup_weaken (cap_entry_lookup old) exact is_value;
        cap_entry_value :=
          cap_value_weaken (cap_entry_value old) exact is_value |}.
Defined.

(** Every valid entry has the singleton type of its own location. *)
Definition cap_world_entry_singleton_location {n : nat}
    {sigma : Store n} {world : CapWorld sigma}
    {valid : CapWorldValid world} {x : Fin n}
    (entry : CapWorldEntry valid x) :
    CapLocationEvidence world x
      (TyCapt (CSingleton (PVar x)) (ShSingle (PVar x))) :=
  CLE_single (cap_entry_lookup entry) (PR_var sigma x)
    (CR_fold (PR_var sigma x) (cap_entry_lookup entry)).

(** A stored joint value realizes its assigned type at the lookup location. *)
Definition cap_value_at_lookup {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {v : Tm n} {T : Ty n} {Q : CaptureSet n}
    (value : CapValue world v T Q) {x : Fin n}
    (lookup : CapLookup world x v Q) :
    CapLocationEvidence world x T.
Proof.
  destruct value.
  - apply (cap_ty_coercion_action_location c0).
    exact (CLE_fun lookup c CTC_refl CDC_refl CR_refl).
  - apply (cap_ty_coercion_action_location c).
    pose (first := cap_world_entry_singleton_location
      (cap_world_valid_entry valid y)).
    pose (second := cap_world_entry_singleton_location
      (cap_world_valid_entry valid z)).
    apply (CLE_pair lookup first).
    + change (CapRealizes world (RLoc z)
        (tau_open (tau_weaken
          (TauTerm (TyCapt (CSingleton (PVar z)) (ShSingle (PVar z)))))
          (PVar y))).
      rewrite tau_weaken_open. exact (CRZ_loc second).
    + exact CR_refl.
  - apply (cap_ty_coercion_action_location c).
    pose (first := cap_world_entry_singleton_location
      (cap_world_valid_entry valid y)).
    apply (CLE_pair lookup first).
    + change (CapRealizes world (RType W)
        (tau_open (tau_weaken (TauType W W)) (PVar y))).
      rewrite tau_weaken_open. exact (CRZ_type CSC_refl CSC_refl).
    + exact CR_refl.
  - apply (cap_ty_coercion_action_location c).
    pose (first := cap_world_entry_singleton_location
      (cap_world_valid_entry valid y)).
    apply (CLE_pair lookup first).
    + change (CapRealizes world (RCapture W)
        (tau_open (tau_weaken (TauCapture W W)) (PVar y))).
      rewrite tau_weaken_open. exact (CRZ_capture CR_refl CR_refl).
    + exact CR_refl.
Defined.

(** A typed runtime path realizes its assigned type at any location to
    which it resolves. *)
Definition cap_term_evidence_path_location_at {n : nat}
    {sigma : Store n} {world : CapWorld sigma}
    {valid : CapWorldValid world} {p : Path n} {T : Ty n}
    {C : CaptureSet n} (term : CapTermEvidence valid (TmPath p) T C)
    {x : Fin n} (resolution : PathResolve sigma p (RLoc x)) :
    CapLocationEvidence world x T :=
  let view := cap_term_evidence_path_view term in
  let entry := cap_world_valid_entry valid x in
  cap_ty_coercion_action_location (cap_path_view_suffix view)
    (CLE_single (cap_entry_lookup entry) resolution
      (CR_fold resolution (cap_entry_lookup entry))).

(** Continuation evidence survives one ambient allocation. *)
Fixpoint cap_cont_evidence_weaken {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {S0 T : Ty n} {E C : CaptureSet n} {cont : TmCont n}
    (continuation : CapContEvidence valid S0 E cont T C)
    {v : Tm n} {A : Ty n} {Q : CaptureSet n}
    (value : CapValue world v A Q) (is_value : Tm_IsValue v)
    {struct continuation} :
    CapContEvidence
      (cap_world_valid_extend (exact := cap_value_to_exact value)
        (is_value := is_value) valid value)
      (ty_weaken S0) (capture_weaken E) (cont_weaken cont)
      (ty_weaken T) (capture_weaken C).
Proof.
  destruct continuation.
  - exact CCE_hole.
  - unfold cont_weaken, cont_rename. cbn.
    eapply CCE_cons.
    + exact (@cap_cont_evidence_weaken _ _ _ _ _ _ _ _ _ continuation
        _ _ _ value is_value).
    + pose proof (cap_body_weaken c (cap_value_to_exact value) is_value)
        as weakened.
      rewrite <- ty_weaken_rename in weakened.
      rewrite <- capture_weaken_rename in weakened.
      exact weakened.
    + exact (cap_ty_coercion_weaken c0 (cap_value_to_exact value) is_value).
    + exact (cap_relation_weaken c1 (cap_value_to_exact value) is_value).
    + exact (cap_relation_weaken c2 (cap_value_to_exact value) is_value).
Defined.

(** Weakening under a lifted binder and opening the fresh location cancel. *)
Lemma cap_weaken_ext_comp_openAt_zero {n : nat} :
    comp (ext (weaken n)) (openAt (@FZ n)) = id (S n).
Proof.
  apply finfun_ext. intro x.
  refine (fin_case (P := fun x =>
    apply (comp (ext (weaken n)) (openAt FZ)) x =
      apply (id (S n)) x) _ _ x).
  - rewrite comp_apply, ext_zero, openAt_zero, id_apply. reflexivity.
  - intro i. rewrite comp_apply, ext_succ, weaken_apply,
      openAt_succ, id_apply. reflexivity.
Qed.

(** Allocate a value consumed by a let frame and instantiate the suspended
    body at the fresh location. *)
Definition cap_body_allocate {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {S0 : Ty n} {body : Tm (S n)} {T : Ty (S n)}
    {C : CaptureSet (S n)} (closure : CapBody world S0 body T C)
    {v : Tm n} {Q : CaptureSet n} (argument : CapValue world v S0 Q)
    (is_value : Tm_IsValue v) :
    CapTermEvidence
      (cap_world_valid_extend (exact := cap_value_to_exact argument)
        (is_value := is_value) valid argument) body T C.
Proof.
  pose (summary := cap_value_to_exact argument).
  pose (new_valid := cap_world_valid_extend
    (exact := summary) (is_value := is_value) valid argument).
  pose (weakened_argument := cap_value_weaken argument summary is_value).
  pose (possible := cap_value_at_lookup (valid := new_valid)
    weakened_argument CapLookup_here).
  pose proof (cap_body_apply (valid := new_valid)
    (cap_body_weaken closure summary is_value) possible) as applied.
  unfold tm_open in applied.
  rewrite tm_rename_rename, cap_weaken_ext_comp_openAt_zero,
    tm_rename_id in applied.
  rewrite <- ty_rename_openAt_eq_open_var in applied.
  rewrite ty_rename_rename, cap_weaken_ext_comp_openAt_zero,
    ty_rename_id in applied.
  rewrite <- capture_rename_openAt_eq_open_var in applied.
  rewrite capture_rename_rename, cap_weaken_ext_comp_openAt_zero,
    capture_rename_id in applied.
  exact applied.
Defined.

Print Assumptions cap_body_to_exact.
Print Assumptions cap_value_to_exact.
Print Assumptions cap_world_valid_entry.
Print Assumptions cap_value_at_lookup.
Print Assumptions cap_term_evidence_path_location_at.
Print Assumptions cap_cont_evidence_weaken.
Print Assumptions cap_weaken_ext_comp_openAt_zero.
Print Assumptions cap_body_allocate.
