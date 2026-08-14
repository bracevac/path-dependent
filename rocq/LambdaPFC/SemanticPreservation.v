From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PathDependent.LambdaPFC Require Import
  FinFun Syntax Runtime RuntimeEquality SemanticEvidence SemanticTyping
  SemanticAction SemanticWeakening SemanticTypingWeakening
  SemanticFundamental SemanticProgress SemanticAllocation.

Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

Derive NoConfusionHom for State.

(** A type transported through zero or more fresh store allocations. *)
Inductive TyExtends : forall {n m : nat}, Ty n -> Ty m -> Prop :=
| TyExtends_refl {n : nat} {T : Ty n} : TyExtends T T
| TyExtends_alloc {n m : nat} {S : Ty n} {T : Ty m} :
    TyExtends S T -> TyExtends S (ty_weaken T).

Arguments TyExtends_refl {n T}.
Arguments TyExtends_alloc {n m S T} _.

(** Allocation extensions compose. *)
Theorem ty_extends_trans {n m l : nat} {S : Ty n} {T : Ty m}
    {U : Ty l} (first : TyExtends S T) (second : TyExtends T U) :
    TyExtends S U.
Proof.
  induction second.
  - exact first.
  - exact (TyExtends_alloc (IHsecond first)).
Qed.

Local Definition tm_abs_body {n : nat} (term : Tm n) :
    option (Tm (Datatypes.S n)) :=
  match term with
  | TmAbs _ body => Some body
  | _ => None
  end.

(** Beta reduction preserves the application result type. *)
Definition term_evidence_beta {n : nat} {sigma : Store n}
    {p q : Path n} {S T : Ty n} {U : Ty (Datatypes.S n)}
    {f y : Fin n} {A : Ty n} {body : Tm (Datatypes.S n)}
    (function : TermEvidence sigma (TmPath p) (TyFun S U))
    (argument : TermEvidence sigma (TmPath q) S)
    (suffix : Coercion sigma (TauTy (ty_open U q)) (TauTy T))
    (function_resolution : PathResolve p sigma (RefLoc f))
    (argument_resolution : PathResolve q sigma (RefLoc y))
    (binding : StoreBinds sigma f (TmAbs A body)) :
    TermEvidence sigma (tm_open body y) T.
Proof.
  pose proof (term_evidence_path_possible_at argument argument_resolution)
    as argument_possible.
  pose proof (term_evidence_path_possible_at function function_resolution)
    as function_possible.
  dependent elimination function_possible.
  pose proof (store_binds_unique s binding) as binding_equality.
  pose proof (f_equal tm_abs_body binding_equality) as body_equality.
  cbn [tm_abs_body] in body_equality.
  injection body_equality as Hbody. subst body.
  pose (paths := PREq_symm
    (PREq_coresolve argument_resolution (Resolve_var y))).
  pose (relocate := Coercion_runtime
    (TRC_replace (TauTy U0) paths)).
  exact (term_evidence_cast
    (term_evidence_cast
      (body_closure_apply b
        (coercion_action_possible c argument_possible))
      (deferred_coercion_instantiate d argument_possible))
    (Coercion_trans relocate suffix)).
Defined.

(** Every CK transition preserves the final type, allowing one weakening at
    an allocation transition. *)
Theorem state_evidence_preservation {n m : nat} {source : State n}
    {target : State m} {T : Ty n} (evidence : StateEvidence source T)
    (step : StateStep source target) :
    exists U : Ty m,
      TyExtends T U /\ inhabited (StateEvidence target U).
Proof.
  destruct evidence as [n0 sigma cont term S0 T0 continuation term_evidence].
  dependent elimination step.
  - destruct (term_evidence_app_view term_evidence)
      as [argument_type codomain function argument suffix].
    match goal with
    | function_resolution : PathResolve p _ _,
      argument_resolution : PathResolve q _ _,
      binding : StoreBinds _ _ (TmAbs _ _) |- _ =>
        pose proof (term_evidence_beta function argument suffix
          function_resolution argument_resolution binding) as reduced
    end.
    exists T0. split.
    + exact TyExtends_refl.
    + exact (inhabits (StateEv_ok continuation reduced)).
  - match goal with
    | resolution : PathResolve _ _ _ |- _ =>
        pose proof resolution as step_resolution
    end.
    destruct (term_evidence_path_view term_evidence)
      as [location stored_resolution suffix].
    pose (back := Coercion_alias step_resolution (Resolve_var _)).
    exists T0. split.
    + exact TyExtends_refl.
    + exact (inhabits (StateEv_ok continuation
        (TermEv_path (Resolve_var _) (Coercion_trans back suffix)))).
  - destruct (term_evidence_let_view term_evidence)
      as [bound_type result_type bound_evidence closure suffix].
    exists T0. split.
    + exact TyExtends_refl.
    + exact (inhabits (StateEv_ok
        (ContEv_cons continuation closure suffix) bound_evidence)).
  - dependent elimination continuation.
    pose proof (term_evidence_path_possible_at term_evidence
      (Resolve_var _)) as argument.
    pose proof (body_closure_apply b argument) as resumed.
    rewrite ty_weaken_open in resumed.
    exists T1. split.
    + exact TyExtends_refl.
    + exact (inhabits (StateEv_ok c
        (term_evidence_cast resumed c0))).
  - dependent elimination continuation.
    destruct (term_evidence_nonempty_value_view term_evidence
      value0) as [value_evidence].
    pose proof (body_closure_allocate b value_evidence value0)
      as body_evidence.
    pose proof (term_evidence_cast body_evidence
      (coercion_weaken c0 (v := v) value0)) as resumed.
    exists (ty_weaken T1). split.
    + exact (TyExtends_alloc TyExtends_refl).
    + exact (inhabits (StateEv_ok
        (cont_evidence_weaken c (v := v) value0)
        resumed)).
Qed.

Print Assumptions ty_extends_trans.
Print Assumptions term_evidence_beta.
Print Assumptions state_evidence_preservation.
