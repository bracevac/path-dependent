From Equations Require Import Equations.
From PathDependent.LambdaPFC Require Import
  FinFun Syntax Runtime SemanticEvidence SemanticTyping SemanticAction
  SemanticWeakening SemanticFundamental SemanticTypingWeakening.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** A stored value realizes its advertised type at its bound location. *)
Definition value_evidence_possible_of_binding {n : nat} {sigma : Store n}
    {v : Tm n} {T : Ty n} (evidence : ValueEvidence sigma v T)
    {x : Fin n} (binding : StoreBinds sigma x v) :
    StorePossible sigma x T.
Proof.
  destruct evidence.
  - exact (coercion_action_possible c
      (Possible_fun binding b Coercion_refl Deferred_refl)).
  - apply (coercion_action_possible c).
    refine (Possible_pair binding (Possible_single (Resolve_var y)) _).
    change (ReferentRealizes sigma (RefLoc z)
      (tau_open (tau_weaken (TauTy (TySingle (PVar z)))) (PVar y))).
    rewrite tau_weaken_open.
    exact (Realizes_loc (Possible_single (Resolve_var z))).
  - apply (coercion_action_possible c).
    refine (Possible_pair binding (Possible_single (Resolve_var y)) _).
    change (ReferentRealizes sigma (RefType W)
      (tau_open (tau_weaken (TauIntv W W)) (PVar y))).
    rewrite tau_weaken_open.
    exact (Realizes_type Coercion_refl Coercion_refl).
Defined.

Arguments value_evidence_possible_of_binding
  {n sigma v T} evidence {x} binding.

(** The newly allocated location realizes the weakened advertised type. *)
Definition value_evidence_fresh_possible {n : nat} {sigma : Store n}
    {v : Tm n} {T : Ty n} (evidence : ValueEvidence sigma v T)
    (value : Tm_IsValue v) :
    StorePossible (StoreVal sigma v value) FZ (ty_weaken T) :=
  value_evidence_possible_of_binding
    (value_evidence_weaken evidence (v := v) value) (StoreBinds_here value).

(** Weakening under a lifted binder and opening the fresh location cancel. *)
Lemma weaken_ext_comp_openAt_zero {n : nat} :
    comp (ext (weaken n)) (openAt (@FZ n)) = id (Datatypes.S n).
Proof.
  apply finfun_ext. intro x.
  refine (fin_case (P := fun x =>
    apply (comp (ext (weaken n)) (openAt FZ)) x =
      apply (id (Datatypes.S n)) x) _ _ x).
  - rewrite comp_apply, ext_zero, openAt_zero, id_apply. reflexivity.
  - intro i. rewrite comp_apply, ext_succ, weaken_apply,
      openAt_succ, id_apply. reflexivity.
Qed.

(** Allocate an argument and interpret a closure at the fresh location. *)
Definition body_closure_allocate {n : nat} {sigma : Store n} {S : Ty n}
    {body : Tm (Datatypes.S n)} {T : Ty (Datatypes.S n)}
    (closure : BodyClosure sigma S body T) {v : Tm n}
    (argument : ValueEvidence sigma v S) (value : Tm_IsValue v) :
    TermEvidence (StoreVal sigma v value) body T.
Proof.
  pose proof (body_closure_apply
    (body_closure_weaken closure (v := v) value)
    (value_evidence_fresh_possible argument value)) as applied.
  unfold tm_open in applied.
  rewrite tm_rename_rename, weaken_ext_comp_openAt_zero,
    tm_rename_id in applied.
  rewrite <- ty_rename_openAt_eq_open_var in applied.
  rewrite ty_rename_rename, weaken_ext_comp_openAt_zero,
    ty_rename_id in applied.
  exact applied.
Defined.

Print Assumptions value_evidence_possible_of_binding.
Print Assumptions value_evidence_fresh_possible.
Print Assumptions weaken_ext_comp_openAt_zero.
Print Assumptions body_closure_allocate.
