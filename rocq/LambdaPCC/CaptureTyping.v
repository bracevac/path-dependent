From Equations Require Import Equations.
From Stdlib Require Import Lists.List.
From PathDependent.LambdaPCC Require Import
  FinFun Syntax Context Typing Runtime RuntimeEquality Valuation
  CaptureEvidence CaptureAction CaptureStatic CaptureCoercion.

Import ListNotations.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.
Unset Equations Derive Eliminator.

Derive Signature for Def.
Derive NoConfusionHom for Def.
Derive NoConfusionHom for Tm.

Definition cap_value_is_value {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {v : Tm n} {T : Ty n} {Q : CaptureSet n}
    (value : CapValue world v T Q) : Tm_IsValue v.
Proof.
  destruct value.
  - exact (IsValue_abs A body).
  - exact (IsValue_pair y a (DefVal z)).
  - exact (IsValue_pair y a (DefType W)).
  - exact (IsValue_pair y a (DefCapture W)).
Defined.

Definition tm_path_value_absurd {n : nat} {p : Path n}
    (value : Tm_IsValue (TmPath p)) : False :=
  match value with end.

Definition tm_app_value_absurd {n : nat} {p q : Path n}
    (value : Tm_IsValue (TmApp p q)) : False :=
  match value with end.

Definition tm_let_value_absurd {n : nat} {bound : Tm n}
    {body : Tm (S n)} (value : Tm_IsValue (TmLet bound body)) : False :=
  match value with end.

Definition cap_value_cast {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {v : Tm n} {S0 T : Ty n}
    {Q : CaptureSet n} (value : CapValue world v S0 Q)
    (suffix : CapTyCoercion world S0 T) : CapValue world v T Q.
Proof.
  destruct value.
  - exact (CV_abs c (CTC_trans c0 suffix)).
  - exact (CV_pair (CTC_trans c suffix)).
  - exact (CV_type_pair (CTC_trans c suffix)).
  - exact (CV_capture_pair (CTC_trans c suffix)).
Defined.

(** Runtime term evidence, indexed jointly by result type and use set. *)
Inductive CapTermEvidence : forall {n : nat} {sigma : Store n}
    {world : CapWorld sigma}, CapWorldValid world ->
    Tm n -> Ty n -> CaptureSet n -> Type :=
| CTE_path {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {valid : CapWorldValid world} {p : Path n} {x : Fin n}
    {T : Ty n} {C : CaptureSet n} :
    PathResolve sigma p (RLoc x) ->
    CapTyCoercion world (TyCapt (CSingleton p) (ShSingle p)) T ->
    CapRelation world (CSingleton p) C ->
    CapTermEvidence valid (TmPath p) T C
| CTE_value {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {valid : CapWorldValid world} {v : Tm n} {T : Ty n}
    {Q C : CaptureSet n} :
    CapValue world v T Q -> CapRelation world CEmpty C ->
    CapTermEvidence valid v T C
| CTE_app {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {valid : CapWorldValid world} {p q : Path n}
    {Cf Cp Cq C : CaptureSet n} {S0 T : Ty n} {U : Ty (S n)} :
    CapTermEvidence valid (TmPath p) (TyCapt Cf (ShFun S0 U)) Cp ->
    CapTermEvidence valid (TmPath q) S0 Cq ->
    CapTyCoercion world (ty_open U q) T ->
    CapRelation world (CUnion Cp Cq) C ->
    CapTermEvidence valid (TmApp p q) T C
| CTE_let {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {valid : CapWorldValid world} {s : Tm n} {body : Tm (S n)}
    {S0 T U : Ty n} {C D : CaptureSet n} :
    CapTermEvidence valid s S0 C ->
    CapBody world S0 body (ty_weaken U) (capture_weaken C) ->
    CapTyCoercion world U T -> CapRelation world C D ->
    CapTermEvidence valid (TmLet s body) T D.

Definition cap_term_evidence_cast_type {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {term : Tm n} {S0 T : Ty n} {C : CaptureSet n}
    (evidence : CapTermEvidence valid term S0 C)
    (suffix : CapTyCoercion world S0 T) :
    CapTermEvidence valid term T C.
Proof.
  destruct evidence.
  - exact (CTE_path p0 (CTC_trans c suffix) c0).
  - exact (CTE_value (cap_value_cast c suffix) c0).
  - exact (CTE_app evidence1 evidence2 (CTC_trans c suffix) c0).
  - exact (CTE_let evidence c (CTC_trans c0 suffix) c1).
Defined.

Definition cap_term_evidence_cast_use {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {term : Tm n} {T : Ty n} {C D : CaptureSet n}
    (evidence : CapTermEvidence valid term T C)
    (coverage : CapRelation world C D) : CapTermEvidence valid term T D.
Proof.
  destruct evidence.
  - exact (CTE_path p0 c (CR_trans c0 coverage)).
  - exact (CTE_value c (CR_trans c0 coverage)).
  - exact (CTE_app evidence1 evidence2 c (CR_trans c0 coverage)).
  - exact (CTE_let evidence c c0 (CR_trans c1 coverage)).
Defined.

Record CapPathEvidenceView {n : nat} {sigma : Store n}
    {world : CapWorld sigma} (valid : CapWorldValid world)
    (p : Path n) (T : Ty n) (C : CaptureSet n) : Type := {
  cap_path_view_location : Fin n;
  cap_path_view_resolution : PathResolve sigma p (RLoc cap_path_view_location);
  cap_path_view_suffix :
    CapTyCoercion world (TyCapt (CSingleton p) (ShSingle p)) T;
  cap_path_view_coverage : CapRelation world (CSingleton p) C
}.

Record CapAppEvidenceView {n : nat} {sigma : Store n}
    {world : CapWorld sigma} (valid : CapWorldValid world)
    (p q : Path n) (T : Ty n) (C : CaptureSet n) : Type := {
  cap_app_view_function_captures : CaptureSet n;
  cap_app_view_function_use : CaptureSet n;
  cap_app_view_argument_use : CaptureSet n;
  cap_app_view_argument_type : Ty n;
  cap_app_view_codomain : Ty (S n);
  cap_app_view_function : CapTermEvidence valid (TmPath p)
    (TyCapt cap_app_view_function_captures
      (ShFun cap_app_view_argument_type cap_app_view_codomain))
    cap_app_view_function_use;
  cap_app_view_argument : CapTermEvidence valid (TmPath q)
    cap_app_view_argument_type cap_app_view_argument_use;
  cap_app_view_suffix :
    CapTyCoercion world (ty_open cap_app_view_codomain q) T;
  cap_app_view_coverage :
    CapRelation world
      (CUnion cap_app_view_function_use cap_app_view_argument_use) C
}.

Record CapLetEvidenceView {n : nat} {sigma : Store n}
    {world : CapWorld sigma} (valid : CapWorldValid world)
    (s : Tm n) (body : Tm (S n)) (T : Ty n)
    (D : CaptureSet n) : Type := {
  cap_let_view_bound_type : Ty n;
  cap_let_view_result_type : Ty n;
  cap_let_view_local_use : CaptureSet n;
  cap_let_view_bound : CapTermEvidence valid s
    cap_let_view_bound_type cap_let_view_local_use;
  cap_let_view_closure : CapBody world cap_let_view_bound_type body
    (ty_weaken cap_let_view_result_type) (capture_weaken cap_let_view_local_use);
  cap_let_view_suffix : CapTyCoercion world cap_let_view_result_type T;
  cap_let_view_coverage : CapRelation world cap_let_view_local_use D
}.

(** A small shape-indexed observation of term evidence.  Splitting the value
    case into its two possible term shapes gives the view lemmas below a
    structural dependent elimination principle, without equality axioms. *)
Inductive CapTermEvidenceObservation {n : nat} {sigma : Store n}
    {world : CapWorld sigma} (valid : CapWorldValid world) :
    Tm n -> Ty n -> CaptureSet n -> Type :=
| CTEO_path {p : Path n} {T : Ty n} {C : CaptureSet n} :
    CapPathEvidenceView valid p T C ->
    CapTermEvidenceObservation valid (TmPath p) T C
| CTEO_abs {A : Ty n} {body : Tm (S n)} {T : Ty n}
    {C Q : CaptureSet n} :
    CapValue world (TmAbs A body) T Q ->
    CapTermEvidenceObservation valid (TmAbs A body) T C
| CTEO_pair {k : Kind} {y : Fin n} {a : Name} {d : Def n k}
    {T : Ty n} {C Q : CaptureSet n} :
    CapValue world (TmPair y a d) T Q ->
    CapTermEvidenceObservation valid (TmPair y a d) T C
| CTEO_app {p q : Path n} {T : Ty n} {C : CaptureSet n} :
    CapAppEvidenceView valid p q T C ->
    CapTermEvidenceObservation valid (TmApp p q) T C
| CTEO_let {s : Tm n} {body : Tm (S n)} {T : Ty n}
    {C : CaptureSet n} :
    CapLetEvidenceView valid s body T C ->
    CapTermEvidenceObservation valid (TmLet s body) T C.

Definition cap_term_evidence_observe {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {term : Tm n} {T : Ty n} {C : CaptureSet n}
    (evidence : CapTermEvidence valid term T C) :
    CapTermEvidenceObservation valid term T C.
Proof.
  destruct evidence.
  - apply CTEO_path. econstructor; eassumption.
  - destruct c.
    + eapply CTEO_abs. econstructor; eassumption.
    + eapply CTEO_pair. econstructor; eassumption.
    + eapply CTEO_pair. econstructor; eassumption.
    + eapply CTEO_pair. econstructor; eassumption.
  - apply CTEO_app. econstructor; eassumption.
  - apply CTEO_let. econstructor; eassumption.
Defined.

Equations cap_observation_path_view {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {p : Path n} {T : Ty n} {C : CaptureSet n}
    (observation : CapTermEvidenceObservation valid (TmPath p) T C) :
    CapPathEvidenceView valid p T C :=
cap_observation_path_view (CTEO_path view) := view.

Definition cap_term_evidence_path_view {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {p : Path n} {T : Ty n} {C : CaptureSet n}
    (term : CapTermEvidence valid (TmPath p) T C) :
    CapPathEvidenceView valid p T C :=
  cap_observation_path_view (cap_term_evidence_observe term).

Equations cap_observation_app_view {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {p q : Path n} {T : Ty n} {C : CaptureSet n}
    (observation : CapTermEvidenceObservation valid (TmApp p q) T C) :
    CapAppEvidenceView valid p q T C :=
cap_observation_app_view (CTEO_app view) := view.

Definition cap_term_evidence_app_view {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {p q : Path n} {T : Ty n} {C : CaptureSet n}
    (term : CapTermEvidence valid (TmApp p q) T C) :
    CapAppEvidenceView valid p q T C :=
  cap_observation_app_view (cap_term_evidence_observe term).

Equations cap_observation_let_view {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {s : Tm n} {body : Tm (S n)} {T : Ty n} {C : CaptureSet n}
    (observation : CapTermEvidenceObservation valid (TmLet s body) T C) :
    CapLetEvidenceView valid s body T C :=
cap_observation_let_view (CTEO_let view) := view.

Definition cap_term_evidence_let_view {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {s : Tm n} {body : Tm (S n)} {T : Ty n} {C : CaptureSet n}
    (term : CapTermEvidence valid (TmLet s body) T C) :
    CapLetEvidenceView valid s body T C :=
  cap_observation_let_view (cap_term_evidence_observe term).

Record CapValueEvidenceView {n : nat} {sigma : Store n}
    (world : CapWorld sigma) (v : Tm n) (T : Ty n) : Type := {
  cap_value_view_assigned_capture_set : CaptureSet n;
  cap_value_view_value :
    CapValue world v T cap_value_view_assigned_capture_set
}.

Lemma cap_term_evidence_nonempty_value_view {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {v : Tm n} {T : Ty n} {C : CaptureSet n}
    (term : CapTermEvidence valid v T C) (is_value : Tm_IsValue v) :
    inhabited (CapValueEvidenceView world v T).
Proof.
  destruct term.
  - dependent elimination is_value.
  - exact (inhabits {| cap_value_view_assigned_capture_set := Q;
      cap_value_view_value := c |}).
  - dependent elimination is_value.
  - dependent elimination is_value.
Qed.

(** Continuation evidence maps the current result and use set to the final
    result and a covering use set. *)
Inductive CapContEvidence : forall {n : nat} {sigma : Store n}
    {world : CapWorld sigma}, CapWorldValid world ->
    Ty n -> CaptureSet n -> TmCont n -> Ty n -> CaptureSet n -> Type :=
| CCE_hole {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {valid : CapWorldValid world} {T : Ty n} {C : CaptureSet n} :
    CapContEvidence valid T C [] T C
| CCE_cons {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {valid : CapWorldValid world} {S0 U V T : Ty n}
    {E F D C : CaptureSet n} {body : Tm (S n)} {cont : TmCont n} :
    CapContEvidence valid U D cont T C ->
    CapBody world S0 body (ty_weaken V) (capture_weaken F) ->
    CapTyCoercion world V U ->
    CapRelation world E C -> CapRelation world F D ->
    CapContEvidence valid S0 E (body :: cont) T C.

Definition cap_cont_evidence_input_coverage {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {S0 T : Ty n} {E C : CaptureSet n} {cont : TmCont n}
    (continuation : CapContEvidence valid S0 E cont T C) :
    CapRelation world E C.
Proof.
  destruct continuation.
  - exact CR_refl.
  - exact c1.
Defined.

Inductive CapStateEvidence : forall {n : nat} {sigma : Store n}
    {world : CapWorld sigma}, CapWorldValid world ->
    State n -> Ty n -> CaptureSet n -> Type :=
| CSE_ok {n : nat} {sigma : Store n} {world : CapWorld sigma}
    {valid : CapWorldValid world} {cont : TmCont n} {term : Tm n}
    {S0 T : Ty n} {E C : CaptureSet n} :
    CapContEvidence valid S0 E cont T C ->
    CapTermEvidence valid term S0 E ->
    CapStateEvidence valid (StateMk sigma cont term) T C.

Print Assumptions CapTermEvidence.
Print Assumptions cap_term_evidence_path_view.
Print Assumptions cap_term_evidence_app_view.
Print Assumptions cap_term_evidence_let_view.
Print Assumptions cap_term_evidence_nonempty_value_view.
Print Assumptions CapStateEvidence.
