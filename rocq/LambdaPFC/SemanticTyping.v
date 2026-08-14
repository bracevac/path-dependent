From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PathDependent.LambdaPFC Require Import
  FinFun Syntax Context Typing Runtime RuntimeEquality Valuation
  SemanticEvidence.

Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Syntax-directed evidence for values. *)
Inductive ValueEvidence : forall {n : nat},
    Store n -> Tm n -> Ty n -> Type :=
| ValueEv_abs {n : nat} {sigma : Store n} {A T : Ty n}
    {body : Tm (S n)} {B : Ty (S n)} :
    BodyClosure sigma A body B ->
    Coercion sigma (TauTy (TyFun A B)) (TauTy T) ->
    ValueEvidence sigma (TmAbs A body) T
| ValueEv_pair {n : nat} {sigma : Store n} {y z : Fin n}
    {a : Name} {T : Ty n} :
    Coercion sigma
      (TauTy (TyPair (TySingle (PVar y)) a
        (TauTy (TySingle (path_weaken (PVar z))))))
      (TauTy T) ->
    ValueEvidence sigma (TmPair y a (DefVal z)) T
| ValueEv_tpair {n : nat} {sigma : Store n} {y : Fin n}
    {a : Name} {W T : Ty n} :
    Coercion sigma
      (TauTy (TyPair (TySingle (PVar y)) a
        (tau_weaken (TauIntv W W))))
      (TauTy T) ->
    ValueEvidence sigma (TmPair y a (DefType W)) T.

(** Runtime typing evidence normalized at the outer constructor. *)
Inductive TermEvidence : forall {n : nat},
    Store n -> Tm n -> Ty n -> Type :=
| TermEv_path {n : nat} {sigma : Store n} {p : Path n}
    {x : Fin n} {T : Ty n} :
    PathResolve p sigma (RefLoc x) ->
    Coercion sigma (TauTy (TySingle p)) (TauTy T) ->
    TermEvidence sigma (TmPath p) T
| TermEv_value {n : nat} {sigma : Store n} {v : Tm n} {T : Ty n} :
    ValueEvidence sigma v T -> TermEvidence sigma v T
| TermEv_app {n : nat} {sigma : Store n} {p q : Path n}
    {S T : Ty n} {U : Ty (Datatypes.S n)} :
    TermEvidence sigma (TmPath p) (TyFun S U) ->
    TermEvidence sigma (TmPath q) S ->
    Coercion sigma (TauTy (ty_open U q)) (TauTy T) ->
    TermEvidence sigma (TmApp p q) T
| TermEv_let {n : nat} {sigma : Store n} {s : Tm n}
    {body : Tm (S n)} {S T U : Ty n} :
    TermEvidence sigma s S ->
    BodyClosure sigma S body (ty_weaken U) ->
    Coercion sigma (TauTy U) (TauTy T) ->
    TermEvidence sigma (TmLet s body) T.

Derive Signature for Def.
Derive NoConfusionHom for Def.
Derive NoConfusionHom for Tm.
Derive Signature for ValueEvidence.
Derive NoConfusionHom for ValueEvidence.
Derive Signature for TermEvidence.
Derive NoConfusionHom for TermEvidence.

Arguments ValueEv_abs {n sigma A T body B} _ _.
Arguments ValueEv_pair {n sigma y z a T} _.
Arguments ValueEv_tpair {n sigma y a W T} _.
Arguments TermEv_path {n sigma p x T} _ _.
Arguments TermEv_value {n sigma v T} _.
Arguments TermEv_app {n sigma p q S T U} _ _ _.
Arguments TermEv_let {n sigma s body S T U} _ _ _.

(** A value derivation supplies the runtime value classifier. *)
Definition value_evidence_is_value {n : nat} {sigma : Store n}
    {v : Tm n} {T : Ty n} (evidence : ValueEvidence sigma v T) :
    Tm_IsValue v.
Proof. destruct evidence; constructor. Defined.

(** Compose a coercion with the suffix already stored by a value. *)
Definition value_evidence_cast {n : nat} {sigma : Store n}
    {v : Tm n} {S T : Ty n} (evidence : ValueEvidence sigma v S)
    (suffix : Coercion sigma (TauTy S) (TauTy T)) :
    ValueEvidence sigma v T.
Proof.
  destruct evidence.
  - exact (ValueEv_abs b (Coercion_trans c suffix)).
  - exact (ValueEv_pair (Coercion_trans c suffix)).
  - exact (ValueEv_tpair (Coercion_trans c suffix)).
Defined.

(** Compose a coercion with the suffix at a term constructor. *)
Definition term_evidence_cast {n : nat} {sigma : Store n}
    {t : Tm n} {S T : Ty n} (evidence : TermEvidence sigma t S)
    (suffix : Coercion sigma (TauTy S) (TauTy T)) :
    TermEvidence sigma t T.
Proof.
  destruct evidence.
  - exact (TermEv_path p0 (Coercion_trans c suffix)).
  - exact (TermEv_value (value_evidence_cast v0 suffix)).
  - exact (TermEv_app evidence1 evidence2 (Coercion_trans c suffix)).
  - exact (TermEv_let evidence b (Coercion_trans c suffix)).
Defined.

(** Syntax-directed path view. *)
Record PathEvidenceView {n : nat} (sigma : Store n)
    (p : Path n) (T : Ty n) : Type := {
  path_view_location : Fin n;
  path_view_resolution : PathResolve p sigma (RefLoc path_view_location);
  path_view_suffix : Coercion sigma (TauTy (TySingle p)) (TauTy T)
}.

Definition term_evidence_path_view {n : nat} {sigma : Store n}
    {p : Path n} {T : Ty n}
    (evidence : TermEvidence sigma (TmPath p) T) :
    PathEvidenceView sigma p T.
Proof.
  dependent elimination evidence.
  - exact {| path_view_location := x;
      path_view_resolution := p1; path_view_suffix := c |}.
  - dependent elimination v0.
Defined.

(** Syntax-directed application view. *)
Record AppEvidenceView {n : nat} (sigma : Store n)
    (p q : Path n) (T : Ty n) : Type := {
  app_view_argument_type : Ty n;
  app_view_codomain : Ty (S n);
  app_view_function : TermEvidence sigma (TmPath p)
    (TyFun app_view_argument_type app_view_codomain);
  app_view_argument : TermEvidence sigma (TmPath q)
    app_view_argument_type;
  app_view_suffix : Coercion sigma
    (TauTy (ty_open app_view_codomain q)) (TauTy T)
}.

Definition term_evidence_app_view {n : nat} {sigma : Store n}
    {p q : Path n} {T : Ty n}
    (evidence : TermEvidence sigma (TmApp p q) T) :
    AppEvidenceView sigma p q T.
Proof.
  dependent elimination evidence.
  - dependent elimination v0.
  - exact {| app_view_argument_type := S0;
      app_view_codomain := U; app_view_function := t;
      app_view_argument := t0; app_view_suffix := c0 |}.
Defined.

(** Syntax-directed let view. *)
Record LetEvidenceView {n : nat} (sigma : Store n) (s : Tm n)
    (body : Tm (S n)) (T : Ty n) : Type := {
  let_view_bound_type : Ty n;
  let_view_result_type : Ty n;
  let_view_bound : TermEvidence sigma s let_view_bound_type;
  let_view_closure : BodyClosure sigma let_view_bound_type body
    (ty_weaken let_view_result_type);
  let_view_suffix : Coercion sigma (TauTy let_view_result_type) (TauTy T)
}.

Definition term_evidence_let_view {n : nat} {sigma : Store n}
    {s : Tm n} {body : Tm (S n)} {T : Ty n}
    (evidence : TermEvidence sigma (TmLet s body) T) :
    LetEvidenceView sigma s body T.
Proof.
  dependent elimination evidence.
  - dependent elimination v0.
  - exact {| let_view_bound_type := S1;
      let_view_result_type := U0; let_view_bound := t1;
      let_view_closure := b; let_view_suffix := c1 |}.
Defined.

(** Value inversion remains propositionally truncated. *)
Theorem term_evidence_nonempty_value_view {n : nat} {sigma : Store n}
    {v : Tm n} {T : Ty n} (evidence : TermEvidence sigma v T)
    (value : Tm_IsValue v) : inhabited (ValueEvidence sigma v T).
Proof.
  dependent elimination evidence.
  - dependent elimination value.
  - exact (inhabits v1).
  - dependent elimination value.
  - dependent elimination value.
Qed.

(** Evidence that a continuation maps its input type to its final type. *)
Inductive ContEvidence : forall {n : nat},
    Store n -> Ty n -> TmCont n -> Ty n -> Type :=
| ContEv_hole {n : nat} {sigma : Store n} {T : Ty n} :
    ContEvidence sigma T [] T
| ContEv_cons {n : nat} {sigma : Store n} {S U V T : Ty n}
    {body : Tm (Datatypes.S n)} {cont : TmCont n} :
    ContEvidence sigma U cont T ->
    BodyClosure sigma S body (ty_weaken V) ->
    Coercion sigma (TauTy V) (TauTy U) ->
    ContEvidence sigma S (body :: cont) T.

(** Store-local invariant for a complete machine state. *)
Inductive StateEvidence : forall {n : nat}, State n -> Ty n -> Type :=
| StateEv_ok {n : nat} {sigma : Store n} {cont : TmCont n}
    {term : Tm n} {S T : Ty n} :
    ContEvidence sigma S cont T ->
    TermEvidence sigma term S ->
    StateEvidence (StateMk sigma cont term) T.

Print Assumptions term_evidence_nonempty_value_view.
