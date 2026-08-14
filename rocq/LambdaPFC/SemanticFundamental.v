From Equations Require Import Equations.
From PathDependent.LambdaPFC Require Import
  FinFun Syntax Context Typing Runtime Valuation SemanticEvidence
  SemanticTyping SemanticAction.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Interpret a source typing derivation in a semantic environment. *)
Fixpoint tm_ty_interpret {n m : nat} {Gamma : Ctx n} {term : Tm n}
    {T : Ty n} {rho : Valuation n m} {sigma : Store m}
    (code : TmTy Gamma term T)
    (environment : Environment Gamma rho sigma) {struct code} :
    TermEvidence sigma (tm_rename term rho) (ty_rename T rho).
Proof.
  destruct code.
  - pose proof (path_ty_resolve environment p0) as result.
    destruct result as [referent resolution realizes].
    rewrite tau_rename_equation_1 in realizes.
    dependent elimination realizes.
    simp tm_rename ty_rename.
    exact (TermEv_path resolution Coercion_refl).
  - simp tm_rename ty_rename.
    exact (TermEv_value
      (ValueEv_abs (Body_source environment code) Coercion_refl)).
  - simp tm_rename ty_rename.
    rewrite ty_open_rename.
    exact (TermEv_app
      (@tm_ty_interpret _ _ _ _ _ _ _ code1 environment)
      (@tm_ty_interpret _ _ _ _ _ _ _ code2 environment)
      Coercion_refl).
  - refine (TermEv_value (ValueEv_pair _)).
    rewrite ty_rename_equation_4, ty_rename_equation_5,
      tau_rename_equation_1, ty_rename_equation_5.
    rewrite <- path_weaken_rename.
    simp path_rename.
    exact Coercion_refl.
  - refine (TermEv_value (ValueEv_tpair _)).
    rewrite ty_rename_equation_4, ty_rename_equation_5.
    rewrite <- tau_weaken_rename, tau_rename_equation_2.
    simp path_rename.
    exact Coercion_refl.
  - simp tm_rename ty_rename.
    refine (TermEv_let
      (@tm_ty_interpret _ _ _ _ _ _ _ code1 environment) _ Coercion_refl).
    pose proof (Body_source environment code2) as closure.
    rewrite <- ty_weaken_rename in closure.
    exact closure.
  - exact (term_evidence_cast
      (@tm_ty_interpret _ _ _ _ _ _ _ code environment)
      (tau_sub_compile environment t)).
Defined.

Arguments tm_ty_interpret {n m Gamma term T rho sigma} code environment.

(** Interpret a closed source body after mapping its formal parameter to a
    concrete argument location. *)
Definition body_closure_apply {m : nat} {sigma : Store m} {S : Ty m}
    {body : Tm (Datatypes.S m)} {T : Ty (Datatypes.S m)}
    (closure : BodyClosure sigma S body T) {x : Fin m}
    (argument : StorePossible sigma x S) :
    TermEvidence sigma (tm_open body x) (ty_open T (PVar x)).
Proof.
  destruct closure.
  pose proof (tm_ty_interpret t (environment_snoc e argument))
    as interpreted.
  unfold tm_open.
  rewrite tm_rename_ext_openAt.
  rewrite <- ty_rename_openAt_eq_open_var.
  rewrite ty_rename_ext_openAt.
  exact interpreted.
Defined.

Print Assumptions tm_ty_interpret.
Print Assumptions body_closure_apply.
