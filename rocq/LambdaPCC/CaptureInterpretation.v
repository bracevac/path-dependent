From Equations Require Import Equations.
From PathDependent.LambdaPCC Require Import
  FinFun Syntax Context Typing Runtime RuntimeEquality Valuation
  CaptureEvidence CaptureAction CaptureStatic CaptureCoercion CaptureTyping.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.
Unset Equations Derive Eliminator.

(** Interpret a source typing derivation in a valid capture-aware world. *)
Fixpoint cap_tm_ty_interpret {n m : nat} {Gamma : Ctx n}
    {term : Tm n} {T : Ty n} {C : CaptureSet n}
    {rho : Valuation n m} {sigma : Store m} {world : CapWorld sigma}
    (code : TermTy Gamma term T C)
    (environment : CapEnvironment world Gamma rho)
    (valid : CapWorldValid world) {struct code} :
    CapTermEvidence valid (tm_rename term rho) (ty_rename T rho)
      (capture_rename C rho).
Proof.
  destruct code.
  - destruct (cap_path_ty_resolve environment p0)
      as [referent resolution realizes].
    dependent elimination realizes.
    simp tm_rename ty_rename capture_rename path_rename.
    exact (CTE_path resolution CTC_refl CR_refl).
  - simp tm_rename ty_rename capture_rename.
    refine (CTE_value (CV_abs _ CTC_refl) CR_refl).
    pose proof (CB_source environment code) as closure.
    simp capture_rename path_rename in closure.
    rewrite <- capture_weaken_rename in closure.
    exact closure.
  - simp tm_rename ty_rename capture_rename.
    rewrite ty_open_rename.
    exact (CTE_app
      (@cap_tm_ty_interpret _ _ _ _ _ _ _ _ _ code1 environment valid)
      (@cap_tm_ty_interpret _ _ _ _ _ _ _ _ _ code2 environment valid)
      CTC_refl CR_refl).
  - refine (CTE_value (CV_pair _) CR_refl).
    rewrite ty_rename_equation_1, shape_rename_equation_4,
      ty_rename_equation_1, shape_rename_equation_5,
      tau_rename_equation_1, ty_rename_equation_1,
      shape_rename_equation_5.
    simp capture_rename path_rename tm_rename def_rename.
    rewrite <- !path_weaken_rename.
    exact CTC_refl.
  - refine (CTE_value (CV_type_pair _) CR_refl).
    rewrite ty_rename_equation_1, shape_rename_equation_4,
      ty_rename_equation_1, shape_rename_equation_5,
      tau_rename_equation_2.
    rewrite <- !shape_weaken_rename.
    simp capture_rename path_rename tm_rename def_rename.
    exact CTC_refl.
  - refine (CTE_value (CV_capture_pair _) CR_refl).
    rewrite ty_rename_equation_1, shape_rename_equation_4,
      ty_rename_equation_1, shape_rename_equation_5,
      tau_rename_equation_3.
    rewrite <- !capture_weaken_rename.
    simp capture_rename path_rename tm_rename def_rename.
    exact CTC_refl.
  - refine (CTE_let
      (@cap_tm_ty_interpret _ _ _ _ _ _ _ _ _ code1 environment valid)
      _ CTC_refl CR_refl).
    pose proof (CB_source environment code2) as closure.
    rewrite <- ty_weaken_rename in closure.
    rewrite <- capture_weaken_rename in closure.
    exact closure.
  - exact (cap_term_evidence_cast_use
      (cap_term_evidence_cast_type
        (@cap_tm_ty_interpret _ _ _ _ _ _ _ _ _ code environment valid)
        (cap_ty_sub_compile environment t))
      (cap_capture_sub_compile environment c)).
Defined.

Arguments cap_tm_ty_interpret
  {n m Gamma term T C rho sigma world} code environment valid.

(** Instantiate a suspended source body with a realized runtime location. *)
Definition cap_body_apply {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {valid : CapWorldValid world}
    {S0 : Ty n} {body : Tm (S n)} {T : Ty (S n)}
    {C : CaptureSet (S n)} (closure : CapBody world S0 body T C)
    {x : Fin n} (argument : CapLocationEvidence world x S0) :
    CapTermEvidence valid (tm_open body x) (ty_open T (PVar x))
      (capture_open C (PVar x)).
Proof.
  dependent elimination closure.
  pose proof (cap_tm_ty_interpret t (cap_environment_snoc c argument) valid)
    as interpreted.
  unfold tm_open.
  rewrite tm_rename_ext_openAt.
  rewrite <- ty_rename_openAt_eq_open_var.
  rewrite ty_rename_ext_openAt.
  rewrite <- capture_rename_openAt_eq_open_var.
  rewrite capture_rename_ext_openAt.
  exact interpreted.
Defined.

Print Assumptions cap_tm_ty_interpret.
Print Assumptions cap_body_apply.
