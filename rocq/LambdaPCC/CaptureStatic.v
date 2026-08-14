From Equations Require Import Equations.
From PathDependent.LambdaPCC Require Import
  FinFun Syntax Context Typing Runtime RuntimeEquality Valuation
  CaptureEvidence CaptureAction.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.
Unset Equations Derive Eliminator.

Arguments PR_var {n} sigma x.
Arguments PR_fst {n} sigma {k p x y a d} _ _.
Arguments PR_sel {n} sigma {k p x y a d} _ _.
Arguments PR_sel_miss {n} sigma {stored_kind p x y a b d referent} _ _ _ _.

(** Lookup in a capture-aware source environment. *)
Definition cap_environment_lookup {n m : nat} {sigma : Store m}
    {world : CapWorld sigma} {Gamma : Ctx n} {rho : Valuation n m}
    (environment : CapEnvironment world Gamma rho) (x : Fin n) :
    CapLocationEvidence world (apply rho x)
      (ty_rename (ctx_lookup Gamma x) rho).
Proof.
  dependent elimination environment.
  match goal with
  | lookup : forall z, CapLocationEvidence _ _ _ |- _ => exact (lookup x)
  end.
Defined.

Definition cap_environment_empty :
    CapEnvironment CapWorld_empty CtxNil (id 0).
Proof.
  apply CE_intro. intro x.
  exact (@fin_elim0 (fun z =>
    CapLocationEvidence CapWorld_empty (apply (id 0) z)
      (ty_rename (ctx_lookup CtxNil z) (id 0))) x).
Defined.

Lemma comp_weaken_valuation_snoc {n m : nat}
    (rho : Valuation n m) (y : Fin m) :
    comp (weaken n) (valuation_snoc rho y) = rho.
Proof.
  apply finfun_ext. intro x. rewrite comp_apply, weaken_apply.
  apply valuation_snoc_succ.
Qed.

(** Extend an environment by assigning the newest source variable to an
    already realized location. *)
Definition cap_environment_snoc {n m : nat} {sigma : Store m}
    {world : CapWorld sigma} {Gamma : Ctx n} {rho : Valuation n m}
    {S0 : Ty n} {y : Fin m} (environment : CapEnvironment world Gamma rho)
    (argument : CapLocationEvidence world y (ty_rename S0 rho)) :
    CapEnvironment world (CtxSnoc Gamma S0) (valuation_snoc rho y).
Proof.
  apply CE_intro. intro x.
  refine (fin_case (P := fun x =>
    CapLocationEvidence world (apply (valuation_snoc rho y) x)
      (ty_rename (ctx_lookup (CtxSnoc Gamma S0) x)
        (valuation_snoc rho y))) _ _ x).
  - rewrite valuation_snoc_zero. simp ctx_lookup.
    unfold ty_weaken. rewrite ty_rename_rename,
      comp_weaken_valuation_snoc. exact argument.
  - intro i. rewrite valuation_snoc_succ. simp ctx_lookup.
    unfold ty_weaken. rewrite ty_rename_rename,
      comp_weaken_valuation_snoc.
    exact (cap_environment_lookup environment i).
Defined.

(** Runtime referent and realization extracted from precise path typing. *)
Record CapPathResolution {n m : nat} {k : Kind} {sigma : Store m}
    (world : CapWorld sigma) (rho : Valuation n m)
    (p : Path n) (d : Tau n k) : Type := {
  cap_resolution_referent : Referent m;
  cap_resolution_path : PathResolve sigma (path_rename p rho)
    cap_resolution_referent;
  cap_resolution_realizes : CapRealizes world cap_resolution_referent
    (tau_rename d rho)
}.

(** Resolve a typed source path under a capture-aware environment. *)
Fixpoint cap_path_ty_resolve {n m : nat} {k : Kind} {sigma : Store m}
    {world : CapWorld sigma} {Gamma : Ctx n} {rho : Valuation n m}
    {p : Path n} {d : Tau n k} (environment : CapEnvironment world Gamma rho)
    (code : PathTy Gamma p d) {struct code} :
    CapPathResolution world rho p d.
Proof.
  destruct code.
  - refine (@Build_CapPathResolution n m KTerm sigma world rho
      (PVar x) (TauTerm (ctx_lookup Gamma x)) (RLoc (apply rho x)) _ _).
    + simp path_rename. exact (PR_var sigma (apply rho x)).
    + simp tau_rename. exact (CRZ_loc (cap_environment_lookup environment x)).
  - destruct (@cap_path_ty_resolve n m KTerm sigma world Gamma rho p
      (TauTerm (TyCapt C (ShPair S0 a d))) environment code)
      as [referent resolution realizes].
    dependent elimination realizes.
    change (@CapLocationEvidence n0 sigma0 world0 x
      (TyCapt (capture_rename C rho)
        (ShPair (ty_rename S0 rho) a (tau_rename d (ext rho))))) in c.
    dependent elimination c.
    match goal with
    | resolution : PathResolve ?store _ (RLoc ?x0),
      lookup : CapLookup ?w ?x0 (TmPair ?y0 ?label ?delta0) ?Q0,
      first : CapLocationEvidence ?w ?y0 _ |- _ =>
        refine (@Build_CapPathResolution _ _ KTerm store w rho
          (PFst p) (TauTerm S0) (RLoc y0) _ _);
        [simp path_rename;
         exact (PR_fst store resolution (cap_lookup_binds lookup))
        |simp tau_rename; exact (CRZ_loc first)]
    end.
  - destruct (@cap_path_ty_resolve n m KTerm sigma world Gamma rho p
      (TauTerm (TyCapt C (ShPair S0 a d))) environment code)
      as [referent resolution realizes].
    dependent elimination realizes.
    change (@CapLocationEvidence n0 sigma0 world0 x
      (TyCapt (capture_rename C rho)
        (ShPair (ty_rename S0 rho) a (tau_rename d (ext rho))))) in c.
    dependent elimination c.
    pose (first_resolution := PR_fst sigma3 resolution
      (cap_lookup_binds c6)).
    pose (paths := PREq_coresolve (PR_var sigma3 y) first_resolution).
    pose (opened := TaRC_replace (tau_rename d (ext rho)) paths).
    pose (converted := cap_realizes_convert c8 opened).
    refine (@Build_CapPathResolution n n3 k0 sigma3 world2 rho
      (PSel p a0) (tau_open d (PFst p)) (def_referent delta) _ _).
    + simp path_rename. exact (PR_sel sigma3 resolution (cap_lookup_binds c6)).
    + rewrite tau_open_rename. exact converted.
  - destruct (@cap_path_ty_resolve n m KTerm sigma world Gamma rho p
      (TauTerm (TyCapt C (ShPair S0 b stored))) environment code1)
      as [receiver_ref receiver_resolution receiver_realizes].
    destruct (@cap_path_ty_resolve n m member_kind sigma world Gamma rho
      (PSel (PFst p) a) d environment code2)
      as [member_ref member_resolution member_realizes].
    dependent elimination receiver_realizes.
    change (@CapLocationEvidence n1 sigma0 world0 x
      (TyCapt (capture_rename C rho)
        (ShPair (ty_rename S0 rho) b
          (tau_rename stored (ext rho))))) in c.
    dependent elimination c.
    change (PathResolve sigma3
      (PSel (PFst (path_rename p rho)) a) member_ref)
      in member_resolution.
    pose (first_resolution := PR_fst sigma3 receiver_resolution
      (cap_lookup_binds c6)).
    pose (tail_resolution := path_resolve_sel_congr member_resolution
      first_resolution (PR_var sigma3 y)).
    refine (@Build_CapPathResolution n n4 member_kind sigma3 world2 rho
      (PSel p a) d member_ref _ member_realizes).
    simp path_rename. eapply PR_sel_miss.
    + exact receiver_resolution.
    + exact (cap_lookup_binds c6).
    + exact n0.
    + exact tail_resolution.
Defined.

(** Static subcapturing remains tied to the environment justifying its path
    premises. *)
Definition cap_capture_sub_compile {n m : nat} {sigma : Store m}
    {world : CapWorld sigma} {Gamma : Ctx n} {rho : Valuation n m}
    {C D : CaptureSet n} (environment : CapEnvironment world Gamma rho)
    (code : CaptureSub Gamma C D) :
    CapRelation world (capture_rename C rho) (capture_rename D rho) :=
  CR_source environment code.

Fixpoint cap_ty_sub_compile {n m : nat} {sigma : Store m}
    {world : CapWorld sigma} {Gamma : Ctx n} {rho : Valuation n m}
    {T U : Ty n} (environment : CapEnvironment world Gamma rho)
    (code : TySub Gamma T U) {struct code} :
    CapTyCoercion world (ty_rename T rho) (ty_rename U rho)
with cap_shape_sub_compile {n m : nat} {sigma : Store m}
    {world : CapWorld sigma} {Gamma : Ctx n} {rho : Valuation n m}
    {S0 T : Shape n} (environment : CapEnvironment world Gamma rho)
    (code : ShapeSub Gamma S0 T) {struct code} :
    CapShapeCoercion world (shape_rename S0 rho) (shape_rename T rho).
Proof.
  - destruct code.
    + exact CTC_refl.
    + exact (CTC_trans
        (@cap_ty_sub_compile _ _ _ _ _ _ _ _ environment code1)
        (@cap_ty_sub_compile _ _ _ _ _ _ _ _ environment code2)).
    + exact (CTC_capt (cap_capture_sub_compile environment c)
        (@cap_shape_sub_compile _ _ _ _ _ _ _ _ environment s)).
  - destruct code.
    + exact CSC_refl.
    + exact (CSC_trans
        (@cap_shape_sub_compile _ _ _ _ _ _ _ _ environment code1)
        (@cap_shape_sub_compile _ _ _ _ _ _ _ _ environment code2)).
    + exact CSC_bot.
    + exact CSC_top.
    + destruct (@cap_path_ty_resolve _ _ _ _ _ _ _ _ _ environment p0)
        as [referent resolution realizes].
      dependent elimination realizes.
      exact (CSC_widen resolution c).
    + destruct (@cap_path_ty_resolve _ _ _ _ _ _ _ _ _ environment p0)
        as [referent resolution realizes].
      dependent elimination realizes.
      change (@CapLocationEvidence n0 sigma0 world0 x
        (TyCapt (capture_rename C rho)
          (ShSingle (path_rename q rho)))) in c.
      dependent elimination c.
      eapply CSC_alias; eassumption.
    + destruct (@cap_path_ty_resolve _ _ _ _ _ _ _ _ _ environment p0)
        as [referent resolution realizes].
      dependent elimination realizes.
      eapply CSC_select_lower; eassumption.
    + destruct (@cap_path_ty_resolve _ _ _ _ _ _ _ _ _ environment p0)
        as [referent resolution realizes].
      dependent elimination realizes.
      eapply CSC_select_upper; eassumption.
    + exact (CSC_fun
        (@cap_ty_sub_compile _ _ _ _ _ _ _ _ environment t)
        (CDC_source environment t0)).
    + exact (CSC_pair
        (@cap_ty_sub_compile _ _ _ _ _ _ _ _ environment t)
        (CMC_source environment t0)).
Defined.

Fixpoint cap_tau_sub_compile {n m : nat} {k : Kind} {sigma : Store m}
    {world : CapWorld sigma} {Gamma : Ctx n} {rho : Valuation n m}
    {d e : Tau n k} (environment : CapEnvironment world Gamma rho)
    (code : TauSub Gamma d e) {struct code} :
    CapCoercion world (tau_rename d rho) (tau_rename e rho).
Proof.
  destruct code.
  - exact CC_refl.
  - exact (CC_trans
      (@cap_tau_sub_compile _ _ _ _ _ _ _ _ _ environment code1)
      (@cap_tau_sub_compile _ _ _ _ _ _ _ _ _ environment code2)).
  - exact (CC_term
      (@cap_ty_sub_compile _ _ _ _ _ _ _ _ environment t)).
  - exact (CC_type
      (@cap_shape_sub_compile _ _ _ _ _ _ _ _ environment s)
      (@cap_shape_sub_compile _ _ _ _ _ _ _ _ environment s0)).
  - exact (CC_capture (cap_capture_sub_compile environment c)
      (cap_capture_sub_compile environment c0)).
Defined.

Print Assumptions cap_environment_snoc.
Print Assumptions cap_path_ty_resolve.
Print Assumptions cap_tau_sub_compile.
