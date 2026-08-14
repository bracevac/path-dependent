From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PathDependent.LambdaPCC Require Import
  FinFun Syntax Context Typing Runtime CaptureSafety.

Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Regression for unrestricted covariance of dependent pairs. *)

Definition label : Name := 0.

Definition pure_top (n : nat) : Ty n := TyCapt CEmpty ShTop.

Definition source : Ty 0 :=
  TyCapt CEmpty
    (ShPair (pure_top 0) label
      (TauType (ShSingle (PVar FZ)) (ShSingle (PVar FZ)))).

Definition target : Ty 0 :=
  TyCapt CEmpty
    (ShPair (pure_top 0) label (TauType ShBot ShTop)).

Local Definition source_sub_target_general {n : nat} {Gamma : Ctx n} :
    TySub Gamma
      (TyCapt CEmpty
        (ShPair (pure_top n) label
          (TauType (ShSingle (PVar FZ)) (ShSingle (PVar FZ)))))
      (TyCapt CEmpty
        (ShPair (pure_top n) label (TauType ShBot ShTop))).
Proof.
  apply TS_capt.
  - apply CS_refl.
  - apply SS_pair.
    + apply TS_refl.
    + apply TAS_type.
      * apply SS_bot.
      * apply SS_top.
      * apply SS_refl.
Defined.

Definition source_sub_target : TySub CtxNil source target :=
  source_sub_target_general.

Local Definition pure_top_wf {n : nat} {Gamma : Ctx n} :
    TyWf Gamma (pure_top n).
Proof. apply TW_capt; [apply CW_empty | apply SW_top]. Defined.

Local Definition source_wf {n : nat} {Gamma : Ctx n} :
    TyWf Gamma
      (TyCapt CEmpty
        (ShPair (pure_top n) label
          (TauType (ShSingle (PVar FZ)) (ShSingle (PVar FZ))))).
Proof.
  apply TW_capt.
  - apply CW_empty.
  - apply SW_pair.
    + apply pure_top_wf.
    + apply TAW_type.
      * eapply SW_singleton. apply PT_var.
      * eapply SW_singleton. apply PT_var.
      * apply SS_refl.
Defined.

Local Definition target_wf {n : nat} {Gamma : Ctx n} :
    TyWf Gamma
      (TyCapt CEmpty
        (ShPair (pure_top n) label (TauType ShBot ShTop))).
Proof.
  apply TW_capt.
  - apply CW_empty.
  - apply SW_pair.
    + apply pure_top_wf.
    + apply TAW_type.
      * apply SW_bot.
      * apply SW_top.
      * apply SS_bot.
Defined.

(** A closed program using the type-member instance of the rule. *)
Definition bound_result : Ty 1 :=
  TyCapt (CSingleton (PVar FZ)) (ShSingle (PVar FZ)).

Definition bound_type : Ty 0 :=
  TyCapt CEmpty (ShFun (pure_top 0) bound_result).

Local Definition bound_result_wf {n : nat} {Gamma : Ctx n} :
    TyWf (CtxSnoc Gamma (pure_top n))
      (TyCapt (CSingleton (PVar FZ)) (ShSingle (PVar FZ))).
Proof.
  apply TW_capt.
  - eapply CW_singleton. apply PT_var.
  - eapply SW_singleton. apply PT_var.
Defined.

Local Definition bound_body_typing :
    TermTy (CtxSnoc CtxNil (pure_top 0))
      (TmPath (PVar FZ)) bound_result
      (CUnion CEmpty (CSingleton (PVar FZ))).
Proof.
  eapply TT_sub.
  - eapply TT_path. apply PT_var.
  - apply TS_refl.
  - apply CS_union_right.
  - apply bound_result_wf.
  - apply CW_union.
    + apply CW_empty.
    + eapply CW_singleton. apply PT_var.
Defined.

Local Definition bound_typing :
    TermTy CtxNil
      (TmAbs (pure_top 0) (TmPath (PVar FZ))) bound_type CEmpty.
Proof.
  apply TT_abs.
  - exact bound_body_typing.
  - apply pure_top_wf.
  - apply CW_empty.
Defined.

Local Definition bound_type_wf {n : nat} {Gamma : Ctx n} :
    TyWf Gamma
      (TyCapt CEmpty
        (ShFun (pure_top n)
          (TyCapt (CSingleton (PVar FZ)) (ShSingle (PVar FZ))))).
Proof.
  apply TW_capt.
  - apply CW_empty.
  - apply SW_fun.
    + apply pure_top_wf.
    + apply bound_result_wf.
Defined.

(** The Equations definitions of weakening and context lookup compute through
    propositional equations rather than conversion.  These small, constructive
    transports expose exactly the type of the newest variable needed below. *)
Local Definition newest_capt_path
    {n : nat} {Gamma : Ctx n} {C : CaptureSet n} {S : Shape n} :
    PathTy (CtxSnoc Gamma (TyCapt C S)) (PVar FZ)
      (TauTerm
        (TyCapt (capture_rename C (weaken n))
          (shape_rename S (weaken n)))).
Proof.
  rewrite <- ty_rename_equation_1.
  change (PathTy (CtxSnoc Gamma (TyCapt C S)) (PVar FZ)
    (TauTerm (ty_weaken (TyCapt C S)))).
  apply PT_var.
Defined.

Local Definition newest_empty_capt_path
    {n : nat} {Gamma : Ctx n} {S : Shape n} :
    PathTy (CtxSnoc Gamma (TyCapt CEmpty S)) (PVar FZ)
      (TauTerm (TyCapt CEmpty (shape_rename S (weaken n)))).
Proof.
  pose proof (@newest_capt_path n Gamma CEmpty S) as H.
  rewrite capture_rename_equation_1 in H.
  exact H.
Defined.

Local Definition previous_empty_capt_path
    {n : nat} {Gamma : Ctx n} {Sh : Shape n} {U : Ty (S n)} :
    PathTy
      (CtxSnoc (CtxSnoc Gamma (TyCapt CEmpty Sh)) U)
      (PVar (FS FZ))
      (TauTerm
        (TyCapt CEmpty
          (shape_rename
            (shape_rename Sh (weaken n)) (weaken (S n))))).
Proof.
  pose proof
    (@PT_var (S (S n))
      (CtxSnoc (CtxSnoc Gamma (TyCapt CEmpty Sh)) U) (FS FZ)) as H.
  rewrite ctx_lookup_equation_3, ctx_lookup_equation_2 in H.
  unfold ty_weaken in H.
  repeat rewrite ty_rename_equation_1 in H.
  repeat rewrite capture_rename_equation_1 in H.
  exact H.
Defined.

Definition exact_first : Ty 1 :=
  TyCapt (CSingleton (PVar FZ)) (ShSingle (PVar FZ)).

Definition stored_shape : Shape 1 := ShSingle (PVar FZ).

Definition exact_body_type : Ty 1 :=
  TyCapt (CSingleton (PVar FZ))
    (ShPair exact_first label
      (TauType (shape_weaken stored_shape) (shape_weaken stored_shape))).

Local Definition stored_shape_wf :
    ShapeWf (CtxSnoc CtxNil bound_type) stored_shape.
Proof. eapply SW_singleton. apply PT_var. Defined.

Local Definition exact_to_source :
    TySub (CtxSnoc CtxNil bound_type) exact_body_type (ty_weaken source).
Proof.
  unfold exact_body_type, exact_first, source, pure_top, stored_shape, label.
  cbn [ty_weaken ty_rename shape_rename tau_rename capture_rename
    shape_weaken path_rename].
  repeat rewrite weaken_apply.
  simp capture_rename.
  repeat rewrite capture_rename_equation_3.
  repeat rewrite path_rename_equation_1.
  repeat rewrite ext_zero.
  repeat rewrite weaken_apply.
  apply TS_capt.
  - eapply CS_path. exact newest_empty_capt_path.
  - apply SS_pair.
    + apply TS_capt.
      * eapply CS_path. exact newest_empty_capt_path.
      * apply SS_top.
    + apply TAS_type.
      * eapply SS_singleton_widen. exact newest_capt_path.
      * eapply SS_singleton_alias. exact newest_capt_path.
      * apply SS_refl.
Defined.

Local Definition source_body_typing :
    TermTy (CtxSnoc CtxNil bound_type)
      (TmPair FZ label (DefType stored_shape))
      (ty_weaken source) CEmpty.
Proof.
  eapply TT_sub.
  - apply TT_type_pair. exact stored_shape_wf.
  - exact exact_to_source.
  - apply CS_refl.
  - unfold source, pure_top, ty_weaken.
    rewrite ty_rename_equation_1, capture_rename_equation_1,
      shape_rename_equation_4, ty_rename_equation_1,
      capture_rename_equation_1, shape_rename_equation_1,
      tau_rename_equation_2, !shape_rename_equation_5,
      !path_rename_equation_1, !ext_zero.
    apply source_wf.
  - apply CW_empty.
Defined.

Local Definition target_body_typing :
    TermTy (CtxSnoc CtxNil bound_type)
      (TmPair FZ label (DefType stored_shape))
      (ty_weaken target) CEmpty.
Proof.
  eapply TT_sub.
  - exact source_body_typing.
  - exact source_sub_target_general.
  - apply CS_refl.
  - unfold target, pure_top, ty_weaken.
    rewrite ty_rename_equation_1, capture_rename_equation_1,
      shape_rename_equation_4, ty_rename_equation_1,
      capture_rename_equation_1, shape_rename_equation_1,
      tau_rename_equation_2, shape_rename_equation_2,
      shape_rename_equation_1.
    apply target_wf.
  - apply CW_empty.
Defined.

Definition term : Tm 0 :=
  TmLet
    (TmAbs (pure_top 0) (TmPath (PVar FZ)))
    (TmLet
      (TmPair FZ label (DefType stored_shape))
      (TmPath (PVar FZ))).

Local Definition target_path_typing :
    TermTy (CtxSnoc (CtxSnoc CtxNil bound_type) (ty_weaken target))
      (TmPath (PVar FZ)) (ty_weaken (ty_weaken target)) CEmpty.
Proof.
  unfold target, pure_top, ty_weaken.
  rewrite ty_rename_rename.
  repeat first
    [ rewrite ty_rename_equation_1
    | rewrite capture_rename_equation_1
    | rewrite shape_rename_equation_1
    | rewrite shape_rename_equation_2
    | rewrite shape_rename_equation_4
    | rewrite shape_rename_equation_5
    | rewrite tau_rename_equation_2
    | rewrite path_rename_equation_1
    | rewrite ext_zero ].
  eapply TT_sub.
  - eapply TT_path. apply PT_var.
  - apply TS_capt.
    + eapply CS_path. exact newest_empty_capt_path.
    + eapply SS_singleton_widen. exact newest_empty_capt_path.
  - eapply CS_path. exact newest_empty_capt_path.
  - apply target_wf.
  - apply CW_empty.
Defined.

Local Definition target_let_typing :
    TermTy (CtxSnoc CtxNil bound_type)
      (TmLet
        (TmPair FZ label (DefType stored_shape))
        (TmPath (PVar FZ)))
      (ty_weaken target) CEmpty.
Proof.
  eapply TT_let.
  - exact target_body_typing.
  - exact target_path_typing.
  - unfold target, pure_top, ty_weaken.
    rewrite ty_rename_equation_1, capture_rename_equation_1,
      shape_rename_equation_4, ty_rename_equation_1,
      capture_rename_equation_1, shape_rename_equation_1,
      tau_rename_equation_2, shape_rename_equation_2,
      shape_rename_equation_1.
    apply target_wf.
  - apply CW_empty.
Defined.

Definition term_typing : TermTy CtxNil term target CEmpty.
Proof.
  unfold term.
  eapply TT_let.
  - exact bound_typing.
  - exact target_let_typing.
  - apply target_wf.
  - apply CW_empty.
Defined.

Definition function_value : Tm 0 :=
  TmAbs (pure_top 0) (TmPath (PVar FZ)).

Definition type_store1 : Store 1 :=
  StoreVal StoreEmpty function_value (IsValue_abs _ _).

Definition type_pair_value : Tm 1 :=
  TmPair FZ label (DefType stored_shape).

Definition type_store2 : Store 2 :=
  StoreVal type_store1 type_pair_value (IsValue_pair _ _ _).

Definition type_final : State 2 :=
  StateMk type_store2 [] (TmPath (PVar FZ)).

Definition term_steps : StateSteps (state_initial term) type_final.
Proof.
  unfold term, type_final, type_store2, type_pair_value, type_store1,
    function_value.
  eapply Steps_tail.
  - apply Step_let_push.
  - eapply Steps_tail.
    + apply Step_allocate.
    + eapply Steps_tail.
      * apply Step_let_push.
      * eapply Steps_tail.
        -- apply Step_allocate.
        -- apply Steps_refl.
Defined.

Theorem term_type_safety {n : nat} {final : State n}
    (steps : StateSteps (state_initial term) final) :
    StateProgress final.
Proof. exact (tm_ty_closed_type_safety term_typing steps). Qed.

Theorem allocated_type_pair_progress : StateProgress type_final.
Proof. exact (tm_ty_closed_type_safety term_typing term_steps). Qed.

(** Capture-set members. *)
Definition capture_source : Ty 0 :=
  TyCapt CEmpty
    (ShPair (pure_top 0) label
      (TauCapture
        (CSingleton (PVar FZ))
        (CSingleton (PVar FZ)))).

Definition capture_target : Ty 0 :=
  TyCapt CEmpty
    (ShPair (pure_top 0) label
      (TauCapture CEmpty (CSingleton (PVar FZ)))).

Local Definition capture_source_sub_capture_target_general
    {n : nat} {Gamma : Ctx n} :
    TySub Gamma
      (TyCapt CEmpty
        (ShPair (pure_top n) label
          (TauCapture
            (CSingleton (PVar FZ))
            (CSingleton (PVar FZ)))))
      (TyCapt CEmpty
        (ShPair (pure_top n) label
          (TauCapture CEmpty (CSingleton (PVar FZ))))).
Proof.
  apply TS_capt.
  - apply CS_refl.
  - apply SS_pair.
    + apply TS_refl.
    + apply TAS_capture.
      * apply CS_empty.
      * apply CS_refl.
      * apply CS_refl.
Defined.

Definition capture_source_sub_capture_target :
    TySub CtxNil capture_source capture_target :=
  capture_source_sub_capture_target_general.

Local Definition capture_source_wf {n : nat} {Gamma : Ctx n} :
    TyWf Gamma
      (TyCapt CEmpty
        (ShPair (pure_top n) label
          (TauCapture
            (CSingleton (PVar FZ))
            (CSingleton (PVar FZ))))).
Proof.
  apply TW_capt.
  - apply CW_empty.
  - apply SW_pair.
    + apply pure_top_wf.
    + apply TAW_capture.
      * eapply CW_singleton. apply PT_var.
      * eapply CW_singleton. apply PT_var.
      * apply CS_refl.
Defined.

Local Definition capture_target_wf {n : nat} {Gamma : Ctx n} :
    TyWf Gamma
      (TyCapt CEmpty
        (ShPair (pure_top n) label
          (TauCapture CEmpty (CSingleton (PVar FZ))))).
Proof.
  apply TW_capt.
  - apply CW_empty.
  - apply SW_pair.
    + apply pure_top_wf.
    + apply TAW_capture.
      * apply CW_empty.
      * eapply CW_singleton. apply PT_var.
      * apply CS_empty.
Defined.

Definition stored_capture : CaptureSet 1 := CSingleton (PVar FZ).

Definition exact_capture_body_type : Ty 1 :=
  TyCapt (CSingleton (PVar FZ))
    (ShPair exact_first label
      (TauCapture
        (capture_weaken stored_capture)
        (capture_weaken stored_capture))).

Local Definition stored_capture_wf :
    CaptureWf (CtxSnoc CtxNil bound_type) stored_capture.
Proof. eapply CW_singleton. apply PT_var. Defined.

Local Definition exact_capture_to_source :
    TySub (CtxSnoc CtxNil bound_type)
      exact_capture_body_type (ty_weaken capture_source).
Proof.
  unfold exact_capture_body_type, exact_first, capture_source, pure_top,
    stored_capture, label.
  cbn [ty_weaken ty_rename shape_rename tau_rename capture_rename
    capture_weaken path_rename].
  repeat rewrite weaken_apply.
  simp capture_rename.
  repeat rewrite capture_rename_equation_3.
  repeat rewrite path_rename_equation_1.
  repeat rewrite ext_zero.
  repeat rewrite weaken_apply.
  apply TS_capt.
  - eapply CS_path. exact newest_empty_capt_path.
  - apply SS_pair.
    + apply TS_capt.
      * eapply CS_path. exact newest_empty_capt_path.
      * apply SS_top.
    + apply TAS_capture.
      * rewrite capture_rename_equation_3, path_rename_equation_1,
          ext_zero.
        eapply CS_path. exact newest_capt_path.
      * rewrite capture_rename_equation_3, path_rename_equation_1,
          ext_zero.
        eapply CS_alias. exact newest_capt_path.
      * apply CS_refl.
Defined.

Local Definition capture_source_body_typing :
    TermTy (CtxSnoc CtxNil bound_type)
      (TmPair FZ label (DefCapture stored_capture))
      (ty_weaken capture_source) CEmpty.
Proof.
  eapply TT_sub.
  - apply TT_capture_pair. exact stored_capture_wf.
  - exact exact_capture_to_source.
  - apply CS_refl.
  - unfold capture_source, pure_top, ty_weaken.
    rewrite ty_rename_equation_1, capture_rename_equation_1,
      shape_rename_equation_4, ty_rename_equation_1,
      capture_rename_equation_1, shape_rename_equation_1,
      tau_rename_equation_3, !capture_rename_equation_3,
      !path_rename_equation_1, !ext_zero.
    apply capture_source_wf.
  - apply CW_empty.
Defined.

Local Definition capture_target_body_typing :
    TermTy (CtxSnoc CtxNil bound_type)
      (TmPair FZ label (DefCapture stored_capture))
      (ty_weaken capture_target) CEmpty.
Proof.
  eapply TT_sub.
  - exact capture_source_body_typing.
  - exact capture_source_sub_capture_target_general.
  - apply CS_refl.
  - unfold capture_target, pure_top, ty_weaken.
    rewrite ty_rename_equation_1, capture_rename_equation_1,
      shape_rename_equation_4, ty_rename_equation_1,
      capture_rename_equation_1, shape_rename_equation_1,
      tau_rename_equation_3, capture_rename_equation_1,
      capture_rename_equation_3, path_rename_equation_1, ext_zero.
    apply capture_target_wf.
  - apply CW_empty.
Defined.

Definition capture_term : Tm 0 :=
  TmLet
    (TmAbs (pure_top 0) (TmPath (PVar FZ)))
    (TmLet
      (TmPair FZ label (DefCapture stored_capture))
      (TmPath (PVar FZ))).

Local Definition capture_target_path_typing :
    TermTy
      (CtxSnoc (CtxSnoc CtxNil bound_type) (ty_weaken capture_target))
      (TmPath (PVar FZ)) (ty_weaken (ty_weaken capture_target)) CEmpty.
Proof.
  unfold capture_target, pure_top, ty_weaken.
  rewrite ty_rename_rename.
  repeat first
    [ rewrite ty_rename_equation_1
    | rewrite capture_rename_equation_1
    | rewrite capture_rename_equation_3
    | rewrite shape_rename_equation_1
    | rewrite shape_rename_equation_4
    | rewrite tau_rename_equation_3
    | rewrite path_rename_equation_1
    | rewrite ext_zero ].
  eapply TT_sub.
  - eapply TT_path. apply PT_var.
  - apply TS_capt.
    + eapply CS_path. exact newest_empty_capt_path.
    + eapply SS_singleton_widen. exact newest_empty_capt_path.
  - eapply CS_path. exact newest_empty_capt_path.
  - apply capture_target_wf.
  - apply CW_empty.
Defined.

Local Definition capture_target_let_typing :
    TermTy (CtxSnoc CtxNil bound_type)
      (TmLet
        (TmPair FZ label (DefCapture stored_capture))
        (TmPath (PVar FZ)))
      (ty_weaken capture_target) CEmpty.
Proof.
  eapply TT_let.
  - exact capture_target_body_typing.
  - exact capture_target_path_typing.
  - unfold capture_target, pure_top, ty_weaken.
    rewrite ty_rename_equation_1, capture_rename_equation_1,
      shape_rename_equation_4, ty_rename_equation_1,
      capture_rename_equation_1, shape_rename_equation_1,
      tau_rename_equation_3, capture_rename_equation_1,
      capture_rename_equation_3, path_rename_equation_1, ext_zero.
    apply capture_target_wf.
  - apply CW_empty.
Defined.

Definition capture_term_typing :
    TermTy CtxNil capture_term capture_target CEmpty.
Proof.
  unfold capture_term.
  eapply TT_let.
  - exact bound_typing.
  - exact capture_target_let_typing.
  - apply capture_target_wf.
  - apply CW_empty.
Defined.

Definition capture_pair_value : Tm 1 :=
  TmPair FZ label (DefCapture stored_capture).

Definition capture_store2 : Store 2 :=
  StoreVal type_store1 capture_pair_value (IsValue_pair _ _ _).

Definition capture_final : State 2 :=
  StateMk capture_store2 [] (TmPath (PVar FZ)).

Definition capture_term_steps :
    StateSteps (state_initial capture_term) capture_final.
Proof.
  unfold capture_term, capture_final, capture_store2, capture_pair_value,
    type_store1, function_value.
  eapply Steps_tail.
  - apply Step_let_push.
  - eapply Steps_tail.
    + apply Step_allocate.
    + eapply Steps_tail.
      * apply Step_let_push.
      * eapply Steps_tail.
        -- apply Step_allocate.
        -- apply Steps_refl.
Defined.

Theorem capture_term_type_safety {n : nat} {final : State n}
    (steps : StateSteps (state_initial capture_term) final) :
    StateProgress final.
Proof. exact (tm_ty_closed_type_safety capture_term_typing steps). Qed.

Theorem allocated_capture_pair_progress : StateProgress capture_final.
Proof.
  exact (tm_ty_closed_type_safety capture_term_typing capture_term_steps).
Qed.

(** Resolving an abstract capture-set selection. *)
Local Definition exact_capture_pair_typing :
    TermTy (CtxSnoc CtxNil bound_type)
      (TmPair FZ label (DefCapture stored_capture))
      exact_capture_body_type CEmpty.
Proof. apply TT_capture_pair. exact stored_capture_wf. Defined.

Local Definition exact_capture_member :
    PathTy
      (CtxSnoc (CtxSnoc CtxNil bound_type) exact_capture_body_type)
      (PSel (PVar FZ) label)
      (TauCapture
        (CSingleton (PVar (FS FZ)))
        (CSingleton (PVar (FS FZ)))).
Proof.
  assert (receiver :
      PathTy
        (CtxSnoc (CtxSnoc CtxNil bound_type) exact_capture_body_type)
        (PVar FZ) (TauTerm (ty_weaken exact_capture_body_type))).
  { change (PathTy
      (CtxSnoc (CtxSnoc CtxNil bound_type) exact_capture_body_type)
      (PVar FZ)
      (TauTerm
        (ctx_lookup
          (CtxSnoc (CtxSnoc CtxNil bound_type) exact_capture_body_type)
          FZ))).
    apply PT_var. }
  pose proof (PT_sel_r receiver) as selected.
  unfold exact_capture_body_type, exact_first, stored_capture, label
    in selected |- *.
  cbn [ctx_lookup ty_weaken ty_rename shape_rename tau_rename
    capture_weaken capture_rename path_rename tau_open tau_subst
    capture_subst path_subst path_subst_openAt] in selected |- *.
  repeat rewrite weaken_apply in selected.
  exact selected.
Defined.

Local Definition capture_selection_to_empty :
    CaptureSub
      (CtxSnoc (CtxSnoc CtxNil bound_type) exact_capture_body_type)
      (CSingleton (PVar (FS FZ))) CEmpty.
Proof.
  eapply CS_trans.
  - eapply CS_select_lower.
    + exact exact_capture_member.
    + apply CS_refl.
  - eapply CS_trans.
    + eapply CS_select_upper.
      * exact exact_capture_member.
      * apply CS_refl.
    + eapply CS_path.
      unfold bound_type.
      exact previous_empty_capt_path.
Defined.

Local Definition selected_bound_subtyping :
    TySub
      (CtxSnoc (CtxSnoc CtxNil bound_type) exact_capture_body_type)
      (TyCapt
        (CSingleton (PVar (FS FZ)))
        (ShSingle (PVar (FS FZ))))
      (ty_weaken (ty_weaken bound_type)).
Proof.
  unfold bound_type, ty_weaken.
  repeat rewrite ty_rename_equation_1.
  repeat rewrite capture_rename_equation_1.
  apply TS_capt.
  - eapply CS_path. exact previous_empty_capt_path.
  - eapply SS_singleton_widen. exact previous_empty_capt_path.
Defined.

Local Definition bound_type_twice_wf :
    TyWf
      (CtxSnoc (CtxSnoc CtxNil bound_type) exact_capture_body_type)
      (ty_weaken (ty_weaken bound_type)).
Proof.
  unfold bound_type, bound_result, pure_top, ty_weaken.
  rewrite ty_rename_rename.
  repeat first
    [ rewrite ty_rename_equation_1
    | rewrite capture_rename_equation_1
    | rewrite capture_rename_equation_3
    | rewrite shape_rename_equation_1
    | rewrite shape_rename_equation_3
    | rewrite shape_rename_equation_5
    | rewrite path_rename_equation_1
    | rewrite ext_zero ].
  apply bound_type_wf.
Defined.

Local Definition selected_capture_body_typing :
    TermTy
      (CtxSnoc (CtxSnoc CtxNil bound_type) exact_capture_body_type)
      (TmPath (PVar (FS FZ)))
      (ty_weaken (ty_weaken bound_type)) CEmpty.
Proof.
  eapply TT_sub.
  - eapply TT_path. apply PT_var.
  - exact selected_bound_subtyping.
  - exact capture_selection_to_empty.
  - exact bound_type_twice_wf.
  - apply CW_empty.
Defined.

Local Definition bound_type_once_wf :
    TyWf (CtxSnoc CtxNil bound_type) (ty_weaken bound_type).
Proof.
  unfold bound_type, bound_result, pure_top, ty_weaken.
  repeat first
    [ rewrite ty_rename_equation_1
    | rewrite capture_rename_equation_1
    | rewrite capture_rename_equation_3
    | rewrite shape_rename_equation_1
    | rewrite shape_rename_equation_3
    | rewrite shape_rename_equation_5
    | rewrite path_rename_equation_1
    | rewrite ext_zero ].
  apply bound_type_wf.
Defined.

Local Definition capture_selection_let_typing :
    TermTy (CtxSnoc CtxNil bound_type)
      (TmLet
        (TmPair FZ label (DefCapture stored_capture))
        (TmPath (PVar (FS FZ))))
      (ty_weaken bound_type) CEmpty.
Proof.
  eapply TT_let.
  - exact exact_capture_pair_typing.
  - exact selected_capture_body_typing.
  - exact bound_type_once_wf.
  - apply CW_empty.
Defined.

Definition capture_selection_term : Tm 0 :=
  TmLet
    function_value
    (TmLet
      (TmPair FZ label (DefCapture stored_capture))
      (TmPath (PVar (FS FZ)))).

Definition capture_selection_term_typing :
    TermTy CtxNil capture_selection_term bound_type CEmpty.
Proof.
  unfold capture_selection_term.
  eapply TT_let.
  - exact bound_typing.
  - exact capture_selection_let_typing.
  - apply bound_type_wf.
  - apply CW_empty.
Defined.

Definition capture_selection_final : State 2 :=
  StateMk capture_store2 [] (TmPath (PVar (FS FZ))).

Definition capture_selection_term_steps :
    StateSteps (state_initial capture_selection_term)
      capture_selection_final.
Proof.
  unfold capture_selection_term, capture_selection_final, capture_store2,
    capture_pair_value, type_store1, function_value.
  eapply Steps_tail.
  - apply Step_let_push.
  - eapply Steps_tail.
    + apply Step_allocate.
    + eapply Steps_tail.
      * apply Step_let_push.
      * eapply Steps_tail.
        -- apply Step_allocate.
        -- apply Steps_refl.
Defined.

Theorem selected_capture_member_progress :
    StateProgress capture_selection_final.
Proof.
  exact (tm_ty_closed_type_safety
    capture_selection_term_typing capture_selection_term_steps).
Qed.

Print Assumptions source_sub_target.
Print Assumptions term_typing.
Print Assumptions term_type_safety.
Print Assumptions allocated_type_pair_progress.
Print Assumptions capture_source_sub_capture_target.
Print Assumptions capture_term_typing.
Print Assumptions capture_term_type_safety.
Print Assumptions allocated_capture_pair_progress.
Print Assumptions exact_capture_member.
Print Assumptions capture_selection_term_typing.
Print Assumptions selected_capture_member_progress.
