From PathDependent.LambdaPCC Require Import FinFun Syntax Context Typing.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Small static capture regressions. *)
Definition capture_label : Name := 0.
Definition term_label : Name := 1.

Definition regression_first_type : Ty 0 := TyCapt CEmpty ShTop.

(** Its capture member is exactly the dependent first component. *)
Definition regression_receiver_type : Ty 0 :=
  TyCapt CEmpty
    (ShPair regression_first_type capture_label
      (TauCapture
        (CSingleton (PVar FZ))
        (CSingleton (PVar FZ)))).

Definition regression_receiver_context : Ctx 1 :=
  CtxSnoc CtxNil regression_receiver_type.

Definition regression_receiver : Path 1 := PVar FZ.

Definition exact_capture_member :
    PathTy regression_receiver_context
      (PSel regression_receiver capture_label)
      (TauCapture
        (CSingleton (PFst regression_receiver))
        (CSingleton (PFst regression_receiver))).
Proof.
  assert (receiver_typed :
      PathTy regression_receiver_context regression_receiver
        (TauTerm (ty_weaken regression_receiver_type))).
  { unfold regression_receiver_context, regression_receiver.
    change (PathTy (CtxSnoc CtxNil regression_receiver_type) (PVar FZ)
      (TauTerm (ctx_lookup (CtxSnoc CtxNil regression_receiver_type) FZ))).
    apply PT_var. }
  pose proof (PT_sel_r receiver_typed) as selected.
  unfold regression_receiver_type, regression_first_type, capture_label,
    regression_receiver in selected |- *.
  cbn [ty_weaken ty_rename shape_rename tau_rename capture_rename
    path_rename tau_open tau_subst capture_subst path_subst
    path_subst_openAt] in selected |- *.
  repeat rewrite weaken_apply in selected.
  exact selected.
Defined.

Definition capture_member_lower :
    CaptureSub regression_receiver_context
      (CSingleton (PFst regression_receiver))
      (CSelect regression_receiver capture_label).
Proof.
  eapply CS_select_lower.
  - exact exact_capture_member.
  - apply CS_refl.
Defined.

Definition capture_member_upper :
    CaptureSub regression_receiver_context
      (CSelect regression_receiver capture_label)
      (CSingleton (PFst regression_receiver)).
Proof.
  eapply CS_select_upper.
  - exact exact_capture_member.
  - apply CS_refl.
Defined.

(** Pair covariance at capture-member kind. *)
Definition capture_pair_source : Shape 0 :=
  ShPair regression_first_type capture_label
    (TauCapture
      (CSingleton (PVar FZ))
      (CSingleton (PVar FZ))).

Definition capture_pair_target : Shape 0 :=
  ShPair regression_first_type capture_label
    (TauCapture CEmpty (CSingleton (PVar FZ))).

Definition capture_pair_covariance :
    ShapeSub CtxNil capture_pair_source capture_pair_target.
Proof.
  unfold capture_pair_source, capture_pair_target.
  apply SS_pair.
  - apply TS_refl.
  - apply TAS_capture.
    + apply CS_empty.
    + apply CS_refl.
    + apply CS_refl.
Defined.

(** A codomain that captures a projection and a selection rooted there. *)
Definition dependent_codomain (n : nat) : Ty (S n) :=
  TyCapt
    (CUnion
      (CSingleton (PFst (PVar FZ)))
      (CSingleton (PSel (PFst (PVar FZ)) term_label)))
    ShTop.

Lemma dependent_codomain_beta {n : nat} (q : Path n) :
    ty_open (dependent_codomain n) q =
      TyCapt
        (CUnion
          (CSingleton (PFst q))
          (CSingleton (PSel (PFst q) term_label)))
        ShTop.
Proof. reflexivity. Qed.

Definition application_opens_capture {n : nat}
    {Gamma : Ctx n} {p q : Path n} {S0 : Ty n}
    {Cfun Cp Cq : CaptureSet n}
    (function_typed : TermTy Gamma (TmPath p)
      (TyCapt Cfun (ShFun S0 (dependent_codomain n))) Cp)
    (argument_typed : TermTy Gamma (TmPath q) S0 Cq) :
    TermTy Gamma (TmApp p q)
      (TyCapt
        (CUnion
          (CSingleton (PFst q))
          (CSingleton (PSel (PFst q) term_label)))
        ShTop)
      (CUnion Cp Cq).
Proof.
  rewrite <- dependent_codomain_beta.
  exact (TT_app function_typed argument_typed).
Defined.

Definition first_projection_contracts {n : nat} {Gamma : Ctx n}
    {p : Path n} {T : Ty n}
    (typed : PathTy Gamma (PFst p) (TauTerm T)) :
    CaptureSub Gamma (CSingleton (PFst p)) (CSingleton p) :=
  CS_fst_root typed.

Definition term_selection_contracts {n : nat} {Gamma : Ctx n}
    {p : Path n} {a : Name} {T : Ty n}
    (typed : PathTy Gamma (PSel p a) (TauTerm T)) :
    CaptureSub Gamma (CSingleton (PSel p a)) (CSingleton p) :=
  CS_sel_root typed.

Print Assumptions exact_capture_member.
Print Assumptions application_opens_capture.
