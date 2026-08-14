From PathDependent.LambdaPFC Require Import
  FinFun Syntax Context Typing Runtime SemanticSafety.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

Definition label : Name := 0.

(** Proper dependent members with a non-singleton first component. *)
Definition proper_source : Ty 0 :=
  TyPair TyTop label
    (TauTy (TySingle (PVar FZ))).

Definition proper_target : Ty 0 :=
  TyPair TyTop label (TauTy TyTop).

Definition proper_subtyping :
    TauSub CtxNil (TauTy proper_source)
      (TauTy proper_target) :=
  TauSub_pair TauSub_refl TauSub_top.

(** Abstract interval members exercise the kind-generic pair rule. *)
Definition interval_source : Ty 0 :=
  TyPair TyTop label
    (TauIntv (TySingle (PVar FZ)) (TySingle (PVar FZ))).

Definition interval_target : Ty 0 :=
  TyPair TyTop label (TauIntv TyBot TyTop).

Definition interval_subtyping :
    TauSub CtxNil (TauTy interval_source)
      (TauTy interval_target) :=
  TauSub_pair TauSub_refl
    (TauSub_bounds TauSub_bot TauSub_top TauSub_refl).

(** Closed term used by the end-to-end regression. *)
Definition term : Tm 0 :=
  TmLet
    (TmAbs TyTop (TmPath (PVar FZ)))
    (TmPair FZ label
      (DefType (TySingle (PVar FZ)))).

Local Definition interval_source_wf {n : nat}
    {Gamma : Ctx n} :
    TauWf Gamma
      (TauTy (TyPair TyTop label
        (TauIntv (TySingle (PVar FZ)) (TySingle (PVar FZ))))) :=
  TauWf_pair TauWf_top
    (TauWf_bounds
      (TauWf_path (PathTy_var (CtxSnoc Gamma TyTop) FZ))
      (TauWf_path (PathTy_var (CtxSnoc Gamma TyTop) FZ))
      TauSub_refl).

Local Definition interval_target_wf {n : nat}
    {Gamma : Ctx n} :
    TauWf Gamma
      (TauTy (TyPair TyTop label
        (TauIntv TyBot TyTop))) :=
  TauWf_pair TauWf_top
    (TauWf_bounds TauWf_bot TauWf_top TauSub_bot).

Local Definition bound_typing :
    TmTy CtxNil (TmAbs TyTop (TmPath (PVar FZ))) TyTop :=
  TmTy_sub
    (TmTy_abs
      (TmTy_path (PathTy_var (CtxSnoc CtxNil TyTop) FZ))
      TauWf_top)
    TauSub_top TauWf_top.

Local Definition exact_to_interval_source :
    TauSub (CtxSnoc CtxNil TyTop)
      (TauTy (TyPair (TySingle (PVar FZ)) label
        (tau_weaken
          (TauIntv (TySingle (PVar FZ)) (TySingle (PVar FZ))))))
      (TauTy (ty_weaken interval_source)) :=
  TauSub_pair TauSub_top
    (TauSub_bounds
      (TauSub_widen
        (PathTy_var
          (CtxSnoc (CtxSnoc CtxNil TyTop) (TySingle (PVar FZ))) FZ))
      (TauSub_symm
        (PathTy_var
          (CtxSnoc (CtxSnoc CtxNil TyTop) (TySingle (PVar FZ))) FZ))
      TauSub_refl).

Local Definition source_typing :
    TmTy (CtxSnoc CtxNil TyTop)
      (TmPair FZ label (DefType (TySingle (PVar FZ))))
      (ty_weaken interval_source) :=
  TmTy_sub
    (TmTy_tpair
      (TauWf_path
        (PathTy_var (CtxSnoc CtxNil TyTop) FZ)))
    exact_to_interval_source
    interval_source_wf.

Local Definition body_typing :
    TmTy (CtxSnoc CtxNil TyTop)
      (TmPair FZ label (DefType (TySingle (PVar FZ))))
      (ty_weaken interval_target) :=
  TmTy_sub source_typing
    (TauSub_pair TauSub_refl
      (TauSub_bounds TauSub_bot TauSub_top TauSub_refl))
    interval_target_wf.

Definition term_typing :
    TmTy CtxNil term interval_target :=
  TmTy_let bound_typing interval_target_wf body_typing.

Theorem term_type_safety {n : nat} {target : State n}
    (steps : StateSteps (state_initial term) target) :
    StateProgress target.
Proof.
  exact (tm_ty_closed_type_safety term_typing steps).
Qed.

Print Assumptions proper_subtyping.
Print Assumptions interval_subtyping.
Print Assumptions term_typing.
Print Assumptions term_type_safety.
