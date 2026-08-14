From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store Cont State Machine PathReduction
  RuntimeConversion ScopedRuntimeEq StructuralRuntimeTyping
  StructuralTermTyping StructuralMachineInvariant
  StructuralApplicationBoundary StructuralApplicationCompatibility.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Beta preservation from precise function reflection. *)
Theorem StructPreserve_app_precise {n : nat} {G : Ctx n}
    {s : Store n} {K : Tm_Cont n} {p q : Path n}
    {x y : Fin.t n} {A : Ty n} {body : Tm (S n)} {T : Ty n}
    (Href : Store_StructPreciseFunctionReflection G s)
    (Hp : Path_reduce p s x) (Hq : Path_reduce q s y)
    (Hbind : Store_Binds s x (tm_abs A body))
    (H : State_StructTy G (mk_state s K (tm_app p q)) T) :
    StructPreserve G (mk_state s K (Tm_open body y)) T.
Proof.
  destruct H as [Input Hstore Hcont Happ].
  destruct (Tm_StructCheck_app_inversion Happ)
    as (S0 & U & Hfun & Harg & post).
  pose proof
    (Store_StructTy_open_application_of_preciseFunctionReflection
      Hstore Href Hp Hq Hbind Hfun Harg) as Hopened.
  apply struct_preserve_same. eapply state_struct_ty_ok.
  - exact Hstore.
  - exact Hcont.
  - exact (post (Tm_open body y) Hopened).
Qed.

(** Every machine transition preserves the structural state invariant,
    assuming precise function reflection for the source store. *)
Theorem State_Step_struct_preservation {n m : nat} {G : Ctx n}
    {source : State n} {target : State m} {T : Ty n}
    (Href : Store_StructPreciseFunctionReflection G (state_store source))
    (step : State_Step source target)
    (H : State_StructTy G source T) :
    StructPreserve G target T.
Proof.
  destruct step.
  - exact (StructPreserve_app_precise Href H0 H1 H2 H).
  - exact (StructPreserve_path H0 H).
  - exact (StructPreserve_let_push H).
  - exact (StructPreserve_rename H).
  - exact (StructPreserve_lift Hv H).
  - exact (StructPreserve_ascribe H).
Qed.

(** Complete preservation with precise reflection reduced to function
    signature pushback. *)
Theorem State_Step_struct_preservation_of_pushback {n m : nat}
    {G : Ctx n} {source : State n} {target : State m} {T : Ty n}
    (Hpush : Store_StructPreciseFunctionPushback G (state_store source))
    (step : State_Step source target)
    (H : State_StructTy G source T) :
    StructPreserve G target T.
Proof.
  exact (State_Step_struct_preservation
    (Store_StructPreciseFunctionPushback_to_preciseFunctionReflection Hpush)
    step H).
Qed.

Print Assumptions StructPreserve_app_precise.
Print Assumptions State_Step_struct_preservation.
Print Assumptions State_Step_struct_preservation_of_pushback.
