From Equations Require Import Equations.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store PathReduction RuntimeConversion
  ScopedRuntimeEq StructuralRuntimeTyping StructuralTermTyping
  StructuralRuntimeLemmas StructuralMachineInvariant
  StructuralApplicationBoundary StructuralPathSubstitution
  StructuralRefinedProgress StructuralValueInversion.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Application compatibility after the operator has resolved to a store
    location.  The argument path is retained because its reduction controls
    both runtime opening and comparison with the statically mentioned path. *)
Definition Store_StructFunctionReflection {n : nat}
    (G : Ctx n) (s : Store n) : Prop :=
  forall (q : Path n) (x y : Fin.t n)
    (S0 A X : Ty n) (U B : Ty (S n)) (body : Tm (S n)),
    Store_StructTy G s ->
    Path_reduce q s y ->
    Store_Binds s x (tm_abs A body) ->
    Ctx_Binds G x X ->
    Tau_StructSub G (Path_RuntimeEq s)
      (tau_ty (ty_fun A B)) (tau_ty X) ->
    Tm_StructCheck G (Path_RuntimeEq s)
      (tm_path (path_var x)) (ty_fun S0 U) ->
    Tm_StructCheck G (Path_RuntimeEq s) (tm_path q) S0 ->
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S0) (tau_ty A) /\
      (forall t : Tm n,
        Tm_StructCheck G (Path_RuntimeEq s) t
          (Ty_rename B (FinFun.openAt y)) ->
        Tm_StructCheck G (Path_RuntimeEq s) t (Ty_open U q)).

(** The original application contract is exactly reflection at the resolved
    operator variable. *)
Theorem Store_structAppCompatibility_iff_functionReflection {n : nat}
    {G : Ctx n} {s : Store n} :
    Store_StructAppCompatibility G s <->
      Store_StructFunctionReflection G s.
Proof.
  split.
  - intros H q x y S0 A X U B body Hstore Hq Hbind Hctx Hactual
      Hfun Harg.
    exact (H (path_var x) q x y S0 A X U B body Hstore
      (path_reduce_var x s) Hq Hbind Hctx Hactual Hfun Harg).
  - intros H p q x y S0 A X U B body Hstore Hp Hq Hbind Hctx
      Hactual Hfun Harg.
    exact (H q x y S0 A X U B body Hstore Hq Hbind Hctx Hactual
      (Tm_StructCheck_reduce_path Hp Hfun) Harg).
Qed.

(** A dependent result opened at a reducing argument path is structurally
    convertible to the same result opened at the runtime location. *)
Theorem Tau_StructConv_open_result_runtime {n : nat} {s : Store n}
    {q : Path n} {y : Fin.t n} {U : Ty (S n)}
    (Hq : Path_reduce q s y) :
    Tau_StructConv (Path_RuntimeEq s)
      (tau_ty (Ty_rename U (FinFun.openAt y)))
      (tau_ty (Ty_open U q)).
Proof.
  change (Tau_StructConv (Path_RuntimeEq s)
    (Tau_rename (tau_ty U) (FinFun.openAt y))
    (Tau_open (tau_ty U) q)).
  rewrite Tau_rename_openAt_eq_open_var.
  apply tau_struct_conv_replace.
  apply path_runtime_eq_symm. exact (Path_RuntimeEq_of_reduce Hq).
Qed.

(** Co-resolution casts a checked term between the two result openings once
    the target opening is known structurally well formed. *)
Theorem Tm_StructCheck_cast_open_result_runtime {n : nat} {G : Ctx n}
    {s : Store n} {q : Path n} {y : Fin.t n} {U : Ty (S n)}
    {t : Tm n}
    (Hq : Path_reduce q s y)
    (HU : Tau_StructWf G (Path_RuntimeEq s) (tau_ty (Ty_open U q)))
    (Ht : Tm_StructCheck G (Path_RuntimeEq s) t
      (Ty_rename U (FinFun.openAt y))) :
    Tm_StructCheck G (Path_RuntimeEq s) t (Ty_open U q).
Proof.
  eapply tm_struct_check_sub.
  - exact Ht.
  - apply tau_struct_sub_conv.
    exact (Tau_StructConv_open_result_runtime Hq).
  - exact HU.
Qed.

(** Internal inversion used to retain the original function indices in
    later proofs. *)
Local Lemma Tau_StructWf_fun_parts {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {S0 : Ty n} {U : Ty (S n)}
    (H : Tau_StructWf G R (tau_ty (ty_fun S0 U))) :
    Tau_StructWf G R (tau_ty S0) /\
      Tau_StructWf (ctx_snoc G S0) (Path_ScopedLift R) (tau_ty U).
Proof.
  dependent elimination H. split; assumption.
Qed.

(** Internal precise-abstraction inversion which keeps the ambient indices
    available to the application proof. *)
Local Lemma Tm_StructPrecise_abs_parts {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {A : Ty n}
    {body : Tm (S n)} {P : Ty n}
    (H : Tm_StructPrecise G R (tm_abs A body) P) :
    exists B : Ty (S n),
      P = ty_fun A B /\
      Tm_StructCheck (ctx_snoc G A) (Path_ScopedLift R) body B /\
      Tau_StructWf G R (tau_ty A).
Proof.
  dependent elimination H. exists T. repeat split; try reflexivity;
    assumption.
Qed.

(** Observation-sized function reflection, where the closure codomain is
    the syntax-directed type supplied by the precise abstraction rule. *)
Definition Store_StructPreciseFunctionReflection {n : nat}
    (G : Ctx n) (s : Store n) : Prop :=
  forall (q : Path n) (x y : Fin.t n)
    (S0 A X : Ty n) (U B : Ty (S n)) (body : Tm (S n)),
    Store_StructTy G s ->
    Path_reduce q s y ->
    Store_Binds s x (tm_abs A body) ->
    Ctx_Binds G x X ->
    Tm_StructPrecise G (Path_RuntimeEq s)
      (tm_abs A body) (ty_fun A B) ->
    Tau_StructSub G (Path_RuntimeEq s)
      (tau_ty (ty_fun A B)) (tau_ty X) ->
    Tm_StructCheck G (Path_RuntimeEq s)
      (tm_path (path_var x)) (ty_fun S0 U) ->
    Tm_StructCheck G (Path_RuntimeEq s) (tm_path q) S0 ->
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S0) (tau_ty A) /\
      (forall t : Tm n,
        Tm_StructCheck G (Path_RuntimeEq s) t
          (Ty_rename B (FinFun.openAt y)) ->
        Tm_StructCheck G (Path_RuntimeEq s) t (Ty_open U q)).

(** Function-specific pushback through a public store type. *)
Definition Store_StructPreciseFunctionPushback {n : nat}
    (G : Ctx n) (s : Store n) : Prop :=
  forall (x : Fin.t n) (S0 A X : Ty n)
    (U B : Ty (S n)) (body : Tm (S n)),
    Store_StructTy G s ->
    Store_Binds s x (tm_abs A body) ->
    Ctx_Binds G x X ->
    Tm_StructPrecise G (Path_RuntimeEq s)
      (tm_abs A body) (ty_fun A B) ->
    Tau_StructSub G (Path_RuntimeEq s)
      (tau_ty (ty_fun A B)) (tau_ty X) ->
    Tm_StructCheck G (Path_RuntimeEq s)
      (tm_path (path_var x)) (ty_fun S0 U) ->
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S0) (tau_ty A) /\
      Tau_StructSub (ctx_snoc G S0)
        (Path_ScopedLift (Path_RuntimeEq s))
        (tau_ty B) (tau_ty U).

(** Dependent substitution and final runtime conversion needed to open the
    result of a beta step. *)
Definition Store_StructResultOpening {n : nat}
    (G : Ctx n) (s : Store n) : Prop :=
  forall (q : Path n) (y : Fin.t n) (S0 : Ty n)
    (B U : Ty (S n)) (t : Tm n),
    Path_reduce q s y ->
    Tm_StructCheck G (Path_RuntimeEq s) (tm_path q) S0 ->
    Tau_StructWf G (Path_RuntimeEq s) (tau_ty (ty_fun S0 U)) ->
    Tau_StructSub (ctx_snoc G S0)
      (Path_ScopedLift (Path_RuntimeEq s))
      (tau_ty B) (tau_ty U) ->
    Tm_StructCheck G (Path_RuntimeEq s) t
      (Ty_rename B (FinFun.openAt y)) ->
    Tm_StructCheck G (Path_RuntimeEq s) t (Ty_open U q).

(** Structural result opening follows constructively from path substitution
    and co-resolution. *)
Theorem Store_structResultOpening {n : nat}
    (G : Ctx n) (s : Store n) : Store_StructResultOpening G s.
Proof.
  intros q y S0 B U t Hq Harg HfunWf Hcod Ht.
  destruct (Tm_StructCheck_path_inversion Harg eq_refl)
    as [P HqCheck HqSingle HqWf].
  assert (HqS : Path_StructCheck G (Path_RuntimeEq s) q (tau_ty S0)).
  { exact (path_struct_check_promote HqCheck HqSingle). }
  pose proof (Tm_StructCheck_reduce_path Hq Harg) as HyArg.
  destruct (Tm_StructCheck_path_inversion HyArg eq_refl)
    as [Q HyCheck HySingle HyWf].
  assert (HyS : Path_StructCheck G (Path_RuntimeEq s)
      (path_var y) (tau_ty S0)).
  { exact (path_struct_check_promote HyCheck HySingle). }
  destruct (Tau_StructWf_fun_parts HfunWf) as [_ HcodWf].
  pose proof (Tau_StructWf_open_path HcodWf
    (Path_RuntimeEq_isEquivCongr s) HqS) as Htarget.
  pose proof (Tau_StructSub_open_var Hcod
    (Path_RuntimeEq_isEquivCongr s) HyS) as Hopened.
  assert (Hresult : Tau_StructSub G (Path_RuntimeEq s)
      (tau_ty (Ty_rename B (FinFun.openAt y)))
      (tau_ty (Ty_open U q))).
  { eapply tau_struct_sub_trans.
    - exact Hopened.
    - apply tau_struct_sub_conv.
      exact (Tau_StructConv_open_result_runtime Hq). }
  eapply tm_struct_check_sub; eassumption.
Qed.

(** Function pushback plus ordinary dependent result opening yields precise
    function reflection. *)
Theorem Store_StructPreciseFunctionPushback_and_resultOpening
    {n : nat} {G : Ctx n} {s : Store n}
    (Hpush : Store_StructPreciseFunctionPushback G s)
    (Hopen : Store_StructResultOpening G s) :
    Store_StructPreciseFunctionReflection G s.
Proof.
  intros q x y S0 A X U B body Hstore Hq Hbind Hctx Hprecise
    Hactual Hfun Harg.
  destruct (Hpush x S0 A X U B body Hstore Hbind Hctx Hprecise
    Hactual Hfun) as [Hdom Hcod].
  destruct (Tm_StructCheck_path_inversion Hfun eq_refl)
    as [P Hcheck Hsingle HfunWf].
  split.
  - exact Hdom.
  - intros t Ht.
    exact (Hopen q y S0 B U t Hq Harg HfunWf Hcod Ht).
Qed.

(** Precise reflection therefore reduces to function pushback alone. *)
Theorem Store_StructPreciseFunctionPushback_to_preciseFunctionReflection
    {n : nat} {G : Ctx n} {s : Store n}
    (Hpush : Store_StructPreciseFunctionPushback G s) :
    Store_StructPreciseFunctionReflection G s.
Proof.
  exact (Store_StructPreciseFunctionPushback_and_resultOpening Hpush
    (@Store_structResultOpening n G s)).
Qed.

(** The original compatibility contract implies its precise,
    observation-sized form. *)
Theorem Store_StructAppCompatibility_to_preciseFunctionReflection
    {n : nat} {G : Ctx n} {s : Store n}
    (Hcompat : Store_StructAppCompatibility G s) :
    Store_StructPreciseFunctionReflection G s.
Proof.
  intros q x y S0 A X U B body Hstore Hq Hbind Hctx Hprecise
    Hactual Hfun Harg.
  exact (Hcompat (path_var x) q x y S0 A X U B body Hstore
    (path_reduce_var x s) Hq Hbind Hctx Hactual Hfun Harg).
Qed.

(** Precise function reflection is sufficient to type the concrete beta
    reduct. *)
Theorem Store_StructTy_open_application_of_preciseFunctionReflection
    {n : nat} {G : Ctx n} {s : Store n}
    {p q : Path n} {x y : Fin.t n} {S0 : Ty n}
    {U : Ty (S n)} {A : Ty n} {body : Tm (S n)}
    (Hstore : Store_StructTy G s)
    (Href : Store_StructPreciseFunctionReflection G s)
    (Hp : Path_reduce p s x) (Hq : Path_reduce q s y)
    (Hbind : Store_Binds s x (tm_abs A body))
    (Hfun : Tm_StructCheck G (Path_RuntimeEq s)
      (tm_path p) (ty_fun S0 U))
    (Harg : Tm_StructCheck G (Path_RuntimeEq s) (tm_path q) S0) :
    Tm_StructCheck G (Path_RuntimeEq s)
      (Tm_open body y) (Ty_open U q).
Proof.
  destruct (Store_StructTy_of_store_binds Hstore Hbind)
    as (X & P & Hctx & Hpublic & Hprecise & HactualPublic).
  destruct (Tm_StructPrecise_abs_parts Hprecise)
    as (B & HP & Hbody & HA).
  subst P.
  destruct (Href q x y S0 A X U B body Hstore Hq Hbind Hctx
    Hprecise
    HactualPublic (Tm_StructCheck_reduce_path Hp Hfun) Harg)
    as [Hdom Hresult].
  pose proof (Tm_StructCheck_reduce_path Hq Harg) as HargAtS.
  assert (HargAtA : Tm_StructCheck G (Path_RuntimeEq s)
      (tm_path (path_var y)) A).
  { eapply tm_struct_check_sub; eassumption. }
  pose proof (Tm_StructCheck_open_var_of_path_term Hbody
    (Path_RuntimeEq_isEquivCongr s) HargAtA) as Hopened.
  exact (Hresult (Tm_open body y) Hopened).
Qed.

Print Assumptions Store_structAppCompatibility_iff_functionReflection.
Print Assumptions Tau_StructConv_open_result_runtime.
Print Assumptions Tm_StructCheck_cast_open_result_runtime.
Print Assumptions Store_structResultOpening.
Print Assumptions Store_StructPreciseFunctionPushback_and_resultOpening.
Print Assumptions
  Store_StructPreciseFunctionPushback_to_preciseFunctionReflection.
Print Assumptions
  Store_StructAppCompatibility_to_preciseFunctionReflection.
Print Assumptions
  Store_StructTy_open_application_of_preciseFunctionReflection.
