From Equations Require Import Equations.
From PathDependent.LambdaPFC Require Import
  FinFun Syntax Context Typing Runtime RuntimeEquality Valuation
  SemanticEvidence.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Scoped runtime equality survives allocation in the ambient store. *)
Definition path_scoped_lift_weaken_runtime {n : nat} {sigma : Store n}
    {p q : Path (S n)}
    (evidence : PathScopedLift (PathRuntimeEq sigma) p q)
    (v : Tm n) (value : Tm_IsValue v) :
    PathScopedLift (PathRuntimeEq (StoreVal sigma v value))
      (path_rename p (ext (weaken n)))
      (path_rename q (ext (weaken n))).
Proof.
  induction evidence.
  - simp path_rename. rewrite ext_zero. exact SL_bound.
  - unfold path_weaken.
    rewrite !path_rename_rename, <- comp_weaken.
    pose proof (SL_old (path_runtime_eq_weaken r (v := v) value)) as old.
    unfold path_weaken in old. rewrite !path_rename_rename in old.
    exact old.
  - exact (SL_symm IHevidence).
  - exact (SL_trans IHevidence1 IHevidence2).
  - simp path_rename. exact (SL_fst IHevidence).
  - simp path_rename. exact (SL_sel IHevidence).
Defined.

(** Runtime conversion below a binder survives allocation. *)
Definition tau_runtime_conv_weaken_scoped {n : nat} {sigma : Store n}
    {k : Kind} {d1 d2 : Tau (S n) k}
    (conversion :
      TauRuntimeConv (PathScopedLift (PathRuntimeEq sigma)) d1 d2)
    (v : Tm n) (value : Tm_IsValue v) :
    TauRuntimeConv
      (PathScopedLift (PathRuntimeEq (StoreVal sigma v value)))
      (tau_rename d1 (ext (weaken n)))
      (tau_rename d2 (ext (weaken n))) :=
  tau_runtime_conv_rename (f := ext (weaken n))
    (fun p q evidence =>
      path_scoped_lift_weaken_runtime evidence (v := v) value)
    conversion.

(** All seven finite semantic-evidence families survive allocation. *)
Fixpoint environment_weaken {n m : nat} {Gamma : Ctx n}
    {rho : Valuation n m} {sigma : Store m}
    (environment : Environment Gamma rho sigma)
    (v : Tm m) (value : Tm_IsValue v) {struct environment} :
    Environment Gamma (valuation_weaken rho) (StoreVal sigma v value)

with store_possible_weaken {m : nat} {sigma : Store m} {x : Fin m}
    {T : Ty m} (possible : StorePossible sigma x T)
    (v : Tm m) (value : Tm_IsValue v) {struct possible} :
    StorePossible (StoreVal sigma v value) (FS x) (ty_weaken T)

with referent_realizes_weaken {m : nat} {k : Kind} {sigma : Store m}
    {referent : PathReferent m} {d : Tau m k}
    (realizes : ReferentRealizes sigma referent d)
    (v : Tm m) (value : Tm_IsValue v) {struct realizes} :
    ReferentRealizes (StoreVal sigma v value)
      (referent_weaken referent) (tau_weaken d)

with coercion_weaken {m : nat} {k : Kind} {sigma : Store m}
    {d1 d2 : Tau m k} (evidence : Coercion sigma d1 d2)
    (v : Tm m) (value : Tm_IsValue v) {struct evidence} :
    Coercion (StoreVal sigma v value) (tau_weaken d1) (tau_weaken d2)

with deferred_coercion_weaken {m : nat} {sigma : Store m} {S : Ty m}
    {T U : Ty (Datatypes.S m)} (deferred : DeferredCoercion sigma S T U)
    (v : Tm m) (value : Tm_IsValue v) {struct deferred} :
    DeferredCoercion (StoreVal sigma v value) (ty_weaken S)
      (ty_rename T (ext (weaken m)))
      (ty_rename U (ext (weaken m)))

with member_closure_weaken {m : nat} {sigma : Store m} {S : Ty m}
    {k : Kind} {d d' : Tau (Datatypes.S m) k}
    (member : MemberClosure sigma S d d')
    (v : Tm m) (value : Tm_IsValue v) {struct member} :
    MemberClosure (StoreVal sigma v value) (ty_weaken S)
      (tau_rename d (ext (weaken m)))
      (tau_rename d' (ext (weaken m)))

with body_closure_weaken {m : nat} {sigma : Store m} {S : Ty m}
    {body : Tm (Datatypes.S m)} {T : Ty (Datatypes.S m)}
    (closure : BodyClosure sigma S body T)
    (v : Tm m) (value : Tm_IsValue v) {struct closure} :
    BodyClosure (StoreVal sigma v value) (ty_weaken S)
      (tm_rename body (ext (weaken m)))
      (ty_rename T (ext (weaken m))).
Proof.
  - destruct environment as [n0 m0 Gamma0 rho0 sigma0 lookup].
    apply Env_intro. intro x.
    unfold valuation_weaken. rewrite comp_apply, weaken_apply.
    unfold ty_weaken. rewrite <- ty_rename_rename.
    exact (store_possible_weaken _ _ _ _ (lookup x) v value).
  - destruct possible as
      [m0 sigma0 x0
      |m0 sigma0 x0 A S0 body B U binding closure domain codomain
      |m0 sigma0 x0 y a k0 delta S0 d binding first member
      |m0 sigma0 x0 p resolution
      |m0 sigma0 x0 p a W resolution witness].
    + cbn [ty_weaken]. simp ty_rename. exact Possible_top.
    + cbn [ty_weaken]. simp ty_rename.
      exact (Possible_fun (StoreBinds_there binding)
        (body_closure_weaken _ _ _ _ _ closure v value)
        (coercion_weaken _ _ _ _ _ domain v value)
        (deferred_coercion_weaken _ _ _ _ _ codomain v value)).
    + cbn [ty_weaken]. simp ty_rename.
      pose proof
        (store_possible_weaken _ _ _ _ first v value) as first_weakened.
      rewrite <- weaken_apply in first_weakened.
      refine (Possible_pair (StoreBinds_there binding)
        first_weakened _).
      pose proof
        (referent_realizes_weaken _ _ _ _ _ member v value) as weakened.
      unfold tau_weaken in weakened.
      rewrite tau_open_rename in weakened.
      simp path_rename in weakened.
      rewrite <- def_referent_weaken in weakened.
      exact weakened.
    + cbn [ty_weaken]. simp ty_rename.
      exact (Possible_single
        (path_resolve_weaken resolution (v := v) value)).
    + cbn [ty_weaken]. simp ty_rename.
      exact (Possible_selection
        (path_resolve_weaken resolution (v := v) value)
        (store_possible_weaken _ _ _ _ witness v value)).
  - destruct realizes.
    + cbn [tau_weaken]. simp tau_rename.
      exact (Realizes_loc
        (store_possible_weaken _ _ _ _ s v value)).
    + cbn [tau_weaken]. simp tau_rename.
      exact (Realizes_type (coercion_weaken _ _ _ _ _ c v value)
        (coercion_weaken _ _ _ _ _ c0 v value)).
  - destruct evidence.
    + exact Coercion_refl.
    + exact (Coercion_trans
        (coercion_weaken _ _ _ _ _ evidence1 v value)
        (coercion_weaken _ _ _ _ _ evidence2 v value)).
    + exact (Coercion_runtime
        (tau_runtime_conv_weaken t (v := v) value)).
    + cbn [tau_weaken]. simp tau_rename. exact Coercion_bot.
    + cbn [tau_weaken]. simp tau_rename. exact Coercion_top.
    + cbn [tau_weaken]. simp tau_rename.
      exact (Coercion_widen (path_resolve_weaken p0 (v := v) value)
        (store_possible_weaken _ _ _ _ s v value)).
    + cbn [tau_weaken]. simp tau_rename.
      exact (Coercion_alias (path_resolve_weaken p0 (v := v) value)
        (path_resolve_weaken p1 (v := v) value)).
    + cbn [tau_weaken]. simp tau_rename.
      exact (Coercion_sel_lo (path_resolve_weaken p0 (v := v) value)
        (coercion_weaken _ _ _ _ _ evidence v value)).
    + cbn [tau_weaken]. simp tau_rename.
      exact (Coercion_sel_hi (path_resolve_weaken p0 (v := v) value)
        (coercion_weaken _ _ _ _ _ evidence v value)).
    + cbn [tau_weaken]. simp tau_rename.
      exact (Coercion_fun
        (coercion_weaken _ _ _ _ _ evidence v value)
        (deferred_coercion_weaken _ _ _ _ _ d v value)).
    + cbn [tau_weaken]. simp tau_rename.
      exact (Coercion_pair
        (coercion_weaken _ _ _ _ _ evidence v value)
        (member_closure_weaken _ _ _ _ _ _ m0 v value)).
    + cbn [tau_weaken]. simp tau_rename.
      exact (Coercion_bounds
        (coercion_weaken _ _ _ _ _ evidence1 v value)
        (coercion_weaken _ _ _ _ _ evidence2 v value)).
  - destruct deferred.
    + exact Deferred_refl.
    + exact (Deferred_trans
        (deferred_coercion_weaken _ _ _ _ _ deferred1 v value)
        (deferred_coercion_weaken _ _ _ _ _ deferred2 v value)).
    + exact (Deferred_runtime
        (tau_runtime_conv_weaken_scoped t (v := v) value)).
    + exact (Deferred_narrow
        (coercion_weaken _ _ _ _ _ c v value)
        (deferred_coercion_weaken _ _ _ _ _ deferred v value)).
    + unfold ty_weaken.
      rewrite !ty_rename_rename, !ext_comp.
      exact (Deferred_source
        (environment_weaken _ _ _ _ _ e v value) t).
  - destruct member.
    unfold ty_weaken.
    rewrite ty_rename_rename, !tau_rename_rename, !ext_comp.
    exact (Member_source
      (environment_weaken _ _ _ _ _ e v value) t).
  - destruct closure.
    unfold ty_weaken.
    rewrite ty_rename_rename, tm_rename_rename, ty_rename_rename,
      !ext_comp.
    exact (Body_source
      (environment_weaken _ _ _ _ _ e v value) t).
Defined.

Print Assumptions path_scoped_lift_weaken_runtime.
Print Assumptions tau_runtime_conv_weaken_scoped.
Print Assumptions environment_weaken.
Print Assumptions store_possible_weaken.
Print Assumptions referent_realizes_weaken.
Print Assumptions coercion_weaken.
Print Assumptions deferred_coercion_weaken.
Print Assumptions member_closure_weaken.
Print Assumptions body_closure_weaken.
