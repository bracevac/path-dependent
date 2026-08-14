From Equations Require Import Equations.
From PathDependent.LambdaPCC Require Import
  FinFun Syntax Context Typing Runtime RuntimeEquality Valuation
  CaptureEvidence.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.
Unset Equations Derive Eliminator.

(** Exact source summaries survive ambient allocation. *)
Definition cap_exact_body_weaken {n : nat} {sigma : Store n} {S0 : Ty n}
    {body : Tm (S n)} {T : Ty (S n)} {C : CaptureSet (S n)}
    (closure : CapExactBody sigma S0 body T C)
    (v : Tm n) (is_value : Tm_IsValue v) :
    CapExactBody (StoreVal sigma v is_value) (ty_weaken S0)
      (tm_rename body (ext (weaken n)))
      (ty_rename T (ext (weaken n)))
      (capture_rename C (ext (weaken n))).
Proof.
  destruct closure.
  unfold ty_weaken, valuation_weaken.
  rewrite ty_rename_rename, tm_rename_rename, ty_rename_rename,
    capture_rename_rename, !ext_comp.
  exact (CEB_source (sigma := StoreVal sigma v is_value) t).
Defined.

Definition cap_exact_value_weaken {n : nat} {sigma : Store n}
    {term : Tm n} {Q : CaptureSet n}
    (value : CapExactValue sigma term Q)
    (v : Tm n) (is_value : Tm_IsValue v) :
    CapExactValue (StoreVal sigma v is_value) (tm_weaken term)
      (capture_weaken Q).
Proof.
  destruct value.
  - unfold tm_weaken. simp tm_rename.
    pose proof (cap_exact_body_weaken c (v := v) is_value) as weakened.
    simp capture_rename path_rename in weakened.
    rewrite <- capture_weaken_rename in weakened.
    exact (CEV_abs weakened).
  - unfold tm_weaken, capture_weaken. simp tm_rename capture_rename path_rename.
    exact CEV_pair.
  - unfold tm_weaken, capture_weaken. simp tm_rename capture_rename path_rename.
    exact CEV_type_pair.
  - unfold tm_weaken, capture_weaken. simp tm_rename capture_rename path_rename.
    exact CEV_capture_pair.
Defined.

Definition cap_lookup_weaken {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {term : Tm n}
    {Q : CaptureSet n} (lookup : CapLookup world x term Q)
    {v : Tm n} {R : CaptureSet n} (exact : CapExactValue sigma v R)
    (is_value : Tm_IsValue v) :
    CapLookup (CapWorld_val world exact (is_value := is_value)) (FS x)
      (tm_weaken term) (capture_weaken Q) :=
  CapLookup_there lookup.

(** All eleven capture-evidence families survive one ambient allocation. *)
Fixpoint cap_environment_weaken {n m : nat} {sigma : Store m}
    {world : CapWorld sigma} {Gamma : Ctx n} {rho : Valuation n m}
    (evidence : CapEnvironment world Gamma rho)
    {v : Tm m} {Q : CaptureSet m} (exact : CapExactValue sigma v Q)
    (is_value : Tm_IsValue v) {struct evidence} :
    CapEnvironment (CapWorld_val world exact (is_value := is_value)) Gamma
      (valuation_weaken rho)

with cap_location_weaken {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {T : Ty n}
    (evidence : CapLocationEvidence world x T)
    {v : Tm n} {Q : CaptureSet n} (exact : CapExactValue sigma v Q)
    (is_value : Tm_IsValue v) {struct evidence} :
    CapLocationEvidence (CapWorld_val world exact (is_value := is_value))
      (FS x) (ty_weaken T)

with cap_realizes_weaken {n : nat} {k : Kind} {sigma : Store n}
    {world : CapWorld sigma} {referent : Referent n} {d : Tau n k}
    (evidence : CapRealizes world referent d)
    {v : Tm n} {Q : CaptureSet n} (exact : CapExactValue sigma v Q)
    (is_value : Tm_IsValue v) {struct evidence} :
    CapRealizes (CapWorld_val world exact (is_value := is_value))
      (referent_weaken referent) (tau_weaken d)

with cap_relation_weaken {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {C D : CaptureSet n}
    (evidence : CapRelation world C D)
    {v : Tm n} {Q : CaptureSet n} (exact : CapExactValue sigma v Q)
    (is_value : Tm_IsValue v) {struct evidence} :
    CapRelation (CapWorld_val world exact (is_value := is_value))
      (capture_weaken C) (capture_weaken D)

with cap_ty_coercion_weaken {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {T U : Ty n}
    (evidence : CapTyCoercion world T U)
    {v : Tm n} {Q : CaptureSet n} (exact : CapExactValue sigma v Q)
    (is_value : Tm_IsValue v) {struct evidence} :
    CapTyCoercion (CapWorld_val world exact (is_value := is_value))
      (ty_weaken T) (ty_weaken U)

with cap_shape_coercion_weaken {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {S0 T : Shape n}
    (evidence : CapShapeCoercion world S0 T)
    {v : Tm n} {Q : CaptureSet n} (exact : CapExactValue sigma v Q)
    (is_value : Tm_IsValue v) {struct evidence} :
    CapShapeCoercion (CapWorld_val world exact (is_value := is_value))
      (shape_weaken S0) (shape_weaken T)

with cap_coercion_weaken {n : nat} {k : Kind} {sigma : Store n}
    {world : CapWorld sigma} {d e : Tau n k}
    (evidence : CapCoercion world d e)
    {v : Tm n} {Q : CaptureSet n} (exact : CapExactValue sigma v Q)
    (is_value : Tm_IsValue v) {struct evidence} :
    CapCoercion (CapWorld_val world exact (is_value := is_value))
      (tau_weaken d) (tau_weaken e)

with cap_deferred_coercion_weaken {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {S0 : Ty n} {T U : Ty (S n)}
    (evidence : CapDeferredCoercion world S0 T U)
    {v : Tm n} {Q : CaptureSet n} (exact : CapExactValue sigma v Q)
    (is_value : Tm_IsValue v) {struct evidence} :
    CapDeferredCoercion (CapWorld_val world exact (is_value := is_value))
      (ty_weaken S0) (ty_rename T (ext (weaken n)))
      (ty_rename U (ext (weaken n)))

with cap_member_closure_weaken {n : nat} {k : Kind} {sigma : Store n}
    {world : CapWorld sigma} {S0 : Ty n} {d e : Tau (S n) k}
    (evidence : CapMemberClosure world S0 d e)
    {v : Tm n} {Q : CaptureSet n} (exact : CapExactValue sigma v Q)
    (is_value : Tm_IsValue v) {struct evidence} :
    CapMemberClosure (CapWorld_val world exact (is_value := is_value))
      (ty_weaken S0) (tau_rename d (ext (weaken n)))
      (tau_rename e (ext (weaken n)))

with cap_body_weaken {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {S0 : Ty n} {body : Tm (S n)}
    {T : Ty (S n)} {C : CaptureSet (S n)}
    (evidence : CapBody world S0 body T C)
    {v : Tm n} {Q : CaptureSet n} (exact : CapExactValue sigma v Q)
    (is_value : Tm_IsValue v) {struct evidence} :
    CapBody (CapWorld_val world exact (is_value := is_value))
      (ty_weaken S0) (tm_rename body (ext (weaken n)))
      (ty_rename T (ext (weaken n)))
      (capture_rename C (ext (weaken n)))

with cap_value_weaken {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {term : Tm n} {T : Ty n}
    {Q : CaptureSet n} (evidence : CapValue world term T Q)
    {v : Tm n} {R : CaptureSet n} (exact : CapExactValue sigma v R)
    (is_value : Tm_IsValue v) {struct evidence} :
    CapValue (CapWorld_val world exact (is_value := is_value))
      (tm_weaken term) (ty_weaken T) (capture_weaken Q).
Proof.
  - destruct evidence.
    apply CE_intro. intro x.
    unfold valuation_weaken. rewrite comp_apply, weaken_apply.
    unfold ty_weaken. rewrite <- ty_rename_rename.
    exact (@cap_location_weaken _ _ _ _ _ (c x) _ _ exact is_value).
  - destruct evidence.
    + cbn [ty_weaken]. simp ty_rename.
      exact (CLE_top (cap_lookup_weaken c exact is_value)
        (@cap_relation_weaken _ _ _ _ _ c0 _ _ exact is_value)).
    + unfold ty_weaken. simp ty_rename.
      apply (CLE_fun
        (B := ty_rename B (ext (weaken n)))
        (U := ty_rename U (ext (weaken n)))
        (cap_lookup_weaken c exact is_value)).
      * replace (capture_weaken (capture_weaken Q0)) with
          (capture_rename (capture_weaken Q0) (ext (weaken n))).
        (* The body premise is now exactly the recursively weakened closure. *)
        exact (@cap_body_weaken _ _ _ _ _ _ _ c0 _ _ exact is_value).
        symmetry. apply capture_weaken_rename.
      * exact (@cap_ty_coercion_weaken _ _ _ _ _ c1 _ _ exact is_value).
      * exact (@cap_deferred_coercion_weaken _ _ _ _ _ _ c2 _ _ exact is_value).
      * exact (@cap_relation_weaken _ _ _ _ _ c3 _ _ exact is_value).
    + unfold ty_weaken. simp ty_rename.
      apply (CLE_pair (cap_lookup_weaken c exact is_value)).
      * pose proof
          (@cap_location_weaken _ _ _ _ _ evidence _ _ exact is_value)
          as first_weakened.
        rewrite <- weaken_apply in first_weakened.
        exact first_weakened.
      * rewrite def_referent_weaken.
        pose proof (@cap_realizes_weaken _ _ _ _ _ _ c0 _ _ exact is_value)
          as weakened.
        unfold tau_weaken in weakened. rewrite tau_open_rename in weakened.
        simp path_rename in weakened.
      * exact (@cap_relation_weaken _ _ _ _ _ c1 _ _ exact is_value).
    + cbn [ty_weaken]. simp ty_rename.
      exact (CLE_single (cap_lookup_weaken c exact is_value)
        (path_resolve_weaken p0 (v := v) is_value)
        (@cap_relation_weaken _ _ _ _ _ c0 _ _ exact is_value)).
    + cbn [ty_weaken]. simp ty_rename.
      exact (CLE_selection (cap_lookup_weaken c exact is_value)
        (path_resolve_weaken p0 (v := v) is_value)
        (@cap_location_weaken _ _ _ _ _ evidence _ _ exact is_value)
        (@cap_relation_weaken _ _ _ _ _ c0 _ _ exact is_value)).
  - destruct evidence.
    + cbn [tau_weaken]. simp tau_rename.
      exact (CRZ_loc (@cap_location_weaken _ _ _ _ _ c _ _ exact is_value)).
    + cbn [tau_weaken]. simp tau_rename.
      exact (CRZ_type
        (@cap_shape_coercion_weaken _ _ _ _ _ c _ _ exact is_value)
        (@cap_shape_coercion_weaken _ _ _ _ _ c0 _ _ exact is_value)).
    + cbn [tau_weaken]. simp tau_rename.
      exact (CRZ_capture
        (@cap_relation_weaken _ _ _ _ _ c _ _ exact is_value)
        (@cap_relation_weaken _ _ _ _ _ c0 _ _ exact is_value)).
  - destruct evidence.
    + unfold valuation_weaken, capture_weaken.
      rewrite !capture_rename_rename.
      exact (CR_source
        (@cap_environment_weaken _ _ _ _ _ _ c _ _ exact is_value) c0).
    + exact CR_refl.
    + exact (CR_trans
        (@cap_relation_weaken _ _ _ _ _ evidence1 _ _ exact is_value)
        (@cap_relation_weaken _ _ _ _ _ evidence2 _ _ exact is_value)).
    + exact (CR_runtime (capture_runtime_conv_weaken c (v := v) is_value)).
    + exact CR_empty.
    + exact CR_union_left.
    + exact CR_union_right.
    + exact (CR_union_elim
        (@cap_relation_weaken _ _ _ _ _ evidence1 _ _ exact is_value)
        (@cap_relation_weaken _ _ _ _ _ evidence2 _ _ exact is_value)).
    + exact (CR_alias (path_resolve_weaken p0 (v := v) is_value)
        (path_resolve_weaken p1 (v := v) is_value)).
    + exact (CR_fold (path_resolve_weaken p0 (v := v) is_value)
        (cap_lookup_weaken c exact is_value)).
    + exact (CR_fst_root (path_resolve_weaken p0 (v := v) is_value)).
    + exact (CR_sel_root (path_resolve_weaken p0 (v := v) is_value)).
    + match goal with
      | lower : CapRelation _ _ _ |- _ =>
          exact (CR_select_lower
            (path_resolve_weaken p0 (v := v) is_value)
            (@cap_relation_weaken _ _ _ _ _ lower _ _ exact is_value))
      end.
    + match goal with
      | upper : CapRelation _ _ _ |- _ =>
          exact (CR_select_upper
            (path_resolve_weaken p0 (v := v) is_value)
            (@cap_relation_weaken _ _ _ _ _ upper _ _ exact is_value))
      end.
  - destruct evidence.
    + exact CTC_refl.
    + exact (CTC_trans
        (@cap_ty_coercion_weaken _ _ _ _ _ evidence1 _ _ exact is_value)
        (@cap_ty_coercion_weaken _ _ _ _ _ evidence2 _ _ exact is_value)).
    + exact (CTC_runtime (ty_runtime_conv_weaken t (v := v) is_value)).
    + cbn [ty_weaken]. simp ty_rename.
      exact (CTC_capt
        (@cap_relation_weaken _ _ _ _ _ c _ _ exact is_value)
        (@cap_shape_coercion_weaken _ _ _ _ _ c0 _ _ exact is_value)).
  - destruct evidence.
    + exact CSC_refl.
    + exact (CSC_trans
        (@cap_shape_coercion_weaken _ _ _ _ _ evidence1 _ _ exact is_value)
        (@cap_shape_coercion_weaken _ _ _ _ _ evidence2 _ _ exact is_value)).
    + exact (CSC_runtime (shape_runtime_conv_weaken s (v := v) is_value)).
    + exact CSC_bot.
    + exact CSC_top.
    + exact (CSC_widen (path_resolve_weaken p0 (v := v) is_value)
        (@cap_location_weaken _ _ _ _ _ c _ _ exact is_value)).
    + exact (CSC_alias (path_resolve_weaken p0 (v := v) is_value)
        (path_resolve_weaken p1 (v := v) is_value)).
    + match goal with
      | lower : CapShapeCoercion _ _ _ |- _ =>
          exact (CSC_select_lower
            (path_resolve_weaken p0 (v := v) is_value)
            (@cap_shape_coercion_weaken _ _ _ _ _ lower _ _ exact is_value))
      end.
    + match goal with
      | upper : CapShapeCoercion _ _ _ |- _ =>
          exact (CSC_select_upper
            (path_resolve_weaken p0 (v := v) is_value)
            (@cap_shape_coercion_weaken _ _ _ _ _ upper _ _ exact is_value))
      end.
    + cbn [shape_weaken]. simp shape_rename.
      exact (CSC_fun
        (@cap_ty_coercion_weaken _ _ _ _ _ c _ _ exact is_value)
        (@cap_deferred_coercion_weaken _ _ _ _ _ _ c0 _ _ exact is_value)).
    + cbn [shape_weaken]. simp shape_rename.
      exact (CSC_pair
        (@cap_ty_coercion_weaken _ _ _ _ _ c _ _ exact is_value)
        (@cap_member_closure_weaken _ _ _ _ _ _ _ c0 _ _ exact is_value)).
  - destruct evidence.
    + exact CC_refl.
    + exact (CC_trans
        (@cap_coercion_weaken _ _ _ _ _ _ evidence1 _ _ exact is_value)
        (@cap_coercion_weaken _ _ _ _ _ _ evidence2 _ _ exact is_value)).
    + exact (CC_runtime (tau_runtime_conv_weaken t (v := v) is_value)).
    + cbn [tau_weaken]. simp tau_rename.
      exact (CC_term (@cap_ty_coercion_weaken _ _ _ _ _ c _ _ exact is_value)).
    + cbn [tau_weaken]. simp tau_rename.
      exact (CC_type
        (@cap_shape_coercion_weaken _ _ _ _ _ c _ _ exact is_value)
        (@cap_shape_coercion_weaken _ _ _ _ _ c0 _ _ exact is_value)).
    + cbn [tau_weaken]. simp tau_rename.
      exact (CC_capture
        (@cap_relation_weaken _ _ _ _ _ c _ _ exact is_value)
        (@cap_relation_weaken _ _ _ _ _ c0 _ _ exact is_value)).
  - destruct evidence.
    + exact CDC_refl.
    + exact (CDC_trans
        (@cap_deferred_coercion_weaken _ _ _ _ _ _ evidence1 _ _ exact is_value)
        (@cap_deferred_coercion_weaken _ _ _ _ _ _ evidence2 _ _ exact is_value)).
    + exact (CDC_runtime (ty_runtime_conv_weaken_scoped t (v := v) is_value)).
    + exact (CDC_narrow
        (@cap_ty_coercion_weaken _ _ _ _ _ c _ _ exact is_value)
        (@cap_deferred_coercion_weaken _ _ _ _ _ _ evidence _ _ exact is_value)).
    + unfold ty_weaken, valuation_weaken.
      rewrite !ty_rename_rename, !ext_comp.
      exact (CDC_source
        (@cap_environment_weaken _ _ _ _ _ _ c _ _ exact is_value) t).
  - destruct evidence.
    unfold ty_weaken, valuation_weaken.
    rewrite ty_rename_rename, !tau_rename_rename, !ext_comp.
    exact (CMC_source
      (@cap_environment_weaken _ _ _ _ _ _ c _ _ exact is_value) t).
  - destruct evidence.
    unfold ty_weaken, valuation_weaken.
    rewrite ty_rename_rename, tm_rename_rename, ty_rename_rename,
      capture_rename_rename, !ext_comp.
    exact (CB_source
      (@cap_environment_weaken _ _ _ _ _ _ c _ _ exact is_value) t).
  - destruct evidence.
    + unfold tm_weaken. simp tm_rename.
      apply (CV_abs (B := ty_rename B (ext (weaken n)))).
      * replace (capture_weaken (capture_weaken Q)) with
          (capture_rename (capture_weaken Q) (ext (weaken n))).
        exact (@cap_body_weaken _ _ _ _ _ _ _ c _ _ exact is_value).
        symmetry. apply capture_weaken_rename.
      * exact (@cap_ty_coercion_weaken _ _ _ _ _ c0 _ _ exact is_value).
    + unfold tm_weaken, capture_weaken.
      rewrite tm_rename_equation_3, def_rename_equation_1,
        capture_rename_equation_2, !capture_rename_equation_3,
        !path_rename_equation_1, !weaken_apply.
      apply CV_pair.
      cbn [ty_weaken]. simp ty_rename shape_rename tau_rename
        capture_rename path_rename.
      pose proof
        (@cap_ty_coercion_weaken _ _ _ _ _ c _ _ exact is_value)
        as weakened_coercion.
      unfold ty_weaken in weakened_coercion.
      rewrite ty_rename_equation_1 in weakened_coercion.
      rewrite shape_rename_equation_4 in weakened_coercion.
      rewrite !ty_rename_equation_1 in weakened_coercion.
      rewrite tau_rename_equation_1 in weakened_coercion.
      rewrite ty_rename_equation_1 in weakened_coercion.
      rewrite !shape_rename_equation_5 in weakened_coercion.
      rewrite capture_rename_equation_2 in weakened_coercion.
      rewrite !capture_rename_equation_3 in weakened_coercion.
      rewrite !path_rename_equation_1 in weakened_coercion.
      rewrite !weaken_apply in weakened_coercion.
      rewrite <- path_weaken_rename in weakened_coercion.
      rewrite !path_rename_equation_1 in weakened_coercion.
      rewrite !weaken_apply in weakened_coercion.
      exact weakened_coercion.
    + unfold tm_weaken, capture_weaken.
      rewrite tm_rename_equation_3, def_rename_equation_2,
        capture_rename_equation_3, path_rename_equation_1, !weaken_apply.
      apply CV_type_pair.
      cbn [ty_weaken]. simp ty_rename shape_rename tau_rename
        capture_rename path_rename.
      pose proof
        (@cap_ty_coercion_weaken _ _ _ _ _ c _ _ exact is_value)
        as weakened_coercion.
      unfold ty_weaken in weakened_coercion.
      rewrite ty_rename_equation_1 in weakened_coercion.
      rewrite shape_rename_equation_4 in weakened_coercion.
      rewrite ty_rename_equation_1 in weakened_coercion.
      rewrite tau_rename_equation_2 in weakened_coercion.
      rewrite shape_rename_equation_5 in weakened_coercion.
      rewrite !capture_rename_equation_3 in weakened_coercion.
      rewrite !path_rename_equation_1 in weakened_coercion.
      rewrite !weaken_apply in weakened_coercion.
      rewrite <- shape_weaken_rename in weakened_coercion.
      exact weakened_coercion.
    + unfold tm_weaken, capture_weaken.
      rewrite tm_rename_equation_3, def_rename_equation_3,
        capture_rename_equation_3, path_rename_equation_1, !weaken_apply.
      apply CV_capture_pair.
      cbn [ty_weaken]. simp ty_rename shape_rename tau_rename
        capture_rename path_rename.
      pose proof
        (@cap_ty_coercion_weaken _ _ _ _ _ c _ _ exact is_value)
        as weakened_coercion.
      unfold ty_weaken in weakened_coercion.
      rewrite ty_rename_equation_1 in weakened_coercion.
      rewrite shape_rename_equation_4 in weakened_coercion.
      rewrite ty_rename_equation_1 in weakened_coercion.
      rewrite tau_rename_equation_3 in weakened_coercion.
      rewrite shape_rename_equation_5 in weakened_coercion.
      rewrite !capture_rename_equation_3 in weakened_coercion.
      rewrite !path_rename_equation_1 in weakened_coercion.
      rewrite !weaken_apply in weakened_coercion.
      rewrite <- capture_weaken_rename in weakened_coercion.
      exact weakened_coercion.
Defined.

Definition cap_world_valid_extend {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {v : Tm n} {is_value : Tm_IsValue v}
    {T : Ty n} {Q : CaptureSet n} {exact : CapExactValue sigma v Q}
    (valid : CapWorldValid world) (value : CapValue world v T Q) :
    CapWorldValid (CapWorld_val world exact (is_value := is_value)) :=
  CWV_val valid value.

Print Assumptions cap_exact_value_weaken.
Print Assumptions cap_environment_weaken.
Print Assumptions cap_value_weaken.
Print Assumptions cap_world_valid_extend.
