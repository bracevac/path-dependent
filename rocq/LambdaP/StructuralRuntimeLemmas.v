From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Renaming Store RuntimeConversion
  PathReduction ScopedRuntimeEq PathPreservation StructuralRuntimeTyping
  StructuralTermTyping.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Bridge the first store-indexed conversion layer into structural
    conversion. *)
Theorem Tau_StructConv_of_runtime {n : nat} {s : Store n} {k : Kind}
    {d1 d2 : Tau n k} (H : Tau_RuntimeConv s d1 d2) :
    Tau_StructConv (Path_RuntimeEq s) d1 d2.
Proof.
  induction H.
  - apply tau_struct_conv_refl.
  - now apply tau_struct_conv_symm.
  - eapply tau_struct_conv_trans; eassumption.
  - now apply tau_struct_conv_replace.
Qed.

Theorem Tau_StructSub_of_runtime {n : nat} {G : Ctx n} {s : Store n}
    {k : Kind} {d1 d2 : Tau n k} (H : Tau_RuntimeSub G s d1 d2) :
    Tau_StructSub G (Path_RuntimeEq s) d1 d2.
Proof.
  induction H.
  - apply tau_struct_sub_refl.
  - exact (Tau_StructSub_of_source H (Path_RuntimeEq s)).
  - apply tau_struct_sub_conv. now apply Tau_StructConv_of_runtime.
  - eapply tau_struct_sub_trans; eassumption.
Qed.

(** Runtime equality is a relation morphism along allocation weakening. *)
Theorem Path_RelHom_runtime_weaken {n : nat} {s : Store n}
    (v : Tm n) (Hv : Tm_IsValue v) :
    Path_RelHom (Path_RuntimeEq s)
      (Path_RuntimeEq (store_val s v Hv)) (FinFun.weaken n).
Proof.
  intros p q Hpq. unfold Path_weaken in *.
  exact (Path_RuntimeEq_weaken Hpq (v := v) Hv).
Qed.

Theorem Path_StructCheck_weaken_runtime {n : nat} {G : Ctx n}
    {s : Store n} {k : Kind} {p : Path n} {d : Tau n k}
    (H : Path_StructCheck G (Path_RuntimeEq s) p d)
    (S0 : Ty n) (v : Tm n) (Hv : Tm_IsValue v) :
    Path_StructCheck (ctx_snoc G S0)
      (Path_RuntimeEq (store_val s v Hv)) (Path_weaken p) (Tau_weaken d).
Proof.
  unfold Path_weaken, Tau_weaken.
  exact (Path_StructCheck_renameExact H (@Renaming_weaken n G S0)
    (Path_RelHom_runtime_weaken (v := v) Hv)).
Qed.

Theorem Tau_StructSub_weaken_runtime {n : nat} {G : Ctx n}
    {s : Store n} {k : Kind} {d1 d2 : Tau n k}
    (H : Tau_StructSub G (Path_RuntimeEq s) d1 d2)
    (S0 : Ty n) (v : Tm n) (Hv : Tm_IsValue v) :
    Tau_StructSub (ctx_snoc G S0)
      (Path_RuntimeEq (store_val s v Hv))
      (Tau_weaken d1) (Tau_weaken d2).
Proof.
  unfold Tau_weaken.
  exact (Tau_StructSub_renameExact H (@Renaming_weaken n G S0)
    (Path_RelHom_runtime_weaken (v := v) Hv)).
Qed.

Theorem Tau_StructWf_weaken_runtime {n : nat} {G : Ctx n}
    {s : Store n} {k : Kind} {d : Tau n k}
    (H : Tau_StructWf G (Path_RuntimeEq s) d)
    (S0 : Ty n) (v : Tm n) (Hv : Tm_IsValue v) :
    Tau_StructWf (ctx_snoc G S0)
      (Path_RuntimeEq (store_val s v Hv)) (Tau_weaken d).
Proof.
  unfold Tau_weaken.
  exact (Tau_StructWf_renameExact H (@Renaming_weaken n G S0)
    (Path_RelHom_runtime_weaken (v := v) Hv)).
Qed.

Theorem Tm_StructCheck_weaken_runtime {n : nat} {G : Ctx n}
    {s : Store n} {t : Tm n} {T : Ty n}
    (H : Tm_StructCheck G (Path_RuntimeEq s) t T)
    (S0 : Ty n) (v : Tm n) (Hv : Tm_IsValue v) :
    Tm_StructCheck (ctx_snoc G S0)
      (Path_RuntimeEq (store_val s v Hv)) (Tm_weaken t) (Ty_weaken T).
Proof.
  unfold Tm_weaken, Ty_weaken.
  exact (Tm_StructCheck_renameExact H (@Renaming_weaken n G S0)
    (Path_RelHom_runtime_weaken (v := v) Hv)).
Qed.

(** The formal scoped relation below a binder becomes concrete runtime
    equality after allocating that binder's value. *)
Theorem Path_ScopedLift_to_runtime_extension {n : nat} {s : Store n}
    {v : Tm n} {Hv : Tm_IsValue v} {p q : Path (S n)}
    (H : Path_ScopedLift (Path_RuntimeEq s) p q) :
    Path_RuntimeEq (store_val s v Hv) p q.
Proof.
  induction H.
  - apply path_runtime_eq_refl.
  - exact (Path_RuntimeEq_weaken H (v := v) Hv).
  - now apply path_runtime_eq_symm.
  - eapply path_runtime_eq_trans; eassumption.
  - exact (path_equiv_fst (Path_RuntimeEq_isEquivCongr _) IHPath_ScopedLift).
  - exact (path_equiv_sel (Path_RuntimeEq_isEquivCongr _)
      IHPath_ScopedLift a).
Qed.

(** Runtime-equivalent paths have structurally convertible singletons. *)
Theorem Tau_StructSub_single_runtime {n : nat} {G : Ctx n}
    {s : Store n} {p q : Path n} (H : Path_RuntimeEq s p q) :
    Tau_StructSub G (Path_RuntimeEq s)
      (tau_ty (ty_single p)) (tau_ty (ty_single q)).
Proof.
  apply tau_struct_sub_conv.
  pose proof (tau_struct_conv_replace
    (R := Path_RuntimeEq s)
    (tau_ty (ty_single (path_var (@Fin.zero n)))) H) as conversion.
  unfold Tau_open in conversion.
  cbn [Tau_subst Ty_subst Path_subst] in conversion.
  rewrite !PathSubst_openAt_zero in conversion. exact conversion.
Qed.

(** Big-step lookup preserves an advertised structural type. *)
Theorem Path_StructCheck_reduce_to_var {n : nat} {G : Ctx n}
    {s : Store n} {p : Path n} {x : Fin.t n} {U : Ty n}
    (Hr : Path_reduce p s x)
    (Hp : Path_StructCheck G (Path_RuntimeEq s) p (tau_ty U)) :
    Path_StructCheck G (Path_RuntimeEq s)
      (path_var x) (tau_ty U).
Proof.
  destruct (Ctx_Binds_exists G x) as [X Hx].
  assert (Heq : Path_RuntimeEq s (path_var x) p).
  { apply path_runtime_eq_symm. exact (Path_RuntimeEq_of_reduce Hr). }
  assert (Hsingle : Tau_StructSub G (Path_RuntimeEq s)
      (tau_ty (ty_single (path_var x))) (tau_ty U)).
  { eapply tau_struct_sub_trans.
    - exact (Tau_StructSub_single_runtime Heq).
    - apply tau_struct_sub_widen. exact Hp. }
  eapply path_struct_check_promote.
  - apply path_struct_check_var. exact Hx.
  - exact Hsingle.
Qed.

(** Replay a singleton-subtyping suffix after replacing a path by its
    lookup result. *)
Theorem Tau_StructSub_reduce_singleton_left {n : nat} {G : Ctx n}
    {s : Store n} {p : Path n} {x : Fin.t n} {T : Ty n}
    (Hr : Path_reduce p s x)
    (H : Tau_StructSub G (Path_RuntimeEq s)
      (tau_ty (ty_single p)) (tau_ty T)) :
    Tau_StructSub G (Path_RuntimeEq s)
      (tau_ty (ty_single (path_var x))) (tau_ty T).
Proof.
  eapply tau_struct_sub_trans.
  - refine (Tau_StructSub_single_runtime
      (G := G) (p := path_var x) (q := p) _).
    apply path_runtime_eq_symm. exact (Path_RuntimeEq_of_reduce Hr).
  - exact H.
Qed.

Print Assumptions Tau_StructSub_of_runtime.
Print Assumptions Path_StructCheck_weaken_runtime.
Print Assumptions Tm_StructCheck_weaken_runtime.
Print Assumptions Path_ScopedLift_to_runtime_extension.
Print Assumptions Path_StructCheck_reduce_to_var.
Print Assumptions Tau_StructSub_reduce_singleton_left.
