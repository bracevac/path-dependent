From PathDependent.LambdaP Require Import
  FinFun Syntax Context Renaming ScopedRuntimeEq StructuralRuntimeTyping
  StructuralTermTyping.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Local Coercion FinFun.apply : FinFun.t >-> Funclass.

(** Identity is a homomorphism for every path relation. *)
Local Lemma Path_RelHom_identity {n : nat}
    (R : Path n -> Path n -> Prop) :
    Path_RelHom R R (FinFun.id n).
Proof.
  intros p q Hpq. rewrite !Path_rename_id. exact Hpq.
Qed.

(** Replacing the newest context entry by a subtype gives a structural
    identity renaming from the old context to the narrowed context. *)
Theorem Path_StructRenaming_narrow {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {S0 S' : Ty n}
    (Hsub : Tau_StructSub G R (tau_ty S') (tau_ty S0)) :
    Path_StructRenaming (ctx_snoc G S0) (FinFun.id (S n))
      (ctx_snoc G S') (Path_ScopedLift R).
Proof.
  intros x T Hx.
  refine (@Fin.cases' n x
    (fun x => Ctx_Binds (ctx_snoc G S0) x T ->
      Path_StructCheck (ctx_snoc G S') (Path_ScopedLift R)
        (path_var (FinFun.id (S n) x))
        (tau_ty (Ty_rename T (FinFun.id (S n))))) _ _ Hx).
  - intro Hhere.
    assert (T = Ty_weaken S0) as ->.
    { exact (Ctx_Binds_unique Hhere (binds_here G S0)). }
    rewrite FinFun.id_apply, Ty_rename_id.
    eapply path_struct_check_sub.
    + apply path_struct_check_var. apply binds_here.
    + pose proof (Tau_StructSub_renameExact Hsub
        (@Renaming_weaken n G S') (@Path_RelHom_weaken n R)) as Hweak.
      cbn [Tau_rename] in Hweak. exact Hweak.
  - intros y Hy.
    assert (T = Ty_weaken (Ctx_lookup G y)) as ->.
    { exact (Ctx_Binds_unique Hy
        (binds_there G S0 (Ctx_lookup G y) y (Ctx_lookup_binds G y))). }
    rewrite FinFun.id_apply, Ty_rename_id.
    apply path_struct_check_var.
    exact (binds_there G S' (Ctx_lookup G y) y (Ctx_lookup_binds G y)).
Qed.

Theorem Path_StructCheck_narrow {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {S0 S' : Ty n}
    {k : Kind} {p : Path (S n)} {d : Tau (S n) k}
    (H : Path_StructCheck (ctx_snoc G S0) (Path_ScopedLift R) p d)
    (Hsub : Tau_StructSub G R (tau_ty S') (tau_ty S0)) :
    Path_StructCheck (ctx_snoc G S') (Path_ScopedLift R) p d.
Proof.
  pose proof (Path_StructCheck_rename H
    (Path_StructRenaming_narrow Hsub)
    (@Path_RelHom_identity (S n) (Path_ScopedLift R))) as renamed.
  rewrite Path_rename_id, Tau_rename_id in renamed. exact renamed.
Qed.

Theorem Tau_StructSub_narrow {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {S0 S' : Ty n}
    {k : Kind} {d1 d2 : Tau (S n) k}
    (H : Tau_StructSub (ctx_snoc G S0) (Path_ScopedLift R) d1 d2)
    (Hsub : Tau_StructSub G R (tau_ty S') (tau_ty S0)) :
    Tau_StructSub (ctx_snoc G S') (Path_ScopedLift R) d1 d2.
Proof.
  pose proof (Tau_StructSub_rename H
    (Path_StructRenaming_narrow Hsub)
    (@Path_RelHom_identity (S n) (Path_ScopedLift R))) as renamed.
  rewrite !Tau_rename_id in renamed. exact renamed.
Qed.

Theorem Tau_StructWf_narrow {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {S0 S' : Ty n}
    {k : Kind} {d : Tau (S n) k}
    (H : Tau_StructWf (ctx_snoc G S0) (Path_ScopedLift R) d)
    (Hsub : Tau_StructSub G R (tau_ty S') (tau_ty S0)) :
    Tau_StructWf (ctx_snoc G S') (Path_ScopedLift R) d.
Proof.
  pose proof (Tau_StructWf_rename H
    (Path_StructRenaming_narrow Hsub)
    (@Path_RelHom_identity (S n) (Path_ScopedLift R))) as renamed.
  rewrite Tau_rename_id in renamed. exact renamed.
Qed.

Theorem Tm_StructCheck_narrow {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {S0 S' : Ty n}
    {t : Tm (S n)} {T : Ty (S n)}
    (H : Tm_StructCheck (ctx_snoc G S0) (Path_ScopedLift R) t T)
    (Hsub : Tau_StructSub G R (tau_ty S') (tau_ty S0)) :
    Tm_StructCheck (ctx_snoc G S') (Path_ScopedLift R) t T.
Proof.
  pose proof (Tm_StructCheck_rename H
    (Path_StructRenaming_narrow Hsub)
    (@Path_RelHom_identity (S n) (Path_ScopedLift R))) as renamed.
  rewrite Tm_rename_id, Ty_rename_id in renamed. exact renamed.
Qed.

Print Assumptions Path_StructRenaming_narrow.
Print Assumptions Path_StructCheck_narrow.
Print Assumptions Tau_StructSub_narrow.
Print Assumptions Tau_StructWf_narrow.
Print Assumptions Tm_StructCheck_narrow.
