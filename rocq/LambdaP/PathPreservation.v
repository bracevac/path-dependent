From Equations Require Import Equations.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Renaming Store PathReduction Lookup
  PreciseStore PathFunctionality TypingInversion.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Derive Signature for Def.
Derive Signature for Tau.
Derive NoConfusionHom for Kind.
Derive NoConfusionHom for Def.
Derive NoConfusionHom for Tau.
Derive NoConfusionHom for Tm.
Derive NoConfusionHom for Ty.

Theorem Ty_weaken_subst_openAt {n : nat} {T : Ty n} {p : Path n} :
    Ty_subst (Ty_weaken T) (PathSubst_openAt p) = T.
Proof. change (Ty_open (Ty_weaken T) p = T). apply Ty_weaken_open. Qed.

(** Homogeneous consequences of the dependent signature equality used by
    path functionality. *)
Local Lemma Tau_DEq_ty_eq {n : nat} {T U : Ty n}
    (H : Tau_DEq (tau_ty T) (tau_ty U)) : T = U.
Proof.
  pose proof (f_equal PackedTau_to_ty (Tau_DEq_pack_eq H)) as E.
  cbn in E. now injection E.
Qed.

Local Lemma Tm_PreciseTy_pair_first_label
    {n : nat} {G : Ctx n} {k k' : Kind}
    {y : Fin.t n} {a b : Name} {d : Def n k}
    {First : Ty n} {member : Tau (S n) k'}
    (H : Tm_PreciseTy G (tm_pair y a d)
      (ty_pair First b member)) :
    First = ty_single (path_var y) /\ a = b.
Proof.
  dependent elimination H; split; reflexivity.
Qed.

Local Lemma Tm_PreciseTy_val_pair_shape
    {n : nat} {G : Ctx n} {y z : Fin.t n} {a b : Name}
    {First : Ty n} {member : Ty (S n)}
    (H : Tm_PreciseTy G (tm_pair y a (def_val z))
      (ty_pair First b (tau_ty member))) :
    First = ty_single (path_var y) /\
    a = b /\
    member = ty_single (Path_weaken (path_var z)).
Proof.
  dependent elimination H; repeat split; reflexivity.
Qed.

(** Strong shape invariant: a successfully resolved, precisely typed proper
    path is either the source variable itself or has the result singleton. *)
Theorem Path_lookup_type_shape_strong
    {n : nat} {G : Ctx n} {s : Store n}
    {p : Path n} {x : Fin.t n} {T : Ty n}
    (Hs : Store_PreciseTy G s)
    (Hr : Path_lookup p s x)
    (Hp : Path_Ty G p (tau_ty T)) :
    (p = path_var x /\ Ctx_Binds G x T) \/
      T = ty_single (path_var x).
Proof.
  revert G T Hs Hp.
  induction Hr as
      [n x s
      |n k p s x y a d Hr IH Hb
      |n p s x y z a Hr IH Hb
      |n k p s x y z a b d Hr IH Hb Hneq Htail IHtail];
      intros G T Hs Hp.
  - destruct (Path_Ty_invert_var Hp) as [U [HU HE]].
    apply Tau_DEq_ty_eq in HE. subst U.
    left. now split.
  - destruct (Path_Ty_invert_fst Hp)
      as (First & label & k' & member & Hparent & HE).
    apply Tau_DEq_ty_eq in HE. subst First.
    destruct (@IH G _ Hs Hparent) as [[Eparent Hbind] | Hbad].
    + pose proof (Store_PreciseTy_lookup Hs Hb Hbind) as Hprecise.
      destruct (Tm_PreciseTy_pair_first_label Hprecise) as [Hfirst Hlabel].
      right. exact Hfirst.
    + discriminate Hbad.
  - destruct (Path_Ty_invert_sel Hp) as
        [(First & k' & member & Hparent & HE)
        |(First & label & k' & member & Hparent & Htyped_tail & Hlabels)].
    + pose proof (Tau_DEq_kind_eq HE) as Hkind. destruct Hkind.
      dependent elimination member.
      apply Tau_DEq_ty_eq in HE. subst T.
      destruct (@IH G _ Hs Hparent) as [[Eparent Hbind] | Hbad].
      * pose proof (Store_PreciseTy_lookup Hs Hb Hbind) as Hprecise.
        destruct (Tm_PreciseTy_val_pair_shape Hprecise)
          as [Hfirst [Hlabel Hmember]].
        rewrite Hmember. right.
        change (Ty_subst (Ty_weaken (ty_single (path_var z)))
          (PathSubst_openAt (path_fst p)) = ty_single (path_var z)).
        apply Ty_weaken_subst_openAt.
      * discriminate Hbad.
    + destruct (@IH G _ Hs Hparent) as [[Eparent Hbind] | Hbad].
      * pose proof (Store_PreciseTy_lookup Hs Hb Hbind) as Hprecise.
        destruct (Tm_PreciseTy_pair_first_label Hprecise)
          as [Hfirst Hlabel].
        exfalso. apply Hlabels. exact Hlabel.
      * discriminate Hbad.
  - destruct (Path_Ty_invert_sel Hp) as
        [(First & k' & member & Hparent & HE)
        |(First & label & k' & member & Hparent & Htyped_tail & Hlabels)].
    + destruct (@IH G _ Hs Hparent) as [[Eparent Hbind] | Hbad].
      * pose proof (Store_PreciseTy_lookup Hs Hb Hbind) as Hprecise.
        destruct (Tm_PreciseTy_pair_first_label Hprecise)
          as [Hfirst Hlabel].
        exfalso. apply Hneq. symmetry. exact Hlabel.
      * discriminate Hbad.
    + destruct (@IHtail G T Hs Htyped_tail) as [[Etail Hbind] | Hsingle].
      * discriminate Etail.
      * right. exact Hsingle.
Qed.

Theorem Path_lookup_type_shape
    {n : nat} {G : Ctx n} {s : Store n}
    {p : Path n} {x : Fin.t n} {T : Ty n}
    (Hs : Store_PreciseTy G s)
    (Hr : Path_lookup p s x)
    (Hp : Path_Ty G p (tau_ty T)) :
    Ctx_Binds G x T \/ T = ty_single (path_var x).
Proof.
  destruct (Path_lookup_type_shape_strong Hs Hr Hp)
    as [[E Hbind] | Hsingle].
  - now left.
  - now right.
Qed.

Theorem Path_lookup_preserves_singleton_alias
    {n : nat} {G : Ctx n} {s : Store n}
    {p : Path n} {x : Fin.t n} {T : Ty n}
    (Hs : Store_PreciseTy G s)
    (Hr : Path_lookup p s x)
    (Hp : Path_Ty G p (tau_ty T)) :
    Tau_Sub G (tau_ty (ty_single (path_var x)))
      (tau_ty (ty_single p)).
Proof.
  destruct (Path_lookup_type_shape_strong Hs Hr Hp)
    as [[E Hbind] | Hsingle].
  - subst p. apply sub_refl.
  - subst T. exact (sub_symm G p (path_var x) Hp).
Qed.

Theorem Path_lookup_preserves_subtyping
    {n : nat} {G : Ctx n} {s : Store n}
    {p : Path n} {x : Fin.t n} {T : Ty n}
    (Hs : Store_PreciseTy G s)
    (Hr : Path_lookup p s x)
    (Hp : Path_Ty G p (tau_ty T)) :
    Tau_Sub G (tau_ty (ty_single (path_var x))) (tau_ty T).
Proof.
  destruct (Path_lookup_type_shape Hs Hr Hp) as [Hbind | Hsingle].
  - apply sub_widen. exact (path_ty_var G x T Hbind).
  - subst T. apply sub_refl.
Qed.

Theorem Path_lookup_preserves_typing
    {n : nat} {G : Ctx n} {s : Store n}
    {p : Path n} {x : Fin.t n} {T : Ty n}
    (Hs : Store_PreciseTy G s)
    (Hr : Path_lookup p s x)
    (Hp : Path_Ty G p (tau_ty T))
    (Hwf : Tau_Wf G (tau_ty T)) :
    Tm_Ty G (tm_path (path_var x)) T.
Proof.
  destruct (Ctx_Binds_exists G x) as [U HU].
  eapply tm_ty_sub.
  - exact (tm_ty_path G (path_var x) U (path_ty_var G x U HU)).
  - exact (Path_lookup_preserves_subtyping Hs Hr Hp).
  - exact Hwf.
Qed.

Theorem Path_reduce_preserves_typing
    {n : nat} {G : Ctx n} {s : Store n}
    {p : Path n} {x : Fin.t n} {T : Ty n}
    (Hs : Store_PreciseTy G s)
    (Hr : Path_reduce p s x)
    (Hp : Path_Ty G p (tau_ty T))
    (Hwf : Tau_Wf G (tau_ty T)) :
    Tm_Ty G (tm_path (path_var x)) T.
Proof.
  exact (Path_lookup_preserves_typing Hs (Path_reduce_toLookup Hr) Hp Hwf).
Qed.

Theorem Path_reduce_preserves_source_typing
    {n : nat} {G : Ctx n} {s : Store n}
    {p : Path n} {x : Fin.t n} {T : Ty n}
    (Hs : Store_PreciseTy G s)
    (Hr : Path_reduce p s x)
    (Ht : Tm_Ty G (tm_path p) T) :
    Tm_Ty G (tm_path (path_var x)) T.
Proof.
  destruct (@Tm_Ty_path_inversion n G (tm_path p) T Ht p eq_refl)
    as (U & Hp & Hsub & Hwf).
  destruct (Ctx_Binds_exists G x) as [X HX].
  eapply tm_ty_sub.
  - exact (tm_ty_path G (path_var x) X (path_ty_var G x X HX)).
  - eapply sub_trans.
    + exact (Path_lookup_preserves_singleton_alias Hs
        (Path_reduce_toLookup Hr) Hp).
    + exact Hsub.
  - exact Hwf.
Qed.

Print Assumptions Path_lookup_type_shape_strong.
Print Assumptions Path_lookup_preserves_typing.
Print Assumptions Path_reduce_preserves_source_typing.
