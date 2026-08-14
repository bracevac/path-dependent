From Equations Require Import Equations.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Renaming Store PathReduction PreciseStore
  PathFunctionality TypingInversion Lookup PathPreservation PathProgress
  StoreRefinement Canonical RuntimeConversion.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Ltac unpack_ty_equality :=
  lazymatch goal with
  | E : @existT nat (fun scope1 => Ty scope1) ?n ?T1 =
        @existT nat (fun scope2 => Ty scope2) ?n ?T2 |- _ =>
      let ET := fresh "Etype" in
      assert (ET : T1 = T2) by exact (PackedNat_same_index_inj E);
      clear E;
      first [is_var T1; subst T1 | is_var T2; subst T2]
  end.

(** A pair head admitted by a generalized type, retaining both its label and
    the kind of its dependent member. *)
Inductive Tau_MayPairHead {n : nat} (G : Ctx n) :
    forall {k : Kind}, Tau n k -> Name -> Kind -> Prop :=
| tau_may_pair_head_top (a : Name) (k' : Kind) :
    Tau_MayPairHead G (tau_ty ty_top) a k'
| tau_may_pair_head_pair {k' : Kind} (S0 : Ty n) (a : Name)
    (d : Tau (S n) k') :
    Tau_MayPairHead G (tau_ty (ty_pair S0 a d)) a k'
| tau_may_pair_head_single (p : Path n) (T : Ty n)
    (a : Name) (k' : Kind) :
    Path_Ty G p (tau_ty T) ->
    Tau_MayPairHead G (tau_ty T) a k' ->
    Tau_MayPairHead G (tau_ty (ty_single p)) a k'
| tau_may_pair_head_tsel (p : Path n) (A : Name) (L U : Ty n)
    (a : Name) (k' : Kind) :
    Path_Ty G (path_sel p A) (tau_intv L U) ->
    Tau_MayPairHead G (tau_ty U) a k' ->
    Tau_MayPairHead G (tau_ty (ty_tsel p A)) a k'
| tau_may_pair_head_interval (L U : Ty n) (a : Name) (k' : Kind) :
    Tau_MayPairHead G (tau_ty U) a k' ->
    Tau_MayPairHead G (tau_intv L U) a k'.

Arguments tau_may_pair_head_top {n} G a k'.
Arguments tau_may_pair_head_pair {n} G {k'} S0 a d.
Arguments tau_may_pair_head_single {n} G p T a k' _ _.
Arguments tau_may_pair_head_tsel {n} G p A L U a k' _ _.
Arguments tau_may_pair_head_interval {n} G L U a k' _.

Ltac align_may_pair_path_type :=
  lazymatch goal with
  | H1 : Path_Ty ?G ?p (tau_ty ?T1),
    H2 : Path_Ty ?G ?p (tau_ty ?T2),
    HH : Tau_MayPairHead ?G (tau_ty ?T1) ?a ?k
    |- Tau_MayPairHead ?G (tau_ty ?T2) ?a ?k =>
      let E := fresh "Etype" in
      assert (E : T1 = T2) by
        (exact (Tau_DEq_ty_eq (Path_Ty_functional H1 H2)));
      subst T2; exact HH
  end.

Ltac align_may_pair_upper :=
  lazymatch goal with
  | H1 : Path_Ty ?G (path_sel ?p ?A) (tau_intv ?L1 ?U1),
    H2 : Path_Ty ?G (path_sel ?p ?A) (tau_intv ?L2 ?U2),
    HH : Tau_MayPairHead ?G (tau_ty ?U1) ?a ?k
    |- Tau_MayPairHead ?G (tau_ty ?U2) ?a ?k =>
      let E := fresh "Eupper" in
      assert (E : U1 = U2) by
        (exact (Tau_DEq_upper_eq (Path_Ty_functional H1 H2)));
      subst U2; exact HH
  end.

Theorem Tau_Sub_mayPairHead
    {n : nat} {G : Ctx n} {k : Kind} {d1 d2 : Tau n k}
    {a : Name} {k' : Kind}
    (Hs : Tau_Sub G d1 d2) (Hh : Tau_MayPairHead G d1 a k') :
    Tau_MayPairHead G d2 a k'.
Proof.
  induction Hs.
  - exact Hh.
  - apply IHHs2. now apply IHHs1.
  - inversion Hh.
  - apply tau_may_pair_head_top.
  - inversion Hh. unpack_path_equality. align_may_pair_path_type.
  - eapply tau_may_pair_head_single; eassumption.
  - inversion Hh. unpack_path_equality. align_may_pair_upper.
  - eapply tau_may_pair_head_tsel; [eassumption | now apply IHHs].
  - inversion Hh.
  - inversion Hh. subst a. subst k'. apply tau_may_pair_head_pair.
  - inversion Hh. subst a. subst k'. apply tau_may_pair_head_pair.
  - inversion Hh. unpack_path_equality. unpack_path_equality.
    apply tau_may_pair_head_interval. now apply IHHs2.
Qed.

(** Possible heads of the first component of a pair-shaped type. *)
Inductive Tau_MayFstHead {n : nat} (G : Ctx n) :
    forall {k : Kind}, Tau n k -> Ty_Head -> Prop :=
| tau_may_fst_head_top (h : Ty_Head) :
    Tau_MayFstHead G (tau_ty ty_top) h
| tau_may_fst_head_pair {k : Kind} (S0 : Ty n) (a : Name)
    (d : Tau (S n) k) (h : Ty_Head) :
    Tau_MayHead G (tau_ty S0) h ->
    Tau_MayFstHead G (tau_ty (ty_pair S0 a d)) h
| tau_may_fst_head_single (p : Path n) (T : Ty n) (h : Ty_Head) :
    Path_Ty G p (tau_ty T) ->
    Tau_MayFstHead G (tau_ty T) h ->
    Tau_MayFstHead G (tau_ty (ty_single p)) h
| tau_may_fst_head_tsel (p : Path n) (A : Name) (L U : Ty n)
    (h : Ty_Head) :
    Path_Ty G (path_sel p A) (tau_intv L U) ->
    Tau_MayFstHead G (tau_ty U) h ->
    Tau_MayFstHead G (tau_ty (ty_tsel p A)) h
| tau_may_fst_head_interval (L U : Ty n) (h : Ty_Head) :
    Tau_MayFstHead G (tau_ty U) h ->
    Tau_MayFstHead G (tau_intv L U) h.

Arguments tau_may_fst_head_top {n} G h.
Arguments tau_may_fst_head_pair {n} G {k} S0 a d h _.
Arguments tau_may_fst_head_single {n} G p T h _ _.
Arguments tau_may_fst_head_tsel {n} G p A L U h _ _.
Arguments tau_may_fst_head_interval {n} G L U h _.

Ltac align_may_fst_path_type :=
  lazymatch goal with
  | H1 : Path_Ty ?G ?p (tau_ty ?T1),
    H2 : Path_Ty ?G ?p (tau_ty ?T2),
    HH : Tau_MayFstHead ?G (tau_ty ?T1) ?h
    |- Tau_MayFstHead ?G (tau_ty ?T2) ?h =>
      let E := fresh "Etype" in
      assert (E : T1 = T2) by
        (exact (Tau_DEq_ty_eq (Path_Ty_functional H1 H2)));
      subst T2; exact HH
  end.

Ltac align_may_fst_upper :=
  lazymatch goal with
  | H1 : Path_Ty ?G (path_sel ?p ?A) (tau_intv ?L1 ?U1),
    H2 : Path_Ty ?G (path_sel ?p ?A) (tau_intv ?L2 ?U2),
    HH : Tau_MayFstHead ?G (tau_ty ?U1) ?h
    |- Tau_MayFstHead ?G (tau_ty ?U2) ?h =>
      let E := fresh "Eupper" in
      assert (E : U1 = U2) by
        (exact (Tau_DEq_upper_eq (Path_Ty_functional H1 H2)));
      subst U2; exact HH
  end.

Theorem Tau_Sub_mayFstHead
    {n : nat} {G : Ctx n} {k : Kind} {d1 d2 : Tau n k}
    {h : Ty_Head}
    (Hs : Tau_Sub G d1 d2) (Hh : Tau_MayFstHead G d1 h) :
    Tau_MayFstHead G d2 h.
Proof.
  induction Hs.
  - exact Hh.
  - apply IHHs2. now apply IHHs1.
  - inversion Hh.
  - apply tau_may_fst_head_top.
  - inversion Hh. unpack_path_equality. align_may_fst_path_type.
  - eapply tau_may_fst_head_single; eassumption.
  - inversion Hh. unpack_path_equality. align_may_fst_upper.
  - eapply tau_may_fst_head_tsel; [eassumption | now apply IHHs].
  - inversion Hh.
  - inversion Hh. unpack_ty_equality.
    apply tau_may_fst_head_pair. eapply Tau_Sub_mayHead; eassumption.
  - inversion Hh. unpack_ty_equality.
    apply tau_may_fst_head_pair. assumption.
  - inversion Hh. unpack_path_equality. unpack_path_equality.
    apply tau_may_fst_head_interval. now apply IHHs2.
Qed.

Theorem Tau_Sub_pair_fst_head
    {n : nat} {G : Ctx n} {k1 k2 : Kind}
    {S0 U : Ty n} {a b : Name}
    {d1 : Tau (S n) k1} {d2 : Tau (S n) k2} {h : Ty_Head}
    (Hs : Tau_Sub G (tau_ty (ty_pair S0 a d1))
      (tau_ty (ty_pair U b d2)))
    (Hh : Tau_MayHead G (tau_ty S0) h) :
    Tau_MayHead G (tau_ty U) h.
Proof.
  pose proof (Tau_Sub_mayFstHead Hs
    (tau_may_fst_head_pair G S0 a d1 h Hh)) as Hout.
  inversion Hout. unpack_ty_equality. assumption.
Qed.

(** Pair label-and-kind observations one first projection below a pair. *)
Inductive Tau_MayFstPairHead {n : nat} (G : Ctx n) :
    forall {k : Kind}, Tau n k -> Name -> Kind -> Prop :=
| tau_may_fst_pair_head_top (a : Name) (k' : Kind) :
    Tau_MayFstPairHead G (tau_ty ty_top) a k'
| tau_may_fst_pair_head_pair {k : Kind} (S0 : Ty n) (a : Name)
    (d : Tau (S n) k) (observed : Name) (k' : Kind) :
    Tau_MayPairHead G (tau_ty S0) observed k' ->
    Tau_MayFstPairHead G (tau_ty (ty_pair S0 a d)) observed k'
| tau_may_fst_pair_head_single (p : Path n) (T : Ty n)
    (a : Name) (k' : Kind) :
    Path_Ty G p (tau_ty T) ->
    Tau_MayFstPairHead G (tau_ty T) a k' ->
    Tau_MayFstPairHead G (tau_ty (ty_single p)) a k'
| tau_may_fst_pair_head_tsel (p : Path n) (A : Name) (L U : Ty n)
    (a : Name) (k' : Kind) :
    Path_Ty G (path_sel p A) (tau_intv L U) ->
    Tau_MayFstPairHead G (tau_ty U) a k' ->
    Tau_MayFstPairHead G (tau_ty (ty_tsel p A)) a k'
| tau_may_fst_pair_head_interval (L U : Ty n) (a : Name) (k' : Kind) :
    Tau_MayFstPairHead G (tau_ty U) a k' ->
    Tau_MayFstPairHead G (tau_intv L U) a k'.

Arguments tau_may_fst_pair_head_top {n} G a k'.
Arguments tau_may_fst_pair_head_pair {n} G {k} S0 a d observed k' _.
Arguments tau_may_fst_pair_head_single {n} G p T a k' _ _.
Arguments tau_may_fst_pair_head_tsel {n} G p A L U a k' _ _.
Arguments tau_may_fst_pair_head_interval {n} G L U a k' _.

Ltac align_may_fst_pair_path_type :=
  lazymatch goal with
  | H1 : Path_Ty ?G ?p (tau_ty ?T1),
    H2 : Path_Ty ?G ?p (tau_ty ?T2),
    HH : Tau_MayFstPairHead ?G (tau_ty ?T1) ?a ?k
    |- Tau_MayFstPairHead ?G (tau_ty ?T2) ?a ?k =>
      let E := fresh "Etype" in
      assert (E : T1 = T2) by
        (exact (Tau_DEq_ty_eq (Path_Ty_functional H1 H2)));
      subst T2; exact HH
  end.

Ltac align_may_fst_pair_upper :=
  lazymatch goal with
  | H1 : Path_Ty ?G (path_sel ?p ?A) (tau_intv ?L1 ?U1),
    H2 : Path_Ty ?G (path_sel ?p ?A) (tau_intv ?L2 ?U2),
    HH : Tau_MayFstPairHead ?G (tau_ty ?U1) ?a ?k
    |- Tau_MayFstPairHead ?G (tau_ty ?U2) ?a ?k =>
      let E := fresh "Eupper" in
      assert (E : U1 = U2) by
        (exact (Tau_DEq_upper_eq (Path_Ty_functional H1 H2)));
      subst U2; exact HH
  end.

Theorem Tau_Sub_mayFstPairHead
    {n : nat} {G : Ctx n} {k : Kind} {d1 d2 : Tau n k}
    {a : Name} {k' : Kind}
    (Hs : Tau_Sub G d1 d2)
    (Hh : Tau_MayFstPairHead G d1 a k') :
    Tau_MayFstPairHead G d2 a k'.
Proof.
  induction Hs.
  - exact Hh.
  - apply IHHs2. now apply IHHs1.
  - inversion Hh.
  - apply tau_may_fst_pair_head_top.
  - inversion Hh. unpack_path_equality. align_may_fst_pair_path_type.
  - eapply tau_may_fst_pair_head_single; eassumption.
  - inversion Hh. unpack_path_equality. align_may_fst_pair_upper.
  - eapply tau_may_fst_pair_head_tsel; [eassumption | now apply IHHs].
  - inversion Hh.
  - inversion Hh. unpack_ty_equality. apply tau_may_fst_pair_head_pair.
    eapply Tau_Sub_mayPairHead; eassumption.
  - inversion Hh. unpack_ty_equality.
    apply tau_may_fst_pair_head_pair. assumption.
  - inversion Hh. unpack_path_equality. unpack_path_equality.
    apply tau_may_fst_pair_head_interval. now apply IHHs2.
Qed.

Theorem Tau_Sub_pair_fst_pairHead
    {n : nat} {G : Ctx n} {k1 k2 : Kind}
    {S0 U : Ty n} {a b c : Name}
    {d1 : Tau (S n) k1} {d2 : Tau (S n) k2} {k' : Kind}
    (Hs : Tau_Sub G (tau_ty (ty_pair S0 a d1))
      (tau_ty (ty_pair U b d2)))
    (Hh : Tau_MayPairHead G (tau_ty S0) c k') :
    Tau_MayPairHead G (tau_ty U) c k'.
Proof.
  pose proof (Tau_Sub_mayFstPairHead Hs
    (tau_may_fst_pair_head_pair G S0 a d1 c k' Hh)) as Hout.
  inversion Hout. unpack_ty_equality. assumption.
Qed.

Theorem Tau_Sub_pair_kind
    {n : nat} {G : Ctx n} {k1 k2 : Kind}
    {S0 U : Ty n} {a b : Name}
    {d1 : Tau (S n) k1} {d2 : Tau (S n) k2}
    (Hs : Tau_Sub G (tau_ty (ty_pair S0 a d1))
      (tau_ty (ty_pair U b d2))) : k1 = k2.
Proof.
  pose proof (Tau_Sub_mayPairHead Hs
    (tau_may_pair_head_pair G S0 a d1)) as Hh.
  inversion Hh. reflexivity.
Qed.

Theorem Tm_PreciseTy_pair_canonical_kind
    {n : nat} {G : Ctx n} {v : Tm n} {P S0 : Ty n}
    {a : Name} {k : Kind} {d : Tau (S n) k}
    (Hp : Tm_PreciseTy G v P)
    (Hs : Tau_Sub G (tau_ty P) (tau_ty (ty_pair S0 a d))) :
    exists (y : Fin.t n) (delta : Def n k),
      v = @tm_pair n k y a delta.
Proof.
  dependent elimination Hp.
  - exfalso. eapply Tau_Sub_fun_not_pair. exact Hs.
  - pose proof (Tau_Sub_pair_label Hs) as Hlabel.
    pose proof (Tau_Sub_pair_kind Hs) as Hkind.
    subst a. destruct Hkind.
    eexists _, (def_val _). reflexivity.
  - pose proof (Tau_Sub_pair_label Hs) as Hlabel.
    pose proof (Tau_Sub_pair_kind Hs) as Hkind.
    subst a. destruct Hkind.
    eexists _, (def_type _). reflexivity.
Qed.

(** Runtime transport of the outer pair shape, label, and member kind. *)
Definition Path_PairTransport {n : nat} (G : Ctx n) (s : Store n) : Prop :=
  forall (p : Path n) (x : Fin.t n) (S0 : Ty n) (a : Name)
    (k : Kind) (d : Tau (S n) k),
    Path_reduce p s x ->
    Path_Ty G p (tau_ty (ty_pair S0 a d)) ->
    exists (y : Fin.t n) (delta : Def n k),
      Store_Binds s x (@tm_pair n k y a delta).

Theorem Store_PreciseTy_pairTransport
    {n : nat} {G : Ctx n} {s : Store n}
    (Hs : Store_PreciseTy G s) : Path_PairTransport G s.
Proof.
  intros p x S0 a k d Hr Hp.
  destruct (Path_lookup_type_shape Hs (Path_reduce_toLookup Hr) Hp)
    as [Hbind | Heq].
  - destruct (Store_PreciseTy_of_ctx_binds Hs Hbind)
      as (v & Hv & Hprecise).
    dependent elimination Hprecise.
    + eexists _, (def_val _). exact Hv.
    + eexists _, (def_type _). exact Hv.
  - discriminate Heq.
Qed.

Theorem Store_PreciseTy_toRefined
    {n : nat} {G : Ctx n} {s : Store n}
    (Hs : Store_PreciseTy G s) : Store_RefinedTy G s.
Proof.
  induction Hs as [|n G s v T Hv Hstore IH Hprecise].
  - apply store_refined_ty_empty.
  - eapply store_refined_ty_val.
    + exact IH.
    + exact Hprecise.
    + exact (Tm_PreciseTy_toTy Hprecise).
    + apply sub_refl.
Qed.

Local Definition Path_RefinedLookupable {n : nat}
    (s : Store n) (p : Path n) {k : Kind} (d : Tau n k) : Prop :=
  match d with
  | tau_ty _ => exists x, Path_reduce p s x
  | tau_intv _ _ => True
  end.

Local Lemma Path_refinedLookupable_fst
    {n : nat} {G : Ctx n} {s : Store n} {p : Path n}
    {S0 : Ty n} {a : Name} {k : Kind} {d : Tau (S n) k}
    (Hpair : Path_PairTransport G s)
    (Hp : Path_Ty G p (tau_ty (ty_pair S0 a d)))
    (IH : Path_RefinedLookupable s p (tau_ty (ty_pair S0 a d))) :
    Path_RefinedLookupable s (path_fst p) (tau_ty S0).
Proof.
  cbn [Path_RefinedLookupable] in IH |- *.
  destruct IH as [x Hx].
  destruct (Hpair p x S0 a k d Hx Hp) as (y & delta & Hbind).
  exists y. eapply path_reduce_fst; eassumption.
Qed.

Local Lemma Path_refinedLookupable_sel_r
    {n : nat} {G : Ctx n} {s : Store n} {p : Path n}
    {S0 : Ty n} {a : Name} {k : Kind} {d : Tau (S n) k}
    (Hpair : Path_PairTransport G s)
    (Hp : Path_Ty G p (tau_ty (ty_pair S0 a d)))
    (IH : Path_RefinedLookupable s p (tau_ty (ty_pair S0 a d))) :
    Path_RefinedLookupable s (path_sel p a) (Tau_open d (path_fst p)).
Proof.
  dependent elimination d.
  - cbn [Path_RefinedLookupable] in IH |- *.
    destruct IH as [x Hx].
    destruct (Hpair p x S0 a star (tau_ty t) Hx Hp)
      as (y & delta & Hbind).
    dependent elimination delta.
    eexists. eapply path_reduce_sel_hit; eassumption.
  - cbn [Path_RefinedLookupable]. exact I.
Qed.

Local Lemma Path_refinedLookupable_sel_l
    {n : nat} {G : Ctx n} {s : Store n} {p : Path n}
    {S0 : Ty n} {a b : Name} {k k' : Kind}
    {d : Tau n k} {d' : Tau (S n) k'}
    (Hpair : Path_PairTransport G s)
    (Hp : Path_Ty G p (tau_ty (ty_pair S0 b d')))
    (Htail : Path_Ty G (path_sel (path_fst p) a) d)
    (Hneq : a <> b)
    (IHp : Path_RefinedLookupable s p (tau_ty (ty_pair S0 b d')))
    (IHtail : Path_RefinedLookupable s (path_sel (path_fst p) a) d) :
    Path_RefinedLookupable s (path_sel p a) d.
Proof.
  dependent elimination d.
  - cbn [Path_RefinedLookupable] in IHp, IHtail |- *.
    destruct IHp as [x Hx]. destruct IHtail as [z Hz].
    destruct (Hpair p x S0 b k' d' Hx Hp)
      as (y & delta & Hbind).
    assert (Hfst : Path_reduce (path_fst p) s y) by
      (eapply path_reduce_fst; eassumption).
    assert (Htail' : Path_reduce (path_sel (path_var y) a) s z).
    { eapply Path_reduce_sel_congr.
      - exact Hz.
      - exact Hfst.
      - apply path_reduce_var. }
    exists z. eapply path_reduce_sel_miss; eassumption.
  - cbn [Path_RefinedLookupable]. exact I.
Qed.

Local Lemma Path_refinedLookupable
    {n : nat} {G : Ctx n} {s : Store n}
    {k : Kind} {p : Path n} {d : Tau n k}
    (Hs : Store_RefinedTy G s)
    (Hpair : Path_PairTransport G s)
    (Hp : Path_Ty G p d) : Path_RefinedLookupable s p d.
Proof.
  induction Hp.
  - cbn [Path_RefinedLookupable]. eexists. apply path_reduce_var.
  - eapply Path_refinedLookupable_fst; [exact Hpair | eassumption |].
    exact (IHHp s Hs Hpair).
  - eapply Path_refinedLookupable_sel_r; [exact Hpair | eassumption |].
    exact (IHHp s Hs Hpair).
  - eapply Path_refinedLookupable_sel_l;
      [exact Hpair | eassumption | eassumption | eassumption |
       exact (IHHp1 s Hs Hpair) | exact (IHHp2 s Hs Hpair)].
Qed.

Theorem Path_reduce_progress_refined_of_pairTransport
    {n : nat} {G : Ctx n} {s : Store n} {p : Path n} {T : Ty n}
    (Hs : Store_RefinedTy G s)
    (Hpair : Path_PairTransport G s)
    (Hp : Path_Ty G p (tau_ty T)) :
    exists x, Path_reduce p s x.
Proof. exact (Path_refinedLookupable Hs Hpair Hp). Qed.

Theorem Path_reduce_progress_precise_via_pairTransport
    {n : nat} {G : Ctx n} {s : Store n} {p : Path n} {T : Ty n}
    (Hs : Store_PreciseTy G s)
    (Hp : Path_Ty G p (tau_ty T)) :
    exists x, Path_reduce p s x.
Proof.
  exact (Path_reduce_progress_refined_of_pairTransport
    (Store_PreciseTy_toRefined Hs) (Store_PreciseTy_pairTransport Hs) Hp).
Qed.

Theorem Store_RefinedTy_variable_pair_transport
    {n : nat} {G : Ctx n} {s : Store n} {x : Fin.t n}
    {S0 : Ty n} {a : Name} {k : Kind} {d : Tau (S n) k}
    (Hs : Store_RefinedTy G s)
    (Hp : Path_Ty G (path_var x) (tau_ty (ty_pair S0 a d))) :
    exists (y : Fin.t n) (delta : Def n k),
      Store_Binds s x (@tm_pair n k y a delta).
Proof.
  destruct (Path_Ty_invert_var Hp) as [U [Hbind HE]].
  apply Tau_DEq_ty_eq in HE. subst U.
  destruct (Store_RefinedTy_of_ctx_binds Hs Hbind)
    as (v & P & Hv & Hprecise & Hvt & Hsub).
  destruct (Tm_PreciseTy_pair_canonical_kind Hprecise Hsub)
    as (y & delta & Heq).
  subst v. exists y, delta. exact Hv.
Qed.

Print Assumptions Tau_Sub_pair_kind.
Print Assumptions Tm_PreciseTy_pair_canonical_kind.
Print Assumptions Store_PreciseTy_pairTransport.
Print Assumptions Path_reduce_progress_refined_of_pairTransport.
Print Assumptions Store_RefinedTy_variable_pair_transport.
