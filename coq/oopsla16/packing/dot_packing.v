(*
Packing in [htp] breaks the OOPSLA'16 DOT calculus.

[has_type] has both [T_VarPack] and [T_VarUnpack] (dot.v:231-240), but [htp],
the judgment that subtyping's type selections go through (dot.v:375-393), has
only [htp_unpack].  This file adds the converse rule to [htp] and nothing else,
and derives, over an ordinary two-object store, a closed term that is well
typed at [TTop], is not a value, and cannot [step] -- so the progress half of
[dot_soundness.v:1131]'s [type_safety] fails.

Everything the construction needs from the reference is in [dot_spec.v], whose
lines 25-410 are byte-identical to dot.v:14-399.

This is a Coq transcription of
  lean/Coercions/Oopsla16/PackingCounterexample.lean
whose intrinsically-scoped encoding drops [closed], [TVarB] and the derivation
size index.  Here all three are present and every side condition is discharged,
so the result does not depend on those choices.
*)

Require Import dot_spec.
Require Import Lia.

(* ############################################################ *)
(*# 1. The extended judgments #*)
(* ############################################################ *)

(* Coq cannot add a constructor to an existing inductive, so the four mutual
   judgments of dot.v:219-393 are re-declared.  Every constructor below is
   COPIED VERBATIM from dot.v; the only edits are mechanical renamings of the
   four judgment names to their P-versions
     has_type -> has_typeP,  dms_has_type -> dms_has_typeP,
     stp      -> stpP,       htp          -> htpP
   so that the recursive occurrences point at the extended judgments.  The
   constructor names are kept, which shadows dot_spec's; the original ones stay
   reachable as [dot_spec.stp_trans] etc., and section 3 below uses them.

   The one addition is [htp_pack] at the very end: the exact converse of
   [htp_unpack] (dot.v:380-383) and the mirror of [T_VarPack] (dot.v:231-235),
   with the same closedness index [closed (S x) (length G1) 1 TX] that
   [htp_unpack] carries.  Nothing else changes; in particular [htp_sub] keeps
   both [length GL = S x] and [GH = GU ++ GL], the second contractiveness
   restriction, unweakened. *)

Inductive has_typeP : tenv -> venv -> tm -> ty -> nat -> Prop :=
  | T_Vary : forall GH G1 x ds ds' T T' n1,
      index x G1 = Some (vobj ds) ->
      dms_has_typeP [T'] G1 ds' T' n1 ->
      subst_dms x ds' = ds ->
      substt x T' = T ->
      closed 0 (length G1) 0 T ->
      has_typeP GH G1 (tvar true x) T (S n1)
  | T_Varz : forall G1 GH x T n1,
      index x GH = Some T ->
      closed (length GH) (length G1) 0 T ->
      has_typeP GH G1 (tvar false x) T (S n1)
  | T_VarPack : forall GH G1 b x T1 T1' n1,
      has_typeP GH G1 (tvar b x) T1' n1 ->
      T1' = (open 0 (TVar b x) T1) ->
      closed (length GH) (length G1) 1 T1 ->
      has_typeP GH G1 (tvar b x) (TBind T1) (S n1)
  | T_VarUnpack : forall GH G1 b x T1 T1' n1,
      has_typeP GH G1 (tvar b x) (TBind T1) n1 ->
      T1' = (open 0 (TVar b x) T1) ->
      closed (length GH) (length G1) 0 T1' ->
      has_typeP GH G1 (tvar b x) T1' (S n1)
  | T_Obj : forall GH G1 ds T T' n1,
      dms_has_typeP (T'::GH) G1 ds T' n1 ->
      T' = open 0 (TVar false (length GH)) T ->
      closed (length GH) (length G1) 1 T ->
      has_typeP GH G1 (tobj ds) (TBind T) (S n1)
  | T_App : forall l T1 T2 GH G1 t1 t2 n1 n2,
      has_typeP GH G1 t1 (TFun l T1 T2) n1 ->
      has_typeP GH G1 t2 T1 n2 ->
      closed (length GH) (length G1) 0 T2 ->
      has_typeP GH G1 (tapp t1 l t2) T2 (S (n1+n2))
  | T_AppVar : forall l T1 T2 T2' GH G1 t1 b2 x2 n1 n2,
      has_typeP GH G1 t1 (TFun l T1 T2) n1 ->
      has_typeP GH G1 (tvar b2 x2) T1 n2 ->
      T2' = (open 0 (TVar b2 x2) T2) ->
      closed (length GH) (length G1) 0 T2' ->
      has_typeP GH G1 (tapp t1 l (tvar b2 x2)) T2' (S (n1+n2))
  | T_Sub : forall GH G1 t T1 T2 n1 n2,
      has_typeP GH G1 t T1 n1 ->
      stpP GH G1 T1 T2 n2 ->
      has_typeP GH G1 t T2 (S (n1 + n2))

(* : -- member initialization *)
with dms_has_typeP: tenv -> venv -> dms -> ty -> nat -> Prop :=
  | D_Nil : forall GH G1 n1,
      dms_has_typeP GH G1 dnil TTop (S n1)
  | D_Typ : forall GH G1 l T11 ds TS T n1,
      dms_has_typeP GH G1 ds TS n1 ->
      closed (length GH) (length G1) 0 T11 ->
      l = length (dms_to_list ds) ->
      T = TAnd (TTyp l T11 T11) TS ->
      dms_has_typeP GH G1 (dcons (dty T11) ds) T (S n1)
  | D_Fun : forall GH G1 l OT11 T11 OT12 T12 T12' t12 ds TS T n1 n2,
      dms_has_typeP GH G1 ds TS n1 ->
      has_typeP (T11::GH) G1 t12 T12' n2 ->
      T12' = (open 0 (TVar false (length GH)) T12) ->
      closed (length GH) (length G1) 0 T11 ->
      closed (length GH) (length G1) 1 T12 ->
      l = length (dms_to_list ds) ->
      T = TAnd (TFun l T11 T12) TS ->
      eq_some OT11 T11 ->
      eq_some OT12 T12 ->
      dms_has_typeP GH G1 (dcons (dfun OT11 OT12 t12) ds) T (S (n1+n2))

(* <: -- subtyping *)
with stpP: tenv -> venv -> ty -> ty -> nat -> Prop :=
| stp_bot: forall GH G1 T n1,
    closed (length GH) (length G1) 0  T ->
    stpP GH G1 TBot T (S n1)
| stp_top: forall GH G1 T n1,
    closed (length GH) (length G1) 0 T ->
    stpP GH G1 T  TTop (S n1)
| stp_fun: forall GH G1 l T1 T2 T3 T4 T2' T4' n1 n2,
    T2' = (open 0 (TVar false (length GH)) T2) ->
    T4' = (open 0 (TVar false (length GH)) T4) ->
    closed (length GH) (length G1) 1 T2 ->
    closed (length GH) (length G1) 1 T4 ->
    stpP GH G1 T3 T1 n1 ->
    stpP (T3::GH) G1 T2' T4' n2 ->
    stpP GH G1 (TFun l T1 T2) (TFun l T3 T4) (S (n1+n2))
| stp_typ: forall GH G1 l T1 T2 T3 T4 n1 n2,
    stpP GH G1 T3 T1 n2 ->
    stpP GH G1 T2 T4 n1 ->
    stpP GH G1 (TTyp l T1 T2) (TTyp l T3 T4) (S (n1+n2))

| stp_strong_sel1: forall GH G1 l T2 ds TX x n1,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    stpP [] G1 TX T2 n1 ->
    stpP GH G1 (TSel (TVar true x) l) T2 (S n1)
| stp_strong_sel2: forall GH G1 l T1 ds TX x n1,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    stpP [] G1 T1 TX n1 ->
    stpP GH G1 T1 (TSel (TVar true x) l) (S n1)

| stp_sel1: forall GH G1 l T2 x n1,
    htpP  GH G1 x (TTyp l TBot T2) n1 ->
    stpP GH G1 (TSel (TVar false x) l) T2 (S n1)

| stp_sel2: forall GH G1 l T1 x n1,
    htpP  GH G1 x (TTyp l T1 TTop) n1 ->
    stpP GH G1 T1 (TSel (TVar false x) l) (S n1)

| stp_selx: forall GH G1 l p1 n1,
    vr_closed (length GH) (length G1) 0 p1 ->
    stpP GH G1 (TSel p1 l) (TSel p1 l) (S n1)

| stp_bind1: forall GH G1 T1 T1' T2 n1,
    stpP (T1'::GH) G1 T1' T2 n1 ->
    T1' = (open 0 (TVar false (length GH)) T1) ->
    closed (length GH) (length G1) 1 T1 ->
    closed (length GH) (length G1) 0 T2 ->
    stpP GH G1 (TBind T1) T2 (S n1)

| stp_bindx: forall GH G1 T1 T1' T2 T2' n1,
    stpP (T1'::GH) G1 T1' T2' n1 ->
    T1' = (open 0 (TVar false (length GH)) T1) ->
    T2' = (open 0 (TVar false (length GH)) T2) ->
    closed (length GH) (length G1) 1 T1 ->
    closed (length GH) (length G1) 1 T2 ->
    stpP GH G1 (TBind T1) (TBind T2) (S n1)

| stp_and11: forall GH G1 T1 T2 T n1,
    stpP GH G1 T1 T n1 ->
    closed (length GH) (length G1) 0 T2 ->
    stpP GH G1 (TAnd T1 T2) T (S n1)
| stp_and12: forall GH G1 T1 T2 T n1,
    stpP GH G1 T2 T n1 ->
    closed (length GH) (length G1) 0 T1 ->
    stpP GH G1 (TAnd T1 T2) T (S n1)
| stp_and2: forall GH G1 T1 T2 T n1 n2,
    stpP GH G1 T T1 n1 ->
    stpP GH G1 T T2 n2 ->
    stpP GH G1 T (TAnd T1 T2) (S (n1+n2))

| stp_or21: forall GH G1 T1 T2 T n1,
    stpP GH G1 T T1 n1 ->
    closed (length GH) (length G1) 0 T2 ->
    stpP GH G1 T (TOr T1 T2) (S n1)
| stp_or22: forall GH G1 T1 T2 T n1,
    stpP GH G1 T T2 n1 ->
    closed (length GH) (length G1) 0 T1 ->
    stpP GH G1 T (TOr T1 T2) (S n1)
| stp_or1: forall GH G1 T1 T2 T n1 n2,
    stpP GH G1 T1 T n1 ->
    stpP GH G1 T2 T n2 ->
    stpP GH G1 (TOr T1 T2) T (S (n1+n2))

| stp_trans: forall GH G1 T1 T2 T3 n1 n2,
    stpP GH G1 T1 T2 n1 ->
    stpP GH G1 T2 T3 n2 ->
    stpP GH G1 T1 T3 (S (n1+n2))

(* :! -- typing for type selection in subtyping *)
with htpP: tenv -> venv -> id -> ty -> nat -> Prop :=
| htp_var: forall GH G1 x TX n1,
    index x GH = Some TX ->
    closed (S x) (length G1) 0 TX ->
    htpP GH G1 x TX (S n1)
| htp_unpack: forall GH G1 x TX n1,
    htpP GH G1 x (TBind TX) n1 ->
    closed (S x) (length G1) 1 TX ->
    htpP GH G1 x (open 0 (TVar false x) TX) (S n1)
| htp_sub: forall GH GU GL G1 x T1 T2 n1 n2,
    (* use restricted GH. note: this is slightly different
    from the big-step version b/c here we do not distinguish
    if variables are bound in terms vs types. it would be easy
    to do exactly the same thing by adding this distinction. *)
    htpP GH G1 x T1 n1 ->
    stpP GL G1 T1 T2 n2 ->
    length GL = S x ->
    GH = GU ++ GL ->
    htpP GH G1 x T2 (S (n1+n2))

(* ---- THE ONE NEW RULE ---------------------------------------------------- *)
| htp_pack: forall GH G1 x TX n1,
    htpP GH G1 x (open 0 (TVar false x) TX) n1 ->
    closed (S x) (length G1) 1 TX ->
    htpP GH G1 x (TBind TX) (S n1).

Definition has_typedP GH G1 t T1 := exists n, has_typeP GH G1 t T1 n.
Definition stpdP GH G1 T1 T2 := exists n, stpP GH G1 T1 T2 n.
Definition htpdP GH G1 x T1 := exists n, htpP GH G1 x T1 n.

#[local] Hint Constructors has_typeP dms_has_typeP stpP htpP : pcore.

(* ############################################################ *)
(*# 2. The extension is a supersystem #*)
(* ############################################################ *)

(* Every derivation of the reference calculus is a derivation of the extended
   one, with the same size index.  So nothing below is proved by weakening the
   original rules: [htp_pack] is the only thing that was added. *)

Scheme has_type_mut := Induction for has_type Sort Prop
with dms_has_type_mut := Induction for dms_has_type Sort Prop
with stp_mut := Induction for stp Sort Prop
with htp_mut := Induction for htp Sort Prop.
Combined Scheme dot_mut from has_type_mut, dms_has_type_mut, stp_mut, htp_mut.

Theorem extend_all :
  (forall GH G t T n, has_type GH G t T n -> has_typeP GH G t T n) /\
  (forall GH G ds T n, dms_has_type GH G ds T n -> dms_has_typeP GH G ds T n) /\
  (forall GH G T1 T2 n, stp GH G T1 T2 n -> stpP GH G T1 T2 n) /\
  (forall GH G x T n, htp GH G x T n -> htpP GH G x T n).
Proof.
  apply dot_mut; intros; eauto 4 with pcore.
Qed.

Lemma stpd_stpdP: forall GH G T1 T2, stpd GH G T1 T2 -> stpdP GH G T1 T2.
Proof.
  intros GH G T1 T2 [n H]. exists n. eapply (proj1 (proj2 (proj2 extend_all))). eauto.
Qed.

Lemma htpd_htpdP: forall GH G x T, htpd GH G x T -> htpdP GH G x T.
Proof.
  intros GH G x T [n H]. exists n. eapply (proj2 (proj2 (proj2 extend_all))). eauto.
Qed.

Lemma has_typed_has_typedP: forall GH G t T, has_typed GH G t T -> has_typedP GH G t T.
Proof.
  intros GH G t T [n H]. exists n. eapply (proj1 extend_all). eauto.
Qed.

(* ############################################################ *)
(*# 3. The construction #*)
(* ############################################################ *)

(*
   p = { B = mu(_. p.B) .. mu(_. p.C)                          (* label 0 *)
       , C = { K : p.B .. p.C } /\ ({ def missing(_:Top):Top } /\ Bot) }
                                                               (* label 1 *)
   q = { A = mu(_. p.B) }                                      (* label 0 *)

   Both D and D' ignore their self binder, so the result does not depend on
   which closedness index a packing mirror is given.
*)

Definition pB    := TSel (TVar true 0) 0.
Definition pC    := TSel (TVar true 0) 1.
Definition D     := TBind pB.
Definition D'    := TBind pC.
Definition Bbody := TTyp 0 D D'.
Definition Cbody := TAnd (TTyp 1 pB pC) (TAnd (TFun 2 TTop TTop) TBot).
Definition pds   := dcons (dty Cbody) (dcons (dty Bbody) dnil).
Definition qds   := dcons (dty D) dnil.
Definition G1    := [vobj qds; vobj pds].

(* [index] (dot.v:77-81) gives the list HEAD the LARGEST index, so with the
   store written above, [p] is at index 0 and [q] at index 1 -- exactly as the
   names [pB], [pC] (which select on [TVar true 0]) assume.  Checked, not
   assumed: *)
Example p_is_0: index 0 G1 = Some (vobj pds).  Proof. reflexivity. Qed.
Example q_is_1: index 1 G1 = Some (vobj qds).  Proof. reflexivity. Qed.
Example p_B: index 0 (dms_to_list pds) = Some (dty Bbody). Proof. reflexivity. Qed.
Example p_C: index 1 (dms_to_list pds) = Some (dty Cbody). Proof. reflexivity. Qed.
Example q_A: index 0 (dms_to_list qds) = Some (dty D).     Proof. reflexivity. Qed.
(* [q] has no member at label 2, which is what makes the term stuck. *)
Example q_no_missing: index 2 (dms_to_list qds) = None.    Proof. reflexivity. Qed.

#[local] Hint Unfold pB pC D D' Bbody Cbody pds qds G1 : unf.
Ltac unf := autounfold with unf in *; simpl in *.

(* Every [closed]/[vr_closed] side condition in this construction. *)
Ltac ccl :=
  unf;
  repeat (match goal with
          | [ |- closed _ _ _ _ ] => econstructor
          | [ |- vr_closed _ _ _ _ ] => econstructor
          end); simpl; try lia.

(* ############################################################ *)
(*# 4. What the UNMODIFIED calculus already proves #*)
(* ############################################################ *)

(* Under the self assumption [z : p.B], the bounds of [z.A] already give
   D <: D'.  This is stated for dot_spec's [stp] and [htp], and uses
   dot_spec's constructors explicitly, so the new rule is provably not doing
   this part of the work. *)

(* [z : {A : D .. D'}], from p's definition of B. *)
Lemma b_member_plain: htpd [pB] G1 0 Bbody.
Proof.
  eexists. eapply dot_spec.htp_sub with (GU:=[]) (GL:=[pB]).
  - eapply dot_spec.htp_var. reflexivity. ccl.
  - eapply dot_spec.stp_strong_sel1 with (x:=0) (ds:=pds) (TX:=Bbody).
    + reflexivity.
    + reflexivity.
    + eapply dot_spec.stp_typ.
      * (* D <: D *) eapply dot_spec.stp_bindx with (T1':=pB) (T2':=pB);
          try solve [reflexivity]; try solve [ccl].
        eapply dot_spec.stp_selx. ccl.
      * (* D' <: D' *) eapply dot_spec.stp_bindx with (T1':=pC) (T2':=pC);
          try solve [reflexivity]; try solve [ccl].
        eapply dot_spec.stp_selx. ccl.
  - reflexivity.
  - reflexivity.
  Unshelve. all: exact 0.
Qed.

(* Reflexivity at the two recursive types, under any GH. *)
Lemma refl_D: forall GH, stpd GH G1 D D.
Proof.
  intros. eexists. eapply dot_spec.stp_bindx with (T1':=pB) (T2':=pB);
    try solve [reflexivity]; try solve [ccl].
  eapply dot_spec.stp_selx. ccl.
  Unshelve. all: exact 0.
Qed.

Lemma refl_D': forall GH, stpd GH G1 D' D'.
Proof.
  intros. eexists. eapply dot_spec.stp_bindx with (T1':=pC) (T2':=pC);
    try solve [reflexivity]; try solve [ccl].
  eapply dot_spec.stp_selx. ccl.
  Unshelve. all: exact 0.
Qed.

(* D <: z.A *)
Lemma d_lower_plain: stpd [pB] G1 D (TSel (TVar false 0) 0).
Proof.
  destruct (refl_D [pB]) as [nd Hd].
  destruct b_member_plain as [nb Hb].
  eexists. eapply dot_spec.stp_sel2 with (x:=0).
  eapply dot_spec.htp_sub with (GU:=[]) (GL:=[pB]).
  - eapply Hb.
  - eapply dot_spec.stp_typ.
    + eapply Hd.
    + eapply dot_spec.stp_top. ccl.
  - reflexivity.
  - reflexivity.
  Unshelve. all: exact 0.
Qed.

(* z.A <: D' *)
Lemma d_upper_plain: stpd [pB] G1 (TSel (TVar false 0) 0) D'.
Proof.
  destruct (refl_D' [pB]) as [nd Hd].
  destruct b_member_plain as [nb Hb].
  eexists. eapply dot_spec.stp_sel1 with (x:=0).
  eapply dot_spec.htp_sub with (GU:=[]) (GL:=[pB]).
  - eapply Hb.
  - eapply dot_spec.stp_typ.
    + eapply dot_spec.stp_bot. ccl.
    + eapply Hd.
  - reflexivity.
  - reflexivity.
  Unshelve. all: exact 0.
Qed.

(* D <: D' under the self assumption, in the UNMODIFIED calculus. *)
Lemma dsub_plain: stpd [pB] G1 D D'.
Proof.
  destruct d_lower_plain as [n1 H1]. destruct d_upper_plain as [n2 H2].
  eexists. eapply dot_spec.stp_trans; eauto.
Qed.

(* Reflexivity at the remaining concrete types of the construction.  All of
   them live in the UNMODIFIED calculus; section 2's embedding lifts them. *)

Lemma refl_pB: forall GH, stpd GH G1 pB pB.
Proof. intros. eexists. eapply dot_spec.stp_selx. ccl. Unshelve. all: exact 0. Qed.

Lemma refl_pC: forall GH, stpd GH G1 pC pC.
Proof. intros. eexists. eapply dot_spec.stp_selx. ccl. Unshelve. all: exact 0. Qed.

Lemma refl_Bbody: forall GH, stpd GH G1 Bbody Bbody.
Proof.
  intros. destruct (refl_D GH) as [? Hd]. destruct (refl_D' GH) as [? Hd'].
  eexists. eapply dot_spec.stp_typ; eauto.
Qed.

Lemma refl_TTypDD: forall GH, stpd GH G1 (TTyp 0 D D) (TTyp 0 D D).
Proof.
  intros. destruct (refl_D GH) as [? Hd].
  eexists. eapply dot_spec.stp_typ; eauto.
Qed.

Lemma refl_KTyp: forall GH, stpd GH G1 (TTyp 1 pB pC) (TTyp 1 pB pC).
Proof.
  intros. destruct (refl_pB GH) as [? Hb]. destruct (refl_pC GH) as [? Hc].
  eexists. eapply dot_spec.stp_typ; eauto.
Qed.

Lemma refl_TFun: forall GH, stpd GH G1 (TFun 2 TTop TTop) (TFun 2 TTop TTop).
Proof.
  intros. eexists. eapply dot_spec.stp_fun with (T2':=TTop) (T4':=TTop);
    try solve [reflexivity]; try solve [ccl];
    eapply dot_spec.stp_top; ccl.
  Unshelve. all: exact 0.
Qed.

Lemma refl_Cbody: forall GH, stpd GH G1 Cbody Cbody.
Proof.
  intros. destruct (refl_KTyp GH) as [? Hk]. destruct (refl_TFun GH) as [? Hf].
  eexists. unfold Cbody.
  eapply dot_spec.stp_and2.
  - eapply dot_spec.stp_and11. eapply Hk. ccl.
  - eapply dot_spec.stp_and12.
    + eapply dot_spec.stp_and2.
      * eapply dot_spec.stp_and11. eapply Hf. ccl.
      * eapply dot_spec.stp_and12. eapply dot_spec.stp_bot. ccl. ccl.
    + ccl.
  Unshelve. all: exact 0.
Qed.

(* The P-versions, by the embedding of section 2 -- no new rule involved. *)
Lemma reflP_D: forall GH, stpdP GH G1 D D.
Proof. intros. apply stpd_stpdP. apply refl_D. Qed.
Lemma reflP_pB: forall GH, stpdP GH G1 pB pB.
Proof. intros. apply stpd_stpdP. apply refl_pB. Qed.
Lemma reflP_pC: forall GH, stpdP GH G1 pC pC.
Proof. intros. apply stpd_stpdP. apply refl_pC. Qed.
Lemma reflP_Bbody: forall GH, stpdP GH G1 Bbody Bbody.
Proof. intros. apply stpd_stpdP. apply refl_Bbody. Qed.
Lemma reflP_TTypDD: forall GH, stpdP GH G1 (TTyp 0 D D) (TTyp 0 D D).
Proof. intros. apply stpd_stpdP. apply refl_TTypDD. Qed.
Lemma reflP_KTyp: forall GH, stpdP GH G1 (TTyp 1 pB pC) (TTyp 1 pB pC).
Proof. intros. apply stpd_stpdP. apply refl_KTyp. Qed.
Lemma reflP_Cbody: forall GH, stpdP GH G1 Cbody Cbody.
Proof. intros. apply stpd_stpdP. apply refl_Cbody. Qed.
Lemma dsubP: stpdP [pB] G1 D D'.
Proof. apply stpd_stpdP. apply dsub_plain. Qed.

(* ############################################################ *)
(*# 5. What the packing rule adds #*)
(* ############################################################ *)

(* One step: [z : p.B] becomes [z : mu(_. p.B)].  Everything after it follows
   from rules that dot.v already has. *)

(* THE STEP THE REFERENCE FORBIDS.  This is the only use of [htp_pack] in the
   whole development. *)
Lemma z_packed: htpdP [pB] G1 0 D.
Proof.
  unfold htpdP, D. eexists. eapply htp_pack with (TX:=pB).
  - eapply htp_var.
    + reflexivity.
    + ccl.
  - ccl.
  Unshelve. all: exact 0.
Qed.

(* Subsuming by [dsub_plain] and unpacking gives [z : p.C]. *)
Lemma z_as_C: htpdP [pB] G1 0 pC.
Proof.
  destruct z_packed as [? Hz]. destruct dsubP as [? Hs].
  eexists. eapply htp_unpack with (TX:=pC).
  - eapply htp_sub with (GU:=[]) (GL:=[pB]).
    + eapply Hz.
    + eapply Hs.
    + reflexivity.
    + reflexivity.
  - ccl.
Qed.

(* [z : {K : p.B .. p.C}] *)
Lemma k_member: htpdP [pB] G1 0 (TTyp 1 pB pC).
Proof.
  destruct z_as_C as [? Hz]. destruct (reflP_Cbody ([]:tenv)) as [? Hc].
  destruct (reflP_KTyp [pB]) as [? Hk].
  eexists. eapply htp_sub with (GU:=[]) (GL:=[pB]).
  - eapply Hz.
  - eapply stp_trans.
    + eapply stp_strong_sel1 with (x:=0) (ds:=pds) (TX:=Cbody).
      * reflexivity.
      * reflexivity.
      * eapply Hc.
    + unfold Cbody. eapply stp_and11.
      * eapply Hk.
      * ccl.
  - reflexivity.
  - reflexivity.
Qed.

(* The [stp_bindx] premise: p.B <: p.C under the self assumption z : p.B. *)
Lemma premise: stpdP [pB] G1 pB pC.
Proof.
  destruct k_member as [? Hk]. destruct (reflP_pB [pB]) as [? Hb].
  destruct (reflP_pC [pB]) as [? Hc].
  eexists. eapply stp_trans.
  - eapply stp_sel2 with (x:=0) (l:=1).
    eapply htp_sub with (GU:=[]) (GL:=[pB]).
    + eapply Hk.
    + eapply stp_typ.
      * eapply Hb.
      * eapply stp_top. ccl.
    + reflexivity.
    + reflexivity.
  - eapply stp_sel1 with (x:=0) (l:=1).
    eapply htp_sub with (GU:=[]) (GL:=[pB]).
    + eapply Hk.
    + eapply stp_typ.
      * eapply stp_bot. ccl.
      * eapply Hc.
    + reflexivity.
    + reflexivity.
  Unshelve. all: exact 0.
Qed.

(* mu(_. p.B) <: mu(_. p.C), in the EMPTY context, over an ordinary store. *)
Lemma bad: stpdP [] G1 D D'.
Proof.
  destruct premise as [? Hp].
  unfold D, D'. eexists. eapply stp_bindx with (T1':=pB) (T2':=pC);
    try solve [reflexivity]; try solve [ccl].
  simpl. eapply Hp.
Qed.

(* ############################################################ *)
(*# 6. A stuck program #*)
(* ############################################################ *)

Definition badTerm := tapp (tvar true 1) 2 (tvar true 1).

(* q at its precise type, by the ordinary rule for a stored object. *)
Lemma q_typed: has_typedP [] G1 (tvar true 1) (TAnd (TTyp 0 D D) TTop).
Proof.
  eexists. eapply T_Vary with (ds:=qds) (ds':=qds) (T':=TAnd (TTyp 0 D D) TTop).
  - reflexivity.
  - eapply D_Typ.
    + eapply D_Nil.
    + ccl.
    + reflexivity.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - ccl.
  Unshelve. all: exact 0.
Qed.

Lemma q_as_decl: has_typedP [] G1 (tvar true 1) (TTyp 0 D D).
Proof.
  destruct q_typed as [? Hq]. destruct (reflP_TTypDD ([]:tenv)) as [? Hr].
  eexists. eapply T_Sub.
  - eapply Hq.
  - eapply stp_and11.
    + eapply Hr.
    + ccl.
Qed.

(* Widening q's upper bound by [bad] gives it p.B. *)
Lemma q_as_B: has_typedP [] G1 (tvar true 1) pB.
Proof.
  destruct q_as_decl as [? Hq]. destruct bad as [? Hbad].
  destruct (reflP_D ([]:tenv)) as [? Hd]. destruct (reflP_Bbody ([]:tenv)) as [? Hb].
  eexists. eapply T_Sub.
  - eapply Hq.
  - eapply stp_trans.
    + eapply stp_typ.
      * eapply Hd.
      * eapply Hbad.
    + eapply stp_strong_sel2 with (x:=0) (ds:=pds) (TX:=Bbody).
      * reflexivity.
      * reflexivity.
      * eapply Hb.
Qed.

(* Pack, subsume by [bad], unpack: q : p.C. *)
Lemma q_as_C: has_typedP [] G1 (tvar true 1) pC.
Proof.
  destruct q_as_B as [? Hq]. destruct bad as [? Hbad].
  eexists. eapply T_VarUnpack with (T1:=pC).
  - eapply T_Sub.
    + eapply T_VarPack with (T1:=pB).
      * eapply Hq.
      * reflexivity.
      * ccl.
    + eapply Hbad.
  - reflexivity.
  - ccl.
Qed.

(* p.C's upper bound contains TBot, so q : TBot. *)
Lemma q_bottom: has_typedP [] G1 (tvar true 1) TBot.
Proof.
  destruct q_as_C as [? Hq]. destruct (reflP_Cbody ([]:tenv)) as [? Hc].
  eexists. eapply T_Sub.
  - eapply Hq.
  - eapply stp_trans.
    + eapply stp_strong_sel1 with (x:=0) (ds:=pds) (TX:=Cbody).
      * reflexivity.
      * reflexivity.
      * eapply Hc.
    + unfold Cbody. eapply stp_and12.
      * eapply stp_and12.
        -- eapply stp_bot. ccl.
        -- ccl.
      * ccl.
  Unshelve. all: exact 0.
Qed.

(* Invoking a method q does not have, at TTop. *)
Lemma bad_term_typed: has_typedP [] G1 badTerm TTop.
Proof.
  destruct q_bottom as [? Hq].
  unfold badTerm. eexists. eapply T_App with (T1:=TTop) (T2:=TTop).
  - eapply T_Sub.
    + eapply Hq.
    + eapply stp_bot. ccl.
  - eapply T_Sub.
    + eapply Hq.
    + eapply stp_bot. ccl.
  - ccl.
  Unshelve. all: exact 0.
Qed.

(* The term is not a value and cannot reduce: [q] has no member at label 2,
   and both operands are already concrete variables. *)
(* The term is not a value and cannot reduce: [q] has no member at label 2
   (its only member is [A] at label 0), and both operands are already concrete
   variables, so no congruence rule applies either. *)
Lemma bad_term_stuck: forall G' t', ~ step G1 badTerm G' t'.
Proof.
  unfold badTerm. intros G' t' H. inversion H; subst.
  - (* ST_AppAbs: index 2 (dms_to_list qds) = None *)
    match goal with
    | [ Hi : index 1 G1 = Some (vobj ?ds0), Hm : index 2 (dms_to_list ?ds0) = Some _ |- _ ] =>
        compute in Hi; inversion Hi; subst; compute in Hm; inversion Hm
    end.
  - (* ST_App1: a concrete variable does not step *)
    match goal with [ Hs : step _ (tvar true 1) _ _ |- _ ] => inversion Hs end.
  - (* ST_App2: likewise *)
    match goal with [ Hs : step _ (tvar true 1) _ _ |- _ ] => inversion Hs end.
Qed.

(* ############################################################ *)
(*# 7. Unsoundness #*)
(* ############################################################ *)

(* The negation of the progress half of dot_soundness.v:1131
     Theorem type_safety : forall G t T n1,
       has_type [] G t T n1 ->
       (exists x, t = tvar true x /\ (exists ds, index x G = Some ds)) \/
       (exists G' t' n2, step G t (G'++G) t' /\ has_type [] (G'++G) t' T n2).
   instantiated at this store and this term, for the EXTENDED judgment.  Note
   the second disjunct is the extended one too, so the statement is not weakened
   by the extension being able to type more. *)
Theorem packing_unsound:
  exists (G : venv) (t : tm) (T : ty) (n1 : nat),
    has_typeP [] G t T n1 /\
    ~ ((exists x, t = tvar true x /\ (exists ds, index x G = Some ds)) \/
       (exists G' t' n2, step G t (G'++G) t' /\ has_typeP [] (G'++G) t' T n2)).
Proof.
  destruct bad_term_typed as [n Ht].
  exists G1. exists badTerm. exists TTop. exists n.
  split.
  - exact Ht.
  - intros [[x [Heq _]] | [G' [t' [n2 [Hstep _]]]]].
    + unfold badTerm in Heq. inversion Heq.
    + eapply bad_term_stuck. eapply Hstep.
Qed.

Print Assumptions packing_unsound.
