(** Regularity of the reference's judgments, ported to Coq 8.19.

    The reference proves [all_closed] (dot.v:668-749) in Coq 8.4pl6.  Its proof
    scripts use [omega] and SfLib's [Case], which Coq 8.19 no longer provides,
    so this file re-proves it together with the helper lemmas it needs.

    Every lemma below except [beq_nat_true_iff] and [beq_nat_false_iff] has
    the statement of the dot.v lemma of the same name, token for token (the
    README gives the check); only the proof scripts are new.  The two
    [beq_nat] lemmas are the Coq 8.4 standard library's ([Arith.EqNat]),
    re-proved for the local [beq_nat] of [dot_spec.v]. *)
Require Import dot_spec.
Require Import Lia.

Lemma beq_nat_true_iff : forall n m, beq_nat n m = true <-> n = m.
Proof.
  induction n; destruct m; simpl; split; intros; try congruence; try reflexivity.
  - f_equal. apply IHn. assumption.
  - apply IHn. congruence.
Qed.

Lemma beq_nat_false_iff : forall n m, beq_nat n m = false <-> n <> m.
Proof.
  intros. split; intros.
  - intro E. apply beq_nat_true_iff in E. congruence.
  - destruct (beq_nat n m) eqn:E; [| reflexivity].
    apply beq_nat_true_iff in E. contradiction.
Qed.

(* dot.v:475 *)
Lemma index_max : forall X vs n (T: X),
                       index n vs = Some T ->
                       n < length vs.
Proof.
  intros X vs. induction vs; intros n T H.
  - inversion H.
  - simpl in H. destruct (beq_nat n (length vs)) eqn:E.
    + apply beq_nat_true_iff in E. subst. simpl. lia.
    + apply IHvs in H. simpl. lia.
Qed.

(* dot.v:531 *)
Lemma index_extend_mult: forall {X} G0 G2 x0 (T:X),
    index x0 G0 = Some T ->
    index x0 (G2++G0) = Some T.
Proof.
  intros X G0 G2. induction G2; intros.
  - simpl. assumption.
  - simpl. destruct (beq_nat x0 (length (G2 ++ G0))) eqn:E.
    + apply beq_nat_true_iff in E. apply index_max in H. subst.
      rewrite app_length in H. lia.
    + apply IHG2. assumption.
Qed.

(* dot.v:616 and 621 *)
Lemma vr_closed_upgrade_gh: forall i i1 j k p1,
  vr_closed i j k p1 -> i <= i1 -> vr_closed i1 j k p1.
Proof. intros. inversion H; subst; econstructor; lia. Qed.
Lemma closed_upgrade_gh: forall i i1 j k T1,
  closed i j k T1 -> i <= i1 -> closed i1 j k T1.
Proof.
  intros. generalize dependent i1. induction H; intros; econstructor; eauto using vr_closed_upgrade_gh.
Qed.

(* dot.v:640 and 645 *)
Lemma vr_closed_upgrade: forall i j k k1 p1,
  vr_closed i j k p1 -> k <= k1 -> vr_closed i j k1 p1.
Proof. intros. inversion H; subst; econstructor; lia. Qed.
Lemma closed_upgrade: forall i j k k1 T1,
  closed i j k T1 -> k <= k1 -> closed i j k1 T1.
Proof.
  intros. generalize dependent k1. induction H; intros; econstructor; eauto using vr_closed_upgrade;
  try (eapply IHclosed2; lia); try (eapply IHclosed; lia).
Qed.

(* dot.v:653 and 661 *)
Lemma vr_closed_open: forall j k n b V p, vr_closed k n (j+1) p -> vr_closed k n j (TVar b V) -> vr_closed k n j (vr_open j (TVar b V) p).
Proof.
  intros. inversion H; subst; simpl; try (econstructor; eauto; fail).
  destruct (beq_nat j x) eqn:E. assumption.
  econstructor. apply beq_nat_false_iff in E. lia.
Qed.

Lemma closed_open: forall j k n b V T, closed k n (j+1) T -> vr_closed k n j (TVar b V) -> closed k n j (open j (TVar b V) T).
Proof.
  intros. generalize dependent j. induction T; intros; inversion H; subst; simpl;
    econstructor; eauto using vr_closed_open;
    try (eapply IHT2; eauto; eapply vr_closed_upgrade; eauto; lia);
    try (eapply IHT; eauto; eapply vr_closed_upgrade; eauto; lia).
Qed.

(* Proof automation for [all_closed]: one step of the reference's case
   analysis, using the induction hypotheses at a smaller index. *)
Ltac ih IHS1 IHS2 IHH1 IHH2 IHT IHD :=
    match goal with
    | H: stp ?GH ?G ?A ?B ?m |- closed (length ?GH) (length ?G) 0 ?A => eapply IHS1; [exact H | lia]
    | H: stp ?GH ?G ?A ?B ?m |- closed (length ?GH) (length ?G) 0 ?B => eapply IHS2; [exact H | lia]
    | H: htp ?GH ?G ?x ?A ?m |- closed (length ?GH) (length ?G) 0 ?A => eapply IHH2; [exact H | lia]
    | H: htp ?GH ?G ?x ?A ?m |- ?x < length ?GH => eapply IHH1; [exact H | lia]
    | H: has_type ?GH ?G ?t ?A ?m |- closed (length ?GH) (length ?G) 0 ?A => eapply IHT; [exact H | lia]
    | H: dms_has_type ?GH ?G ?t ?A ?m |- closed (length ?GH) (length ?G) 0 ?A => eapply IHD; [exact H | lia]
    end.
Ltac step IHS1 IHS2 IHH1 IHH2 IHT IHD :=
    first
    [ eassumption
    | ih IHS1 IHS2 IHH1 IHH2 IHT IHD
    | match goal with
      | H: stp [] ?G ?A ?B ?m |- closed ?ii (length ?G) 0 ?A =>
          eapply closed_upgrade_gh with (i := length ([]:tenv)); [eapply IHS1; [exact H | lia] | simpl; lia]
      | H: stp [] ?G ?A ?B ?m |- closed ?ii (length ?G) 0 ?B =>
          eapply closed_upgrade_gh with (i := length ([]:tenv)); [eapply IHS2; [exact H | lia] | simpl; lia]
      end
    | match goal with
      | H: htp ?GH ?G ?x (TTyp ?l ?A ?B) ?m |- closed (length ?GH) (length ?G) 0 ?A =>
          let C := fresh in assert (C: closed (length GH) (length G) 0 (TTyp l A B)) by (eapply IHH2; [exact H | lia]);
          inversion C; assumption
      | H: htp ?GH ?G ?x (TTyp ?l ?A ?B) ?m |- closed (length ?GH) (length ?G) 0 ?B =>
          let C := fresh in assert (C: closed (length GH) (length G) 0 (TTyp l A B)) by (eapply IHH2; [exact H | lia]);
          inversion C; assumption
      end
    | match goal with
      | H: index ?x ?G = Some _ |- vr_closed _ (length ?G) _ (TVar true ?x) => econstructor; eapply index_max; exact H
      | H: index ?x ?G = Some _ |- vr_closed (length ?G) _ _ (TVar false ?x) => econstructor; eapply index_max; exact H
      | H: htp ?GH _ ?x _ _ |- vr_closed (length ?GH) _ _ (TVar false ?x) => econstructor; eapply IHH1; [exact H | lia]
      | H: index ?x ?G = Some _ |- ?x < length ?G => eapply index_max; exact H
      end
    | match goal with
      | H: index ?x ?GH = Some ?T, C: closed (S ?x) ?j 0 ?T |- closed (length ?GH) ?j 0 ?T =>
          eapply closed_upgrade_gh; [exact C | eapply index_max in H; lia]
      end
    | match goal with
      | H: htp ?GH ?G ?x (TBind ?TX) ?m, C: closed (S ?x) ?j 1 ?TX |- closed (length ?GH) ?j 0 (open 0 (TVar false ?x) ?TX) =>
          let L := fresh in assert (L: x < length GH) by (eapply IHH1; [exact H | lia]);
          eapply closed_open; [ simpl; eapply closed_upgrade_gh; [exact C | lia]
                              | econstructor; exact L ]
      end
    | match goal with
      | H: stp ?GL ?G ?A ?B ?m, E: length ?GL = S ?x |- closed (length (?GU ++ ?GL)) (length ?G) 0 ?B =>
          eapply closed_upgrade_gh; [eapply IHS2; [exact H | lia] | rewrite app_length; lia]
      end
    | match goal with
      | C: closed 0 ?j 0 ?T |- closed ?ii ?j 0 ?T => eapply closed_upgrade_gh; [exact C | lia]
      end
    | econstructor ].

(* dot.v:668; the reference's proof is at dot.v:687-749. *)
Lemma all_closed: forall ni,
  (forall GH G1 T1 T2 n,
     stp GH G1 T1 T2 n -> n < ni ->
     closed (length GH) (length G1) 0 T1) /\
  (forall GH G1 T1 T2 n,
     stp GH G1 T1 T2 n -> n < ni ->
     closed (length GH) (length G1) 0 T2) /\
  (forall x GH G1 T2 n,
     htp GH G1 x T2 n -> n < ni ->
     x < length GH) /\
  (forall x GH G1 T2 n,
     htp GH G1 x T2 n -> n < ni ->
     closed (length GH) (length G1) 0 T2) /\
  (forall GH G1 t T n,
     has_type GH G1 t T n -> n < ni ->
     closed (length GH) (length G1) 0 T) /\
  (forall GH G1 ds T n,
     dms_has_type GH G1 ds T n -> n < ni ->
     closed (length GH) (length G1) 0 T).
Proof.
  intros n. induction n. repeat split; intros; lia.
  destruct IHn as [IHS1 [IHS2 [IHH1 [IHH2 [IHT IHD]]]]].
  repeat split; intros; inversion H; subst; repeat (step IHS1 IHS2 IHH1 IHH2 IHT IHD).
Qed.

(* dot.v:781 *)
Lemma htp_closed: forall x GH G1 T2 n,
  htp GH G1 x T2 n ->
  closed (length GH) (length G1) 0 T2.
Proof. intros. edestruct all_closed as [_ [_ [_ [A _]]]]. eapply A. eauto. eauto. Qed.

(* dot.v:786 *)
Lemma htp_closed1: forall x GH G1 T2 n,
  htp GH G1 x T2 n ->
  x < length GH.
Proof. intros. edestruct all_closed as [_ [_ [A _]]]. eapply A. eauto. eauto. Qed.

(* dot.v:791 *)
Lemma has_type_closed: forall GH G1 t T n1,
  has_type GH G1 t T n1 ->
  closed (length GH) (length G1) 0 T.
Proof. intros. edestruct all_closed as [_ [_ [_ [_ [A _]]]]]. eapply A. eauto. eauto. Qed.

(* dot.v:796 *)
Lemma dms_has_type_closed: forall GH G1 t T n1,
  dms_has_type GH G1 t T n1 ->
  closed (length GH) (length G1) 0 T.
Proof. intros. edestruct all_closed as [_ [_ [_ [_ [_ A]]]]]. eapply A. eauto. eauto. Qed.

(* dot.v:830 *)
Lemma stp_closed1 : forall GH G1 T1 T2 n1,
                      stp GH G1 T1 T2 n1 ->
                      closed (length GH) (length G1) 0 T1.
Proof. intros. edestruct all_closed as [A _]. eapply A. eauto. eauto. Qed.

(* dot.v:835 *)
Lemma stp_closed2 : forall GH G1 T1 T2 n1,
                      stp GH G1 T1 T2 n1 ->
                      closed (length GH) (length G1) 0 T2.
Proof. intros. edestruct all_closed as [_ [A _]]. eapply A. eauto. eauto. Qed.
