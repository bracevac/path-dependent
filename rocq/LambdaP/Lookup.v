From Equations Require Import Equations.
From PathDependent.LambdaP Require Import FinFun Syntax Store PathReduction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Static-aligned big-step path lookup. *)
Inductive Path_lookup : forall {n : nat},
    Path n -> Store n -> Fin.t n -> Prop :=
| path_lookup_var {n : nat} (x : Fin.t n) (s : Store n) :
    Path_lookup (path_var x) s x
| path_lookup_fst {n : nat} {k : Kind} (p : Path n) (s : Store n)
    (x y : Fin.t n) (a : Name) (d : Def n k) :
    Path_lookup p s x ->
    Store_Binds s x (tm_pair y a d) ->
    Path_lookup (path_fst p) s y
| path_lookup_sel_hit {n : nat} (p : Path n) (s : Store n)
    (x y z : Fin.t n) (a : Name) :
    Path_lookup p s x ->
    Store_Binds s x (tm_pair y a (def_val z)) ->
    Path_lookup (path_sel p a) s z
| path_lookup_sel_miss {n : nat} {k : Kind} (p : Path n) (s : Store n)
    (x y z : Fin.t n) (a b : Name) (d : Def n k) :
    Path_lookup p s x ->
    Store_Binds s x (tm_pair y b d) ->
    a <> b ->
    Path_lookup (path_sel (path_fst p) a) s z ->
    Path_lookup (path_sel p a) s z.

Ltac align_lookup_bound_locations :=
  lazymatch goal with
  | IH : forall q, Path_lookup ?p ?s q -> ?x = q,
    HR : Path_lookup ?p ?s ?y,
    HB1 : Store_Binds ?s ?x _,
    HB2 : Store_Binds ?s ?y _ |- _ =>
      let E := fresh "Eloc" in
      assert (E : x = y) by (apply IH; exact HR);
      subst y
  end.

Ltac align_reduction_prefix Hbase :=
  lazymatch type of Hbase with
  | Path_reduce ?p ?s ?x =>
      match goal with
      | Hother : Path_reduce p s ?y |- _ =>
          first [ constr_eq Hbase Hother; fail 1
                | let E := fresh "Eprefix" in
                  assert (E : x = y) by
                    (eapply Path_reduce_deterministic;
                     [exact Hbase | exact Hother]);
                  subst y ]
      end
  end.

(** Static-aligned lookup is the graph of a partial function. *)
Theorem Path_lookup_deterministic {n : nat} {p : Path n} {s : Store n}
    {x1 x2 : Fin.t n} (H1 : Path_lookup p s x1)
    (H2 : Path_lookup p s x2) : x1 = x2.
Proof.
  induction H1 in x2, H2 |- *.
  - dependent elimination H2. reflexivity.
  - dependent elimination H2.
    align_lookup_bound_locations.
    eapply Store_Binds_pair_first_unique; eassumption.
  - dependent elimination H2.
    + align_lookup_bound_locations.
      eapply Store_Binds_pair_referent_unique; eassumption.
    + align_lookup_bound_locations. contradict_pair_labels.
  - dependent elimination H2.
    + align_lookup_bound_locations. contradict_pair_labels.
    + align_lookup_bound_locations.
      lazymatch goal with
      | Hleft : Store_Binds ?s ?x (tm_pair ?y1 _ _),
        Hright : Store_Binds ?s ?x (tm_pair ?y2 _ _) |- _ =>
          let E := fresh "Efirst" in
          assert (E : y1 = y2) by
            (eapply Store_Binds_pair_first_unique;
             [exact Hleft | exact Hright]);
          subst y2
      end.
      lazymatch goal with
      | |- ?z1 = ?z2 =>
          lazymatch goal with
          | IH : forall q, Path_lookup ?p ?s q -> z1 = q,
            HR : Path_lookup ?p ?s z2 |- _ => exact (IH _ HR)
          end
      end.
Qed.

Ltac align_lookup_prefix Hbase :=
  lazymatch type of Hbase with
  | Path_lookup ?p ?s ?x =>
      match goal with
      | Hother : Path_lookup p s ?y |- _ =>
          first [ constr_eq Hbase Hother; fail 1
                | let E := fresh "Eprefix" in
                  assert (E : x = y) by
                    (eapply Path_lookup_deterministic;
                     [exact Hbase | exact Hother]);
                  subst y ]
      end
  end.

(** Selection depends only on the location of its prefix. *)
Theorem Path_reduce_sel_congr {n : nat} {p q : Path n} {a : Name}
    {s : Store n} {x z : Fin.t n}
    (Hs : Path_reduce (path_sel p a) s z)
    (Hp : Path_reduce p s x) (Hq : Path_reduce q s x) :
    Path_reduce (path_sel q a) s z.
Proof.
  dependent elimination Hs.
  - align_reduction_prefix Hp.
    eapply path_reduce_sel_hit; eassumption.
  - align_reduction_prefix Hp.
    eapply path_reduce_sel_miss; eassumption.
Qed.

(** Induction-strengthened form of selection-prefix replacement. *)
Theorem Path_lookup_sel_congr_of_eq {n : nat} {r : Path n}
    {s : Store n} {z : Fin.t n} (Hs : Path_lookup r s z) :
    forall (p : Path n) (a : Name), r = path_sel p a ->
      forall (x : Fin.t n) (q : Path n),
        Path_lookup p s x -> Path_lookup q s x ->
        Path_lookup (path_sel q a) s z.
Proof.
  induction Hs; intros p0 a0 E x0 q Hp Hq; dependent elimination E.
  - align_lookup_prefix Hp.
    eapply path_lookup_sel_hit; eassumption.
  - align_lookup_prefix Hp.
    eapply path_lookup_sel_miss; [exact Hq|eassumption|eassumption|].
    eapply IHHs2.
    + reflexivity.
    + eapply path_lookup_fst; eassumption.
    + eapply path_lookup_fst; eassumption.
Qed.

Theorem Path_lookup_sel_congr {n : nat} {p q : Path n} {a : Name}
    {s : Store n} {x z : Fin.t n}
    (Hs : Path_lookup (path_sel p a) s z)
    (Hp : Path_lookup p s x) (Hq : Path_lookup q s x) :
    Path_lookup (path_sel q a) s z.
Proof. exact (Path_lookup_sel_congr_of_eq Hs eq_refl Hp Hq). Qed.

Theorem Path_lookup_toReduce {n : nat} {p : Path n} {s : Store n}
    {x : Fin.t n} (H : Path_lookup p s x) : Path_reduce p s x.
Proof.
  induction H.
  - apply path_reduce_var.
  - eapply path_reduce_fst; eassumption.
  - eapply path_reduce_sel_hit; eassumption.
  - eapply path_reduce_sel_miss; [exact IHPath_lookup1|eassumption|eassumption|].
    eapply Path_reduce_sel_congr.
    + exact IHPath_lookup2.
    + eapply path_reduce_fst; eassumption.
    + apply path_reduce_var.
Qed.

Theorem Path_reduce_toLookup {n : nat} {p : Path n} {s : Store n}
    {x : Fin.t n} (H : Path_reduce p s x) : Path_lookup p s x.
Proof.
  induction H.
  - apply path_lookup_var.
  - eapply path_lookup_fst; eassumption.
  - eapply path_lookup_sel_hit; eassumption.
  - eapply path_lookup_sel_miss; [exact IHPath_reduce1|eassumption|eassumption|].
    eapply Path_lookup_sel_congr.
    + exact IHPath_reduce2.
    + apply path_lookup_var.
    + eapply path_lookup_fst; eassumption.
Qed.

Theorem Path_lookup_iff_reduce {n : nat} {p : Path n}
    {s : Store n} {x : Fin.t n} :
    Path_lookup p s x <-> Path_reduce p s x.
Proof. split; [apply Path_lookup_toReduce|apply Path_reduce_toLookup]. Qed.
