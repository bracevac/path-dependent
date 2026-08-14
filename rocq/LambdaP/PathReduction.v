From Equations Require Import Equations.
From PathDependent.LambdaP Require Import FinFun Syntax Store.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Derive NoConfusion for Path.

(** Resolve a path to an atomic store location. *)
Inductive Path_reduce : forall {n : nat},
    Path n -> Store n -> Fin.t n -> Prop :=
| path_reduce_var {n : nat} (x : Fin.t n) (s : Store n) :
    Path_reduce (path_var x) s x
| path_reduce_fst {n : nat} {k : Kind} (p : Path n) (s : Store n)
    (x y : Fin.t n) (a : Name) (d : Def n k) :
    Path_reduce p s x ->
    Store_Binds s x (tm_pair y a d) ->
    Path_reduce (path_fst p) s y
| path_reduce_sel_hit {n : nat} (p : Path n) (s : Store n)
    (x y z : Fin.t n) (a : Name) :
    Path_reduce p s x ->
    Store_Binds s x (tm_pair y a (def_val z)) ->
    Path_reduce (path_sel p a) s z
| path_reduce_sel_miss {n : nat} {k : Kind} (p : Path n) (s : Store n)
    (x y z : Fin.t n) (a b : Name) (d : Def n k) :
    Path_reduce p s x ->
    Store_Binds s x (tm_pair y b d) ->
    a <> b ->
    Path_reduce (path_sel (path_var y) a) s z ->
    Path_reduce (path_sel p a) s z.

(** First-order observations used to compare stored pairs without dependent
    inversion of their member kind. *)
Definition tm_pair_first {n : nat} (t : Tm n) : option (Fin.t n) :=
  match t with
  | tm_pair y _ _ => Some y
  | _ => None
  end.

Definition tm_pair_label {n : nat} (t : Tm n) : option Name :=
  match t with
  | tm_pair _ a _ => Some a
  | _ => None
  end.

Definition def_referent {n : nat} {k : Kind}
    (d : Def n k) : option (Fin.t n) :=
  match d in Def n' k' return option (Fin.t n') with
  | def_val z => Some z
  | def_type _ => None
  end.

Definition tm_pair_referent {n : nat} (t : Tm n) : option (Fin.t n) :=
  match t in Tm n' return option (Fin.t n') with
  | tm_pair _ _ d => def_referent d
  | _ => None
  end.

Lemma Store_Binds_pair_first_unique {n : nat} {s : Store n}
    {x y1 y2 : Fin.t n} {k1 k2 : Kind} {a1 a2 : Name}
    {d1 : Def n k1} {d2 : Def n k2}
    (H1 : Store_Binds s x (tm_pair y1 a1 d1))
    (H2 : Store_Binds s x (tm_pair y2 a2 d2)) : y1 = y2.
Proof.
  pose proof (f_equal tm_pair_first (Store_Binds_unique H1 H2)) as H.
  cbn in H. now injection H.
Qed.

Lemma Store_Binds_pair_label_unique {n : nat} {s : Store n}
    {x y1 y2 : Fin.t n} {k1 k2 : Kind} {a1 a2 : Name}
    {d1 : Def n k1} {d2 : Def n k2}
    (H1 : Store_Binds s x (tm_pair y1 a1 d1))
    (H2 : Store_Binds s x (tm_pair y2 a2 d2)) : a1 = a2.
Proof.
  pose proof (f_equal tm_pair_label (Store_Binds_unique H1 H2)) as H.
  cbn in H. now injection H.
Qed.

Lemma Store_Binds_pair_referent_unique {n : nat} {s : Store n}
    {x y1 y2 z1 z2 : Fin.t n} {a1 a2 : Name}
    (H1 : Store_Binds s x (tm_pair y1 a1 (def_val z1)))
    (H2 : Store_Binds s x (tm_pair y2 a2 (def_val z2))) : z1 = z2.
Proof.
  pose proof (f_equal tm_pair_referent (Store_Binds_unique H1 H2)) as H.
  cbn in H. now injection H.
Qed.

Ltac align_bound_locations :=
  lazymatch goal with
  | IH : forall q, Path_reduce ?p ?s q -> ?x = q,
    HR : Path_reduce ?p ?s ?y,
    HB1 : Store_Binds ?s ?x _,
    HB2 : Store_Binds ?s ?y _ |- _ =>
      let E := fresh "Eloc" in
      assert (E : x = y) by (apply IH; exact HR);
      subst y
  end.

Ltac contradict_pair_labels :=
  lazymatch goal with
  | Hneq : ?a <> ?b,
    H1 : Store_Binds ?s ?x (tm_pair _ ?a _),
    H2 : Store_Binds ?s ?x (tm_pair _ ?b _) |- _ =>
      exfalso; apply Hneq;
      eapply Store_Binds_pair_label_unique; [exact H1 | exact H2]
  | Hneq : ?a <> ?b,
    H1 : Store_Binds ?s ?x (tm_pair _ ?b _),
    H2 : Store_Binds ?s ?x (tm_pair _ ?a _) |- _ =>
      exfalso; apply Hneq; symmetry;
      eapply Store_Binds_pair_label_unique; [exact H1 | exact H2]
  end.

(** Big-step path reduction is the graph of a partial function. *)
Theorem Path_reduce_deterministic {n : nat} {p : Path n} {s : Store n}
    {x1 x2 : Fin.t n} (H1 : Path_reduce p s x1)
    (H2 : Path_reduce p s x2) : x1 = x2.
Proof.
  induction H1 in x2, H2 |- *.
  - dependent elimination H2. reflexivity.
  - dependent elimination H2.
    align_bound_locations.
    eapply Store_Binds_pair_first_unique; eassumption.
  - dependent elimination H2.
    + align_bound_locations.
      eapply Store_Binds_pair_referent_unique; eassumption.
    + align_bound_locations. contradict_pair_labels.
  - dependent elimination H2.
    + align_bound_locations. contradict_pair_labels.
    + align_bound_locations.
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
          | IH : forall q, Path_reduce ?p ?s q -> z1 = q,
            HR : Path_reduce ?p ?s z2 |- _ => exact (IH _ HR)
          end
      end.
Qed.
