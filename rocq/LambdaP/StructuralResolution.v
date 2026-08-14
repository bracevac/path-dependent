From Equations Require Import Equations.
From PathDependent.LambdaP Require Import FinFun Syntax Store
  PathReduction RuntimeConversion.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** The two possible outcomes of following a path through a store. *)
Inductive Path_Endpoint (n : nat) : Type :=
| endpoint_val : Fin.t n -> Path_Endpoint n
| endpoint_type : Ty n -> Path_Endpoint n.

Arguments endpoint_val {n} _.
Arguments endpoint_type {n} _.

Derive NoConfusion for Path_Endpoint.

(** Follow a path to either a value location or a stored type definition. *)
Inductive Path_Resolve : forall {n : nat},
    Path n -> Store n -> Path_Endpoint n -> Prop :=
| path_resolve_var {n : nat} (x : Fin.t n) (s : Store n) :
    Path_Resolve (path_var x) s (endpoint_val x)
| path_resolve_fst {n : nat} {k : Kind} (p : Path n) (s : Store n)
    (x y : Fin.t n) (a : Name) (d : Def n k) :
    Path_Resolve p s (endpoint_val x) ->
    Store_Binds s x (tm_pair y a d) ->
    Path_Resolve (path_fst p) s (endpoint_val y)
| path_resolve_sel_val {n : nat} (p : Path n) (s : Store n)
    (x y z : Fin.t n) (a : Name) :
    Path_Resolve p s (endpoint_val x) ->
    Store_Binds s x (tm_pair y a (def_val z)) ->
    Path_Resolve (path_sel p a) s (endpoint_val z)
| path_resolve_sel_type {n : nat} (p : Path n) (s : Store n)
    (x y : Fin.t n) (a : Name) (U : Ty n) :
    Path_Resolve p s (endpoint_val x) ->
    Store_Binds s x (tm_pair y a (def_type U)) ->
    Path_Resolve (path_sel p a) s (endpoint_type U)
| path_resolve_sel_miss {n : nat} {k : Kind} (p : Path n) (s : Store n)
    (x y : Fin.t n) (a b : Name) (d : Def n k) (e : Path_Endpoint n) :
    Path_Resolve p s (endpoint_val x) ->
    Store_Binds s x (tm_pair y b d) ->
    a <> b ->
    Path_Resolve (path_sel (path_var y) a) s e ->
    Path_Resolve (path_sel p a) s e.

Definition endpoint_location {n : nat} (e : Path_Endpoint n) :
    option (Fin.t n) :=
  match e with endpoint_val x => Some x | endpoint_type _ => None end.

Lemma endpoint_val_inj {n : nat} {x y : Fin.t n}
    (E : @endpoint_val n x = endpoint_val y) : x = y.
Proof. now injection E. Qed.

Definition def_type_member {n : nat} {k : Kind}
    (d : Def n k) : option (Ty n) :=
  match d in Def n' _ return option (Ty n') with
  | def_val _ => None
  | def_type U => Some U
  end.

Definition tm_pair_type_member {n : nat} (t : Tm n) : option (Ty n) :=
  match t in Tm n' return option (Ty n') with
  | tm_pair _ _ d => def_type_member d
  | _ => None
  end.

Definition tm_pair_member_is_type {n : nat} (t : Tm n) : option bool :=
  match t with
  | tm_pair _ _ (def_val _) => Some false
  | tm_pair _ _ (def_type _) => Some true
  | _ => None
  end.

Lemma Store_Binds_pair_type_unique {n : nat} {s : Store n}
    {x y1 y2 : Fin.t n} {a1 a2 : Name} {U1 U2 : Ty n}
    (H1 : Store_Binds s x (tm_pair y1 a1 (def_type U1)))
    (H2 : Store_Binds s x (tm_pair y2 a2 (def_type U2))) : U1 = U2.
Proof.
  pose proof (f_equal tm_pair_type_member (Store_Binds_unique H1 H2)) as E.
  cbn in E. now injection E.
Qed.

Lemma Store_Binds_val_type_absurd {n : nat} {s : Store n}
    {x y1 y2 z : Fin.t n} {a1 a2 : Name} {U : Ty n}
    (H1 : Store_Binds s x (tm_pair y1 a1 (def_val z)))
    (H2 : Store_Binds s x (tm_pair y2 a2 (def_type U))) : False.
Proof.
  pose proof (f_equal tm_pair_member_is_type
    (Store_Binds_unique H1 H2)) as E. discriminate E.
Qed.

Ltac align_resolve_bound_locations :=
  lazymatch goal with
  | IH : forall e, Path_Resolve ?p ?s e -> endpoint_val ?x = e,
    HR : Path_Resolve ?p ?s (endpoint_val ?y),
    HB1 : Store_Binds ?s ?x _, HB2 : Store_Binds ?s ?y _ |- _ =>
      let Eendpoint := fresh "Eendpoint" in
      pose proof (IH _ HR) as Eendpoint;
      let Eloc := fresh "Eloc" in
      assert (Eloc : x = y) by exact (endpoint_val_inj Eendpoint);
      subst y
  end.

Ltac contradict_pair_member_shapes :=
  lazymatch goal with
  | Hv : Store_Binds ?s ?x (tm_pair ?yv ?av (def_val ?z)),
    Ht : Store_Binds ?s ?x (tm_pair ?yt ?atype_label (def_type ?U)) |- _ =>
      exfalso; exact (Store_Binds_val_type_absurd Hv Ht)
  | Ht : Store_Binds ?s ?x (tm_pair ?yt ?atype_label (def_type ?U)),
    Hv : Store_Binds ?s ?x (tm_pair ?yv ?av (def_val ?z)) |- _ =>
      exfalso; exact (Store_Binds_val_type_absurd Hv Ht)
  end.

(** Generalized resolution is the graph of a partial function. *)
Theorem Path_Resolve_deterministic {n : nat} {p : Path n} {s : Store n}
    {e1 e2 : Path_Endpoint n} (H1 : Path_Resolve p s e1)
    (H2 : Path_Resolve p s e2) : e1 = e2.
Proof.
  induction H1 in e2, H2 |- *.
  - dependent elimination H2. reflexivity.
  - dependent elimination H2.
    align_resolve_bound_locations.
    f_equal. eapply Store_Binds_pair_first_unique; eassumption.
  - dependent elimination H2.
    + align_resolve_bound_locations.
      f_equal. eapply Store_Binds_pair_referent_unique; eassumption.
    + align_resolve_bound_locations. contradict_pair_member_shapes.
    + align_resolve_bound_locations. contradict_pair_labels.
  - dependent elimination H2.
    + align_resolve_bound_locations. contradict_pair_member_shapes.
    + align_resolve_bound_locations.
      f_equal. eapply Store_Binds_pair_type_unique; eassumption.
    + align_resolve_bound_locations. contradict_pair_labels.
  - dependent elimination H2.
    + align_resolve_bound_locations. contradict_pair_labels.
    + align_resolve_bound_locations. contradict_pair_labels.
    + align_resolve_bound_locations.
      lazymatch goal with
      | Hleft : Store_Binds ?s ?x (tm_pair ?y1 _ _),
        Hright : Store_Binds ?s ?x (tm_pair ?y2 _ _) |- _ =>
          let Efirst := fresh "Efirst" in
          assert (Efirst : y1 = y2) by
            (eapply Store_Binds_pair_first_unique;
             [exact Hleft | exact Hright]);
          subst y2
      end.
      lazymatch goal with
      | IH : forall e2, Path_Resolve ?tail ?s e2 -> ?e1 = e2,
        HR : Path_Resolve ?tail ?s ?e2 |- _ => exact (IH _ HR)
      end.
Qed.

(** Agreement with the source term-path evaluator. *)
Theorem Path_reduce_toResolve {n : nat} {p : Path n} {s : Store n}
    {x : Fin.t n} (H : Path_reduce p s x) :
    Path_Resolve p s (endpoint_val x).
Proof.
  induction H.
  - apply path_resolve_var.
  - eapply path_resolve_fst; eassumption.
  - eapply path_resolve_sel_val; eassumption.
  - eapply path_resolve_sel_miss; eassumption.
Qed.

Theorem Path_Resolve_toReduce_of_eq {n : nat} {p : Path n}
    {s : Store n} {e : Path_Endpoint n} (H : Path_Resolve p s e) :
    forall x : Fin.t n, e = endpoint_val x -> Path_reduce p s x.
Proof.
  induction H; intros target E.
  - injection E as Ex. subst target. apply path_reduce_var.
  - injection E as Ex. subst target.
    eapply path_reduce_fst; [apply IHPath_Resolve; reflexivity | exact H0].
  - injection E as Ex. subst target.
    eapply path_reduce_sel_hit;
      [apply IHPath_Resolve; reflexivity | exact H0].
  - discriminate E.
  - eapply path_reduce_sel_miss.
    + apply IHPath_Resolve1. reflexivity.
    + exact H0.
    + exact H1.
    + apply IHPath_Resolve2. exact E.
Qed.

Theorem Path_Resolve_toReduce {n : nat} {p : Path n} {s : Store n}
    {x : Fin.t n} (H : Path_Resolve p s (endpoint_val x)) :
    Path_reduce p s x.
Proof. exact (Path_Resolve_toReduce_of_eq H eq_refl). Qed.

Theorem Path_resolve_val_iff_reduce {n : nat} {p : Path n}
    {s : Store n} {x : Fin.t n} :
    Path_Resolve p s (endpoint_val x) <-> Path_reduce p s x.
Proof. split; [apply Path_Resolve_toReduce | apply Path_reduce_toResolve]. Qed.

(** Pointwise-equivalent substitutions have the same generalized resolution
    graph after substitution into an arbitrary path. *)
Theorem Path_Resolve_subst_congr {l n : nat} {s : Store n}
    {r : Path l} {rho1 rho2 : PathSubst l n} {e : Path_Endpoint n}
    (Hrho : forall (x : Fin.t l) (endpoint : Path_Endpoint n),
      Path_Resolve (rho1 x) s endpoint <->
      Path_Resolve (rho2 x) s endpoint)
    (H : Path_Resolve (Path_subst r rho1) s e) :
    Path_Resolve (Path_subst r rho2) s e.
Proof.
  induction r as [x|r IH|r IH a] in e, H |- *; cbn in H |- *.
  - exact (proj1 (Hrho x e) H).
  - dependent elimination H.
    eapply path_resolve_fst; [eapply IH; eassumption | eassumption].
  - dependent elimination H.
    + eapply path_resolve_sel_val; [eapply IH; eassumption | eassumption].
    + eapply path_resolve_sel_type; [eapply IH; eassumption | eassumption].
    + eapply path_resolve_sel_miss;
        [eapply IH; eassumption | eassumption | eassumption | eassumption].
Qed.

Theorem Path_Resolve_subst_iff {l n : nat} {s : Store n}
    {r : Path l} {rho1 rho2 : PathSubst l n} {e : Path_Endpoint n}
    (Hrho : forall (x : Fin.t l) (endpoint : Path_Endpoint n),
      Path_Resolve (rho1 x) s endpoint <->
      Path_Resolve (rho2 x) s endpoint) :
    Path_Resolve (Path_subst r rho1) s e <->
      Path_Resolve (Path_subst r rho2) s e.
Proof.
  split.
  - apply Path_Resolve_subst_congr. exact Hrho.
  - apply Path_Resolve_subst_congr.
    intros x endpoint. symmetry. apply Hrho.
Qed.

Theorem Path_Resolve_open_iff {n : nat} {s : Store n}
    {p q : Path n} {e : Path_Endpoint n}
    (Hpq : forall endpoint : Path_Endpoint n,
      Path_Resolve p s endpoint <-> Path_Resolve q s endpoint)
    (r : Path (S n)) :
    Path_Resolve (Path_open r p) s e <->
      Path_Resolve (Path_open r q) s e.
Proof.
  unfold Path_open. apply Path_Resolve_subst_iff.
  intros x endpoint.
  refine (@Fin.cases' n x
    (fun x => Path_Resolve (PathSubst_openAt p x) s endpoint <->
      Path_Resolve (PathSubst_openAt q x) s endpoint) _ _).
  - rewrite !PathSubst_openAt_zero. apply Hpq.
  - intro y. rewrite !PathSubst_openAt_succ. reflexivity.
Qed.

(** Runtime equality preserves the generalized resolution graph at both
    kinds. *)
Theorem Path_RuntimeEq_resolve_iff {n : nat} {s : Store n}
    {p q : Path n} (H : Path_RuntimeEq s p q)
    (e : Path_Endpoint n) :
    Path_Resolve p s e <-> Path_Resolve q s e.
Proof.
  induction H in e |- *.
  - reflexivity.
  - symmetry. apply IHPath_RuntimeEq.
  - transitivity (Path_Resolve q s e).
    + apply IHPath_RuntimeEq1.
    + apply IHPath_RuntimeEq2.
  - lazymatch goal with
    | Hp : Path_reduce ?p ?s ?x,
      Hq : Path_reduce ?q ?s ?x
      |- Path_Resolve ?p ?s ?e <-> Path_Resolve ?q ?s ?e =>
        split; intro He;
        [ pose proof (Path_Resolve_deterministic He
            (Path_reduce_toResolve Hp)) as Ee;
          subst e; exact (Path_reduce_toResolve Hq)
        | pose proof (Path_Resolve_deterministic He
            (Path_reduce_toResolve Hq)) as Ee;
          subst e; exact (Path_reduce_toResolve Hp) ]
    end.
  - apply Path_Resolve_open_iff. intro endpoint.
    apply IHPath_RuntimeEq.
Qed.

Print Assumptions Path_Resolve_deterministic.
Print Assumptions Path_resolve_val_iff_reduce.
Print Assumptions Path_RuntimeEq_resolve_iff.
