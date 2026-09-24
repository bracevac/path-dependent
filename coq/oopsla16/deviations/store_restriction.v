(** Stores: the reference types closed terms over stores the Lean port cannot
    express (DEV item 9).

    The reference's store is [venv := list vl] (dot.v:69), with no
    well-formedness condition, and [type_safety] (dot_soundness.v:1131) is
    stated for every store [G]:

      forall G t T n1, has_type [] G t T n1 -> ...

    The Lean port's store is [Store σ σ], whose entries are [Dms σ []]
    (Oopsla16/Syntax.lean, [Store]).  Being intrinsically scoped, every stored
    definition list mentions no abstract variable, no unbound [TVarB] and only
    allocated locations.  [store_types_ok] below states the part of that
    condition that concerns type members, in the reference's own definitions:
    it is implied by the Lean store's shape (argued, not proved: the two
    systems cannot be related formally), so a store violating it has no Lean
    counterpart.

    Each of the three stores below holds one object with two type members.
    Member 1 violates [store_types_ok] in one of the three possible ways;
    member 0 is [dty TTop].  (Member labels count from the end: that is the
    definition of [index], dot.v:77-81, applied to [dms_to_list],
    dot.v:59-63.)
    [stp_strong_sel1] and [stp_strong_sel2] (dot.v:305 and 310) look up only
    the member they select, so the reference derives judgments over these
    stores through member 0.  In particular it types a closed term over each
    of them, so [type_safety]'s hypothesis holds there and its conclusion is a
    statement about these stores.  The Lean safety theorems do not, and
    cannot, cover them. *)
Require Import dot_spec.
Require Import Lia.

(** Every type member of every stored object is closed in the empty context
    and mentions only allocated locations.  A necessary condition for a store
    to be expressible as a Lean [Store σ σ]. *)
Definition store_types_ok (G1: venv) :=
  forall x ds l TX,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    closed 0 (length G1) 0 TX.

(** Member 1 mentions a free abstract variable. *)
Definition Gbad_abs : venv := [vobj (dcons (dty (TSel (TVar false 3) 0)) (dcons (dty TTop) dnil))].
(** Member 1 mentions an unallocated location. *)
Definition Gbad_loc : venv := [vobj (dcons (dty (TSel (TVar true 7) 0)) (dcons (dty TTop) dnil))].
(** Member 1 mentions a dangling bound variable. *)
Definition Gbad_bvar : venv := [vobj (dcons (dty (TSel (TVarB 0) 0)) (dcons (dty TTop) dnil))].

Lemma bad_stores_not_ok:
  ~ store_types_ok Gbad_abs /\ ~ store_types_ok Gbad_loc /\ ~ store_types_ok Gbad_bvar.
Proof.
  unfold store_types_ok.
  repeat split; intro H;
    specialize (H 0 _ 1 _ eq_refl eq_refl);
    inversion H; subst;
    match goal with V: vr_closed _ _ _ _ |- _ => inversion V; simpl in *; lia end.
Qed.

(** Over any one-object store whose member 0 is [dty TTop], the selection on
    location 0 is a subtype of [TTop], and the empty object [tobj dnil] has
    that selection as its type: typed at [TBind TTop] by [T_Obj], then
    subsumed by [stp_strong_sel2]. *)
Lemma typed_over_top_member: forall ds,
  index 0 (dms_to_list ds) = Some (dty TTop) ->
  stp [] [vobj ds] (TSel (TVar true 0) 0) TTop 2 /\
  has_type [] [vobj ds] (tobj dnil) (TSel (TVar true 0) 0) 5.
Proof.
  intros ds E. split.
  - eapply stp_strong_sel1; [reflexivity | exact E | eapply stp_top; constructor].
  - change 5 with (S (2 + 2)). eapply T_Sub.
    + eapply T_Obj with (T := TTop) (T' := TTop) (n1 := 1).
      * eapply D_Nil.
      * reflexivity.
      * constructor.
    + eapply stp_strong_sel2 with (TX := TTop) (n1 := 1); [reflexivity | exact E | ].
      eapply stp_top. repeat constructor.
Qed.

(** The reference derives a subtyping judgment and types a closed term over
    each of the three stores, although none of them satisfies
    [store_types_ok]. *)
Theorem store_restriction_is_real:
  forall G, G = Gbad_abs \/ G = Gbad_loc \/ G = Gbad_bvar ->
  ~ store_types_ok G /\
  stp [] G (TSel (TVar true 0) 0) TTop 2 /\
  has_type [] G (tobj dnil) (TSel (TVar true 0) 0) 5.
Proof.
  intros G HG. destruct bad_stores_not_ok as [A [L B]].
  destruct HG as [-> | [-> | ->]];
    (split; [assumption | apply typed_over_top_member; reflexivity]).
Qed.
