From Stdlib Require Import Program.Wf Arith.Wf_nat Lia
  Wellfounded.Lexicographic_Product Wellfounded.Inverse_Image.
From Equations Require Import Equations.
From PathDependent.LambdaPCC Require Import
  FinFun Syntax Context Typing Runtime RuntimeEquality Valuation
  StoreStratification CaptureEvidence CaptureAction CaptureStatic.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.
Unset Equations Derive Eliminator.

Derive Signature for Fin.
Derive NoConfusionHom for Fin.
Derive NoConfusionHom for Referent.

#[local] Instance cap_action_pair_wf : WellFounded
    (Relation_Operators.slexprod nat nat lt lt) :=
  wf_slexprod nat nat lt lt lt_wf lt_wf.

Definition cap_action_same_stratum {s smaller larger : nat}
    (less : smaller < larger) :
    Relation_Operators.slexprod nat nat lt lt
      (s, smaller) (s, larger) :=
  Relation_Operators.right_slex nat nat lt lt s smaller larger less.

Definition cap_action_lower_stratum {smaller larger a b : nat}
    (less : smaller < larger) :
    Relation_Operators.slexprod nat nat lt lt
      (smaller, a) (larger, b) :=
  Relation_Operators.left_slex nat nat lt lt smaller larger a b less.

Definition cap_realizes_location_evidence {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {T : Ty n}
    (realizes : CapRealizes world (RLoc x) (TauTerm T)) :
    CapLocationEvidence world x T.
Proof. dependent elimination realizes. exact c. Defined.

(** Instantiate a source member closure at a realized location. *)
Definition cap_member_closure_instantiate {n : nat} {k : Kind}
    {sigma : Store n} {world : CapWorld sigma} {S0 : Ty n}
    {d e : Tau (S n) k} {x : Fin n}
    (closure : CapMemberClosure world S0 d e)
    (argument : CapLocationEvidence world x S0) :
    CapCoercion world (tau_open d (PVar x)) (tau_open e (PVar x)).
Proof.
  dependent elimination closure.
  pose (extended := cap_environment_snoc c argument).
  pose (compiled := cap_tau_sub_compile extended t).
  rewrite <- !tau_rename_openAt_eq_open_var.
  rewrite !tau_rename_ext_openAt. exact compiled.
Defined.

(** Tree sizes used as the second component of coercion-action
    termination. *)
Fixpoint cap_ty_coercion_tree_size {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {T U : Ty n}
    (coercion : CapTyCoercion world T U) {struct coercion} : nat
with cap_shape_coercion_tree_size {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {S0 T : Shape n}
    (coercion : CapShapeCoercion world S0 T) {struct coercion} : nat.
Proof.
  - destruct coercion.
    + exact 1.
    + exact (@cap_ty_coercion_tree_size n sigma world T U coercion1 +
        @cap_ty_coercion_tree_size n sigma world U V coercion2 + 1).
    + exact 1.
    + exact (@cap_shape_coercion_tree_size n sigma world S0 T c0 + 1).
  - destruct coercion.
    + exact 1.
    + exact (@cap_shape_coercion_tree_size n sigma world S0 T coercion1 +
        @cap_shape_coercion_tree_size n sigma world T U coercion2 + 2).
    + exact 1.
    + exact 1.
    + exact 1.
    + exact 1.
    + exact 1.
    + match goal with
      | sub : @CapShapeCoercion ?n0 ?sigma0 ?world0 ?A ?B |- _ =>
          exact (@cap_shape_coercion_tree_size n0 sigma0 world0 A B sub + 2)
      end.
    + match goal with
      | sub : @CapShapeCoercion ?n0 ?sigma0 ?world0 ?A ?B |- _ =>
          exact (@cap_shape_coercion_tree_size n0 sigma0 world0 A B sub + 2)
      end.
    + match goal with
      | sub : @CapTyCoercion ?n0 ?sigma0 ?world0 ?A ?B |- _ =>
          exact (@cap_ty_coercion_tree_size n0 sigma0 world0 A B sub + 1)
      end.
    + match goal with
      | sub : @CapTyCoercion ?n0 ?sigma0 ?world0 ?A ?B |- _ =>
          exact (@cap_ty_coercion_tree_size n0 sigma0 world0 A B sub + 1)
      end.
Defined.

Fixpoint cap_coercion_tree_size {n : nat} {k : Kind}
    {sigma : Store n} {world : CapWorld sigma} {d e : Tau n k}
    (coercion : CapCoercion world d e) {struct coercion} : nat.
Proof.
  destruct coercion.
  - exact 1.
  - exact (@cap_coercion_tree_size n k sigma world d e coercion1 +
      @cap_coercion_tree_size n k sigma world e f coercion2 + 1).
  - exact 1.
  - exact (@cap_ty_coercion_tree_size n sigma world T U c + 1).
  - exact (@cap_shape_coercion_tree_size n sigma world L' L c +
      @cap_shape_coercion_tree_size n sigma world U U' c0 + 1).
  - exact 1.
Defined.

(** Apply a capture-aware coercion to a realized generalized referent.  The
    lexicographic measure mirrors the Lean development: stored pair fields
    decrease the referent stratum; all other recursive calls decrease the
    coercion tree. *)
(* The first direct Program encoding of the lexicographic recursion is kept
   out of the compiled development: its single generated proof term is far
   too large for practical kernel checking.  The factored Equations encoding
   below has the same recursion and exposes small, checkable equations. *)
(*
Program Fixpoint cap_coercion_action_aux {n : nat} {k : Kind}
    {sigma : Store n} {world : CapWorld sigma} {d e : Tau n k}
    {referent : Referent n} (coercion : CapCoercion world d e)
    (realizes : CapRealizes world referent d)
    (key : nat * nat)
    (key_ok : key =
      (referent_stratum referent, cap_coercion_tree_size coercion))
    {wf (Relation_Operators.slexprod nat nat lt lt) key} :
    CapRealizes world referent e := ltac:(
  subst key;
  destruct coercion;
  [ exact realizes
  | exact (@cap_coercion_action_aux _ _ _ _ _ _ _ coercion2
      (@cap_coercion_action_aux _ _ _ _ _ _ _ coercion1 realizes
        (referent_stratum referent, cap_coercion_tree_size coercion1)
        (@Logic.eq_refl _ _)
        (@cap_action_same_stratum (referent_stratum referent)
          (cap_coercion_tree_size coercion1)
          (cap_coercion_tree_size (CC_trans coercion1 coercion2))
          (ltac:(cbn [cap_coercion_tree_size];
            lia))))
      (referent_stratum referent, cap_coercion_tree_size coercion2)
      (@Logic.eq_refl _ _)
      (@cap_action_same_stratum (referent_stratum referent)
        (cap_coercion_tree_size coercion2)
        (cap_coercion_tree_size (CC_trans coercion1 coercion2))
        (ltac:(cbn [cap_coercion_tree_size]; lia))))
  | exact (cap_realizes_convert realizes t)
  | dependent elimination realizes;
    dependent elimination c;
    [ exact (CRZ_loc c0)
    | exact (@cap_coercion_action_aux _ _ _ _ _ _ _ (CC_term c1)
        (@cap_coercion_action_aux _ _ _ _ _ _ _ (CC_term c)
          (CRZ_loc c0)
          (referent_stratum (RLoc x), cap_coercion_tree_size (CC_term c))
          (@Logic.eq_refl _ _)
          (@cap_action_same_stratum (referent_stratum (RLoc x))
            (cap_coercion_tree_size (CC_term c))
            (cap_coercion_tree_size (CC_term (CTC_trans c c1)))
            (ltac:(cbn [cap_coercion_tree_size
              cap_ty_coercion_tree_size]; lia))))
        (referent_stratum (RLoc x), cap_coercion_tree_size (CC_term c1))
        (@Logic.eq_refl _ _)
        (@cap_action_same_stratum (referent_stratum (RLoc x))
          (cap_coercion_tree_size (CC_term c1))
          (cap_coercion_tree_size (CC_term (CTC_trans c c1)))
          (ltac:(cbn [cap_coercion_tree_size
            cap_ty_coercion_tree_size]; lia))))
    | exact (CRZ_loc (cap_location_convert c0 t))
    | match goal with
      | shape_coercion : CapShapeCoercion _ _ _ |- _ =>
          dependent elimination shape_coercion
      end;
      [ match goal with
        | captures : CapRelation ?w ?C ?D,
          possible : CapLocationEvidence ?w ?x0 (TyCapt ?C ?S) |- _ =>
            exact (CRZ_loc (cap_location_widen_capture_set possible captures))
        end
      | match goal with
        | captures : CapRelation ?w ?C ?D,
          first_code : CapShapeCoercion ?w ?S ?M,
          second_code : CapShapeCoercion ?w ?M ?T,
          possible : CapLocationEvidence ?w ?x0 (TyCapt ?C ?S) |- _ =>
          let first_result := constr:(@cap_coercion_action_aux _ _ _ _ _ _ _
            (CC_term (CTC_capt CR_refl first_code)) (CRZ_loc possible)
            (referent_stratum (RLoc x0),
              cap_coercion_tree_size
                (CC_term (CTC_capt CR_refl first_code)))
            (@Logic.eq_refl _ _)
            (@cap_action_same_stratum (referent_stratum (RLoc x0))
              (cap_coercion_tree_size
                (CC_term (CTC_capt CR_refl first_code)))
              (cap_coercion_tree_size
                (CC_term (CTC_capt captures
                  (CSC_trans first_code second_code))))
              (ltac:(cbn [cap_coercion_tree_size cap_ty_coercion_tree_size
                cap_shape_coercion_tree_size]; lia)))) in
          let second_result := constr:(@cap_coercion_action_aux _ _ _ _ _ _ _
            (CC_term (CTC_capt CR_refl second_code)) first_result
            (referent_stratum (RLoc x0),
              cap_coercion_tree_size
                (CC_term (CTC_capt CR_refl second_code)))
            (@Logic.eq_refl _ _)
            (@cap_action_same_stratum (referent_stratum (RLoc x0))
              (cap_coercion_tree_size
                (CC_term (CTC_capt CR_refl second_code)))
              (cap_coercion_tree_size
                (CC_term (CTC_capt captures
                  (CSC_trans first_code second_code))))
              (ltac:(cbn [cap_coercion_tree_size cap_ty_coercion_tree_size
                cap_shape_coercion_tree_size]; lia)))) in
          pose second_result as mapped;
          dependent elimination mapped;
          match goal with
          | result : CapLocationEvidence ?w ?x0 (TyCapt ?C ?T) |- _ =>
              exact (CRZ_loc
                (cap_location_widen_capture_set result captures))
          end
        end
      | match goal with
        | captures : CapRelation ?w ?C ?D,
          conversion : ShapeRuntimeConv (PathRuntimeEq ?store) ?S ?T,
          possible : CapLocationEvidence ?w ?x0 (TyCapt ?C ?S) |- _ =>
          let operations := constr:(path_runtime_eq_congruence store) in
          let types := constr:(TRCG_capt
            (capture_runtime_congruent_refl operations C)
            (shape_runtime_conv_congruent operations conversion)) in
          exact (CRZ_loc (cap_location_widen_capture_set
            (cap_location_convert_congruent possible types) captures))
        end
      | dependent elimination c0
      | match goal with
        | captures : CapRelation ?w ?C ?D,
          possible : CapLocationEvidence ?w ?x0 (TyCapt ?C ?S) |- _ =>
            exact (CRZ_loc (cap_location_widen_capture_set
              (cap_location_to_top possible) captures))
        end
      | dependent elimination c0;
        match goal with
        | captures : CapRelation ?w ?C ?D,
          target_resolution : PathResolve ?store ?path (RLoc ?target_x),
          target : CapLocationEvidence ?w ?target_x (TyCapt ?E ?S),
          lookup : CapLookup ?w ?source_x ?value ?Q,
          source_resolution : PathResolve ?store ?path (RLoc ?source_x),
          source_coverage : CapRelation ?w ?Q ?C |- _ =>
            pose proof (path_resolve_deterministic source_resolution
              target_resolution) as equality;
            dependent elimination equality;
            exact (CRZ_loc (cap_location_replace_lookup target lookup
              (CR_trans source_coverage captures)))
        end
      | dependent elimination c0;
        match goal with
        | captures : CapRelation ?w ?C ?D,
          target_resolution : PathResolve ?store ?target_path (RLoc ?target_x),
          declared_source : PathResolve ?store ?source_path (RLoc ?target_x),
          lookup : CapLookup ?w ?source_x ?value ?Q,
          actual_source : PathResolve ?store ?source_path (RLoc ?source_x),
          source_coverage : CapRelation ?w ?Q ?C |- _ =>
            pose proof (path_resolve_deterministic actual_source
              declared_source) as equality;
            dependent elimination equality;
            exact (CRZ_loc (CLE_single lookup target_resolution
              (CR_trans source_coverage captures)))
        end
      | match goal with
        | captures : CapRelation ?w ?C ?D,
          resolution : PathResolve ?store ?selected_path ?selected_referent,
          lower : CapShapeCoercion ?w ?L ?W,
          possible : CapLocationEvidence ?w ?x0 (TyCapt ?C ?L) |- _ =>
          let view := constr:(cap_location_capture_set_view possible) in
          let mapped := constr:(@cap_coercion_action_aux _ _ _ _ _ _ _
            (CC_term (CTC_capt CR_refl lower)) (CRZ_loc possible)
            (referent_stratum (RLoc x0),
              cap_coercion_tree_size (CC_term (CTC_capt CR_refl lower)))
            (@Logic.eq_refl _ _)
            (@cap_action_same_stratum (referent_stratum (RLoc x0))
              (cap_coercion_tree_size (CC_term (CTC_capt CR_refl lower)))
              (cap_coercion_tree_size
                (CC_term (CTC_capt captures
                  (CSC_select_lower resolution lower))))
              (ltac:(cbn [cap_coercion_tree_size cap_ty_coercion_tree_size
                cap_shape_coercion_tree_size]; lia)))) in
          let witness := constr:(cap_realizes_location_evidence mapped) in
          exact (CRZ_loc
            (CLE_selection (cap_view_lookup view) resolution witness
              (CR_trans (cap_view_captures view) captures)))
        end
      | dependent elimination c0;
        match goal with
        | captures : CapRelation ?w ?C ?D,
          target_resolution : PathResolve ?store ?selected (RType ?target_W),
          upper : CapShapeCoercion ?w ?target_W ?U,
          lookup : CapLookup ?w ?x0 ?value ?Q,
          source_resolution : PathResolve ?store ?selected (RType ?source_W),
          witness : CapLocationEvidence ?w ?x0 (TyCapt ?E ?source_W),
          source_coverage : CapRelation ?w ?Q ?C |- _ =>
          pose proof (path_resolve_deterministic source_resolution
            target_resolution) as equality;
          dependent elimination equality;
          let mapped := constr:(@cap_coercion_action_aux _ _ _ _ _ _ _
            (CC_term (CTC_capt CR_refl upper)) (CRZ_loc witness)
            (referent_stratum (RLoc x0),
              cap_coercion_tree_size (CC_term (CTC_capt CR_refl upper)))
            (@Logic.eq_refl _ _)
            (@cap_action_same_stratum (referent_stratum (RLoc x0))
              (cap_coercion_tree_size (CC_term (CTC_capt CR_refl upper)))
              (cap_coercion_tree_size
                (CC_term (CTC_capt captures
                  (CSC_select_upper target_resolution upper))))
              (ltac:(cbn [cap_coercion_tree_size cap_ty_coercion_tree_size
                cap_shape_coercion_tree_size]; lia)))) in
          let result := constr:(cap_realizes_location_evidence mapped) in
          exact (CRZ_loc (cap_location_replace_lookup result lookup
            (CR_trans source_coverage captures)))
        end
      | dependent elimination c0;
        match goal with
        | captures : CapRelation ?w ?C ?D,
          domain : CapTyCoercion ?w ?Sprime ?S,
          codomain : CapDeferredCoercion ?w ?Sprime ?U ?Uprime,
          lookup : CapLookup ?w ?x0 (TmAbs ?A ?body_term) ?Q,
          body_evidence : CapBody ?w ?A ?body_term ?B ?body_captures,
          input : CapTyCoercion ?w ?S ?A,
          output : CapDeferredCoercion ?w ?S ?B ?U,
          source_coverage : CapRelation ?w ?Q ?C |- _ =>
            exact (CRZ_loc (CLE_fun lookup body_evidence
              (CTC_trans domain input)
              (CDC_trans (CDC_narrow domain output) codomain)
              (CR_trans source_coverage captures)))
        end
      | dependent elimination c0;
        match goal with
        | captures : CapRelation ?w ?C ?D,
          first_code : CapTyCoercion ?w ?S ?Sprime,
          member_closure : CapMemberClosure ?w ?S ?d ?dprime,
          lookup : CapLookup ?w ?x0 (TmPair ?y0 ?label ?delta) ?Q,
          first : CapLocationEvidence ?w ?y0 ?S,
          member : CapRealizes ?w (def_referent ?delta)
            (tau_open ?d (PVar ?y0)),
          source_coverage : CapRelation ?w ?Q ?C |- _ =>
          let mapped := constr:(@cap_coercion_action_aux _ _ _ _ _ _ _
            (CC_term first_code) (CRZ_loc first)
            (referent_stratum (RLoc y0),
              cap_coercion_tree_size (CC_term first_code))
            (@Logic.eq_refl _ _)
            (@cap_action_lower_stratum
              (referent_stratum (RLoc y0))
              (referent_stratum (RLoc x0))
              (cap_coercion_tree_size (CC_term first_code))
              (cap_coercion_tree_size
                (CC_term (CTC_capt captures
                  (CSC_pair first_code member_closure))))
              (store_binds_pair_first_stratum_lt
                (cap_lookup_binds lookup)))) in
          let mapped_first := constr:(cap_realizes_location_evidence mapped) in
          let instantiated := constr:(cap_member_closure_instantiate
            member_closure first) in
          let mapped_member := constr:(@cap_coercion_action_aux _ _ _ _ _ _ _
            instantiated member
            (referent_stratum (def_referent delta),
              cap_coercion_tree_size instantiated)
            (@Logic.eq_refl _ _)
            (@cap_action_lower_stratum
              (referent_stratum (def_referent delta))
              (referent_stratum (RLoc x0))
              (cap_coercion_tree_size instantiated)
              (cap_coercion_tree_size
                (CC_term (CTC_capt captures
                  (CSC_pair first_code member_closure))))
              (store_binds_pair_referent_stratum_lt
                (cap_lookup_binds lookup)))) in
          exact (CRZ_loc (CLE_pair lookup mapped_first mapped_member
            (CR_trans source_coverage captures)))
        end
      ]
    ]
  | dependent elimination realizes;
    match goal with
    | outer_lower : CapShapeCoercion ?w ?Lprime ?L,
      outer_upper : CapShapeCoercion ?w ?U ?Uprime,
      source_lower : CapShapeCoercion ?w ?L ?W,
      source_upper : CapShapeCoercion ?w ?W ?U |- _ =>
        exact (CRZ_type (CSC_trans outer_lower source_lower)
          (CSC_trans source_upper outer_upper))
    end
  | dependent elimination realizes;
    match goal with
    | outer_lower : CapRelation ?w ?Lprime ?L,
      outer_upper : CapRelation ?w ?U ?Uprime,
      source_lower : CapRelation ?w ?L ?W,
      source_upper : CapRelation ?w ?W ?U |- _ =>
        exact (CRZ_capture (CR_trans outer_lower source_lower)
          (CR_trans source_upper outer_upper))
    end
  ]).

Next Obligation.
  apply wf_slexprod; apply lt_wf.
Qed.

Definition cap_coercion_action {n : nat} {k : Kind} {sigma : Store n}
    {world : CapWorld sigma} {d e : Tau n k} {referent : Referent n}
    (coercion : CapCoercion world d e)
    (realizes : CapRealizes world referent d) :
    CapRealizes world referent e :=
  @cap_coercion_action_aux n k sigma world d e referent coercion realizes
    (referent_stratum referent, cap_coercion_tree_size coercion)
    (@Logic.eq_refl _ _).
*)

Definition cap_coercion_action_order : (nat * nat) -> (nat * nat) -> Prop :=
  Relation_Operators.slexprod nat nat lt lt.

Lemma cap_coercion_action_order_wf : well_founded cap_coercion_action_order.
Proof.
  unfold cap_coercion_action_order. apply wf_slexprod; apply lt_wf.
Qed.

#[global] Instance cap_coercion_action_order_well_founded :
    WellFounded cap_coercion_action_order := cap_coercion_action_order_wf.

(** The impossible bottom-location case is isolated so that the main action
    can remain an equation per coercion constructor. *)
Definition cap_shape_bottom_action {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {C D : CaptureSet n}
    {target : Shape n}
    (possible : CapLocationEvidence world x (TyCapt C ShBot)) :
    CapRealizes world (RLoc x) (TauTerm (TyCapt D target)).
Proof. dependent elimination possible. Defined.

Definition cap_shape_runtime_action {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {C D : CaptureSet n}
    {source target : Shape n}
    (captures : CapRelation world C D)
    (conversion : ShapeRuntimeConv (PathRuntimeEq sigma) source target)
    (possible : CapLocationEvidence world x (TyCapt C source)) :
    CapRealizes world (RLoc x) (TauTerm (TyCapt D target)) :=
  let operations := path_runtime_eq_congruence sigma in
  let types := TRCG_capt
    (capture_runtime_congruent_refl operations C)
    (shape_runtime_conv_congruent operations conversion) in
  CRZ_loc (cap_location_widen_capture_set
    (cap_location_convert_congruent possible types) captures).

Definition cap_shape_widen_action {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x target_x : Fin n}
    {C D E : CaptureSet n} {p : Path n} {target : Shape n}
    (captures : CapRelation world C D)
    (target_resolution : PathResolve sigma p (RLoc target_x))
    (target_possible : CapLocationEvidence world target_x (TyCapt E target))
    (possible : CapLocationEvidence world x (TyCapt C (ShSingle p))) :
    CapRealizes world (RLoc x) (TauTerm (TyCapt D target)).
Proof.
  dependent elimination possible.
  pose proof (path_resolve_deterministic p1 target_resolution) as equality.
  dependent elimination equality.
  match goal with
  | lookup : CapLookup _ _ _ _, coverage : CapRelation _ _ _ |- _ =>
      exact (CRZ_loc (cap_location_replace_lookup target_possible lookup
        (CR_trans coverage captures)))
  end.
Defined.

Definition cap_shape_alias_action {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x target_x : Fin n}
    {C D : CaptureSet n} {p q : Path n}
    (captures : CapRelation world C D)
    (target_resolution : PathResolve sigma p (RLoc target_x))
    (source_resolution : PathResolve sigma q (RLoc target_x))
    (possible : CapLocationEvidence world x (TyCapt C (ShSingle q))) :
    CapRealizes world (RLoc x) (TauTerm (TyCapt D (ShSingle p))).
Proof.
  dependent elimination possible.
  pose proof (path_resolve_deterministic p1 source_resolution) as equality.
  dependent elimination equality.
  match goal with
  | lookup : CapLookup _ _ _ _, coverage : CapRelation _ _ _ |- _ =>
      exact (CRZ_loc
        (CLE_single lookup target_resolution (CR_trans coverage captures)))
  end.
Defined.

Record CapSelectionLocationView {n : nat} {sigma : Store n}
    {world : CapWorld sigma} (x : Fin n) (C : CaptureSet n)
    (p : Path n) (a : Name) : Type := {
  cap_selection_value : Tm n;
  cap_selection_lookup_captures : CaptureSet n;
  cap_selection_witness_captures : CaptureSet n;
  cap_selection_shape : Shape n;
  cap_selection_lookup : CapLookup world x cap_selection_value
    cap_selection_lookup_captures;
  cap_selection_resolution : PathResolve sigma (PSel p a)
    (RType cap_selection_shape);
  cap_selection_witness : CapLocationEvidence world x
    (TyCapt cap_selection_witness_captures cap_selection_shape);
  cap_selection_coverage : CapRelation world cap_selection_lookup_captures C
}.

Equations cap_location_selection_view {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {C : CaptureSet n}
    {p : Path n} {a : Name}
    (possible : CapLocationEvidence world x (TyCapt C (ShTSel p a))) :
    @CapSelectionLocationView n sigma world x C p a
    by struct possible :=
cap_location_selection_view
    (@CLE_selection n sigma world x value Q C E p a W
      lookup resolution witness coverage) :=
  {| cap_selection_value := value;
     cap_selection_lookup_captures := Q;
     cap_selection_witness_captures := E;
     cap_selection_shape := W;
     cap_selection_lookup := lookup;
     cap_selection_resolution := resolution;
     cap_selection_witness := witness;
     cap_selection_coverage := coverage |}.

Definition cap_selection_witness_align {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {E : CaptureSet n}
    {p : Path n} {a : Name} {source target : Shape n}
    (source_resolution : PathResolve sigma (PSel p a) (RType source))
    (target_resolution : PathResolve sigma (PSel p a) (RType target))
    (witness : CapLocationEvidence world x (TyCapt E source)) :
    CapLocationEvidence world x (TyCapt E target).
Proof.
  pose proof (path_resolve_deterministic source_resolution target_resolution)
    as equality.
  dependent elimination equality. exact witness.
Defined.

Definition cap_shape_fun_action {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {C D : CaptureSet n}
    {S0 Sprime : Ty n} {T Tprime : Ty (S n)}
    (captures : CapRelation world C D)
    (domain : CapTyCoercion world Sprime S0)
    (codomain : CapDeferredCoercion world Sprime T Tprime)
    (possible : CapLocationEvidence world x (TyCapt C (ShFun S0 T))) :
    CapRealizes world (RLoc x) (TauTerm (TyCapt D (ShFun Sprime Tprime))).
Proof.
  dependent elimination possible.
  match goal with
  | lookup : CapLookup _ _ _ _, body_evidence : CapBody _ _ _ _ _,
    input : CapTyCoercion _ _ _, output : CapDeferredCoercion _ _ _ _,
    coverage : CapRelation _ _ _ |- _ =>
      exact (CRZ_loc (CLE_fun lookup body_evidence
        (CTC_trans domain input)
        (CDC_trans (CDC_narrow domain output) codomain)
        (CR_trans coverage captures)))
  end.
Defined.

Record CapPairLocationView {n : nat} {k : Kind} {sigma : Store n}
    {world : CapWorld sigma} (x : Fin n) (C : CaptureSet n)
    (S0 : Ty n) (a : Name) (d : Tau (S n) k) : Type := {
  cap_pair_first_location : Fin n;
  cap_pair_definition : Def n k;
  cap_pair_lookup_captures : CaptureSet n;
  cap_pair_lookup : CapLookup world x
    (TmPair cap_pair_first_location a cap_pair_definition)
    cap_pair_lookup_captures;
  cap_pair_first : CapLocationEvidence world cap_pair_first_location S0;
  cap_pair_member : CapRealizes world (def_referent cap_pair_definition)
    (tau_open d (PVar cap_pair_first_location));
  cap_pair_coverage : CapRelation world cap_pair_lookup_captures C
}.

Equations cap_location_pair_view {n : nat} {k : Kind}
    {sigma : Store n} {world : CapWorld sigma} {x : Fin n}
    {C : CaptureSet n} {S0 : Ty n} {a : Name} {d : Tau (S n) k}
    (possible : CapLocationEvidence world x (TyCapt C (ShPair S0 a d))) :
    @CapPairLocationView n k sigma world x C S0 a d
    by struct possible :=
cap_location_pair_view
    (@CLE_pair n k sigma world x y Q C a delta S0 d
      lookup first member coverage) :=
  {| cap_pair_first_location := y;
     cap_pair_definition := delta;
     cap_pair_lookup_captures := Q;
     cap_pair_lookup := lookup;
     cap_pair_first := first;
     cap_pair_member := member;
     cap_pair_coverage := coverage |}.

Equations cap_pair_view_first_stratum_lt {n : nat} {k : Kind}
    {sigma : Store n} {world : CapWorld sigma} {x : Fin n}
    {C : CaptureSet n} {S0 : Ty n} {a : Name} {d : Tau (S n) k}
    (possible : CapLocationEvidence world x (TyCapt C (ShPair S0 a d))) :
    referent_stratum
      (RLoc (cap_pair_first_location (cap_location_pair_view possible))) <
      referent_stratum (RLoc x) by struct possible :=
cap_pair_view_first_stratum_lt
    (@CLE_pair n k sigma world x y Q C a delta S0 d
      lookup first member coverage) :=
  store_binds_pair_first_stratum_lt (cap_lookup_binds lookup).

Equations cap_pair_view_referent_stratum_lt {n : nat} {k : Kind}
    {sigma : Store n} {world : CapWorld sigma} {x : Fin n}
    {C : CaptureSet n} {S0 : Ty n} {a : Name} {d : Tau (S n) k}
    (possible : CapLocationEvidence world x (TyCapt C (ShPair S0 a d))) :
    referent_stratum
      (def_referent
        (cap_pair_definition (cap_location_pair_view possible))) <
      referent_stratum (RLoc x) by struct possible :=
cap_pair_view_referent_stratum_lt
    (@CLE_pair n k sigma world x y Q C a delta S0 d
      lookup first member coverage) :=
  store_binds_pair_referent_stratum_lt (cap_lookup_binds lookup).

(* The direct Equations presentation below documents the defining equations,
   but its generated coverage term is also too large.  The checked action is
   assembled from separately opaque dispatchers immediately afterwards. *)
(*
(** Factored well-founded action.  Recursive calls either reduce the
    coercion tree at the same referent, or enter a stored pair component at a
    strictly smaller store stratum. *)
Equations cap_coercion_action {n : nat} {k : Kind} {sigma : Store n}
    {world : CapWorld sigma} {d e : Tau n k} {referent : Referent n}
    (coercion : CapCoercion world d e)
    (realizes : CapRealizes world referent d) :
    CapRealizes world referent e
    by wf (referent_stratum referent, cap_coercion_tree_size coercion)
      cap_coercion_action_order :=
cap_coercion_action CC_refl realizes := realizes;
cap_coercion_action (CC_trans first second) realizes :=
  cap_coercion_action second (cap_coercion_action first realizes);
cap_coercion_action (CC_runtime conversion) realizes :=
  cap_realizes_convert realizes conversion;
cap_coercion_action (CC_type lower upper)
    (CRZ_type source_lower source_upper) :=
  CRZ_type (CSC_trans lower source_lower) (CSC_trans source_upper upper);
cap_coercion_action (CC_capture lower upper)
    (CRZ_capture source_lower source_upper) :=
  CRZ_capture (CR_trans lower source_lower) (CR_trans source_upper upper);
cap_coercion_action (CC_term CTC_refl) (CRZ_loc possible) :=
  CRZ_loc possible;
cap_coercion_action (CC_term (CTC_trans first second)) (CRZ_loc possible) :=
  cap_coercion_action (CC_term second)
    (cap_coercion_action (CC_term first) (CRZ_loc possible));
cap_coercion_action (CC_term (CTC_runtime conversion)) (CRZ_loc possible) :=
  CRZ_loc (cap_location_convert possible conversion);
cap_coercion_action (CC_term (CTC_capt captures CSC_refl))
    (CRZ_loc possible) :=
  CRZ_loc (cap_location_widen_capture_set possible captures);
cap_coercion_action
    (CC_term (CTC_capt captures (CSC_trans first second)))
    (CRZ_loc possible) :=
  let first_result := cap_coercion_action
    (CC_term (CTC_capt CR_refl first)) (CRZ_loc possible) in
  let second_result := cap_coercion_action
    (CC_term (CTC_capt CR_refl second)) first_result in
  CRZ_loc (cap_location_widen_capture_set
    (cap_realizes_location_evidence second_result) captures);
cap_coercion_action
    (CC_term (CTC_capt captures (CSC_runtime conversion)))
    (CRZ_loc possible) :=
  cap_shape_runtime_action captures conversion possible;
cap_coercion_action (CC_term (CTC_capt captures CSC_bot))
    (CRZ_loc possible) := cap_shape_bottom_action possible;
cap_coercion_action (CC_term (CTC_capt captures CSC_top))
    (CRZ_loc possible) :=
  CRZ_loc (cap_location_widen_capture_set
    (cap_location_to_top possible) captures);
cap_coercion_action
    (CC_term (CTC_capt captures (CSC_widen resolution target)))
    (CRZ_loc possible) :=
  cap_shape_widen_action captures resolution target possible;
cap_coercion_action
    (CC_term (CTC_capt captures (CSC_alias target_resolution
      source_resolution))) (CRZ_loc possible) :=
  cap_shape_alias_action captures target_resolution source_resolution possible;
cap_coercion_action
    (CC_term (CTC_capt captures (CSC_select_lower resolution lower)))
    (CRZ_loc possible) :=
  let view := cap_location_capture_set_view possible in
  let mapped := cap_coercion_action
    (CC_term (CTC_capt CR_refl lower)) (CRZ_loc possible) in
  CRZ_loc (CLE_selection (cap_view_lookup view) resolution
    (cap_realizes_location_evidence mapped)
    (CR_trans (cap_view_captures view) captures));
cap_coercion_action
    (CC_term (CTC_capt captures (CSC_select_upper resolution upper)))
    (CRZ_loc possible) :=
  let view := cap_location_selection_view possible in
  let witness := cap_selection_witness_align
    (cap_selection_resolution view) resolution
    (cap_selection_witness view) in
  let mapped := cap_coercion_action
    (CC_term (CTC_capt CR_refl upper)) (CRZ_loc witness) in
  CRZ_loc (cap_location_replace_lookup
    (cap_realizes_location_evidence mapped)
    (cap_selection_lookup view)
    (CR_trans (cap_selection_coverage view) captures));
cap_coercion_action
    (CC_term (CTC_capt captures (CSC_fun domain codomain)))
    (CRZ_loc possible) :=
  cap_shape_fun_action captures domain codomain possible;
cap_coercion_action
    (CC_term (CTC_capt captures (CSC_pair first_code member_closure)))
    (CRZ_loc possible) :=
  let view := cap_location_pair_view possible in
  let mapped_first := cap_coercion_action (CC_term first_code)
    (CRZ_loc (cap_pair_first view)) in
  let instantiated := cap_member_closure_instantiate member_closure
    (cap_pair_first view) in
  let mapped_member := cap_coercion_action instantiated
    (cap_pair_member view) in
  CRZ_loc (CLE_pair (cap_pair_lookup view)
    (cap_realizes_location_evidence mapped_first) mapped_member
    (CR_trans (cap_pair_coverage view) captures)).

Ltac solve_cap_coercion_action_decrease :=
  unfold cap_coercion_action_order;
  first
    [ apply cap_action_same_stratum;
      cbn [cap_coercion_tree_size cap_ty_coercion_tree_size
        cap_shape_coercion_tree_size]; lia
    | apply cap_action_lower_stratum;
      eauto using store_binds_pair_first_stratum_lt,
        store_binds_pair_referent_stratum_lt ].

Next Obligation. solve_cap_coercion_action_decrease. Qed.
Next Obligation. solve_cap_coercion_action_decrease. Qed.
Next Obligation. solve_cap_coercion_action_decrease. Qed.
Next Obligation. solve_cap_coercion_action_decrease. Qed.
Next Obligation. solve_cap_coercion_action_decrease. Qed.
Next Obligation. solve_cap_coercion_action_decrease. Qed.
Next Obligation. solve_cap_coercion_action_decrease. Qed.
Next Obligation. solve_cap_coercion_action_decrease. Qed.
Next Obligation.
  unfold cap_coercion_action_order. apply cap_action_lower_stratum.
  match goal with
  | possible : CapLocationEvidence ?w ?x
      (TyCapt ?C (ShPair ?S0 ?a ?d)) |- _ =>
      exact (cap_pair_view_first_stratum_lt possible)
  end.
Qed.
Next Obligation.
  unfold cap_coercion_action_order. apply cap_action_lower_stratum.
  match goal with
  | possible : CapLocationEvidence ?w ?x
      (TyCapt ?C (ShPair ?S0 ?a ?d)) |- _ =>
      exact (cap_pair_view_referent_stratum_lt possible)
  end.
Qed.
*)

Definition CapActionRecursive (current : nat * nat) : Type :=
  forall (n : nat) (k : Kind) (sigma : Store n) (world : CapWorld sigma)
    (d e : Tau n k) (referent : Referent n)
    (coercion : CapCoercion world d e),
    CapRealizes world referent d ->
    cap_coercion_action_order
      (referent_stratum referent, cap_coercion_tree_size coercion) current ->
    CapRealizes world referent e.

Definition cap_shape_coercion_action_dispatch {n : nat}
    {sigma : Store n} {world : CapWorld sigma} {x : Fin n}
    {C D : CaptureSet n} {S0 T : Shape n}
    (captures : CapRelation world C D)
    (coercion : CapShapeCoercion world S0 T)
    (possible : CapLocationEvidence world x (TyCapt C S0))
    (recur : CapActionRecursive
      (referent_stratum (RLoc x),
        cap_coercion_tree_size (CC_term (CTC_capt captures coercion)))) :
    CapLocationEvidence world x (TyCapt D T).
Proof.
  destruct coercion.
  - exact (cap_location_widen_capture_set possible captures).
  - pose (first_result := @recur n KTerm sigma world
      (TauTerm (TyCapt C S0)) (TauTerm (TyCapt C T)) (RLoc x)
      (CC_term (CTC_capt CR_refl coercion1)) (CRZ_loc possible)
      (ltac:(apply cap_action_same_stratum;
        cbn [cap_coercion_tree_size cap_ty_coercion_tree_size
          cap_shape_coercion_tree_size]; lia))).
    pose (second_result := @recur n KTerm sigma world
      (TauTerm (TyCapt C T)) (TauTerm (TyCapt C U)) (RLoc x)
      (CC_term (CTC_capt CR_refl coercion2)) first_result
      (ltac:(apply cap_action_same_stratum;
        cbn [cap_coercion_tree_size cap_ty_coercion_tree_size
          cap_shape_coercion_tree_size]; lia))).
    exact (cap_location_widen_capture_set
      (cap_realizes_location_evidence second_result) captures).
  - exact (cap_realizes_location_evidence
      (cap_shape_runtime_action captures s possible)).
  - exact (cap_realizes_location_evidence (cap_shape_bottom_action possible)).
  - exact (cap_location_widen_capture_set
      (cap_location_to_top possible) captures).
  - exact (cap_realizes_location_evidence
      (cap_shape_widen_action captures p0 c possible)).
  - exact (cap_realizes_location_evidence
      (cap_shape_alias_action captures p0 p1 possible)).
  - match goal with
    | resolution : PathResolve _ _ _,
      lower : CapShapeCoercion _ _ _ |- _ =>
        let view := constr:(cap_location_capture_set_view possible) in
        let mapped := constr:(@recur n KTerm sigma world _ _ (RLoc x)
          (CC_term (CTC_capt CR_refl lower)) (CRZ_loc possible)
          (ltac:(apply cap_action_same_stratum;
            cbn [cap_coercion_tree_size cap_ty_coercion_tree_size
              cap_shape_coercion_tree_size]; lia))) in
        exact (CLE_selection (cap_view_lookup view) resolution
          (cap_realizes_location_evidence mapped)
          (CR_trans (cap_view_captures view) captures))
    end.
  - match goal with
    | resolution : PathResolve _ _ _,
      upper : CapShapeCoercion _ _ _ |- _ =>
        let view := constr:(cap_location_selection_view possible) in
        let witness := constr:(cap_selection_witness_align
          (cap_selection_resolution view) resolution
          (cap_selection_witness view)) in
        let mapped := constr:(@recur n KTerm sigma world _ _ (RLoc x)
          (CC_term (CTC_capt CR_refl upper)) (CRZ_loc witness)
          (ltac:(apply cap_action_same_stratum;
            cbn [cap_coercion_tree_size cap_ty_coercion_tree_size
              cap_shape_coercion_tree_size]; lia))) in
        exact (cap_location_replace_lookup
          (cap_realizes_location_evidence mapped)
          (cap_selection_lookup view)
          (CR_trans (cap_selection_coverage view) captures))
    end.
  - match goal with
    | domain : CapTyCoercion _ _ _,
      codomain : CapDeferredCoercion _ _ _ _ |- _ =>
        exact (cap_realizes_location_evidence
          (cap_shape_fun_action captures domain codomain possible))
    end.
  - match goal with
    | first_code : CapTyCoercion _ _ _,
      member_closure : CapMemberClosure _ _ _ _ |- _ =>
        let view := constr:(cap_location_pair_view possible) in
        let mapped_first := constr:(@recur n KTerm sigma world _ _
          (RLoc (cap_pair_first_location view)) (CC_term first_code)
          (CRZ_loc (cap_pair_first view))
          (ltac:(apply cap_action_lower_stratum;
            exact (cap_pair_view_first_stratum_lt possible)))) in
        let instantiated := constr:(cap_member_closure_instantiate
          member_closure (cap_pair_first view)) in
        let mapped_member := constr:(@recur n _ sigma world _ _
          (def_referent (cap_pair_definition view)) instantiated
          (cap_pair_member view)
          (ltac:(apply cap_action_lower_stratum;
            exact (cap_pair_view_referent_stratum_lt possible)))) in
        exact (CLE_pair (cap_pair_lookup view)
          (cap_realizes_location_evidence mapped_first) mapped_member
          (CR_trans (cap_pair_coverage view) captures))
    end.
Defined.

Definition cap_ty_coercion_action_dispatch {n : nat}
    {sigma : Store n} {world : CapWorld sigma} {x : Fin n} {T U : Ty n}
    (coercion : CapTyCoercion world T U)
    (possible : CapLocationEvidence world x T)
    (recur : CapActionRecursive
      (referent_stratum (RLoc x),
        cap_coercion_tree_size (CC_term coercion))) :
    CapLocationEvidence world x U.
Proof.
  destruct coercion.
  - exact possible.
  - pose (first_result := @recur n KTerm sigma world
      (TauTerm T) (TauTerm U) (RLoc x) (CC_term coercion1)
      (CRZ_loc possible)
      (ltac:(apply cap_action_same_stratum;
        cbn [cap_coercion_tree_size cap_ty_coercion_tree_size]; lia))).
    pose (second_result := @recur n KTerm sigma world
      (TauTerm U) (TauTerm V) (RLoc x) (CC_term coercion2)
      first_result
      (ltac:(apply cap_action_same_stratum;
        cbn [cap_coercion_tree_size cap_ty_coercion_tree_size]; lia))).
    exact (cap_realizes_location_evidence second_result).
  - exact (cap_location_convert possible t).
  - exact (@cap_shape_coercion_action_dispatch n sigma world x C D S0 T
      c c0 possible recur).
Defined.

Definition cap_coercion_action_dispatch {n : nat} {k : Kind}
    {sigma : Store n} {world : CapWorld sigma} {d e : Tau n k}
    {referent : Referent n} (coercion : CapCoercion world d e)
    (realizes : CapRealizes world referent d)
    (recur : CapActionRecursive
      (referent_stratum referent, cap_coercion_tree_size coercion)) :
    CapRealizes world referent e.
Proof.
  destruct coercion.
  - exact realizes.
  - exact (@recur n k sigma world e f referent coercion2
      (@recur n k sigma world d e referent coercion1 realizes
        (ltac:(apply cap_action_same_stratum;
          cbn [cap_coercion_tree_size]; lia)))
      (ltac:(apply cap_action_same_stratum;
        cbn [cap_coercion_tree_size]; lia))).
  - exact (cap_realizes_convert realizes t).
  - dependent elimination realizes.
    exact (CRZ_loc
      (@cap_ty_coercion_action_dispatch _ _ _ _ _ _ c c0 recur)).
  - dependent elimination realizes.
    match goal with
    | outer_lower : CapShapeCoercion ?w ?Lprime ?L,
      outer_upper : CapShapeCoercion ?w ?U ?Uprime,
      source_lower : CapShapeCoercion ?w ?L ?W,
      source_upper : CapShapeCoercion ?w ?W ?U |- _ =>
        exact (CRZ_type (CSC_trans outer_lower source_lower)
          (CSC_trans source_upper outer_upper))
    end.
  - dependent elimination realizes.
    match goal with
    | outer_lower : CapRelation ?w ?Lprime ?L,
      outer_upper : CapRelation ?w ?U ?Uprime,
      source_lower : CapRelation ?w ?L ?W,
      source_upper : CapRelation ?w ?W ?U |- _ =>
        exact (CRZ_capture (CR_trans outer_lower source_lower)
          (CR_trans source_upper outer_upper))
    end.
Defined.

Inductive CapActionInput : Type :=
| CapActionPack (n : nat) (k : Kind) (sigma : Store n)
    (world : CapWorld sigma) (d e : Tau n k) (referent : Referent n)
    (coercion : CapCoercion world d e)
    (realizes : CapRealizes world referent d).

Definition cap_action_input_measure (input : CapActionInput) : nat * nat :=
  match input with
  | @CapActionPack n k sigma world d e referent coercion realizes =>
      (referent_stratum referent, cap_coercion_tree_size coercion)
  end.

Definition cap_action_input_order (left right : CapActionInput) : Prop :=
  cap_coercion_action_order
    (cap_action_input_measure left) (cap_action_input_measure right).

Lemma cap_action_input_order_wf : well_founded cap_action_input_order.
Proof.
  exact (@wf_inverse_image CapActionInput (nat * nat)
    cap_coercion_action_order cap_action_input_measure
    cap_coercion_action_order_wf).
Qed.

Definition cap_action_input_result (input : CapActionInput) : Type :=
  match input with
  | @CapActionPack n k sigma world d e referent coercion realizes =>
      CapRealizes world referent e
  end.

Definition cap_action_input_step (input : CapActionInput)
    (recur : forall next : CapActionInput,
      cap_action_input_order next input -> cap_action_input_result next) :
    cap_action_input_result input.
Proof.
  destruct input as [n k sigma world d e referent coercion realizes].
  apply (@cap_coercion_action_dispatch n k sigma world d e referent
    coercion realizes).
  intros n0 k0 sigma0 world0 d0 e0 referent0 coercion0 realizes0 less.
  exact (recur
    (@CapActionPack n0 k0 sigma0 world0 d0 e0 referent0 coercion0 realizes0)
    less).
Defined.

Definition cap_action_input_execute :
    forall input : CapActionInput, cap_action_input_result input :=
  @Fix CapActionInput cap_action_input_order cap_action_input_order_wf
    cap_action_input_result cap_action_input_step.

Definition cap_coercion_action {n : nat} {k : Kind} {sigma : Store n}
    {world : CapWorld sigma} {d e : Tau n k} {referent : Referent n}
    (coercion : CapCoercion world d e)
    (realizes : CapRealizes world referent d) :
    CapRealizes world referent e :=
  cap_action_input_execute
    (@CapActionPack n k sigma world d e referent coercion realizes).

(** Term-location wrappers for the general action. *)
Definition cap_coercion_action_location {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {T U : Ty n}
    (coercion : CapCoercion world (TauTerm T) (TauTerm U))
    (possible : CapLocationEvidence world x T) :
    CapLocationEvidence world x U.
Proof.
  pose (mapped := cap_coercion_action coercion (CRZ_loc possible)).
  dependent elimination mapped. exact c.
Defined.

Definition cap_ty_coercion_action_location {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {T U : Ty n}
    (coercion : CapTyCoercion world T U)
    (possible : CapLocationEvidence world x T) :
    CapLocationEvidence world x U :=
  cap_coercion_action_location (CC_term coercion) possible.

(** Instantiate a suspended function-result coercion. *)
Fixpoint cap_deferred_coercion_instantiate {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {S0 : Ty n} {T U : Ty (S n)} {x : Fin n}
    (deferred : CapDeferredCoercion world S0 T U)
    (argument : CapLocationEvidence world x S0) {struct deferred} :
    CapTyCoercion world (ty_open T (PVar x)) (ty_open U (PVar x)).
Proof.
  destruct deferred.
  - exact CTC_refl.
  - exact (CTC_trans
      (@cap_deferred_coercion_instantiate n sigma world S0 T U x
        deferred1 argument)
      (@cap_deferred_coercion_instantiate n sigma world S0 U V x
        deferred2 argument)).
  - exact (CTC_runtime (ty_runtime_conv_open_same
      (path_runtime_eq_congruence sigma) t (PVar x))).
  - exact (@cap_deferred_coercion_instantiate n sigma world S0 T U x
      deferred (cap_ty_coercion_action_location c argument)).
  - pose (extended := cap_environment_snoc c argument).
    pose (compiled := cap_ty_sub_compile extended t).
    rewrite <- !ty_rename_openAt_eq_open_var.
    rewrite !ty_rename_ext_openAt. exact compiled.
Defined.

Print Assumptions cap_member_closure_instantiate.
Print Assumptions cap_coercion_action.
Print Assumptions cap_deferred_coercion_instantiate.
