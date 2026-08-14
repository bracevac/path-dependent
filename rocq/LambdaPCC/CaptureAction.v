From Equations Require Import Equations.
From PathDependent.LambdaPCC Require Import
  FinFun Syntax Context Typing Runtime RuntimeEquality Valuation
  CaptureEvidence.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.
Unset Equations Derive Eliminator.

Derive NoConfusionHom for Ty.
Derive NoConfusionHom for Shape.
Derive NoConfusionHom for Kind.
Derive Signature for Tau.
Derive NoConfusionHom for Tau.

(** Composition operations used throughout the capture interpretation. *)
Definition cap_relation_comp {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {C D E : CaptureSet n}
    (first : CapRelation world C D) (second : CapRelation world D E) :
    CapRelation world C E := CR_trans first second.

Definition cap_ty_coercion_comp {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {T U V : Ty n}
    (first : CapTyCoercion world T U) (second : CapTyCoercion world U V) :
    CapTyCoercion world T V := CTC_trans first second.

(** Every coercion of capturing types contains the corresponding capture
    relation. *)
Fixpoint cap_ty_coercion_capture_relation {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {T U : Ty n}
    (coercion : CapTyCoercion world T U) {struct coercion} :
    CapRelation world (ty_capture_set T) (ty_capture_set U).
Proof.
  destruct coercion.
  - exact CR_refl.
  - exact (CR_trans
      (@cap_ty_coercion_capture_relation n sigma world T U coercion1)
      (@cap_ty_coercion_capture_relation n sigma world U V coercion2)).
  - exact (CR_runtime (ty_runtime_conv_capture_conversion t)).
  - exact c.
Defined.

(** The lookup and introduction capture set carried by any location
    inhabitant. *)
Record CapCaptureSetView {n : nat} {sigma : Store n}
    (world : CapWorld sigma) (x : Fin n) (C : CaptureSet n) : Type := {
  cap_view_value : Tm n;
  cap_view_assigned : CaptureSet n;
  cap_view_lookup : CapLookup world x cap_view_value cap_view_assigned;
  cap_view_captures : CapRelation world cap_view_assigned C
}.

Definition cap_location_capture_set_view {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {C : CaptureSet n} {S0 : Shape n}
    (possible : CapLocationEvidence world x (TyCapt C S0)) :
    CapCaptureSetView world x C.
Proof.
  dependent elimination possible.
  all: match goal with
       | lookup : CapLookup ?w ?x ?v ?Q,
         captures : CapRelation ?w ?Q ?C
         |- CapCaptureSetView ?w ?x ?C =>
           exact {| cap_view_value := v; cap_view_assigned := Q;
             cap_view_lookup := lookup; cap_view_captures := captures |}
       end.
Defined.

Definition cap_location_to_top {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {C : CaptureSet n} {S0 : Shape n}
    (possible : CapLocationEvidence world x (TyCapt C S0)) :
    CapLocationEvidence world x (TyCapt C ShTop) :=
  let view := cap_location_capture_set_view possible in
  CLE_top (cap_view_lookup view) (cap_view_captures view).

(** World lookup entails lookup in the underlying store. *)
Fixpoint cap_lookup_binds {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {v : Tm n} {Q : CaptureSet n}
    (evidence : CapLookup world x v Q) {struct evidence} :
    StoreBinds sigma x v.
Proof.
  destruct evidence.
  - exact (@SB_here n sigma v is_value).
  - exact (@SB_there n sigma x v u is_value
      (@cap_lookup_binds n sigma world x v Q evidence)).
Defined.

(** A first-order observation of the capture set assigned by a world. *)
Fixpoint cap_world_lookup_capture_set {n : nat} {sigma : Store n}
    (world : CapWorld sigma) {struct world} : Fin n -> CaptureSet n :=
  match world in CapWorld _ return Fin _ -> CaptureSet _ with
  | CapWorld_empty => fun x => fin_elim0 x
  | @CapWorld_val n' sigma' v is_value Q old exact =>
      fun x => fin_case (capture_weaken Q)
        (fun y => capture_weaken (cap_world_lookup_capture_set old y)) x
  end.

Lemma cap_lookup_capture_set_eq {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {v : Tm n} {Q : CaptureSet n}
    (evidence : CapLookup world x v Q) :
    cap_world_lookup_capture_set world x = Q.
Proof.
  induction evidence.
  - cbn [cap_world_lookup_capture_set]. simp fin_case. reflexivity.
  - cbn [cap_world_lookup_capture_set]. simp fin_case.
    now rewrite IHevidence.
Qed.

(** World lookup is deterministic at a location. *)
Lemma cap_lookup_unique {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {v u : Tm n}
    {Q R : CaptureSet n} (first : CapLookup world x v Q)
    (second : CapLookup world x u R) : v = u /\ Q = R.
Proof.
  split.
  - exact (store_binds_unique (cap_lookup_binds first)
      (cap_lookup_binds second)).
  - rewrite <- (cap_lookup_capture_set_eq first).
    exact (cap_lookup_capture_set_eq second).
Qed.

(** Widen the capture set while preserving the stored shape evidence. *)
Definition cap_location_widen_capture_set {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {C D : CaptureSet n}
    {S0 : Shape n} (possible : CapLocationEvidence world x (TyCapt C S0))
    (captures : CapRelation world C D) :
    CapLocationEvidence world x (TyCapt D S0).
Proof.
  dependent elimination possible.
  all: econstructor; try eassumption;
    eapply CR_trans; [eassumption | exact captures].
Defined.

(** Replace the lookup proof at the same world location. *)
Definition cap_location_replace_lookup {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {C D Q : CaptureSet n}
    {S0 : Shape n} {v : Tm n}
    (possible : CapLocationEvidence world x (TyCapt C S0))
    (lookup : CapLookup world x v Q) (captures : CapRelation world Q D) :
    CapLocationEvidence world x (TyCapt D S0).
Proof.
  dependent elimination possible.
  all: match goal with
       | old : CapLookup ?w ?x ?oldv ?oldQ,
         old_captures : CapRelation ?w ?oldQ ?oldC,
         lookup : CapLookup ?w ?x ?v ?Q,
         captures : CapRelation ?w ?Q ?D |- _ =>
           destruct (cap_lookup_unique old lookup) as [Hv HQ]
       end;
       destruct Hv; destruct HQ.
  all: match goal with
       | |- CapLocationEvidence _ _ (TyCapt _ ShTop) => eapply CLE_top
       | |- CapLocationEvidence _ _ (TyCapt _ (ShFun _ _)) => eapply CLE_fun
       | |- CapLocationEvidence _ _ (TyCapt _ (ShPair _ _ _)) => eapply CLE_pair
       | |- CapLocationEvidence _ _ (TyCapt _ (ShSingle _)) => eapply CLE_single
       | |- CapLocationEvidence _ _ (TyCapt _ (ShTSel _ _)) =>
           eapply CLE_selection
       end; eassumption.
Defined.

(** Structural runtime conversion preserves capture-aware inhabitants and
    generalized referent realization. *)
Equations cap_location_convert_congruent {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {T U : Ty n}
    (possible : CapLocationEvidence world x T)
    (conversion : TyRuntimeCongruent (PathRuntimeEq sigma) T U) :
    CapLocationEvidence world x U by struct possible :=
cap_location_convert_congruent (CLE_top lookup captures)
    (TRCG_capt capture_conversion SRCG_top) :=
  CLE_top lookup
    (CR_trans captures
      (CR_runtime (capture_runtime_congruent_to_conv capture_conversion)));
cap_location_convert_congruent
    (CLE_fun lookup body input output captures)
    (TRCG_capt capture_conversion (SRCG_fun domain codomain)) :=
  let operations := path_runtime_eq_congruence sigma in
  let backwards := CTC_runtime
    (ty_runtime_congruent_to_conv
      (ty_runtime_congruent_symm operations domain)) in
  CLE_fun lookup body
    (CTC_trans backwards input)
    (CDC_trans (CDC_narrow backwards output)
      (CDC_runtime (ty_runtime_congruent_to_conv codomain)))
    (CR_trans captures
      (CR_runtime (capture_runtime_congruent_to_conv capture_conversion)));
cap_location_convert_congruent
    (CLE_pair lookup first member captures)
    (TRCG_capt capture_conversion (SRCG_pair first_conversion member_conversion)) :=
  let operations := path_runtime_eq_congruence sigma in
  let opened := tau_runtime_conv_open_same operations
    (tau_runtime_congruent_to_conv member_conversion) (PVar y) in
  CLE_pair lookup
    (cap_location_convert_congruent first first_conversion)
    (cap_realizes_convert_congruent member
      (tau_runtime_conv_congruent operations opened))
    (CR_trans captures
      (CR_runtime (capture_runtime_congruent_to_conv capture_conversion)));
cap_location_convert_congruent
    (CLE_single lookup resolution captures)
    (TRCG_capt capture_conversion (SRCG_single paths)) :=
  CLE_single lookup
    (proj1 (path_runtime_eq_resolve_iff paths (RLoc x)) resolution)
    (CR_trans captures
      (CR_runtime (capture_runtime_congruent_to_conv capture_conversion)));
cap_location_convert_congruent
    (@CLE_selection n sigma world x v Q C E p a W
      lookup resolution witness captures)
    (TRCG_capt capture_conversion
      (@SRCG_selection n R p q a paths)) :=
  CLE_selection lookup
    (proj1 (path_runtime_eq_resolve_iff (PREq_sel paths a) (RType W))
      resolution)
    witness
    (CR_trans captures
      (CR_runtime (capture_runtime_congruent_to_conv capture_conversion)))
with cap_realizes_convert_congruent {n : nat} {k : Kind}
    {sigma : Store n} {world : CapWorld sigma} {referent : Referent n}
    {d e : Tau n k} (realizes : CapRealizes world referent d)
    (conversion : TauRuntimeCongruent (PathRuntimeEq sigma) d e) :
    CapRealizes world referent e by struct realizes :=
cap_realizes_convert_congruent (CRZ_loc possible) (TaRCG_term types) :=
  CRZ_loc (cap_location_convert_congruent possible types);
cap_realizes_convert_congruent (CRZ_type lower upper)
    (TaRCG_type lower_conversion upper_conversion) :=
  let operations := path_runtime_eq_congruence sigma in
  CRZ_type
    (CSC_trans
      (CSC_runtime (shape_runtime_congruent_to_conv
        (shape_runtime_congruent_symm operations lower_conversion))) lower)
    (CSC_trans upper
      (CSC_runtime (shape_runtime_congruent_to_conv upper_conversion)));
cap_realizes_convert_congruent (CRZ_capture lower upper)
    (TaRCG_capture lower_conversion upper_conversion) :=
  let operations := path_runtime_eq_congruence sigma in
  CRZ_capture
    (CR_trans
      (CR_runtime (capture_runtime_congruent_to_conv
        (capture_runtime_congruent_symm operations lower_conversion))) lower)
    (CR_trans upper
      (CR_runtime (capture_runtime_congruent_to_conv upper_conversion))).

(** General conversion is normalized to the structural view before acting. *)
Definition cap_location_convert {n : nat} {sigma : Store n}
    {world : CapWorld sigma} {x : Fin n} {T U : Ty n}
    (possible : CapLocationEvidence world x T)
    (conversion : TyRuntimeConv (PathRuntimeEq sigma) T U) :
    CapLocationEvidence world x U :=
  cap_location_convert_congruent possible
    (ty_runtime_conv_congruent (path_runtime_eq_congruence sigma) conversion).

Definition cap_realizes_convert {n : nat} {k : Kind} {sigma : Store n}
    {world : CapWorld sigma} {referent : Referent n} {d e : Tau n k}
    (realizes : CapRealizes world referent d)
    (conversion : TauRuntimeConv (PathRuntimeEq sigma) d e) :
    CapRealizes world referent e :=
  cap_realizes_convert_congruent realizes
    (tau_runtime_conv_congruent (path_runtime_eq_congruence sigma) conversion).

Print Assumptions cap_lookup_unique.
Print Assumptions cap_realizes_convert.
