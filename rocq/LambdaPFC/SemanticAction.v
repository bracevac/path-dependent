From Stdlib Require Import Arith.Wf_nat Lia
  Wellfounded.Lexicographic_Product.
From Equations Require Import Equations.
From PathDependent.LambdaPFC Require Import
  FinFun Syntax Context Typing Runtime Valuation StoreStratification
  RuntimeEquality SemanticEvidence.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Structural runtime conversion preserves inhabitants and referents. *)
Equations store_possible_convert_congruent {m : nat} {sigma : Store m}
    {x : Fin m} {S T : Ty m} (possible : StorePossible sigma x S)
    (congruent : TauRuntimeCongruent (PathRuntimeEq sigma)
      (TauTy S) (TauTy T)) : StorePossible sigma x T
    by struct possible :=
store_possible_convert_congruent Possible_top TRG_top := Possible_top;
store_possible_convert_congruent
    (Possible_fun binding body input output) (TRG_fun domain codomain) :=
  let operations := path_runtime_eq_congruence sigma in
  let backwards := Coercion_runtime
    (tau_runtime_congruent_to_runtime_conv
      (tau_runtime_congruent_symm operations domain)) in
  Possible_fun binding body
    (Coercion_trans backwards input)
    (Deferred_trans (Deferred_narrow backwards output)
      (Deferred_runtime
        (tau_runtime_congruent_to_runtime_conv codomain)));
store_possible_convert_congruent
    (Possible_pair binding first member) (TRG_pair first_conv member_conv) :=
  let operations := path_runtime_eq_congruence sigma in
  let opened := tau_runtime_conv_open_same operations
    (tau_runtime_congruent_to_runtime_conv member_conv) (PVar y) in
  Possible_pair binding
    (store_possible_convert_congruent first first_conv)
    (referent_realizes_convert_congruent member
      (tau_runtime_conv_runtime_congruent operations opened));
store_possible_convert_congruent
    (Possible_single resolution) (TRG_single paths) :=
  Possible_single
    (proj1 (path_runtime_eq_resolve_iff paths (RefLoc x)) resolution);
store_possible_convert_congruent
    (@Possible_selection _ _ _ p a W resolution witness)
    (@TRG_selection _ _ _ _ _ paths) :=
  Possible_selection
    (proj1 (path_runtime_eq_resolve_iff (PREq_sel paths a) (RefType W))
      resolution) witness
with referent_realizes_convert_congruent {m : nat} {k : Kind}
    {sigma : Store m} {referent : PathReferent m} {d1 d2 : Tau m k}
    (realizes : ReferentRealizes sigma referent d1)
    (congruent : TauRuntimeCongruent (PathRuntimeEq sigma) d1 d2) :
    ReferentRealizes sigma referent d2 by struct realizes :=
referent_realizes_convert_congruent
    (Realizes_loc possible) TRG_top :=
  Realizes_loc (store_possible_convert_congruent possible TRG_top);
referent_realizes_convert_congruent
    (Realizes_loc possible) TRG_bot :=
  Realizes_loc (store_possible_convert_congruent possible TRG_bot);
referent_realizes_convert_congruent
    (Realizes_loc possible) (TRG_fun domain codomain) :=
  Realizes_loc
    (store_possible_convert_congruent possible (TRG_fun domain codomain));
referent_realizes_convert_congruent
    (Realizes_loc possible) (TRG_pair first member) :=
  Realizes_loc
    (store_possible_convert_congruent possible (TRG_pair first member));
referent_realizes_convert_congruent
    (Realizes_loc possible) (TRG_single paths) :=
  Realizes_loc
    (store_possible_convert_congruent possible (TRG_single paths));
referent_realizes_convert_congruent
    (Realizes_loc possible) (TRG_selection paths) :=
  Realizes_loc
    (store_possible_convert_congruent possible (TRG_selection paths));
referent_realizes_convert_congruent
    (Realizes_type lower upper) (TRG_interval lower_conv upper_conv) :=
  let operations := path_runtime_eq_congruence sigma in
  Realizes_type
    (Coercion_trans
      (Coercion_runtime
        (tau_runtime_congruent_to_runtime_conv
          (tau_runtime_congruent_symm operations lower_conv))) lower)
    (Coercion_trans upper
      (Coercion_runtime
        (tau_runtime_congruent_to_runtime_conv upper_conv))).

Arguments store_possible_convert_congruent {m sigma x S T} possible congruent.
Arguments referent_realizes_convert_congruent
  {m k sigma referent d1 d2} realizes congruent.

(** Direct action of arbitrary runtime conversion on realization. *)
Definition referent_realizes_convert {m : nat} {k : Kind}
    {sigma : Store m} {referent : PathReferent m} {d1 d2 : Tau m k}
    (realizes : ReferentRealizes sigma referent d1)
    (conversion : TauRuntimeConv (PathRuntimeEq sigma) d1 d2) :
    ReferentRealizes sigma referent d2 :=
  referent_realizes_convert_congruent realizes
    (tau_runtime_conv_runtime_congruent
      (path_runtime_eq_congruence sigma) conversion).

(** Semantic result of resolving a source path-typing derivation. *)
Record PathTyResolution {n m : nat} {k : Kind} (sigma : Store m)
    (rho : Valuation n m) (p : Path n) (d : Tau n k) : Type := {
  path_ty_referent : PathReferent m;
  path_ty_resolution : PathResolve (path_rename p rho) sigma path_ty_referent;
  path_ty_realizes : ReferentRealizes sigma path_ty_referent
    (tau_rename d rho)
}.

(** Resolve a typed source path and retain its precise realization. *)
Fixpoint path_ty_resolve {n m : nat} {Gamma : Ctx n}
    {rho : Valuation n m} {sigma : Store m} {k : Kind}
    {p : Path n} {d : Tau n k} (environment : Environment Gamma rho sigma)
    (code : PathTy Gamma p d) {struct code} :
    PathTyResolution sigma rho p d.
Proof.
  destruct code.
  - refine {| path_ty_referent := RefLoc (apply rho x) |}.
    + simp path_rename. exact (Resolve_var (apply rho x)).
    + simp tau_rename. exact (Realizes_loc (environment_lookup environment x)).
  - pose proof (@path_ty_resolve n m Gamma rho sigma KStar p
      (TauTy (TyPair first a member)) environment code) as result.
    destruct result as [referent resolution realizes].
    rewrite tau_rename_equation_1, ty_rename_equation_4 in realizes.
    dependent elimination realizes.
    match goal with
    | possible : StorePossible _ _ _ |- _ => dependent elimination possible
    end.
    match goal with
    | binding : StoreBinds _ _ (TmPair ?y _ _),
      first_possible : StorePossible _ y _ |- _ =>
        refine {| path_ty_referent := RefLoc y |};
        [ simp path_rename; exact (Resolve_fst resolution binding)
        | simp tau_rename; exact (Realizes_loc first_possible) ]
    end.
  - pose proof (@path_ty_resolve n m Gamma rho sigma KStar p
      (TauTy (TyPair first a member)) environment code) as result.
    destruct result as [referent resolution realizes].
    rewrite tau_rename_equation_1, ty_rename_equation_4 in realizes.
    dependent elimination realizes.
    match goal with
    | possible : StorePossible _ _ _ |- _ => dependent elimination possible
    end.
    pose (first_resolution := Resolve_fst resolution s0).
    pose (paths := PREq_coresolve (Resolve_var y) first_resolution).
    pose (converted := referent_realizes_convert r
      (TRC_replace (tau_rename member (ext rho)) paths)).
    assert (converted' : ReferentRealizes sigma3 (def_referent delta)
      (tau_rename (tau_open member (PFst p)) rho)).
    { rewrite tau_open_rename. exact converted. }
    refine {| path_ty_referent := def_referent delta |}.
    + simp path_rename. exact (Resolve_sel resolution s0).
    + exact converted'.
  - pose proof (@path_ty_resolve n m Gamma rho sigma KStar p
      (TauTy (TyPair first b receiver_member)) environment code1)
      as receiver_result.
    pose proof (@path_ty_resolve n m Gamma rho sigma k
      (PSel (PFst p) a) member environment code2) as member_result.
    destruct receiver_result as [receiver_ref receiver_resolution
      receiver_realizes].
    destruct member_result as [member_ref member_resolution member_realizes].
    rewrite tau_rename_equation_1, ty_rename_equation_4
      in receiver_realizes.
    dependent elimination receiver_realizes.
    match goal with
    | possible : StorePossible _ _ _ |- _ => dependent elimination possible
    end.
    match goal with
    | binding : StoreBinds _ _ (TmPair ?y ?label _),
      mismatch : a <> ?label |- _ =>
        pose (first_resolution := Resolve_fst receiver_resolution binding);
        pose (tail_resolution := path_resolve_sel_congr member_resolution
          first_resolution (Resolve_var y));
        refine {| path_ty_referent := member_ref |};
        [ simp path_rename;
          exact (Resolve_sel_miss receiver_resolution binding mismatch
            tail_resolution)
        | exact member_realizes ]
    end.
Defined.

Arguments path_ty_resolve {n m Gamma rho sigma k p d} environment code.

(** Eagerly compile source subtyping under a semantic environment. *)
Fixpoint tau_sub_compile {n m : nat} {Gamma : Ctx n}
    {rho : Valuation n m} {sigma : Store m} {k : Kind}
    {d1 d2 : Tau n k} (environment : Environment Gamma rho sigma)
    (code : TauSub Gamma d1 d2) {struct code} :
    Coercion sigma (tau_rename d1 rho) (tau_rename d2 rho).
Proof.
  destruct code.
  - exact Coercion_refl.
  - exact (Coercion_trans
      (@tau_sub_compile n m Gamma rho sigma k d1 d2 environment code1)
      (@tau_sub_compile n m Gamma rho sigma k d2 d3 environment code2)).
  - exact Coercion_bot.
  - exact Coercion_top.
  - pose proof (path_ty_resolve environment p0) as result.
    destruct result as [referent resolution realizes].
    rewrite tau_rename_equation_1 in realizes.
    dependent elimination realizes.
    exact (Coercion_widen resolution s).
  - pose proof (path_ty_resolve environment p0) as result.
    destruct result as [referent resolution realizes].
    rewrite tau_rename_equation_1, ty_rename_equation_5 in realizes.
    dependent elimination realizes.
    dependent elimination s.
    rewrite !tau_rename_equation_1, !ty_rename_equation_5.
    exact (Coercion_alias resolution p2).
  - pose proof (path_ty_resolve environment p0) as result.
    destruct result as [referent resolution realizes].
    rewrite tau_rename_equation_2 in realizes.
    dependent elimination realizes.
    exact (Coercion_sel_hi resolution c0).
  - pose proof (path_ty_resolve environment p0) as result.
    destruct result as [referent resolution realizes].
    rewrite tau_rename_equation_2 in realizes.
    dependent elimination realizes.
    exact (Coercion_sel_lo resolution c).
  - exact (Coercion_fun
      (@tau_sub_compile n m Gamma rho sigma KStar _ _ environment code1)
      (Deferred_source environment code2)).
  - exact (Coercion_pair
      (@tau_sub_compile n m Gamma rho sigma KStar _ _ environment code1)
      (Member_source environment code2)).
  - exact (Coercion_bounds
      (@tau_sub_compile n m Gamma rho sigma KStar _ _ environment code1)
      (@tau_sub_compile n m Gamma rho sigma KStar _ _ environment code2)).
Defined.

Arguments tau_sub_compile {n m Gamma rho sigma k d1 d2} environment code.

(** Instantiate a delayed pair member at its concrete first component. *)
Definition member_closure_instantiate {m : nat} {sigma : Store m}
    {S : Ty m} {k : Kind} {d d' : Tau (Datatypes.S m) k} {x : Fin m}
    (closure : MemberClosure sigma S d d')
    (argument : StorePossible sigma x S) :
    Coercion sigma (tau_open d (PVar x)) (tau_open d' (PVar x)).
Proof.
  destruct closure.
  pose (extended := environment_snoc e argument).
  pose (compiled := tau_sub_compile extended t).
  rewrite <- !tau_rename_ext_openAt in compiled.
  rewrite !tau_rename_openAt_eq_open_var in compiled.
  exact compiled.
Defined.

(** Secondary structural size for coercion action. *)
Equations coercion_tree_size {m : nat} {sigma : Store m} {k : Kind}
    {d1 d2 : Tau m k} (coercion : Coercion sigma d1 d2) : nat
    by struct coercion :=
coercion_tree_size (Coercion_trans first second) :=
  coercion_tree_size first + coercion_tree_size second + 1;
coercion_tree_size (Coercion_sel_lo resolution lower) :=
  coercion_tree_size lower + 1;
coercion_tree_size (Coercion_sel_hi resolution upper) :=
  coercion_tree_size upper + 1;
coercion_tree_size (Coercion_fun domain codomain) :=
  coercion_tree_size domain + 1;
coercion_tree_size (Coercion_pair first member) :=
  coercion_tree_size first + 1;
coercion_tree_size (Coercion_bounds lower upper) :=
  coercion_tree_size lower + coercion_tree_size upper + 1;
coercion_tree_size _ := 1.

Definition coercion_action_order : (nat * nat) -> (nat * nat) -> Prop :=
  Relation_Operators.slexprod nat nat lt lt.

Lemma coercion_action_order_wf : well_founded coercion_action_order.
Proof.
  unfold coercion_action_order. apply wf_slexprod; apply lt_wf.
Qed.

#[global] Instance coercion_action_order_well_founded :
    WellFounded coercion_action_order := coercion_action_order_wf.

Definition coercion_bot_action {m : nat} {sigma : Store m} {T : Ty m}
    {referent : PathReferent m}
    (realizes : ReferentRealizes sigma referent (TauTy TyBot)) :
    ReferentRealizes sigma referent (TauTy T).
Proof. dependent elimination realizes. dependent elimination s. Defined.

Definition coercion_top_action {m : nat} {sigma : Store m} {T : Ty m}
    {referent : PathReferent m}
    (realizes : ReferentRealizes sigma referent (TauTy T)) :
    ReferentRealizes sigma referent (TauTy TyTop).
Proof. dependent elimination realizes. exact (Realizes_loc Possible_top). Defined.

Definition coercion_widen_action {m : nat} {sigma : Store m}
    {p : Path m} {x : Fin m} {T : Ty m} {referent : PathReferent m}
    (resolution : PathResolve p sigma (RefLoc x))
    (target : StorePossible sigma x T)
    (realizes : ReferentRealizes sigma referent (TauTy (TySingle p))) :
    ReferentRealizes sigma referent (TauTy T).
Proof.
  dependent elimination realizes. dependent elimination s.
  pose proof (path_resolve_deterministic p1 resolution) as equality.
  dependent elimination equality. exact (Realizes_loc target).
Defined.

Definition coercion_alias_action {m : nat} {sigma : Store m}
    {p q : Path m} {x : Fin m} {referent : PathReferent m}
    (target_resolution : PathResolve p sigma (RefLoc x))
    (source_resolution : PathResolve q sigma (RefLoc x))
    (realizes : ReferentRealizes sigma referent
      (TauTy (TySingle q))) :
    ReferentRealizes sigma referent (TauTy (TySingle p)).
Proof.
  dependent elimination realizes. dependent elimination s.
  pose proof (path_resolve_deterministic p1 source_resolution) as equality.
  dependent elimination equality.
  exact (Realizes_loc (Possible_single target_resolution)).
Defined.

Definition coercion_sel_lo_finish {m : nat} {sigma : Store m}
    {p : Path m} {a : Name} {W : Ty m} {referent : PathReferent m}
    (resolution : PathResolve (PSel p a) sigma (RefType W))
    (witness : ReferentRealizes sigma referent (TauTy W)) :
    ReferentRealizes sigma referent (TauTy (TyTSel p a)).
Proof.
  dependent elimination witness.
  exact (Realizes_loc (Possible_selection resolution s)).
Defined.

Definition coercion_sel_hi_source {m : nat} {sigma : Store m}
    {p : Path m} {a : Name} {W : Ty m} {referent : PathReferent m}
    (resolution : PathResolve (PSel p a) sigma (RefType W))
    (realizes : ReferentRealizes sigma referent
      (TauTy (TyTSel p a))) :
    ReferentRealizes sigma referent (TauTy W).
Proof.
  dependent elimination realizes. dependent elimination s.
  pose proof (path_resolve_deterministic p3 resolution) as equality.
  dependent elimination equality. exact (Realizes_loc s2).
Defined.

Definition coercion_fun_action {m : nat} {sigma : Store m}
    {S S' : Ty m} {T T' : Ty (Datatypes.S m)}
    {referent : PathReferent m}
    (domain : Coercion sigma (TauTy S') (TauTy S))
    (codomain : DeferredCoercion sigma S' T T')
    (realizes : ReferentRealizes sigma referent
      (TauTy (TyFun S T))) :
    ReferentRealizes sigma referent (TauTy (TyFun S' T')).
Proof.
  dependent elimination realizes. dependent elimination s.
  exact (Realizes_loc (Possible_fun s b
    (Coercion_trans domain c)
    (Deferred_trans (Deferred_narrow domain d) codomain))).
Defined.

Definition coercion_bounds_action {m : nat} {sigma : Store m}
    {S S' T T' : Ty m} {referent : PathReferent m}
    (lower : Coercion sigma (TauTy S') (TauTy S))
    (upper : Coercion sigma (TauTy T) (TauTy T'))
    (realizes : ReferentRealizes sigma referent (TauIntv S T)) :
    ReferentRealizes sigma referent (TauIntv S' T').
Proof.
  dependent elimination realizes.
  exact (Realizes_type (Coercion_trans lower c)
    (Coercion_trans c0 upper)).
Defined.

Definition referent_realizes_location {m : nat} {sigma : Store m}
    {x : Fin m} {T : Ty m}
    (realizes : ReferentRealizes sigma (RefLoc x) (TauTy T)) :
    StorePossible sigma x T.
Proof. dependent elimination realizes. exact s. Defined.

(** Execute a finite coercion on generalized referent realization. *)
Equations coercion_action {m : nat} {sigma : Store m} {k : Kind}
    {d1 d2 : Tau m k} {referent : PathReferent m}
    (coercion : Coercion sigma d1 d2)
    (realizes : ReferentRealizes sigma referent d1) :
    ReferentRealizes sigma referent d2
    by wf (referent_stratum referent, coercion_tree_size coercion)
      coercion_action_order :=
coercion_action Coercion_refl realizes := realizes;
coercion_action (Coercion_trans first second) realizes :=
  coercion_action second (coercion_action first realizes);
coercion_action (Coercion_runtime conversion) realizes :=
  referent_realizes_convert realizes conversion;
coercion_action Coercion_bot realizes := coercion_bot_action realizes;
coercion_action Coercion_top realizes := coercion_top_action realizes;
coercion_action (Coercion_widen resolution target) realizes :=
  coercion_widen_action resolution target realizes;
coercion_action
    (Coercion_alias target_resolution source_resolution) realizes :=
  coercion_alias_action target_resolution source_resolution realizes;
coercion_action (Coercion_sel_lo resolution lower) realizes :=
  coercion_sel_lo_finish resolution (coercion_action lower realizes);
coercion_action (Coercion_sel_hi resolution upper) realizes :=
  coercion_action upper (coercion_sel_hi_source resolution realizes);
coercion_action (Coercion_fun domain codomain) realizes :=
  coercion_fun_action domain codomain realizes;
coercion_action (Coercion_pair first_code member_closure)
    (Realizes_loc (Possible_pair binding first member)) :=
  Realizes_loc (Possible_pair binding
    (referent_realizes_location
      (coercion_action first_code (Realizes_loc first)))
    (coercion_action
      (member_closure_instantiate member_closure first) member));
coercion_action (Coercion_bounds lower upper) realizes :=
  coercion_bounds_action lower upper realizes.

Ltac solve_coercion_action_decrease :=
  unfold coercion_action_order;
  first
    [ apply Relation_Operators.right_slex;
      simp coercion_tree_size; lia
    | apply Relation_Operators.left_slex;
      eauto using store_binds_pair_first_stratum_lt,
        store_binds_pair_referent_stratum_lt ].

Next Obligation.
  unfold coercion_action_order. apply Relation_Operators.right_slex.
  rewrite coercion_tree_size_equation_2. lia.
Qed.
Next Obligation.
  unfold coercion_action_order. apply Relation_Operators.right_slex.
  rewrite coercion_tree_size_equation_2. lia.
Qed.
Next Obligation.
  unfold coercion_action_order. apply Relation_Operators.right_slex.
  rewrite coercion_tree_size_equation_8. lia.
Qed.
Next Obligation.
  unfold coercion_action_order. apply Relation_Operators.right_slex.
  rewrite coercion_tree_size_equation_9. lia.
Qed.
Next Obligation.
  unfold coercion_action_order. apply Relation_Operators.left_slex.
  exact (store_binds_pair_first_stratum_lt binding).
Qed.
Next Obligation.
  unfold coercion_action_order. apply Relation_Operators.left_slex.
  exact (store_binds_pair_referent_stratum_lt binding).
Qed.

(** Proper-type specialization of coercion action. *)
Definition coercion_action_possible {m : nat} {sigma : Store m}
    {x : Fin m} {S T : Ty m}
    (coercion : Coercion sigma (TauTy S) (TauTy T))
    (possible : StorePossible sigma x S) : StorePossible sigma x T :=
  referent_realizes_location
    (coercion_action coercion (Realizes_loc possible)).

(** Supply the concrete argument of a deferred codomain coercion. *)
Equations deferred_coercion_instantiate {m : nat} {sigma : Store m}
    {S : Ty m} {T U : Ty (Datatypes.S m)} {x : Fin m}
    (deferred : DeferredCoercion sigma S T U)
    (argument : StorePossible sigma x S) :
    Coercion sigma (TauTy (ty_open T (PVar x)))
      (TauTy (ty_open U (PVar x))) by struct deferred :=
deferred_coercion_instantiate Deferred_refl argument := Coercion_refl;
deferred_coercion_instantiate (Deferred_trans first second) argument :=
  Coercion_trans
    (deferred_coercion_instantiate first argument)
    (deferred_coercion_instantiate second argument);
deferred_coercion_instantiate (Deferred_runtime conversion) argument :=
  Coercion_runtime (tau_runtime_conv_open_same
    (path_runtime_eq_congruence sigma) conversion (PVar x));
deferred_coercion_instantiate (Deferred_narrow domain deferred) argument :=
  deferred_coercion_instantiate deferred
    (coercion_action_possible domain argument);
deferred_coercion_instantiate
    (Deferred_source environment code) argument :=
  member_closure_instantiate (Member_source environment code) argument.

Print Assumptions path_ty_resolve.
Print Assumptions tau_sub_compile.
Print Assumptions coercion_action.
Print Assumptions deferred_coercion_instantiate.
