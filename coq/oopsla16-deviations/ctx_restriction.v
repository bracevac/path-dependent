(** Contexts: the Lean port's restriction changes no judgment (DEV item 8), and
    the fact the Lean port's [Htp] indexing relies on (DEV item 4).

    The Lean port represents a context as [Ctx σ s] (Oopsla16/Context.lean): the
    entry for a variable lives in the scope of that variable and the older ones.
    In the reference's terms, the entry at position [x] of [GH] is
    [closed (S x) (length G1) 0].  The reference's [tenv] (dot.v:70) is any
    list of types, so the Lean port has fewer contexts.  [ctx_ok] below is that
    restriction written in the reference's own definitions; that it is the
    exact Coq image of Lean's [Ctx] is argued, not proved (the two systems
    cannot be related formally).

    [has_type_r], [dms_has_type_r], [stp_r] and [htp_r] are the reference's four
    judgments (dot.v:219-393) with a single premise [ctx_ok GH G1] added as the
    first premise of each of the 32 rules, so that every context occurring in
    a restricted derivation is a [ctx_ok] context.  Apart from that line and
    the [_r] suffix on the judgment and rule names, the block is identical to
    dot.v:219-393, line for line; [check_block.sh] checks this.

    Main results:
    - [restriction_harmless]: from a [ctx_ok] context, the reference's rules
      and the restricted rules derive exactly the same judgments, at the same
      size index.  [restriction_harmless_empty] is the case of the empty
      context, the one [type_safety] (dot_soundness.v:1131) uses.
    - [ctx_restriction_is_real]: the restriction is a real one: outside
      [ctx_ok] the reference derives judgments the restricted family cannot.
    - [htp_closed_Sx]: every type [htp] assigns to [x] is closed at [S x]. *)
Require Import dot_spec.
Require Import regularity.
Require Import Lia.

(** The Lean port's context shape: the entry at [x] mentions only abstract
    variables [0 .. x], only allocated locations, and no dangling [TVarB]. *)
Definition ctx_ok (GH: tenv) (G1: venv) :=
  forall x T, index x GH = Some T -> closed (S x) (length G1) 0 T.

(** The reference's four judgments (dot.v:219-393), each rule with the extra
    first premise [ctx_ok GH G1]. *)
Inductive has_type_r : tenv -> venv -> tm -> ty -> nat -> Prop :=
  | T_Vary_r : forall GH G1 x ds ds' T T' n1,
    ctx_ok GH G1 ->
      index x G1 = Some (vobj ds) ->
      dms_has_type_r [T'] G1 ds' T' n1 ->
      subst_dms x ds' = ds ->
      substt x T' = T ->
      closed 0 (length G1) 0 T ->
      has_type_r GH G1 (tvar true x) T (S n1)
  | T_Varz_r : forall G1 GH x T n1,
    ctx_ok GH G1 ->
      index x GH = Some T ->
      closed (length GH) (length G1) 0 T ->
      has_type_r GH G1 (tvar false x) T (S n1)
  | T_VarPack_r : forall GH G1 b x T1 T1' n1,
    ctx_ok GH G1 ->
      has_type_r GH G1 (tvar b x) T1' n1 ->
      T1' = (open 0 (TVar b x) T1) ->
      closed (length GH) (length G1) 1 T1 ->
      has_type_r GH G1 (tvar b x) (TBind T1) (S n1)
  | T_VarUnpack_r : forall GH G1 b x T1 T1' n1,
    ctx_ok GH G1 ->
      has_type_r GH G1 (tvar b x) (TBind T1) n1 ->
      T1' = (open 0 (TVar b x) T1) ->
      closed (length GH) (length G1) 0 T1' ->
      has_type_r GH G1 (tvar b x) T1' (S n1)
  | T_Obj_r : forall GH G1 ds T T' n1,
    ctx_ok GH G1 ->
      dms_has_type_r (T'::GH) G1 ds T' n1 ->
      T' = open 0 (TVar false (length GH)) T ->
      closed (length GH) (length G1) 1 T ->
      has_type_r GH G1 (tobj ds) (TBind T) (S n1)
  | T_App_r : forall l T1 T2 GH G1 t1 t2 n1 n2,
    ctx_ok GH G1 ->
      has_type_r GH G1 t1 (TFun l T1 T2) n1 ->
      has_type_r GH G1 t2 T1 n2 ->
      closed (length GH) (length G1) 0 T2 ->
      has_type_r GH G1 (tapp t1 l t2) T2 (S (n1+n2))
  | T_AppVar_r : forall l T1 T2 T2' GH G1 t1 b2 x2 n1 n2,
    ctx_ok GH G1 ->
      has_type_r GH G1 t1 (TFun l T1 T2) n1 ->
      has_type_r GH G1 (tvar b2 x2) T1 n2 ->
      T2' = (open 0 (TVar b2 x2) T2) ->
      closed (length GH) (length G1) 0 T2' ->
      has_type_r GH G1 (tapp t1 l (tvar b2 x2)) T2' (S (n1+n2))
  | T_Sub_r : forall GH G1 t T1 T2 n1 n2,
    ctx_ok GH G1 ->
      has_type_r GH G1 t T1 n1 ->
      stp_r GH G1 T1 T2 n2 ->
      has_type_r GH G1 t T2 (S (n1 + n2))

(* : -- member initialization *)
with dms_has_type_r: tenv -> venv -> dms -> ty -> nat -> Prop :=
  | D_Nil_r : forall GH G1 n1,
    ctx_ok GH G1 ->
      dms_has_type_r GH G1 dnil TTop (S n1)
  | D_Typ_r : forall GH G1 l T11 ds TS T n1,
    ctx_ok GH G1 ->
      dms_has_type_r GH G1 ds TS n1 ->
      closed (length GH) (length G1) 0 T11 ->
      l = length (dms_to_list ds) ->
      T = TAnd (TTyp l T11 T11) TS ->
      dms_has_type_r GH G1 (dcons (dty T11) ds) T (S n1)
  | D_Fun_r : forall GH G1 l OT11 T11 OT12 T12 T12' t12 ds TS T n1 n2,
    ctx_ok GH G1 ->
      dms_has_type_r GH G1 ds TS n1 ->
      has_type_r (T11::GH) G1 t12 T12' n2 ->
      T12' = (open 0 (TVar false (length GH)) T12) ->
      closed (length GH) (length G1) 0 T11 ->
      closed (length GH) (length G1) 1 T12 ->
      l = length (dms_to_list ds) ->
      T = TAnd (TFun l T11 T12) TS ->
      eq_some OT11 T11 ->
      eq_some OT12 T12 ->
      dms_has_type_r GH G1 (dcons (dfun OT11 OT12 t12) ds) T (S (n1+n2))

(* <: -- subtyping *)
with stp_r: tenv -> venv -> ty -> ty -> nat -> Prop :=
| stp_bot_r: forall GH G1 T n1,
    ctx_ok GH G1 ->
    closed (length GH) (length G1) 0  T ->
    stp_r GH G1 TBot T (S n1)
| stp_top_r: forall GH G1 T n1,
    ctx_ok GH G1 ->
    closed (length GH) (length G1) 0 T ->
    stp_r GH G1 T  TTop (S n1)
| stp_fun_r: forall GH G1 l T1 T2 T3 T4 T2' T4' n1 n2,
    ctx_ok GH G1 ->
    T2' = (open 0 (TVar false (length GH)) T2) ->
    T4' = (open 0 (TVar false (length GH)) T4) ->
    closed (length GH) (length G1) 1 T2 ->
    closed (length GH) (length G1) 1 T4 ->
    stp_r GH G1 T3 T1 n1 ->
    stp_r (T3::GH) G1 T2' T4' n2 ->
    stp_r GH G1 (TFun l T1 T2) (TFun l T3 T4) (S (n1+n2))
| stp_typ_r: forall GH G1 l T1 T2 T3 T4 n1 n2,
    ctx_ok GH G1 ->
    stp_r GH G1 T3 T1 n2 ->
    stp_r GH G1 T2 T4 n1 ->
    stp_r GH G1 (TTyp l T1 T2) (TTyp l T3 T4) (S (n1+n2))

| stp_strong_sel1_r: forall GH G1 l T2 ds TX x n1,
    ctx_ok GH G1 ->
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    stp_r [] G1 TX T2 n1 ->
    stp_r GH G1 (TSel (TVar true x) l) T2 (S n1)
| stp_strong_sel2_r: forall GH G1 l T1 ds TX x n1,
    ctx_ok GH G1 ->
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    stp_r [] G1 T1 TX n1 ->
    stp_r GH G1 T1 (TSel (TVar true x) l) (S n1)

| stp_sel1_r: forall GH G1 l T2 x n1,
    ctx_ok GH G1 ->
    htp_r  GH G1 x (TTyp l TBot T2) n1 ->
    stp_r GH G1 (TSel (TVar false x) l) T2 (S n1)

| stp_sel2_r: forall GH G1 l T1 x n1,
    ctx_ok GH G1 ->
    htp_r  GH G1 x (TTyp l T1 TTop) n1 ->
    stp_r GH G1 T1 (TSel (TVar false x) l) (S n1)

| stp_selx_r: forall GH G1 l p1 n1,
    ctx_ok GH G1 ->
    vr_closed (length GH) (length G1) 0 p1 ->
    stp_r GH G1 (TSel p1 l) (TSel p1 l) (S n1)

| stp_bind1_r: forall GH G1 T1 T1' T2 n1,
    ctx_ok GH G1 ->
    stp_r (T1'::GH) G1 T1' T2 n1 ->
    T1' = (open 0 (TVar false (length GH)) T1) ->
    closed (length GH) (length G1) 1 T1 ->
    closed (length GH) (length G1) 0 T2 ->
    stp_r GH G1 (TBind T1) T2 (S n1)

| stp_bindx_r: forall GH G1 T1 T1' T2 T2' n1,
    ctx_ok GH G1 ->
    stp_r (T1'::GH) G1 T1' T2' n1 ->
    T1' = (open 0 (TVar false (length GH)) T1) ->
    T2' = (open 0 (TVar false (length GH)) T2) ->
    closed (length GH) (length G1) 1 T1 ->
    closed (length GH) (length G1) 1 T2 ->
    stp_r GH G1 (TBind T1) (TBind T2) (S n1)

| stp_and11_r: forall GH G1 T1 T2 T n1,
    ctx_ok GH G1 ->
    stp_r GH G1 T1 T n1 ->
    closed (length GH) (length G1) 0 T2 ->
    stp_r GH G1 (TAnd T1 T2) T (S n1)
| stp_and12_r: forall GH G1 T1 T2 T n1,
    ctx_ok GH G1 ->
    stp_r GH G1 T2 T n1 ->
    closed (length GH) (length G1) 0 T1 ->
    stp_r GH G1 (TAnd T1 T2) T (S n1)
| stp_and2_r: forall GH G1 T1 T2 T n1 n2,
    ctx_ok GH G1 ->
    stp_r GH G1 T T1 n1 ->
    stp_r GH G1 T T2 n2 ->
    stp_r GH G1 T (TAnd T1 T2) (S (n1+n2))

| stp_or21_r: forall GH G1 T1 T2 T n1,
    ctx_ok GH G1 ->
    stp_r GH G1 T T1 n1 ->
    closed (length GH) (length G1) 0 T2 ->
    stp_r GH G1 T (TOr T1 T2) (S n1)
| stp_or22_r: forall GH G1 T1 T2 T n1,
    ctx_ok GH G1 ->
    stp_r GH G1 T T2 n1 ->
    closed (length GH) (length G1) 0 T1 ->
    stp_r GH G1 T (TOr T1 T2) (S n1)
| stp_or1_r: forall GH G1 T1 T2 T n1 n2,
    ctx_ok GH G1 ->
    stp_r GH G1 T1 T n1 ->
    stp_r GH G1 T2 T n2 ->
    stp_r GH G1 (TOr T1 T2) T (S (n1+n2))

| stp_trans_r: forall GH G1 T1 T2 T3 n1 n2,
    ctx_ok GH G1 ->
    stp_r GH G1 T1 T2 n1 ->
    stp_r GH G1 T2 T3 n2 ->
    stp_r GH G1 T1 T3 (S (n1+n2))

(* :! -- typing for type selection in subtyping *)
with htp_r: tenv -> venv -> id -> ty -> nat -> Prop :=
| htp_var_r: forall GH G1 x TX n1,
    ctx_ok GH G1 ->
    index x GH = Some TX ->
    closed (S x) (length G1) 0 TX ->
    htp_r GH G1 x TX (S n1)
| htp_unpack_r: forall GH G1 x TX n1,
    ctx_ok GH G1 ->
    htp_r GH G1 x (TBind TX) n1 ->
    closed (S x) (length G1) 1 TX ->
    htp_r GH G1 x (open 0 (TVar false x) TX) (S n1)
| htp_sub_r: forall GH GU GL G1 x T1 T2 n1 n2,
    ctx_ok GH G1 ->
    (* use restricted GH. note: this is slightly different
    from the big-step version b/c here we do not distinguish
    if variables are bound in terms vs types. it would be easy
    to do exactly the same thing by adding this distinction. *)
    htp_r GH G1 x T1 n1 ->
    stp_r GL G1 T1 T2 n2 ->
    length GL = S x ->
    GH = GU ++ GL ->
    htp_r GH G1 x T2 (S (n1+n2)).


(** Structural facts about [ctx_ok]. *)

Lemma ctx_ok_nil: forall G1, ctx_ok [] G1.
Proof. unfold ctx_ok. intros. inversion H. Qed.

Lemma ctx_ok_cons: forall GH G1 T,
  ctx_ok GH G1 -> closed (S (length GH)) (length G1) 0 T -> ctx_ok (T::GH) G1.
Proof.
  unfold ctx_ok. intros GH G1 T H C x T0 E. simpl in E.
  destruct (beq_nat x (length GH)) eqn:B.
  - apply beq_nat_true_iff in B. subst. inversion E. subst. assumption.
  - apply H. assumption.
Qed.

Lemma ctx_ok_suffix: forall GU GL G1, ctx_ok (GU ++ GL) G1 -> ctx_ok GL G1.
Proof. unfold ctx_ok. intros. apply H. apply index_extend_mult. assumption. Qed.

Lemma open_closed_S: forall (GH: tenv) (G1: venv) T,
  closed (length GH) (length G1) 1 T ->
  closed (S (length GH)) (length G1) 0 (open 0 (TVar false (length GH)) T).
Proof.
  intros. eapply closed_open. simpl. eapply closed_upgrade_gh. eassumption. lia.
  econstructor. lia.
Qed.

(** Not proved in the reference: the type [htp] assigns to [x] mentions only
    [x] and older abstract variables, i.e. it is closed at [S x].  The
    reference proves only the weaker [closed (length GH) ...] ([htp_closed],
    dot.v:781) and [x < length GH] ([htp_closed1], dot.v:786); both are in
    [regularity.v].  The Lean port types [Htp] in the prefix scope of [x]
    (Oopsla16/Typing.lean, [Ty σ (scopeUpTo x)]), which can express the
    reference's [htp] conclusions only because of this fact.  It holds for
    every context, [ctx_ok] or not. *)
Lemma htp_closed_Sx: forall GH G1 x T n,
  htp GH G1 x T n -> closed (S x) (length G1) 0 T.
Proof.
  intros. induction H.
  - assumption.
  - eapply closed_open. simpl. assumption. econstructor. lia.
  - rewrite <- H1. eapply stp_closed2. eassumption.
Qed.

(** The equivalence.  Both directions are proved by induction on the size
    index, re-applying the same rule; the forward direction also shows that
    every context in the premises of a rule is again [ctx_ok]. *)

Ltac solve_ctx :=
  first
  [ eassumption
  | apply ctx_ok_nil
  | (eapply ctx_ok_suffix; eassumption)
  | (apply ctx_ok_cons;
      [ first [ eassumption | apply ctx_ok_nil ]
      | first [ (eapply open_closed_S; eassumption)
              | (eapply closed_upgrade_gh; [eassumption | simpl; lia])
              | (eapply closed_upgrade_gh; [eapply stp_closed1; eassumption | simpl; lia])
              | (eapply closed_upgrade_gh; [eapply dms_has_type_closed; eassumption | simpl; lia]) ] ]) ].

Ltac prem_fwd IHS IHH IHT IHD :=
  match goal with
  | |- ctx_ok _ _ => solve_ctx
  | H: stp _ _ _ _ _ |- stp_r _ _ _ _ _ => eapply IHS; [exact H | lia | solve_ctx]
  | H: htp _ _ _ _ _ |- htp_r _ _ _ _ _ => eapply IHH; [exact H | lia | solve_ctx]
  | H: has_type _ _ _ _ _ |- has_type_r _ _ _ _ _ => eapply IHT; [exact H | lia | solve_ctx]
  | H: dms_has_type _ _ _ _ _ |- dms_has_type_r _ _ _ _ _ => eapply IHD; [exact H | lia | solve_ctx]
  | |- _ => solve [ eassumption | reflexivity ]
  end.

Ltac rcon_fwd IHS IHH IHT IHD :=
  let fin := repeat (prem_fwd IHS IHH IHT IHD) in
  first
  [ solve [eapply stp_bot_r; fin] | solve [eapply stp_top_r; fin]
  | solve [eapply stp_fun_r; fin] | solve [eapply stp_typ_r; fin]
  | solve [eapply stp_strong_sel1_r; fin] | solve [eapply stp_strong_sel2_r; fin]
  | solve [eapply stp_sel1_r; fin] | solve [eapply stp_sel2_r; fin]
  | solve [eapply stp_selx_r; fin] | solve [eapply stp_bind1_r; fin]
  | solve [eapply stp_bindx_r; fin] | solve [eapply stp_and11_r; fin]
  | solve [eapply stp_and12_r; fin] | solve [eapply stp_and2_r; fin]
  | solve [eapply stp_or21_r; fin] | solve [eapply stp_or22_r; fin]
  | solve [eapply stp_or1_r; fin] | solve [eapply stp_trans_r; fin]
  | solve [eapply htp_var_r; fin] | solve [eapply htp_unpack_r; fin]
  | solve [eapply htp_sub_r; fin]
  | solve [eapply T_Vary_r; fin] | solve [eapply T_Varz_r; fin]
  | solve [eapply T_VarPack_r; fin] | solve [eapply T_VarUnpack_r; fin]
  | solve [eapply T_Obj_r; fin] | solve [eapply T_App_r; fin]
  | solve [eapply T_AppVar_r; fin] | solve [eapply T_Sub_r; fin]
  | solve [eapply D_Nil_r; fin] | solve [eapply D_Typ_r; fin]
  | solve [eapply D_Fun_r; fin] ].

(** From a [ctx_ok] context, every derivation of the reference is a derivation
    of the restricted family, at the same index. *)
Lemma all_restrict: forall ni,
  (forall GH G1 T1 T2 n, stp GH G1 T1 T2 n -> n < ni -> ctx_ok GH G1 -> stp_r GH G1 T1 T2 n) /\
  (forall GH G1 x T n, htp GH G1 x T n -> n < ni -> ctx_ok GH G1 -> htp_r GH G1 x T n) /\
  (forall GH G1 t T n, has_type GH G1 t T n -> n < ni -> ctx_ok GH G1 -> has_type_r GH G1 t T n) /\
  (forall GH G1 ds T n, dms_has_type GH G1 ds T n -> n < ni -> ctx_ok GH G1 -> dms_has_type_r GH G1 ds T n).
Proof.
  intros ni. induction ni. repeat split; intros; lia.
  destruct IHni as [IHS [IHH [IHT IHD]]].
  repeat split; intros; inversion H; subst; clear H; rcon_fwd IHS IHH IHT IHD.
Qed.

Ltac prem_bwd IHS IHH IHT IHD :=
  match goal with
  | H: stp_r _ _ _ _ _ |- stp _ _ _ _ _ => eapply IHS; [exact H | lia]
  | H: htp_r _ _ _ _ _ |- htp _ _ _ _ _ => eapply IHH; [exact H | lia]
  | H: has_type_r _ _ _ _ _ |- has_type _ _ _ _ _ => eapply IHT; [exact H | lia]
  | H: dms_has_type_r _ _ _ _ _ |- dms_has_type _ _ _ _ _ => eapply IHD; [exact H | lia]
  | |- _ => solve [ eassumption | reflexivity ]
  end.

Ltac rcon_bwd IHS IHH IHT IHD :=
  let fin := repeat (prem_bwd IHS IHH IHT IHD) in
  first
  [ solve [eapply stp_bot; fin] | solve [eapply stp_top; fin]
  | solve [eapply stp_fun; fin] | solve [eapply stp_typ; fin]
  | solve [eapply stp_strong_sel1; fin] | solve [eapply stp_strong_sel2; fin]
  | solve [eapply stp_sel1; fin] | solve [eapply stp_sel2; fin]
  | solve [eapply stp_selx; fin] | solve [eapply stp_bind1; fin]
  | solve [eapply stp_bindx; fin] | solve [eapply stp_and11; fin]
  | solve [eapply stp_and12; fin] | solve [eapply stp_and2; fin]
  | solve [eapply stp_or21; fin] | solve [eapply stp_or22; fin]
  | solve [eapply stp_or1; fin] | solve [eapply stp_trans; fin]
  | solve [eapply htp_var; fin] | solve [eapply htp_unpack; fin]
  | solve [eapply htp_sub; fin]
  | solve [eapply T_Vary; fin] | solve [eapply T_Varz; fin]
  | solve [eapply T_VarPack; fin] | solve [eapply T_VarUnpack; fin]
  | solve [eapply T_Obj; fin] | solve [eapply T_App; fin]
  | solve [eapply T_AppVar; fin] | solve [eapply T_Sub; fin]
  | solve [eapply D_Nil; fin] | solve [eapply D_Typ; fin]
  | solve [eapply D_Fun; fin] ].

(** The restricted family is a subsystem of the reference. *)
Lemma all_unrestrict: forall ni,
  (forall GH G1 T1 T2 n, stp_r GH G1 T1 T2 n -> n < ni -> stp GH G1 T1 T2 n) /\
  (forall GH G1 x T n, htp_r GH G1 x T n -> n < ni -> htp GH G1 x T n) /\
  (forall GH G1 t T n, has_type_r GH G1 t T n -> n < ni -> has_type GH G1 t T n) /\
  (forall GH G1 ds T n, dms_has_type_r GH G1 ds T n -> n < ni -> dms_has_type GH G1 ds T n).
Proof.
  intros ni. induction ni. repeat split; intros; lia.
  destruct IHni as [IHS [IHH [IHT IHD]]].
  repeat split; intros; inversion H; subst; clear H; rcon_bwd IHS IHH IHT IHD.
Qed.

Theorem restriction_harmless: forall GH G1, ctx_ok GH G1 ->
  (forall T1 T2 n, stp GH G1 T1 T2 n <-> stp_r GH G1 T1 T2 n) /\
  (forall x T n, htp GH G1 x T n <-> htp_r GH G1 x T n) /\
  (forall t T n, has_type GH G1 t T n <-> has_type_r GH G1 t T n) /\
  (forall ds T n, dms_has_type GH G1 ds T n <-> dms_has_type_r GH G1 ds T n).
Proof.
  intros GH G1 OK.
  repeat split; intros D.
  - eapply (all_restrict (S n)); eauto.
  - eapply (all_unrestrict (S n)); eauto.
  - eapply (all_restrict (S n)); eauto.
  - eapply (all_unrestrict (S n)); eauto.
  - eapply (all_restrict (S n)); eauto.
  - eapply (all_unrestrict (S n)); eauto.
  - eapply (all_restrict (S n)); eauto.
  - eapply (all_unrestrict (S n)); eauto.
Qed.

Corollary restriction_harmless_empty: forall G1 t T n,
  has_type [] G1 t T n <-> has_type_r [] G1 t T n.
Proof. intros. eapply restriction_harmless. apply ctx_ok_nil. Qed.

(** The restriction is a real one.  In [GHbad] the entry of the oldest
    variable, 0, mentions the newer variable 1, so [GHbad] is not [ctx_ok] and
    no Lean [Ctx] has this shape.  The reference nevertheless derives a typing
    judgment in it: [T_Varz] (dot.v:227) checks only
    [closed (length GH) ...].  [htp_var] (dot.v:376) checks
    [closed (S x) ...] instead, and indeed no [htp] derivation at all gives
    variable 0 that type.  The last conjunct holds simply because every
    restricted rule has the premise [ctx_ok GH G1]: the restricted family
    derives nothing in a context outside [ctx_ok]. *)
Definition GHbad : tenv := [TTop; TSel (TVar false 1) 0].

Theorem ctx_restriction_is_real:
  ~ ctx_ok GHbad [] /\
  has_type GHbad [] (tvar false 0) (TSel (TVar false 1) 0) 1 /\
  (forall n, ~ htp GHbad [] 0 (TSel (TVar false 1) 0) n) /\
  (forall t T n, ~ has_type_r GHbad [] t T n).
Proof.
  assert (NOK: ~ ctx_ok GHbad []).
  { unfold ctx_ok, GHbad. intro H.
    specialize (H 0 (TSel (TVar false 1) 0) eq_refl).
    inversion H; subst. match goal with V: vr_closed _ _ _ _ |- _ => inversion V; lia end. }
  split; [exact NOK|]. split; [|split].
  - eapply T_Varz. reflexivity. repeat econstructor.
  - intros n D. apply htp_closed_Sx in D. inversion D; subst.
    match goal with V: vr_closed _ _ _ _ |- _ => inversion V; lia end.
  - intros t T n D. apply NOK. inversion D; assumption.
Qed.
