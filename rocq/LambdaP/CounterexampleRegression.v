From Stdlib Require Import Logic.Eqdep_dec.
From Equations Require Import Equations.
From PathDependent.LambdaP Require Import FinFun Syntax Context Typing
  Canonical.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Module CounterexampleRegression.

Definition label : Name := 0.

(** A pair type with an exact abstract member [A = Top]. *)
Definition qType0 : Ty 0 :=
  ty_pair ty_top label (Tau_weaken (tau_intv ty_top ty_top)).

Definition GammaQ : Ctx 1 := ctx_snoc ctx_nil qType0.
Definition q1 : Fin.t 1 := Fin.zero.
Definition qSelection1 : Path 1 := path_sel (path_var q1) label.
Definition argumentType1 : Ty 1 := ty_tsel (path_var q1) label.

(** The critical function-body context: [q] followed by [z : q.A]. *)
Definition GammaZ : Ctx 2 := ctx_snoc GammaQ argumentType1.
Definition z : Fin.t 2 := Fin.zero.
Definition q : Fin.t 2 := Fin.succ Fin.zero.
Definition qSelection : Path 2 := path_sel (path_var q) label.

Definition qType : Ty 2 := Ty_weaken (Ty_weaken qType0).
Definition argumentType : Ty 2 := Ty_weaken argumentType1.

Theorem argumentType_eq :
    argumentType = ty_tsel (path_var q) label.
Proof. reflexivity. Qed.

Theorem z_binding : Ctx_Binds GammaZ z argumentType.
Proof. apply binds_here. Qed.

Theorem q_binding : Ctx_Binds GammaZ q qType.
Proof. apply binds_there. apply binds_here. Qed.

Theorem q_selection_typing :
    Path_Ty GammaZ qSelection (tau_intv ty_top ty_top).
Proof.
  pose proof (path_ty_var GammaZ q qType q_binding) as Hroot.
  pose proof (@path_ty_sel_r 2 iota GammaZ (path_var q)
    _ _ _ Hroot) as Hsel.
  unfold qSelection, qType, qType0 in Hsel.
  cbn [Ty_weaken Ty_rename Tau_weaken Tau_rename Path_weaken
    Path_rename] in Hsel.
  exact Hsel.
Qed.

(** Shape interpretation parameterized by the observable singleton paths. *)
Definition TypeMarked {n : nat} (M : Path n -> Prop) (T : Ty n) : Prop :=
  match T in Ty n' return (Path n' -> Prop) -> Prop with
  | ty_top => fun _ => True
  | ty_bot => fun _ => False
  | ty_fun _ _ => fun _ => True
  | ty_pair _ _ _ => fun _ => True
  | ty_single p => fun M' => M' p
  | ty_tsel _ _ => fun _ => True
  end M.

Definition SignatureMarked {n : nat} {k : Kind}
    (M : Path n -> Prop) (d : Tau n k) : Prop :=
  match d in Tau n' _ return (Path n' -> Prop) -> Prop with
  | tau_ty T => fun M' => TypeMarked M' T
  | tau_intv _ _ => fun _ => True
  end M.

Definition ProperResultsMarked {n : nat}
    (G : Ctx n) (M : Path n -> Prop) : Prop :=
  forall (p : Path n) (T : Ty n),
    Path_Ty G p (tau_ty T) -> M p -> TypeMarked M T.

Definition SingletonAliasesMarked {n : nat}
    (G : Ctx n) (M : Path n -> Prop) : Prop :=
  forall (p r : Path n),
    Path_Ty G p (tau_ty (ty_single r)) -> M r -> M p.

Definition IntervalUppersMarked {n : nat}
    (G : Ctx n) (M : Path n -> Prop) : Prop :=
  forall (p : Path n) (L U : Ty n),
    Path_Ty G p (tau_intv L U) -> TypeMarked M U.

(** Every current subtyping rule preserves the interpretation, including
    primitive transitivity. *)
Theorem sub_preserves_mark {n : nat} {G : Ctx n}
    {M : Path n -> Prop} {k : Kind} {d1 d2 : Tau n k}
    (Hresults : ProperResultsMarked G M)
    (Halias : SingletonAliasesMarked G M)
    (Huppers : IntervalUppersMarked G M)
    (H : Tau_Sub G d1 d2) :
    SignatureMarked M d1 -> SignatureMarked M d2.
Proof.
  induction H; intro Hmark; cbn [SignatureMarked TypeMarked] in *.
  - exact Hmark.
  - exact (IHTau_Sub2 M Hresults Halias Huppers
      (IHTau_Sub1 M Hresults Halias Huppers Hmark)).
  - contradiction.
  - exact I.
  - exact (Hresults _ _ H Hmark).
  - exact (Halias _ _ H Hmark).
  - exact (Huppers _ _ _ H).
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
Qed.

(** Complete classification of paths in the critical context. *)
Inductive KnownPathTy : forall {k : Kind}, Path 2 -> Tau 2 k -> Prop :=
| known_path_z : KnownPathTy (path_var z) (tau_ty argumentType)
| known_path_q : KnownPathTy (path_var q) (tau_ty qType)
| known_path_q_fst :
    KnownPathTy (path_fst (path_var q)) (tau_ty ty_top)
| known_path_q_sel :
    KnownPathTy qSelection (tau_intv ty_top ty_top).

Ltac unpack_same_nat_index :=
  lazymatch goal with
  | E : @existT nat ?P ?n ?x = @existT nat ?P ?n ?y |- _ =>
      let Exy := fresh "Eindex" in
      assert (Exy : x = y) by exact (PackedNat_same_index_inj E);
      clear E;
      first [is_var x; subst x | is_var y; subst y | idtac]
  end.

Ltac unpack_ty_index :=
  match goal with
  | E : @existT nat ?P ?scope_idx ?x =
      @existT nat ?P ?scope_idx ?y |- _ =>
      lazymatch type of x with
      | Ty ?ty_scope =>
          let Exy := fresh "Etype" in
          assert (Exy : x = y) by exact (PackedNat_same_index_inj E);
          clear E;
          first [is_var x; subst x | is_var y; subst y]
      end
  end.

Ltac unpack_kind_index :=
  match goal with
  | E : @existT Kind ?P ?kind_idx ?x =
      @existT Kind ?P ?kind_idx ?y |- _ =>
      lazymatch type of x with
      | Tau ?scope ?member_kind =>
          let Exy := fresh "Emember" in
          assert (Exy : x = y) by
            exact (inj_pair2_eq_dec Kind Kind_eq_dec
              P kind_idx x y E);
          clear E;
          first [is_var x; subst x | is_var y; subst y]
      end
  end.

Theorem path_typing_known {k : Kind} {p : Path 2} {d : Tau 2 k}
    (H : Path_Ty GammaZ p d) : KnownPathTy p d.
Proof.
  revert k p d H.
  fix IH 4.
  intros k p d H.
  dependent elimination H.
  - lazymatch goal with
    | Hb : Ctx_Binds GammaZ ?x ?T |-
        KnownPathTy (path_var ?x) (tau_ty ?T) =>
      refine (@Fin.cases' 1 x
        (fun x => Ctx_Binds GammaZ x T ->
          KnownPathTy (path_var x) (tau_ty T)) _ _ Hb)
    end.
    + intro Hb.
      assert (T = argumentType) as -> by
        (eapply Ctx_Binds_unique; [exact Hb | exact z_binding]).
      apply known_path_z.
    + intros y Hy.
      refine (@Fin.cases' 0 y
        (fun y => Ctx_Binds GammaZ (Fin.succ y) T ->
          KnownPathTy (path_var (Fin.succ y)) (tau_ty T)) _ _ Hy).
      * intro Hq.
        assert (T = qType) as -> by
          (eapply Ctx_Binds_unique; [exact Hq | exact q_binding]).
        apply known_path_q.
      * intros impossible. exact (Fin.elim0 impossible).
  - lazymatch goal with
    | Hp : Path_Ty GammaZ ?r ?member |- _ =>
        pose proof (IH _ _ _ Hp) as Hknown
    end.
    inversion Hknown. unpack_ty_index. apply known_path_q_fst.
  - lazymatch goal with
    | Hp : Path_Ty GammaZ ?r ?member |- _ =>
        pose proof (IH _ _ _ Hp) as Hknown
    end.
    inversion Hknown. subst k1.
    unpack_same_nat_index. unpack_kind_index.
    apply known_path_q_sel.
  - lazymatch goal with
    | Htail : Path_Ty GammaZ (path_sel (path_fst ?r) ?a) ?member |- _ =>
        pose proof (IH _ _ _ Htail) as Hknown
    end.
    inversion Hknown.
Qed.

(** All paths except the argument variable [z] are marked. *)
Definition PathMarked (p : Path 2) : Prop := p <> path_var z.

Theorem proper_results_marked : ProperResultsMarked GammaZ PathMarked.
Proof.
  intros p T Hp Hmarked.
  pose proof (path_typing_known Hp) as Hknown.
  inversion Hknown.
  - exfalso. apply Hmarked. symmetry. assumption.
  - unpack_ty_index. exact I.
  - unpack_ty_index. exact I.
Qed.

Theorem singleton_aliases_marked :
    SingletonAliasesMarked GammaZ PathMarked.
Proof.
  intros p r Hp Hr.
  pose proof (path_typing_known Hp) as Hknown.
  inversion Hknown.
Qed.

Theorem interval_uppers_marked :
    IntervalUppersMarked GammaZ PathMarked.
Proof.
  intros p L U Hp.
  pose proof (path_typing_known Hp) as Hknown.
  inversion Hknown. unpack_ty_index. unpack_ty_index. exact I.
Qed.

Theorem q_singleton_marked :
    SignatureMarked PathMarked (tau_ty (ty_single (path_var q))).
Proof.
  cbn [SignatureMarked TypeMarked PathMarked q z].
  intro E. discriminate E.
Qed.

Theorem z_singleton_unmarked :
    ~ SignatureMarked PathMarked (tau_ty (ty_single (path_var z))).
Proof.
  cbn [SignatureMarked TypeMarked PathMarked].
  intro H. apply H. reflexivity.
Qed.

(** The critical false alias used to type the historical closure body is no
    longer derivable. *)
Theorem historical_body_subtyping_blocked :
    ~ Tau_Sub GammaZ
      (tau_ty (ty_single (path_var q)))
      (tau_ty (ty_single (path_var z))).
Proof.
  intro Hsub. apply z_singleton_unmarked.
  exact (sub_preserves_mark proper_results_marked
    singleton_aliases_marked interval_uppers_marked Hsub
    q_singleton_marked).
Qed.

(** The old last edge [q.A <: {z}] is not recoverable through
    transitivity. *)
Theorem selection_to_argument_singleton_blocked :
    ~ Tau_Sub GammaZ
      (tau_ty (ty_tsel (path_var q) label))
      (tau_ty (ty_single (path_var z))).
Proof.
  intro Hsub. apply z_singleton_unmarked.
  apply (sub_preserves_mark proper_results_marked
    singleton_aliases_marked interval_uppers_marked Hsub).
  exact I.
Qed.

Print Assumptions historical_body_subtyping_blocked.
Print Assumptions selection_to_argument_singleton_blocked.

End CounterexampleRegression.
