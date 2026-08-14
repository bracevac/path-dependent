From Stdlib Require Import Lists.List.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store Renaming Cont State Machine
  PathReduction RuntimeConversion ScopedRuntimeEq StructuralRuntimeTyping
  StructuralTermTyping StructuralRuntimeLemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Structural typing of a store, with every stored value checked against
    the concrete runtime equality induced by the preceding store. *)
Inductive Store_StructTy : forall {n : nat}, Ctx n -> Store n -> Prop :=
| store_struct_ty_empty : Store_StructTy ctx_nil store_empty
| store_struct_ty_val {n : nat} (G : Ctx n) (s : Store n)
    (v : Tm n) (T : Ty n) (Hv : Tm_IsValue v) :
    Store_StructTy G s ->
    Tm_StructCheck G (Path_RuntimeEq s) v T ->
    Store_StructTy (ctx_snoc G T) (store_val s v Hv).

Arguments store_struct_ty_val {n} G s v T Hv _ _.

Theorem Store_Ty_toStruct {n : nat} {G : Ctx n} {s : Store n}
    (H : Store_Ty G s) : Store_StructTy G s.
Proof.
  induction H.
  - apply store_struct_ty_empty.
  - eapply store_struct_ty_val.
    + exact IHStore_Ty.
    + exact (Tm_StructCheck_of_source H0 (Path_RuntimeEq s)).
Qed.

(** Every context index of a structurally typed store contains a runtime
    value. *)
Theorem Store_StructTy_lookup_value {n : nat} {G : Ctx n} {s : Store n}
    (H : Store_StructTy G s) (x : Fin.t n) :
    exists v, Store_Binds s x v /\ Tm_IsValue v.
Proof.
  induction H.
  - exact (Fin.elim0 x).
  - refine (@Fin.cases' n x
      (fun x => exists u : Tm (S n),
        Store_Binds (store_val s v Hv) x u /\ Tm_IsValue u) _ _).
    + exists (Tm_weaken v). split.
      * apply store_binds_here.
      * now apply Tm_IsValue_weaken.
    + intro y. destruct (IHStore_StructTy y) as (u & Hu & Huv).
      exists (Tm_weaken u). split.
      * now apply store_binds_there.
      * now apply Tm_IsValue_weaken.
Qed.

(** Structural typing of a suspended evaluation frame. *)
Inductive Tm_Frame_StructTy {n : nat} (G : Ctx n) (s : Store n) :
    Ty n -> Tm_Frame n -> Ty n -> Prop :=
| tm_frame_struct_ty_let (S0 T : Ty n) (t : Tm (S n)) :
    Tm_StructCheck (ctx_snoc G S0)
      (Path_ScopedLift (Path_RuntimeEq s)) t (Ty_weaken T) ->
    Tm_Frame_StructTy G s S0 (tm_frame_let t) T.

Arguments tm_frame_struct_ty_let {n G s} S0 T t _.

(** Structural typing of continuation stacks. *)
Inductive Tm_Cont_StructTy {n : nat} (G : Ctx n) (s : Store n) :
    Ty n -> Tm_Cont n -> Ty n -> Prop :=
| tm_cont_struct_ty_hole (S0 T : Ty n) :
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S0) (tau_ty T) ->
    Tm_Cont_StructTy G s S0 nil T
| tm_cont_struct_ty_cons (S0 U T : Ty n)
    (F : Tm_Frame n) (K : Tm_Cont n) :
    Tm_Cont_StructTy G s S0 K T ->
    Tm_Frame_StructTy G s U F S0 ->
    Tm_Cont_StructTy G s U (cons F K) T.

Arguments tm_cont_struct_ty_hole {n G s} S0 T _.
Arguments tm_cont_struct_ty_cons {n G s} S0 U T F K _ _.

Theorem Tm_Frame_Ty_toStruct {n : nat} {G : Ctx n} {s : Store n}
    {S0 T : Ty n} {F : Tm_Frame n} (H : Tm_Frame_Ty G S0 F T) :
    Tm_Frame_StructTy G s S0 F T.
Proof.
  destruct H. apply tm_frame_struct_ty_let.
  exact (Tm_StructCheck_of_source H (Path_ScopedLift (Path_RuntimeEq s))).
Qed.

Theorem Tm_Cont_Ty_toStruct {n : nat} {G : Ctx n} {s : Store n}
    {S0 T : Ty n} {K : Tm_Cont n} (H : Tm_Cont_Ty G S0 K T) :
    Tm_Cont_StructTy G s S0 K T.
Proof.
  induction H.
  - apply tm_cont_struct_ty_hole.
    exact (Tau_StructSub_of_source H (Path_RuntimeEq s)).
  - eapply tm_cont_struct_ty_cons.
    + exact (IHTm_Cont_Ty s).
    + exact (Tm_Frame_Ty_toStruct (s := s) H0).
Qed.

(** Fully structural typing of a machine state.  Referring to the state's
    projections keeps inversion first-order even though [State] is
    intrinsically scoped. *)
Inductive State_StructTy {n : nat} (G : Ctx n)
    (st : State n) (T : Ty n) : Prop :=
| state_struct_ty_ok (S0 : Ty n) :
    Store_StructTy G (state_store st) ->
    Tm_Cont_StructTy G (state_store st) S0 (state_cont st) T ->
    Tm_StructCheck G (Path_RuntimeEq (state_store st))
      (state_term st) S0 ->
    State_StructTy G st T.

Arguments state_struct_ty_ok {n G st T} S0 _ _ _.

Theorem State_Ty_toStruct {n : nat} {G : Ctx n}
    {st : State n} {T : Ty n} (H : State_Ty G st T) :
    State_StructTy G st T.
Proof.
  destruct H. eapply state_struct_ty_ok.
  - exact (Store_Ty_toStruct H).
  - exact (Tm_Cont_Ty_toStruct (s := s) H0).
  - exact (Tm_StructCheck_of_source H1 (Path_RuntimeEq s)).
Qed.

(** A step either preserves the current scope or extends it by the value
    allocated by the machine. *)
Inductive StructPreserve : forall {n m : nat},
    Ctx n -> State m -> Ty n -> Prop :=
| struct_preserve_same {n : nat} {G : Ctx n}
    {st : State n} {T : Ty n} :
    State_StructTy G st T -> StructPreserve G st T
| struct_preserve_extend {n : nat} {G : Ctx n} {S0 T : Ty n}
    {st : State (S n)} :
    State_StructTy (ctx_snoc G S0) st (Ty_weaken T) ->
    StructPreserve G st T.

Arguments struct_preserve_same {n G st T} _.
Arguments struct_preserve_extend {n G S0 T st} _.

(** Replacing a path term by its resolved store variable preserves its
    advertised structural type. *)
Theorem Tm_StructCheck_reduce_path {n : nat} {G : Ctx n}
    {s : Store n} {p : Path n} {x : Fin.t n} {T : Ty n}
    (Hr : Path_reduce p s x)
    (H : Tm_StructCheck G (Path_RuntimeEq s) (tm_path p) T) :
    Tm_StructCheck G (Path_RuntimeEq s) (tm_path (path_var x)) T.
Proof.
  destruct (@Tm_StructCheck_path_inversion n G (Path_RuntimeEq s)
    (tm_path p) T H p eq_refl)
    as [U Hp Hsub Hwf].
  eapply tm_struct_check_sub.
  - exact (tm_struct_check_path G (Path_RuntimeEq s)
      (path_var x) U (Path_StructCheck_reduce_to_var Hr Hp)).
  - exact (Tau_StructSub_reduce_singleton_left Hr Hsub).
  - exact Hwf.
Qed.

Theorem StructPreserve_path {n : nat} {G : Ctx n} {s : Store n}
    {K : Tm_Cont n} {p : Path n} {x : Fin.t n} {T : Ty n}
    (Hr : Path_reduce p s x)
    (H : State_StructTy G (mk_state s K (tm_path p)) T) :
    StructPreserve G (mk_state s K (tm_path (path_var x))) T.
Proof.
  destruct H as [S0 Hstore Hcont Hterm].
  apply struct_preserve_same. eapply state_struct_ty_ok.
  - exact Hstore.
  - exact Hcont.
  - exact (Tm_StructCheck_reduce_path Hr Hterm).
Qed.

(** Inversion through any trailing structural subsumption. *)
Definition tm_typed_term_payload {n : nat} (u : Tm n) : option (Tm n) :=
  match u with
  | tm_typed t _ => Some t
  | _ => None
  end.

Definition tm_typed_type_payload {n : nat} (u : Tm n) : option (Ty n) :=
  match u with
  | tm_typed _ A => Some A
  | _ => None
  end.

Definition tm_let_scrutinee_payload {n : nat} (u : Tm n) : option (Tm n) :=
  match u with
  | tm_let s _ => Some s
  | _ => None
  end.

Definition tm_let_body_payload {n : nat} (u : Tm n) : option (Tm (S n)) :=
  match u with
  | tm_let _ t => Some t
  | _ => None
  end.

Local Lemma Tm_StructCheck_typed_inv_of_eq {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {u : Tm n} {T : Ty n}
    (H : Tm_StructCheck G R u T) :
    forall (t : Tm n) (A : Ty n), u = tm_typed t A ->
      Tm_StructCheck G R t T /\ Tau_StructWf G R (tau_ty T).
Proof.
  induction H; intros target annotation Heq; try discriminate Heq.
  - pose proof (f_equal tm_typed_term_payload Heq) as Et.
    pose proof (f_equal tm_typed_type_payload Heq) as EA.
    cbn [tm_typed_term_payload] in Et.
    cbn [tm_typed_type_payload] in EA.
    injection Et as Et'. injection EA as EA'. subst target. subst annotation.
    split; assumption.
  - destruct (IHTm_StructCheck target annotation Heq) as [Ht _].
    split.
    + eapply tm_struct_check_sub; eassumption.
    + exact H1.
Qed.

Theorem Tm_StructCheck_typed_inv {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {t : Tm n} {A T : Ty n}
    (H : Tm_StructCheck G R (tm_typed t A) T) :
    Tm_StructCheck G R t T /\ Tau_StructWf G R (tau_ty T).
Proof.
  exact (@Tm_StructCheck_typed_inv_of_eq n G R (tm_typed t A) T
    H t A eq_refl).
Qed.

Local Lemma Tm_StructCheck_let_inv_of_eq {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {u : Tm n} {T : Ty n}
    (H : Tm_StructCheck G R u T) :
    forall (s : Tm n) (t : Tm (S n)), u = tm_let s t ->
      exists S0,
        Tm_StructCheck G R s S0 /\
        Tau_StructWf G R (tau_ty T) /\
        Tm_StructCheck (ctx_snoc G S0) (Path_ScopedLift R)
          t (Ty_weaken T).
Proof.
  induction H; intros scrutinee body Heq; try discriminate Heq.
  - pose proof (f_equal tm_let_scrutinee_payload Heq) as Es.
    pose proof (f_equal tm_let_body_payload Heq) as Et.
    cbn [tm_let_scrutinee_payload] in Es.
    cbn [tm_let_body_payload] in Et.
    injection Es as Es'. injection Et as Et'.
    subst scrutinee. subst body.
    exists S0. repeat split; assumption.
  - destruct (IHTm_StructCheck scrutinee body Heq)
      as (U & Hscrutinee & Hinner_wf & Hbody).
    pose proof (Tau_StructSub_renameExact H0
      (@Renaming_weaken n G U) (@Path_RelHom_weaken n R)) as Hsub.
    pose proof (Tau_StructWf_renameExact H1
      (@Renaming_weaken n G U) (@Path_RelHom_weaken n R)) as Hwf.
    exists U. repeat split.
    + exact Hscrutinee.
    + exact H1.
    + eapply tm_struct_check_sub.
      * exact Hbody.
      * exact Hsub.
      * exact Hwf.
Qed.

Theorem Tm_StructCheck_let_inv {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {s : Tm n} {t : Tm (S n)}
    {T : Ty n} (H : Tm_StructCheck G R (tm_let s t) T) :
    exists S0,
      Tm_StructCheck G R s S0 /\
      Tau_StructWf G R (tau_ty T) /\
      Tm_StructCheck (ctx_snoc G S0) (Path_ScopedLift R)
        t (Ty_weaken T).
Proof.
  exact (@Tm_StructCheck_let_inv_of_eq n G R (tm_let s t) T
    H s t eq_refl).
Qed.

(** Administrative machine transitions. *)
Theorem StructPreserve_let_push {n : nat} {G : Ctx n}
    {s : Store n} {K : Tm_Cont n} {u : Tm n}
    {t : Tm (S n)} {T : Ty n}
    (H : State_StructTy G (mk_state s K (tm_let u t)) T) :
    StructPreserve G (mk_state s (cons (tm_frame_let t) K) u) T.
Proof.
  destruct H as [S0 Hstore Hcont Hterm].
  destruct (Tm_StructCheck_let_inv Hterm) as (U & Hu & Hwf & Hbody).
  apply struct_preserve_same. eapply state_struct_ty_ok.
  - exact Hstore.
  - eapply tm_cont_struct_ty_cons.
    + exact Hcont.
    + exact (tm_frame_struct_ty_let U S0 t Hbody).
  - exact Hu.
Qed.

Theorem StructPreserve_ascribe {n : nat} {G : Ctx n}
    {s : Store n} {K : Tm_Cont n} {t : Tm n} {A T : Ty n}
    (H : State_StructTy G (mk_state s K (tm_typed t A)) T) :
    StructPreserve G (mk_state s K t) T.
Proof.
  destruct H as [S0 Hstore Hcont Hterm].
  apply struct_preserve_same. eapply state_struct_ty_ok.
  - exact Hstore.
  - exact Hcont.
  - exact (proj1 (Tm_StructCheck_typed_inv Hterm)).
Qed.

(** Structural frames and continuations survive runtime allocation. *)
Theorem Tm_Frame_StructTy_weaken_runtime {n : nat} {G : Ctx n}
    {s : Store n} {S0 T U : Ty n} {F : Tm_Frame n}
    (H : Tm_Frame_StructTy G s S0 F T)
    (v : Tm n) (Hv : Tm_IsValue v) :
    Tm_Frame_StructTy (ctx_snoc G U) (store_val s v Hv)
      (Ty_weaken S0) (Tm_Frame_weaken F) (Ty_weaken T).
Proof.
  destruct H as [S0 T t Hbody].
  apply tm_frame_struct_ty_let.
  pose proof (Tm_StructCheck_renameExact Hbody
    (Renaming_ext (@Renaming_weaken n G U))
    (Path_RelHom_scoped
      (Path_RelHom_runtime_weaken (v := v) Hv))) as Hrenamed.
  rewrite <- Ty_weaken_rename in Hrenamed.
  cbn [Tm_Frame_weaken Tm_Frame_rename].
  exact Hrenamed.
Qed.

Theorem Tm_Cont_StructTy_weaken_runtime {n : nat} {G : Ctx n}
    {s : Store n} {S0 T U : Ty n} {K : Tm_Cont n}
    (H : Tm_Cont_StructTy G s S0 K T)
    (v : Tm n) (Hv : Tm_IsValue v) :
    Tm_Cont_StructTy (ctx_snoc G U) (store_val s v Hv)
      (Ty_weaken S0) (Tm_Cont_weaken K) (Ty_weaken T).
Proof.
  induction H.
  - unfold Tm_Cont_weaken, Tm_Cont_rename. cbn.
    apply tm_cont_struct_ty_hole.
    exact (Tau_StructSub_weaken_runtime H U (v := v) Hv).
  - unfold Tm_Cont_weaken, Tm_Cont_rename in *. cbn in *.
    eapply tm_cont_struct_ty_cons.
    + exact IHTm_Cont_StructTy.
    + exact (Tm_Frame_StructTy_weaken_runtime H0 (v := v) Hv).
Qed.

Local Lemma Path_RelHom_scoped_to_runtime_extension {n : nat}
    {s : Store n} {v : Tm n} {Hv : Tm_IsValue v} :
    Path_RelHom (Path_ScopedLift (Path_RuntimeEq s))
      (Path_RuntimeEq (store_val s v Hv)) (FinFun.id (S n)).
Proof.
  intros p q Hpq. rewrite !Path_rename_id.
  exact (Path_ScopedLift_to_runtime_extension Hpq).
Qed.

Theorem StructPreserve_lift {n : nat} {G : Ctx n} {s : Store n}
    {K : Tm_Cont n} {t : Tm (S n)} {v : Tm n} {T : Ty n}
    (Hv : Tm_IsValue v)
    (H : State_StructTy G
      (mk_state s (cons (tm_frame_let t) K) v) T) :
    StructPreserve G
      (mk_state (store_val s v Hv) (Tm_Cont_weaken K) t) T.
Proof.
  destruct H as [Input Hstore Hcont Hvalue].
  inversion Hcont as [|S0 U T0 F Ktail Hrest Hframe]; subst.
  inversion Hframe as [Input0 Result body Hbody]; subst.
  pose proof (Tm_StructCheck_renameExact Hbody
    (@Renaming_id (S n) (ctx_snoc G Input))
    (@Path_RelHom_scoped_to_runtime_extension n s v Hv)) as Hbody'.
  apply (struct_preserve_extend (S0 := Input)).
  eapply state_struct_ty_ok.
  - eapply store_struct_ty_val; eassumption.
  - exact (Tm_Cont_StructTy_weaken_runtime Hrest (v := v) Hv).
  - rewrite Tm_rename_id, Ty_rename_id in Hbody'. exact Hbody'.
Qed.

(** Opening a suspended body with an already checked variable discharges
    its scoped relation. *)
Theorem StructPreserve_rename {n : nat} {G : Ctx n} {s : Store n}
    {K : Tm_Cont n} {t : Tm (S n)} {x : Fin.t n} {T : Ty n}
    (H : State_StructTy G
      (mk_state s (cons (tm_frame_let t) K)
        (tm_path (path_var x))) T) :
    StructPreserve G (mk_state s K (Tm_open t x)) T.
Proof.
  destruct H as [Input Hstore Hcont Harg].
  inversion Hcont as [|S0 U T0 F Ktail Hrest Hframe]; subst.
  inversion Hframe as [Input0 Result body Hbody]; subst.
  pose proof (Tm_StructCheck_open_var_of_path_term Hbody
    (Path_RuntimeEq_isEquivCongr s) Harg) as Hopened.
  unfold Ty_weaken in Hopened.
  rewrite Ty_rename_rename, FinFun.openAt_weaken, Ty_rename_id in Hopened.
  apply struct_preserve_same. eapply state_struct_ty_ok; eassumption.
Qed.

Print Assumptions Store_StructTy_lookup_value.
Print Assumptions State_Ty_toStruct.
Print Assumptions Tm_StructCheck_reduce_path.
Print Assumptions Tm_StructCheck_let_inv.
Print Assumptions Tm_Frame_StructTy_weaken_runtime.
Print Assumptions StructPreserve_lift.
Print Assumptions StructPreserve_rename.
