From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store Cont State Machine Progress
  PathReduction RuntimeConversion ScopedRuntimeEq StructuralRuntimeTyping
  StructuralTermTyping StructuralRuntimeLemmas StructuralMachineInvariant
  StructuralApplicationBoundary StructuralRefinedProgress.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Lookupability is needed only for ordinary types.  Interval-typed paths
    never occur as machine terms. *)
Local Definition Path_StructLookupable {n : nat} (s : Store n)
    {k : Kind} (p : Path n) (d : Tau n k) : Prop :=
  match k as observed return Tau n observed -> Prop with
  | star => fun _ => exists x, Path_reduce p s x
  | iota => fun _ => True
  end d.

Local Definition Path_StructLookupableMotive {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) {k : Kind}
    (p : Path n) (d : Tau n k)
    (_ : Path_StructCheck G R p d) : Prop :=
  forall s : Store n,
    Store_PairCheckReflection G s ->
    R = Path_RuntimeEq s ->
    Path_StructLookupable s p d.

Local Definition Tau_StructSubLookupableMotive {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) {k : Kind}
    (d1 d2 : Tau n k) (_ : Tau_StructSub G R d1 d2) : Prop := True.

(** A member definition at the term kind is constructively a value member. *)
Equations Store_Binds_star_member {n : nat} {s : Store n}
    {x y : Fin.t n} {a : Name} (delta : Def n star)
    (H : Store_Binds s x (@tm_pair n star y a delta)) :
    { z : Fin.t n & Store_Binds s x (tm_pair y a (def_val z)) } :=
Store_Binds_star_member (delta := def_val z) H := existT _ z H.

(** Mutual induction with the subtyping motive collapsed to [True]. *)
Local Lemma Path_structLookupable_mut :
    (forall n G R k p d (H : Path_StructCheck G R p d),
      @Path_StructLookupableMotive n G R k p d H) /\
    (forall n G R k d1 d2 (H : Tau_StructSub G R d1 d2),
      @Tau_StructSubLookupableMotive n G R k d1 d2 H).
Proof.
  apply PathStruct_mutind;
    unfold Path_StructLookupableMotive,
      Tau_StructSubLookupableMotive.
  - intros n G R x T Hbind s Hreflect HR.
    exists x. apply path_reduce_var.
  - intros n k G R p d1 d2 Hp IHp Hsub IHsub s Hreflect HR.
    destruct k.
    + exact (IHp s Hreflect HR).
    + exact I.
  - intros n G R p U T Hp IHp Hsub IHsub s Hreflect HR.
    exact (IHp s Hreflect HR).
  - intros n k G R p S0 a d Hp IHp s Hreflect HR.
    destruct (IHp s Hreflect HR) as [x Hx].
    assert (Hp_runtime : Path_StructCheck G (Path_RuntimeEq s) p
      (tau_ty (ty_pair S0 a d))).
    { rewrite <- HR. exact Hp. }
    destruct (Hreflect x S0 a k d
      (Path_StructCheck_reduce_to_var Hx Hp_runtime))
      as (y & delta & Hbinding).
    exists y. exact (@path_reduce_fst n k p s x y a delta Hx Hbinding).
  - intros n k G R p S0 a d Hp IHp s Hreflect HR.
    destruct k.
    + destruct (IHp s Hreflect HR) as [x Hx].
      assert (Hp_runtime : Path_StructCheck G (Path_RuntimeEq s) p
        (tau_ty (ty_pair S0 a d))).
      { rewrite <- HR. exact Hp. }
      destruct (Hreflect x S0 a star d
        (Path_StructCheck_reduce_to_var Hx Hp_runtime))
        as (y & delta & Hbinding).
      destruct (Store_Binds_star_member (delta := delta) Hbinding)
        as [z Hvalue_binding].
      exists z.
      exact (@path_reduce_sel_hit n p s x y z a Hx Hvalue_binding).
    + exact I.
  - intros n k k' G R p S0 a b d d' Hp IHp Htail IHtail Hne
      s Hreflect HR.
    destruct k.
    + destruct (IHp s Hreflect HR) as [x Hx].
      destruct (IHtail s Hreflect HR) as [z Hz].
      assert (Hp_runtime : Path_StructCheck G (Path_RuntimeEq s) p
        (tau_ty (ty_pair S0 b d'))).
      { rewrite <- HR. exact Hp. }
      destruct (Hreflect x S0 b k' d'
        (Path_StructCheck_reduce_to_var Hx Hp_runtime))
        as (y & delta & Hbinding).
      assert (Hfst : Path_reduce (path_fst p) s y).
      { exact (@path_reduce_fst n k' p s x y b delta Hx Hbinding). }
      assert (Heq : Path_RuntimeEq s (path_fst p) (path_var y)).
      { exact (path_runtime_eq_coresolve Hfst (path_reduce_var y s)). }
      assert (Hsel : Path_RuntimeEq s
        (path_sel (path_fst p) a) (path_sel (path_var y) a)).
      { exact (path_equiv_sel (Path_RuntimeEq_isEquivCongr s) Heq a). }
      pose proof (proj1 (Path_RuntimeEq_reduce_iff Hsel z) Hz) as Htail'.
      exists z.
      exact (@path_reduce_sel_miss n k' p s x y z a b delta
        Hx Hbinding Hne Htail').
    + exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
Qed.

Local Theorem Path_structLookupable {n : nat} {G : Ctx n} {s : Store n}
    {R : Path n -> Path n -> Prop} {k : Kind}
    {p : Path n} {d : Tau n k}
    (Hreflect : Store_PairCheckReflection G s)
    (Hp : Path_StructCheck G R p d)
    (HR : R = Path_RuntimeEq s) : Path_StructLookupable s p d.
Proof.
  exact (proj1 Path_structLookupable_mut _ _ _ _ _ _ Hp s Hreflect HR).
Qed.

(** Every structurally checked term-level path resolves under pair-shape
    reflection. *)
Theorem Path_reduce_progress_structural {n : nat} {G : Ctx n}
    {s : Store n} {p : Path n} {T : Ty n}
    (Hreflect : Store_PairCheckReflection G s)
    (Hp : Path_StructCheck G (Path_RuntimeEq s) p (tau_ty T)) :
    exists x, Path_reduce p s x.
Proof. exact (Path_structLookupable Hreflect Hp eq_refl). Qed.

(** Function-shape reflection at an occupied location. *)
Definition Store_FunCheckReflection {n : nat}
    (G : Ctx n) (s : Store n) : Prop :=
  forall (x : Fin.t n) (S0 : Ty n) (U : Ty (S n)) (v : Tm n),
    Store_Binds s x v ->
    Path_StructCheck G (Path_RuntimeEq s) (path_var x)
      (tau_ty (ty_fun S0 U)) ->
    exists (A : Ty n) (body : Tm (S n)), v = tm_abs A body.

(** Complete store-facing contract required by progress. *)
Record Store_StructOperational {n : nat}
    (G : Ctx n) (s : Store n) : Prop := {
  store_struct_operational_pair_reflect : Store_PairCheckReflection G s;
  store_struct_operational_fun_reflect : Store_FunCheckReflection G s
}.

(** Path-term evidence supplies the operational classification. *)
Local Theorem Tm_StructCheck_resolve_path {n : nat} {G : Ctx n}
    {s : Store n} {p : Path n} {T : Ty n}
    (Hops : Store_StructOperational G s)
    (H : Tm_StructCheck G (Path_RuntimeEq s) (tm_path p) T) :
    exists x, Path_reduce p s x.
Proof.
  destruct (@Tm_StructCheck_path_inversion n G (Path_RuntimeEq s)
    (tm_path p) T H p eq_refl) as [U Hp Hsub Hwf].
  exact (Path_reduce_progress_structural
    (store_struct_operational_pair_reflect Hops) Hp).
Qed.

(** Conditional progress for the fully structural machine invariant. *)
Theorem State_StructTy_progress {n : nat} {G : Ctx n} {s : Store n}
    {K : Tm_Cont n} {t : Tm n} {T : Ty n}
    (Hops : Store_StructOperational G s)
    (H : State_StructTy G (mk_state s K t) T) :
    State_Progress (mk_state s K t).
Proof.
  destruct H as [Input Hstore Hcont Hterm].
  destruct t as
    [scope p|scope A body|scope k y a delta|scope p q
    |scope bound body|scope term annotation].
  - destruct p as [x|p|p a].
    + destruct K as [|frame rest].
      * destruct (Store_StructTy_lookup_value Hstore x)
          as (v & Hbind & Hvalue).
        apply state_progress_final. exact (state_final_var s x v Hbind).
      * destruct frame as [body]. eapply state_progress_step.
        apply state_step_rename.
    + destruct (Tm_StructCheck_resolve_path Hops Hterm) as [x Hx].
      eapply state_progress_step. eapply state_step_path.
      * exact Hx.
      * intro Hvar. inversion Hvar.
    + destruct (Tm_StructCheck_resolve_path Hops Hterm) as [x Hx].
      eapply state_progress_step. eapply state_step_path.
      * exact Hx.
      * intro Hvar. inversion Hvar.
  - destruct K as [|frame rest].
    + apply state_progress_final. apply state_final_val. constructor.
    + destruct frame as [suspended]. eapply state_progress_step.
      exact (state_step_lift s rest suspended (tm_abs A body)
        (value_abs A body)).
  - destruct K as [|frame rest].
    + apply state_progress_final. apply state_final_val. constructor.
    + destruct frame as [suspended]. eapply state_progress_step.
      exact (state_step_lift s rest suspended (tm_pair y a delta)
        (value_pair y a delta)).
  - destruct (Tm_StructCheck_app_inversion Hterm)
      as (S0 & U & Hfunction & Hargument & post).
    destruct (Tm_StructCheck_resolve_path Hops Hfunction)
      as [x Hfunction_reduce].
    destruct (Tm_StructCheck_resolve_path Hops Hargument)
      as [arg_location Hargument_reduce].
    destruct (@Tm_StructCheck_path_inversion scope G (Path_RuntimeEq s)
      (tm_path p) (ty_fun S0 U) Hfunction p eq_refl)
      as [P Hpath Hsingle Hwf].
    assert (Hfunction_at_public : Path_StructCheck G (Path_RuntimeEq s) p
      (tau_ty (ty_fun S0 U))).
    { exact (path_struct_check_promote Hpath Hsingle). }
    assert (Hfunction_at_location : Path_StructCheck G (Path_RuntimeEq s)
      (path_var x) (tau_ty (ty_fun S0 U))).
    { exact (Path_StructCheck_reduce_to_var
        Hfunction_reduce Hfunction_at_public). }
    destruct (Store_StructTy_lookup_value Hstore x)
      as (v & Hbind & Hvalue).
    destruct (@store_struct_operational_fun_reflect scope G s Hops
      x S0 U v Hbind Hfunction_at_location) as (Actual & closure & Ev).
    rewrite Ev in Hbind.
    eapply state_progress_step.
    exact (state_step_app s K p q x arg_location Actual closure
      Hfunction_reduce Hargument_reduce Hbind).
  - eapply state_progress_step. apply state_step_let_push.
  - eapply state_progress_step. apply state_step_ascribe.
Qed.

Print Assumptions Path_reduce_progress_structural.
Print Assumptions Tm_StructCheck_resolve_path.
Print Assumptions State_StructTy_progress.
