From Equations Require Import Equations.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store PathReduction Lookup RuntimeConversion
  ScopedRuntimeEq StructuralRuntimeTyping StructuralTermTyping
  StructuralRuntimeLemmas StructuralMachineInvariant StructuralResolution
  StructuralValueInversion StructuralPreciseStore
  StructuralApplicationCompatibility
  StructuralRefinedProgress.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Function observation at a store variable is reflected by an abstraction
    in that cell. *)
Definition Store_FunctionCheckReflection {n : nat}
    (G : Ctx n) (s : Store n) : Prop :=
  forall (x : Fin.t n) (S0 : Ty n) (U : Ty (S n)),
    Path_StructCheck G (Path_RuntimeEq s) (path_var x)
      (tau_ty (ty_fun S0 U)) ->
    exists (A : Ty n) (body : Tm (S n)),
      Store_Binds s x (tm_abs A body).

(** The two concrete head observations consumed by path and machine
    progress. *)
Record Store_HeadCheckReflection {n : nat}
    (G : Ctx n) (s : Store n) : Prop := {
  store_head_check_reflection_function : Store_FunctionCheckReflection G s;
  store_head_check_reflection_pair : Store_PairCheckReflection G s
}.

(** Promote a reducing path from its result singleton to the exact context
    type of that result. *)
Local Theorem Path_StructCheck_at_precise_result {n : nat} {G : Ctx n}
    {s : Store n} {p : Path n} {x : Fin.t n} {P : Ty n}
    (Hr : Path_reduce p s x)
    (Hp : Path_StructCheck G (Path_RuntimeEq s) p
      (tau_ty (ty_single (path_var x))))
    (Hx : Ctx_Binds G x P) :
    Path_StructCheck G (Path_RuntimeEq s) p (tau_ty P).
Proof.
  assert (Hsingle : Tau_StructSub G (Path_RuntimeEq s)
      (tau_ty (ty_single p)) (tau_ty P)).
  { eapply tau_struct_sub_trans.
    - exact (Tau_StructSub_single_runtime (Path_RuntimeEq_of_reduce Hr)).
    - apply tau_struct_sub_widen.
      apply path_struct_check_var. exact Hx. }
  exact (path_struct_check_promote Hp Hsingle).
Qed.

(** First-order precise-type view of a stored term-member pair. *)
Local Lemma Tm_StructPrecise_value_pair_type {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {y z : Fin.t n} {a : Name}
    {P : Ty n}
    (H : Tm_StructPrecise G R (tm_pair y a (def_val z)) P) :
    P = ty_pair (ty_single (path_var y)) a
      (tau_ty (ty_single (Path_weaken (path_var z)))).
Proof.
  dependent elimination H. reflexivity.
Qed.

(** Static-aligned lookup reconstructs the term singleton of its result in
    an exact structural store. *)
Theorem Store_StructPreciseTy_lookup_singleton {n : nat} {G : Ctx n}
    {s : Store n} {p : Path n} {x : Fin.t n}
    (Hstore : Store_StructPreciseTy G s)
    (Hr : Path_lookup p s x) :
    Path_StructCheck G (Path_RuntimeEq s) p
      (tau_ty (ty_single (path_var x))).
Proof.
  revert G Hstore.
  induction Hr as
      [n x s
      |n k p s x y a d Hr IH Hbind
      |n p s x y z a Hr IH Hbind
      |n k p s x y z a b d Hr IH Hbind Hne Htail IHtail];
    intros G Hstore.
  - destruct (Ctx_Binds_exists G x) as [P Hx].
    eapply path_struct_check_promote.
    + apply path_struct_check_var. exact Hx.
    + apply tau_struct_sub_refl.
  - destruct (Store_StructPreciseTy_of_store_binds Hstore Hbind)
      as (P & Hx & Hprecise).
    pose proof (Path_StructCheck_at_precise_result
      (Path_lookup_toReduce Hr) (IH G Hstore) Hx) as Hp.
    dependent elimination Hprecise;
      eapply path_struct_check_fst; exact Hp.
  - destruct (Store_StructPreciseTy_of_store_binds Hstore Hbind)
      as (P & Hx & Hprecise).
    pose proof (Tm_StructPrecise_value_pair_type Hprecise) as EP.
    subst P.
    pose proof (Path_StructCheck_at_precise_result
      (Path_lookup_toReduce Hr) (IH G Hstore) Hx) as Hp.
    pose proof (path_struct_check_sel_r Hp) as Hsel.
    rewrite <- (Tau_weaken_open
      (tau_ty (ty_single (path_var z))) (path_fst p)).
    exact Hsel.
  - destruct (Store_StructPreciseTy_of_store_binds Hstore Hbind)
      as (P & Hx & Hprecise).
    pose proof (Path_StructCheck_at_precise_result
      (Path_lookup_toReduce Hr) (IH G Hstore) Hx) as Hp.
    pose proof (IHtail G Hstore) as HtailCheck.
    dependent elimination Hprecise.
    + eapply path_struct_check_sel_l;
        [exact Hp | exact HtailCheck | exact Hne].
    + eapply path_struct_check_sel_l;
        [exact Hp | exact HtailCheck | exact Hne].
Qed.

(** Big-step term-path reduction has the same singleton reconstruction
    property. *)
Theorem Store_StructPreciseTy_reduce_singleton {n : nat} {G : Ctx n}
    {s : Store n} {p : Path n} {x : Fin.t n}
    (Hstore : Store_StructPreciseTy G s) (Hr : Path_reduce p s x) :
    Path_StructCheck G (Path_RuntimeEq s) p
      (tau_ty (ty_single (path_var x))).
Proof.
  exact (Store_StructPreciseTy_lookup_singleton Hstore
    (Path_reduce_toLookup Hr)).
Qed.

(** In an exact structural store, a reducing term path and its result
    variable support the same proper structural checks. *)
Theorem Store_StructPreciseTy_reduce_check_iff {n : nat} {G : Ctx n}
    {s : Store n} {p : Path n} {x : Fin.t n} {T : Ty n}
    (Hstore : Store_StructPreciseTy G s) (Hr : Path_reduce p s x) :
    Path_StructCheck G (Path_RuntimeEq s) p (tau_ty T) <->
      Path_StructCheck G (Path_RuntimeEq s)
        (path_var x) (tau_ty T).
Proof.
  split.
  - intro Hp. exact (Path_StructCheck_reduce_to_var Hr Hp).
  - intro Hx.
    pose proof (Store_StructPreciseTy_reduce_singleton Hstore Hr) as Halias.
    assert (Hsub : Tau_StructSub G (Path_RuntimeEq s)
        (tau_ty (ty_single p)) (tau_ty T)).
    { eapply tau_struct_sub_trans.
      - exact (Tau_StructSub_single_runtime (Path_RuntimeEq_of_reduce Hr)).
      - apply tau_struct_sub_widen. exact Hx. }
    exact (path_struct_check_promote Halias Hsub).
Qed.

(** Runtime equality transports proper checks between paths which actually
    resolve. *)
Theorem Store_StructPreciseTy_runtimeEq_reduce_check_iff {n : nat}
    {G : Ctx n} {s : Store n} {p q : Path n} {x : Fin.t n}
    {T : Ty n} (Hstore : Store_StructPreciseTy G s)
    (Heq : Path_RuntimeEq s p q) (Hp : Path_reduce p s x) :
    Path_StructCheck G (Path_RuntimeEq s) p (tau_ty T) <->
      Path_StructCheck G (Path_RuntimeEq s) q (tau_ty T).
Proof.
  pose proof (proj1 (Path_RuntimeEq_reduce_iff Heq x) Hp) as Hq.
  split; intro Hcheck.
  - apply (proj2 (Store_StructPreciseTy_reduce_check_iff Hstore Hq)).
    exact (proj1 (Store_StructPreciseTy_reduce_check_iff Hstore Hp) Hcheck).
  - apply (proj2 (Store_StructPreciseTy_reduce_check_iff Hstore Hp)).
    exact (proj1 (Store_StructPreciseTy_reduce_check_iff Hstore Hq) Hcheck).
Qed.

(** Exact singleton-head pushback needed by concrete progress. *)
Record Store_StructPreciseSingletonHeadPushback {n : nat}
    (G : Ctx n) (s : Store n) : Prop := {
  store_struct_precise_singleton_head_pushback_function :
    forall (x : Fin.t n) (S0 : Ty n) (U : Ty (S n)),
      Store_StructPreciseTy G s ->
      Tau_StructSub G (Path_RuntimeEq s)
        (tau_ty (ty_single (path_var x)))
        (tau_ty (ty_fun S0 U)) ->
      exists (A : Ty n) (body : Tm (S n)),
        Store_Binds s x (tm_abs A body);
  store_struct_precise_singleton_head_pushback_pair :
    forall (x : Fin.t n) (S0 : Ty n) (a : Name)
      (k : Kind) (d : Tau (S n) k),
      Store_StructPreciseTy G s ->
      Tau_StructSub G (Path_RuntimeEq s)
        (tau_ty (ty_single (path_var x)))
        (tau_ty (ty_pair S0 a d)) ->
      exists (y : Fin.t n) (delta : Def n k),
        Store_Binds s x (@tm_pair n k y a delta)
}.

(** Singleton-head pushback supplies the pair/function reflection consumed
    by structural progress. *)
Theorem Store_StructPreciseTy_headCheckReflection_of_singletonPushback
    {n : nat} {G : Ctx n} {s : Store n}
    (Hstore : Store_StructPreciseTy G s)
    (Hpush : Store_StructPreciseSingletonHeadPushback G s) :
    Store_HeadCheckReflection G s.
Proof.
  constructor.
  - intros x S0 U Hfun.
    apply (store_struct_precise_singleton_head_pushback_function
      (x := x) (S0 := S0) (U := U) Hpush Hstore).
    apply tau_struct_sub_widen. exact Hfun.
  - intros x S0 a k d Hpair.
    apply (store_struct_precise_singleton_head_pushback_pair
      (x := x) (S0 := S0) (a := a) (k := k) (d := d) Hpush Hstore).
    apply tau_struct_sub_widen. exact Hpair.
Qed.

(** Function-signature inversion at an exact context entry, stated over the
    singleton suffix produced by path-term inversion. *)
Definition Store_StructPreciseSingletonFunctionPushback {n : nat}
    (G : Ctx n) (s : Store n) : Prop :=
  forall (x : Fin.t n) (S0 A : Ty n) (U B : Ty (S n)),
    Store_StructPreciseTy G s ->
    Ctx_Binds G x (ty_fun A B) ->
    Tau_StructSub G (Path_RuntimeEq s)
      (tau_ty (ty_single (path_var x)))
      (tau_ty (ty_fun S0 U)) ->
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S0) (tau_ty A) /\
      Tau_StructSub (ctx_snoc G S0)
        (Path_ScopedLift (Path_RuntimeEq s))
        (tau_ty B) (tau_ty U).

(** Function pushback tied directly to the exact context entry and stored
    closure. *)
Definition Store_StructExactFunctionPushback {n : nat}
    (G : Ctx n) (s : Store n) : Prop :=
  forall (x : Fin.t n) (S0 A : Ty n) (U B : Ty (S n))
    (body : Tm (S n)),
    Store_StructPreciseTy G s ->
    Store_Binds s x (tm_abs A body) ->
    Ctx_Binds G x (ty_fun A B) ->
    Tm_StructCheck G (Path_RuntimeEq s)
      (tm_path (path_var x)) (ty_fun S0 U) ->
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S0) (tau_ty A) /\
      Tau_StructSub (ctx_snoc G S0)
        (Path_ScopedLift (Path_RuntimeEq s))
        (tau_ty B) (tau_ty U).

(** Singleton function pushback is sufficient for exact function
    pushback. *)
Theorem Store_StructPreciseSingletonFunctionPushback_to_exact {n : nat}
    {G : Ctx n} {s : Store n}
    (Hpush : Store_StructPreciseSingletonFunctionPushback G s) :
    Store_StructExactFunctionPushback G s.
Proof.
  intros x S0 A U B body Hstore Hbind Hctx Hfun.
  destruct (Tm_StructCheck_path_inversion Hfun eq_refl)
    as [P Hp Hsingle Hwf].
  exact (Hpush x S0 A U B Hstore Hctx Hsingle).
Qed.

(** Internal precise-abstraction inversion retaining the ambient indices. *)
Local Lemma Tm_StructPrecise_abs_parts_exact {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {A : Ty n}
    {body : Tm (S n)} {P : Ty n}
    (H : Tm_StructPrecise G R (tm_abs A body) P) :
    exists B : Ty (S n),
      P = ty_fun A B /\
      Tm_StructCheck (ctx_snoc G A) (Path_ScopedLift R) body B /\
      Tau_StructWf G R (tau_ty A).
Proof.
  dependent elimination H. exists T. repeat split; try reflexivity;
    assumption.
Qed.

(** Exact-store beta opening from the minimal explicit function-pushback
    property. *)
Theorem Store_StructPreciseTy_open_application_of_exactPushback
    {n : nat} {G : Ctx n} {s : Store n}
    {p q : Path n} {x y : Fin.t n} {S0 : Ty n}
    {U : Ty (S n)} {A : Ty n} {body : Tm (S n)}
    (Hstore : Store_StructPreciseTy G s)
    (Hpush : Store_StructExactFunctionPushback G s)
    (Hp : Path_reduce p s x) (Hq : Path_reduce q s y)
    (Hbind : Store_Binds s x (tm_abs A body))
    (Hfun : Tm_StructCheck G (Path_RuntimeEq s)
      (tm_path p) (ty_fun S0 U))
    (Harg : Tm_StructCheck G (Path_RuntimeEq s) (tm_path q) S0) :
    Tm_StructCheck G (Path_RuntimeEq s)
      (Tm_open body y) (Ty_open U q).
Proof.
  destruct (Store_StructPreciseTy_of_store_binds Hstore Hbind)
    as (P & Hctx & Hprecise).
  destruct (Tm_StructPrecise_abs_parts_exact Hprecise)
    as (B & HP & Hbody & HA).
  subst P.
  pose proof (Tm_StructCheck_reduce_path Hp Hfun) as HfunAtX.
  destruct (Hpush x S0 A U B body Hstore Hbind Hctx HfunAtX)
    as [Hdom Hcod].
  pose proof (Tm_StructCheck_reduce_path Hq Harg) as HargAtS.
  assert (HargAtA : Tm_StructCheck G (Path_RuntimeEq s)
      (tm_path (path_var y)) A).
  { eapply tm_struct_check_sub; eassumption. }
  pose proof (Tm_StructCheck_open_var_of_path_term Hbody
    (Path_RuntimeEq_isEquivCongr s) HargAtA) as Hopened.
  destruct (Tm_StructCheck_path_inversion Hfun eq_refl)
    as [Q Hcheck Hsingle HfunWf].
  exact (@Store_structResultOpening n G s q y S0 B U
    (Tm_open body y) Hq Harg HfunWf Hcod Hopened).
Qed.

Print Assumptions Store_StructPreciseTy_lookup_singleton.
Print Assumptions Store_StructPreciseTy_reduce_singleton.
Print Assumptions Store_StructPreciseTy_reduce_check_iff.
Print Assumptions Store_StructPreciseTy_runtimeEq_reduce_check_iff.
Print Assumptions
  Store_StructPreciseTy_headCheckReflection_of_singletonPushback.
Print Assumptions
  Store_StructPreciseSingletonFunctionPushback_to_exact.
Print Assumptions
  Store_StructPreciseTy_open_application_of_exactPushback.
