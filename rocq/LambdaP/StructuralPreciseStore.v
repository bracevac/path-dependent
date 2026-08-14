From Stdlib Require Import Lists.List.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store Renaming Cont State Machine
  RuntimeConversion ScopedRuntimeEq StructuralRuntimeTyping
  StructuralTermTyping StructuralRuntimeLemmas StructuralMachineInvariant
  StructuralNarrowing StructuralValueInversion.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** A store and context built in lockstep from exact structural
    value-introduction types. *)
Inductive Store_StructPreciseTy : forall {n : nat},
    Ctx n -> Store n -> Prop :=
| store_struct_precise_ty_empty :
    Store_StructPreciseTy ctx_nil store_empty
| store_struct_precise_ty_val {n : nat} (G : Ctx n) (s : Store n)
    (v : Tm n) (P : Ty n) (Hv : Tm_IsValue v) :
    Store_StructPreciseTy G s ->
    Tm_StructPrecise G (Path_RuntimeEq s) v P ->
    Store_StructPreciseTy (ctx_snoc G P) (store_val s v Hv).

Arguments store_struct_precise_ty_val {n} G s v P Hv _ _.

(** Forgetting exact introduction types yields ordinary structural store
    typing at the same context. *)
Theorem Store_StructPreciseTy_toStructTy {n : nat} {G : Ctx n}
    {s : Store n} (H : Store_StructPreciseTy G s) : Store_StructTy G s.
Proof.
  induction H.
  - apply store_struct_ty_empty.
  - eapply store_struct_ty_val.
    + exact IHStore_StructPreciseTy.
    + exact (Tm_StructPrecise_toStructCheck H0).
Qed.

(** Every precise store location has aligned bindings and an exact witness
    transported to the current intrinsic scope. *)
Theorem Store_StructPreciseTy_lookup_exists {n : nat} {G : Ctx n}
    {s : Store n} (H : Store_StructPreciseTy G s) (x : Fin.t n) :
    exists (v : Tm n) (P : Ty n),
      Store_Binds s x v /\
      Ctx_Binds G x P /\
      Tm_StructPrecise G (Path_RuntimeEq s) v P.
Proof.
  induction H.
  - exact (Fin.elim0 x).
  - refine (@Fin.cases' n x
      (fun x => exists (u : Tm (S n)) (Q : Ty (S n)),
        Store_Binds (store_val s v Hv) x u /\
        Ctx_Binds (ctx_snoc G P) x Q /\
        Tm_StructPrecise (ctx_snoc G P)
          (Path_RuntimeEq (store_val s v Hv)) u Q) _ _).
    + exists (Tm_weaken v), (Ty_weaken P). repeat split.
      * apply store_binds_here.
      * apply binds_here.
      * exact (Tm_StructPrecise_weaken_runtime H0 P (u := v) Hv).
    + intro y.
      destruct (IHStore_StructPreciseTy y)
        as (u & U & Hu & HU & Hprecise).
      exists (Tm_weaken u), (Ty_weaken U). repeat split.
      * apply store_binds_there. exact Hu.
      * apply binds_there. exact HU.
      * exact (Tm_StructPrecise_weaken_runtime Hprecise P (u := v) Hv).
Qed.

(** Concrete store-binding inversion in the full current store scope. *)
Theorem Store_StructPreciseTy_of_store_binds {n : nat} {G : Ctx n}
    {s : Store n} {x : Fin.t n} {v : Tm n}
    (H : Store_StructPreciseTy G s) (Hb : Store_Binds s x v) :
    exists P,
      Ctx_Binds G x P /\
      Tm_StructPrecise G (Path_RuntimeEq s) v P.
Proof.
  destruct (Store_StructPreciseTy_lookup_exists H x)
    as (u & P & Hu & HP & Hprecise).
  pose proof (Store_Binds_unique Hu Hb) as E. subst u.
  now exists P.
Qed.

(** A precise-context binding identifies the aligned stored value and exact
    current-scope introduction witness. *)
Theorem Store_StructPreciseTy_of_ctx_binds {n : nat} {G : Ctx n}
    {s : Store n} {x : Fin.t n} {P : Ty n}
    (H : Store_StructPreciseTy G s) (Hb : Ctx_Binds G x P) :
    exists v,
      Store_Binds s x v /\
      Tm_StructPrecise G (Path_RuntimeEq s) v P.
Proof.
  destruct (Store_StructPreciseTy_lookup_exists H x)
    as (v & U & Hv & HU & Hprecise).
  pose proof (Ctx_Binds_unique HU Hb) as E. subst U.
  now exists v.
Qed.

(** Aligned lookups force their exact introduction witness. *)
Theorem Store_StructPreciseTy_lookup {n : nat} {G : Ctx n}
    {s : Store n} {x : Fin.t n} {v : Tm n} {P : Ty n}
    (H : Store_StructPreciseTy G s)
    (Hs : Store_Binds s x v) (Hc : Ctx_Binds G x P) :
    Tm_StructPrecise G (Path_RuntimeEq s) v P.
Proof.
  destruct (Store_StructPreciseTy_of_store_binds H Hs)
    as (U & HU & Hprecise).
  pose proof (Ctx_Binds_unique HU Hc) as E. subst U. exact Hprecise.
Qed.

(** Precise store typing retains the value-existence fact needed for
    machine progress. *)
Theorem Store_StructPreciseTy_lookup_value {n : nat} {G : Ctx n}
    {s : Store n} (H : Store_StructPreciseTy G s) (x : Fin.t n) :
    exists v, Store_Binds s x v /\ Tm_IsValue v.
Proof.
  destruct (Store_StructPreciseTy_lookup_exists H x)
    as (v & P & Hv & HP & Hprecise).
  exists v. split.
  - exact Hv.
  - exact (Tm_StructPrecise_isValue Hprecise).
Qed.

(** Structural state typing whose store context contains exact value
    introduction types. *)
Inductive State_PreciseStructTy {n : nat} (G : Ctx n)
    (st : State n) (T : Ty n) : Prop :=
| state_precise_struct_ty_ok (S0 : Ty n) :
    Store_StructPreciseTy G (state_store st) ->
    Tm_Cont_StructTy G (state_store st) S0 (state_cont st) T ->
    Tm_StructCheck G (Path_RuntimeEq (state_store st))
      (state_term st) S0 ->
    State_PreciseStructTy G st T.

Arguments state_precise_struct_ty_ok {n G st T} S0 _ _ _.

(** Forgetting store precision recovers ordinary structural state typing. *)
Theorem State_PreciseStructTy_toStructTy {n : nat} {G : Ctx n}
    {st : State n} {T : Ty n} (H : State_PreciseStructTy G st T) :
    State_StructTy G st T.
Proof.
  destruct H as [S0 Hstore Hcont Hterm].
  eapply state_struct_ty_ok.
  - exact (Store_StructPreciseTy_toStructTy Hstore).
  - exact Hcont.
  - exact Hterm.
Qed.

(** Preservation for precise states either keeps the scope or appends one
    exact introduction type. *)
Inductive PreciseStructPreserve : forall {n m : nat},
    Ctx n -> State m -> Ty n -> Prop :=
| precise_struct_preserve_same {n : nat} {G : Ctx n}
    {st : State n} {T : Ty n} :
    State_PreciseStructTy G st T -> PreciseStructPreserve G st T
| precise_struct_preserve_extend {n : nat} {G : Ctx n}
    {P T : Ty n} {st : State (S n)} :
    State_PreciseStructTy (ctx_snoc G P) st (Ty_weaken T) ->
    PreciseStructPreserve G st T.

Arguments precise_struct_preserve_same {n G st T} _.
Arguments precise_struct_preserve_extend {n G P T st} _.

Theorem PreciseStructPreserve_toStructPreserve {n m : nat}
    {G : Ctx n} {st : State m} {T : Ty n}
    (H : PreciseStructPreserve G st T) : StructPreserve G st T.
Proof.
  destruct H.
  - apply struct_preserve_same.
    exact (State_PreciseStructTy_toStructTy H).
  - apply (struct_preserve_extend (S0 := P)).
    exact (State_PreciseStructTy_toStructTy H).
Qed.

(** Scoped pre-allocation runtime equations map into the concrete relation
    of the extended store. *)
Local Theorem Path_RelHom_structPrecise_scoped_to_runtime {n : nat}
    {s : Store n} {v : Tm n} {Hv : Tm_IsValue v} :
    Path_RelHom (Path_ScopedLift (Path_RuntimeEq s))
      (Path_RuntimeEq (store_val s v Hv)) (FinFun.id (S n)).
Proof.
  intros p q Hpq. rewrite !Path_rename_id.
  exact (Path_ScopedLift_to_runtime_extension Hpq).
Qed.

(** Allocation preserves precise structural state typing after value
    inversion, structural narrowing, and runtime-relation transport. *)
Theorem PreciseStructPreserve_lift {n : nat} {G : Ctx n}
    {s : Store n} {K : Tm_Cont n} {v : Tm n}
    {t : Tm (S n)} {T : Ty n}
    (Hv : Tm_IsValue v)
    (H : State_PreciseStructTy G
      (mk_state s (cons (tm_frame_let t) K) v) T) :
    PreciseStructPreserve G
      (mk_state (store_val s v Hv) (Tm_Cont_weaken K) t) T.
Proof.
  destruct H as [Input Hstore Hcont Hvalue].
  inversion Hcont as [|S0 U T0 F Ktail Hrest Hframe]; subst.
  inversion Hframe as [Input0 Result body Hbody]; subst.
  destruct (Tm_StructCheck_value_inversion Hvalue Hv)
    as (P & Hprecise & Hsub).
  pose proof (Tm_StructCheck_narrow Hbody Hsub) as HbodyNarrow.
  pose proof (Tm_StructCheck_renameExact HbodyNarrow
    (@Renaming_id (S n) (ctx_snoc G P))
    (@Path_RelHom_structPrecise_scoped_to_runtime n s v Hv))
    as HbodyRuntime.
  apply (precise_struct_preserve_extend (P := P)).
  eapply state_precise_struct_ty_ok.
  - eapply store_struct_precise_ty_val; eassumption.
  - exact (Tm_Cont_StructTy_weaken_runtime Hrest (v := v) Hv).
  - rewrite Tm_rename_id, Ty_rename_id in HbodyRuntime.
    exact HbodyRuntime.
Qed.

(** Packaging for the corresponding machine allocation step. *)
Theorem State_Step_precise_lift_preservation {n : nat} {G : Ctx n}
    {s : Store n} {K : Tm_Cont n} {v : Tm n}
    {t : Tm (S n)} {T : Ty n} {Hv : Tm_IsValue v}
    (step : State_Step
      (mk_state s (cons (tm_frame_let t) K) v)
      (mk_state (store_val s v Hv) (Tm_Cont_weaken K) t))
    (H : State_PreciseStructTy G
      (mk_state s (cons (tm_frame_let t) K) v) T) :
    PreciseStructPreserve G
      (mk_state (store_val s v Hv) (Tm_Cont_weaken K) t) T.
Proof.
  exact (PreciseStructPreserve_lift Hv H).
Qed.

Print Assumptions Store_StructPreciseTy_toStructTy.
Print Assumptions Store_StructPreciseTy_lookup_exists.
Print Assumptions Store_StructPreciseTy_of_store_binds.
Print Assumptions Store_StructPreciseTy_of_ctx_binds.
Print Assumptions Store_StructPreciseTy_lookup.
Print Assumptions Store_StructPreciseTy_lookup_value.
Print Assumptions State_PreciseStructTy_toStructTy.
Print Assumptions PreciseStructPreserve_toStructPreserve.
Print Assumptions PreciseStructPreserve_lift.
Print Assumptions State_Step_precise_lift_preservation.
