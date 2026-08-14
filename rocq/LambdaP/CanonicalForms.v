From Stdlib Require Import Arith.PeanoNat.
From Equations Require Import Equations.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store PathReduction RuntimeConversion
  ScopedRuntimeEq StructuralRuntimeTyping StructuralTermTyping
  StructuralValueInversion StructuralResolution StructuralPreciseStore
  StructuralRealization Realization StructuralPreciseCanonical
  StructuralPreciseSafety.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Semantic interpretation of a subtype whose source is an exact store
    location.  This is the common canonical-forms step for functions and
    pairs. *)
Theorem Tau_StructSub_mappedPossible_of_singleton {n : nat}
    {G : Ctx n} {s : Store n} {x : Fin.t n} {T : Ty n}
    (hstore : Store_StructPreciseTy G s)
    (hsub : Tau_StructSub G (Path_RuntimeEq s)
      (tau_ty (ty_single (path_var x))) (tau_ty T)) :
    Store_MappedPossible G s x T.
Proof.
  pose proof (Tau_SemMap_action (Tau_StructSub_mapped hstore hsub)
    (endpoint_mapped_realizes_val
      (store_mapped_possible_single G (path_resolve_var x s)))) as htarget.
  dependent elimination htarget. assumption.
Qed.

(** Exact stores satisfy both concrete-head observations used by progress. *)
Theorem Store_StructPreciseTy_mapped_singletonHeadPushback {n : nat}
    {G : Ctx n} {s : Store n}
    (hstore : Store_StructPreciseTy G s) :
    Store_StructPreciseSingletonHeadPushback G s.
Proof.
  constructor.
  - intros x S0 U _ hsub.
    pose proof (Tau_StructSub_mappedPossible_of_singleton hstore hsub)
      as hpossible.
    destruct (Store_MappedPossible_fun_binding hpossible)
      as (A & body & hbind).
    now exists A, body.
  - intros x S0 a k d _ hsub.
    pose proof (Tau_StructSub_mappedPossible_of_singleton hstore hsub)
      as hpossible.
    destruct (Store_MappedPossible_pair_binding hpossible)
      as (y & delta & hbind).
    now exists y, delta.
Qed.

(** A singleton-to-function map exposes the stored closure's exact
    signature. *)
Theorem Store_StructPreciseTy_mapped_singletonFunctionPushback {n : nat}
    {G : Ctx n} {s : Store n}
    (hstore : Store_StructPreciseTy G s) :
    Store_StructPreciseSingletonFunctionPushback G s.
Proof.
  intros x S0 A U B _ hctx hsub.
  pose proof (Tau_StructSub_mappedPossible_of_singleton hstore hsub)
    as hpossible.
  destruct (Store_MappedPossible_function_signature hpossible)
    as (A' & body & B' & hbind & hctx' & hprecise & hdom & hcod).
  pose proof (Ctx_Binds_unique hctx' hctx) as E.
  injection E as EA EB.
  assert (EA' : A' = A).
  { exact (@Eqdep_dec.inj_pair2_eq_dec nat Nat.eq_dec
      (fun j => Ty j) n A' A EA). }
  assert (EB' : B' = B).
  { exact (@Eqdep_dec.inj_pair2_eq_dec nat Nat.eq_dec
      (fun j => Ty (S j)) n B' B EB). }
  subst A'. subst B'. exact (conj hdom hcod).
Qed.

(** Exact function pushback, in the interface consumed by beta
    preservation. *)
Theorem Store_StructPreciseTy_mapped_exactFunctionPushback {n : nat}
    {G : Ctx n} {s : Store n}
    (hstore : Store_StructPreciseTy G s) :
    Store_StructExactFunctionPushback G s.
Proof.
  exact (Store_StructPreciseSingletonFunctionPushback_to_exact
    (Store_StructPreciseTy_mapped_singletonFunctionPushback hstore)).
Qed.

(** The semantic-map fundamental theorem discharges all conditional
    canonical assumptions in finite-run safety. *)
Theorem Store_mappedPreciseStructSafetyLaws :
    Store_PreciseStructSafetyLaws.
Proof.
  constructor.
  - intros n G s hstore.
    exact (Store_StructPreciseTy_mapped_singletonHeadPushback hstore).
  - intros n G s hstore.
    exact (Store_StructPreciseTy_mapped_exactFunctionPushback hstore).
Qed.

Print Assumptions Tau_StructSub_mappedPossible_of_singleton.
Print Assumptions Store_StructPreciseTy_mapped_singletonHeadPushback.
Print Assumptions Store_StructPreciseTy_mapped_singletonFunctionPushback.
Print Assumptions Store_StructPreciseTy_mapped_exactFunctionPushback.
Print Assumptions Store_mappedPreciseStructSafetyLaws.
