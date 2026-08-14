From PathDependent.LambdaP Require Import FinFun Syntax Context Typing Store
  RuntimeConversion PathReduction ScopedRuntimeEq StructuralRuntimeTyping
  StoreRefinement RefinedPathProgress StructuralRuntimeLemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Open a structural member-subtyping premise under the precise singleton
    binder, then transport only the target member along an ambient path
    equation. *)
Theorem Tau_StructSub_open_precise_member {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {y : Fin.t n} {r : Path n}
    {k : Kind} {d1 d2 : Tau (S n) k}
    (HR : Path_IsEquivCongr R)
    (H : Tau_StructSub (ctx_snoc G (ty_single (path_var y)))
      (Path_ScopedLift R) d1 d2)
    (Hyr : R (path_var y) r) :
    Tau_StructSub G R (Tau_open d1 (path_var y)) (Tau_open d2 r).
Proof.
  destruct (Ctx_Binds_exists G y) as [U Hy].
  assert (HyCheck : Path_StructCheck G R (path_var y) (tau_ty U)).
  { apply path_struct_check_var. exact Hy. }
  pose proof (Tau_StructSub_open_var_of_singleton H HR HyCheck
    (tau_struct_sub_refl G R
      (tau_ty (ty_single (path_var y))))) as Hopen.
  rewrite !Tau_rename_openAt_eq_open_var in Hopen.
  eapply tau_struct_sub_trans.
  - exact Hopen.
  - apply tau_struct_sub_conv.
    exact (tau_struct_conv_replace d2 Hyr).
Qed.

(** Runtime specialization using co-resolution of a reducing path. *)
Theorem Tau_StructSub_open_precise_member_runtime {n : nat}
    {G : Ctx n} {s : Store n} {y : Fin.t n} {r : Path n}
    {k : Kind} {d1 d2 : Tau (S n) k}
    (H : Tau_StructSub
      (ctx_snoc G (ty_single (path_var y)))
      (Path_ScopedLift (Path_RuntimeEq s)) d1 d2)
    (Hr : Path_reduce r s y) :
    Tau_StructSub G (Path_RuntimeEq s)
      (Tau_open d1 (path_var y)) (Tau_open d2 r).
Proof.
  eapply Tau_StructSub_open_precise_member.
  - exact (Path_RuntimeEq_isEquivCongr s).
  - exact H.
  - apply path_runtime_eq_symm. exact (Path_RuntimeEq_of_reduce Hr).
Qed.

(** Source pair-member subtyping embeds structurally and therefore enjoys
    runtime-aware two-path opening. *)
Theorem Tau_Sub_open_precise_member_runtime {n : nat}
    {G : Ctx n} {s : Store n} {y : Fin.t n} {r : Path n}
    {k : Kind} {d1 d2 : Tau (S n) k}
    (H : Tau_Sub (ctx_snoc G (ty_single (path_var y))) d1 d2)
    (Hr : Path_reduce r s y) :
    Tau_StructSub G (Path_RuntimeEq s)
      (Tau_open d1 (path_var y)) (Tau_open d2 r).
Proof.
  exact (@Tau_StructSub_open_precise_member_runtime n G s y r k d1 d2
    (Tau_StructSub_of_source H
      (Path_ScopedLift (Path_RuntimeEq s))) Hr).
Qed.

(** Concrete term-member instance for the syntax-directed singleton
    member. *)
Theorem Tau_Sub_open_precise_value_member_runtime {n : nat}
    {G : Ctx n} {s : Store n} {y z : Fin.t n} {r : Path n}
    {d : Tau (S n) star}
    (H : Tau_Sub (ctx_snoc G (ty_single (path_var y)))
      (Tau_weaken (tau_ty (ty_single (path_var z)))) d)
    (Hr : Path_reduce r s y) :
    Tau_StructSub G (Path_RuntimeEq s)
      (tau_ty (ty_single (path_var z))) (Tau_open d r).
Proof.
  pose proof (Tau_Sub_open_precise_member_runtime H Hr) as Hopen.
  rewrite Tau_weaken_open in Hopen. exact Hopen.
Qed.

(** Concrete type-member instance for the syntax-directed precise
    interval. *)
Theorem Tau_Sub_open_precise_type_member_runtime {n : nat}
    {G : Ctx n} {s : Store n} {y : Fin.t n} {r : Path n}
    {U : Ty n} {d : Tau (S n) iota}
    (H : Tau_Sub (ctx_snoc G (ty_single (path_var y)))
      (Tau_weaken (tau_intv U U)) d)
    (Hr : Path_reduce r s y) :
    Tau_StructSub G (Path_RuntimeEq s)
      (tau_intv U U) (Tau_open d r).
Proof.
  pose proof (Tau_Sub_open_precise_member_runtime H Hr) as Hopen.
  rewrite Tau_weaken_open in Hopen. exact Hopen.
Qed.

(** Runtime pair-check reflection at an already resolved variable. *)
Definition Store_PairCheckReflection {n : nat}
    (G : Ctx n) (s : Store n) : Prop :=
  forall (x : Fin.t n) (S0 : Ty n) (a : Name)
    (k : Kind) (d : Tau (S n) k),
    Path_StructCheck G (Path_RuntimeEq s) (path_var x)
      (tau_ty (ty_pair S0 a d)) ->
    exists (y : Fin.t n) (delta : Def n k),
      Store_Binds s x (@tm_pair n k y a delta).

(** Refined store typing plus the minimal pair-check reflection property. *)
Record Store_RefinedPairSimulation {n : nat}
    (G : Ctx n) (s : Store n) : Prop := {
  store_refined_pair_simulation_refined : Store_RefinedTy G s;
  store_refined_pair_simulation_reflect : Store_PairCheckReflection G s
}.

(** The structural simulation yields the weak pair-transport contract. *)
Theorem Store_RefinedPairSimulation_pairTransport {n : nat}
    {G : Ctx n} {s : Store n}
    (H : Store_RefinedPairSimulation G s) : Path_PairTransport G s.
Proof.
  intros p x S0 a k d Hr Hp.
  pose proof (store_refined_pair_simulation_reflect H) as Hreflect.
  unfold Store_PairCheckReflection in Hreflect.
  eapply Hreflect.
  apply (Path_StructCheck_reduce_to_var Hr).
  exact (Path_StructCheck_of_source Hp (Path_RuntimeEq s)).
Qed.

(** Refined-store path progress follows from the local reflection premise. *)
Theorem Path_reduce_progress_refined_of_simulation {n : nat}
    {G : Ctx n} {s : Store n} {p : Path n} {T : Ty n}
    (H : Store_RefinedPairSimulation G s)
    (Hp : Path_Ty G p (tau_ty T)) :
    exists x, Path_reduce p s x.
Proof.
  exact (Path_reduce_progress_refined_of_pairTransport
    (store_refined_pair_simulation_refined H)
    (Store_RefinedPairSimulation_pairTransport H) Hp).
Qed.

Print Assumptions Tau_StructSub_open_precise_member.
Print Assumptions Tau_StructSub_open_precise_member_runtime.
Print Assumptions Tau_Sub_open_precise_value_member_runtime.
Print Assumptions Tau_Sub_open_precise_type_member_runtime.
Print Assumptions Store_RefinedPairSimulation_pairTransport.
Print Assumptions Path_reduce_progress_refined_of_simulation.
