From Equations Require Import Equations.
From PathDependent.LambdaP Require Import FinFun Syntax Context Typing Store
  Renaming RuntimeConversion ScopedRuntimeEq StructuralRuntimeTyping
  StructuralTermTyping StructuralRuntimeLemmas StructuralMachineInvariant
  Canonical.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Local Coercion FinFun.apply : FinFun.t >-> Funclass.

(** The type assigned directly by a structural value-introduction rule. *)
Inductive Tm_StructPrecise : forall {n : nat}, Ctx n ->
    (Path n -> Path n -> Prop) -> Tm n -> Ty n -> Prop :=
| tm_struct_precise_abs {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (S0 : Ty n)
    (t : Tm (S n)) (T : Ty (S n)) :
    Tm_StructCheck (ctx_snoc G S0) (Path_ScopedLift R) t T ->
    Tau_StructWf G R (tau_ty S0) ->
    Tm_StructPrecise G R (tm_abs S0 t) (ty_fun S0 T)
| tm_struct_precise_pair {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (y z : Fin.t n)
    (S0 T : Ty n) (a : Name) :
    Ctx_Binds G y S0 -> Ctx_Binds G z T ->
    Tm_StructPrecise G R (tm_pair y a (def_val z))
      (ty_pair (ty_single (path_var y)) a
        (tau_ty (ty_single (Path_weaken (path_var z)))))
| tm_struct_precise_tpair {n : nat} (G : Ctx n)
    (R : Path n -> Path n -> Prop) (y : Fin.t n)
    (S0 T : Ty n) (A : Name) :
    Ctx_Binds G y S0 -> Tau_StructWf G R (tau_ty T) ->
    Tm_StructPrecise G R (tm_pair y A (def_type T))
      (ty_pair (ty_single (path_var y)) A
        (Tau_weaken (tau_intv T T))).

Arguments tm_struct_precise_abs {n} G R S0 t T _ _.
Arguments tm_struct_precise_pair {n} G R y z S0 T a _ _.
Arguments tm_struct_precise_tpair {n} G R y S0 T A _ _.

Theorem Tm_StructPrecise_isValue {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {v : Tm n} {P : Ty n}
    (H : Tm_StructPrecise G R v P) : Tm_IsValue v.
Proof.
  destruct H.
  - apply value_abs.
  - apply value_pair.
  - apply value_pair.
Qed.

(** Forgetting precision recovers structural checking. *)
Theorem Tm_StructPrecise_toStructCheck {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {v : Tm n} {P : Ty n}
    (H : Tm_StructPrecise G R v P) : Tm_StructCheck G R v P.
Proof.
  destruct H.
  - now apply tm_struct_check_abs.
  - eapply tm_struct_check_pair; eassumption.
  - eapply tm_struct_check_tpair; eassumption.
Qed.

(** Exact relation-respecting renaming for structural precise values. *)
Theorem Tm_StructPrecise_renameExact {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {v : Tm n} {P : Ty n}
    (H : Tm_StructPrecise G R v P) :
    forall {m : nat} {f : FinFun.t n m} {D : Ctx m}
      {E : Path m -> Path m -> Prop},
      Renaming G f D -> Path_RelHom R E f ->
      Tm_StructPrecise D E (Tm_rename v f) (Ty_rename P f).
Proof.
  destruct H; intros m f D E rho Hrel.
  - cbn [Tm_rename Ty_rename]. apply tm_struct_precise_abs.
    + exact (Tm_StructCheck_renameExact H (Renaming_ext rho)
        (Path_RelHom_scoped Hrel)).
    + exact (Tau_StructWf_renameExact H0 rho Hrel).
  - cbn [Tm_rename Def_rename Ty_rename Tau_rename Path_rename].
    rewrite <- Path_weaken_rename.
    eapply tm_struct_precise_pair.
    + exact (rho y S0 H).
    + exact (rho z T H0).
  - cbn [Tm_rename Def_rename Ty_rename Tau_rename Path_rename].
    rewrite <- Tau_weaken_rename.
    eapply tm_struct_precise_tpair.
    + exact (rho y S0 H).
    + exact (Tau_StructWf_renameExact H0 rho Hrel).
Qed.

(** Runtime-store growth weakens the precise witness together with its
    context and concrete runtime relation. *)
Theorem Tm_StructPrecise_weaken_runtime {n : nat} {G : Ctx n}
    {s : Store n} {v : Tm n} {P : Ty n}
    (H : Tm_StructPrecise G (Path_RuntimeEq s) v P)
    (S0 : Ty n) (u : Tm n) (Hu : Tm_IsValue u) :
    Tm_StructPrecise (ctx_snoc G S0)
      (Path_RuntimeEq (store_val s u Hu)) (Tm_weaken v) (Ty_weaken P).
Proof.
  unfold Tm_weaken, Ty_weaken.
  exact (Tm_StructPrecise_renameExact H
    (@Renaming_weaken n G S0)
    (Path_RelHom_runtime_weaken (v := u) Hu)).
Qed.

(** Every structural checking derivation of a value factors through its
    syntax-directed introduction type. *)
Theorem Tm_StructCheck_value_inversion {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {v : Tm n} {T : Ty n}
    (H : Tm_StructCheck G R v T) (Hv : Tm_IsValue v) :
    exists P,
      Tm_StructPrecise G R v P /\
      Tau_StructSub G R (tau_ty P) (tau_ty T).
Proof.
  induction H.
  - inversion Hv.
  - exists (ty_fun S0 T). split.
    + now apply tm_struct_precise_abs.
    + apply tau_struct_sub_refl.
  - inversion Hv.
  - exists (ty_pair (ty_single (path_var y)) a
      (tau_ty (ty_single (Path_weaken (path_var z))))).
    split.
    + eapply tm_struct_precise_pair; eassumption.
    + apply tau_struct_sub_refl.
  - exists (ty_pair (ty_single (path_var y)) A
      (Tau_weaken (tau_intv T T))).
    split.
    + eapply tm_struct_precise_tpair; eassumption.
    + apply tau_struct_sub_refl.
  - inversion Hv.
  - inversion Hv.
  - destruct (IHTm_StructCheck Hv) as (P & Hp & Hsub).
    exists P. split.
    + exact Hp.
    + eapply tau_struct_sub_trans; eassumption.
Qed.

(** Every location of a structurally typed store has public and precise
    checking witnesses in the current store scope. *)
Theorem Store_StructTy_lookup_exists {n : nat} {G : Ctx n}
    {s : Store n} (H : Store_StructTy G s) (x : Fin.t n) :
    exists (v : Tm n) (T P : Ty n),
      Store_Binds s x v /\
      Ctx_Binds G x T /\
      Tm_StructCheck G (Path_RuntimeEq s) v T /\
      Tm_StructPrecise G (Path_RuntimeEq s) v P /\
      Tau_StructSub G (Path_RuntimeEq s) (tau_ty P) (tau_ty T).
Proof.
  induction H.
  - exact (Fin.elim0 x).
  - refine (@Fin.cases' n x
      (fun x => exists (u : Tm (S n)) (U Q : Ty (S n)),
        Store_Binds (store_val s v Hv) x u /\
        Ctx_Binds (ctx_snoc G T) x U /\
        Tm_StructCheck (ctx_snoc G T)
          (Path_RuntimeEq (store_val s v Hv)) u U /\
        Tm_StructPrecise (ctx_snoc G T)
          (Path_RuntimeEq (store_val s v Hv)) u Q /\
        Tau_StructSub (ctx_snoc G T)
          (Path_RuntimeEq (store_val s v Hv))
          (tau_ty Q) (tau_ty U)) _ _).
    + destruct (Tm_StructCheck_value_inversion H0 Hv)
        as (P & Hprecise & Hsub).
      exists (Tm_weaken v), (Ty_weaken T), (Ty_weaken P).
      repeat split.
      * apply store_binds_here.
      * apply binds_here.
      * exact (Tm_StructCheck_weaken_runtime H0 T (v := v) Hv).
      * exact (Tm_StructPrecise_weaken_runtime Hprecise T (u := v) Hv).
      * exact (Tau_StructSub_weaken_runtime Hsub T (v := v) Hv).
    + intro y.
      destruct (IHStore_StructTy y)
        as (u & U & P & Hu & HU & Hcheck & Hprecise & Hsub).
      exists (Tm_weaken u), (Ty_weaken U), (Ty_weaken P).
      repeat split.
      * apply store_binds_there. exact Hu.
      * apply binds_there. exact HU.
      * exact (Tm_StructCheck_weaken_runtime Hcheck T (v := v) Hv).
      * exact (Tm_StructPrecise_weaken_runtime Hprecise T (u := v) Hv).
      * exact (Tau_StructSub_weaken_runtime Hsub T (v := v) Hv).
Qed.

(** A concrete store lookup recovers its aligned public context type and
    precise structural factorization. *)
Theorem Store_StructTy_of_store_binds {n : nat} {G : Ctx n}
    {s : Store n} {x : Fin.t n} {v : Tm n}
    (H : Store_StructTy G s) (Hb : Store_Binds s x v) :
    exists T P,
      Ctx_Binds G x T /\
      Tm_StructCheck G (Path_RuntimeEq s) v T /\
      Tm_StructPrecise G (Path_RuntimeEq s) v P /\
      Tau_StructSub G (Path_RuntimeEq s) (tau_ty P) (tau_ty T).
Proof.
  destruct (Store_StructTy_lookup_exists H x)
    as (u & T & P & Hu & HT & Hcheck & Hprecise & Hsub).
  pose proof (Store_Binds_unique Hu Hb) as E. subst u.
  exists T, P. repeat split; assumption.
Qed.

(** A public context lookup recovers the matching stored value and the same
    current-scope factorization. *)
Theorem Store_StructTy_of_ctx_binds {n : nat} {G : Ctx n}
    {s : Store n} {x : Fin.t n} {T : Ty n}
    (H : Store_StructTy G s) (Hb : Ctx_Binds G x T) :
    exists v P,
      Store_Binds s x v /\
      Tm_StructCheck G (Path_RuntimeEq s) v T /\
      Tm_StructPrecise G (Path_RuntimeEq s) v P /\
      Tau_StructSub G (Path_RuntimeEq s) (tau_ty P) (tau_ty T).
Proof.
  destruct (Store_StructTy_lookup_exists H x)
    as (v & U & P & Hv & HU & Hcheck & Hprecise & Hsub).
  pose proof (Ctx_Binds_unique HU Hb) as E. subst U.
  exists v, P. repeat split; assumption.
Qed.

(** A source-subtyping suffix from a precise structural value to a function
    type forces an abstraction. *)
Theorem Tm_StructPrecise_fun_canonical_source {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {v : Tm n} {P S0 : Ty n}
    {T : Ty (S n)}
    (Hp : Tm_StructPrecise G R v P)
    (Hs : Tau_Sub G (tau_ty P) (tau_ty (ty_fun S0 T))) :
    exists (A : Ty n) (body : Tm (S n)) (B : Ty (S n)),
      v = tm_abs A body /\
      P = ty_fun A B /\
      Tm_StructCheck (ctx_snoc G A) (Path_ScopedLift R) body B /\
      Tau_StructWf G R (tau_ty A).
Proof.
  dependent elimination Hp.
  - exists S1, t, T0. repeat split.
    + exact t0.
    + exact t1.
  - exfalso. exact (Tau_Sub_pair_not_fun Hs).
  - exfalso. exact (Tau_Sub_pair_not_fun Hs).
Qed.

(** A source-subtyping suffix to a pair preserves the label and the
    term/type definition distinction. *)
Theorem Tm_StructPrecise_pair_canonical_source {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {v : Tm n} {P S0 : Ty n}
    {a : Name} {k : Kind} {d : Tau (S n) k}
    (Hp : Tm_StructPrecise G R v P)
    (Hs : Tau_Sub G (tau_ty P) (tau_ty (ty_pair S0 a d))) :
    (exists y z,
      v = tm_pair y a (def_val z) /\
      P = ty_pair (ty_single (path_var y)) a
        (tau_ty (ty_single (Path_weaken (path_var z))))) \/
    (exists y U,
      v = tm_pair y a (def_type U) /\
      P = ty_pair (ty_single (path_var y)) a
        (Tau_weaken (tau_intv U U))).
Proof.
  dependent elimination Hp.
  - exfalso. exact (Tau_Sub_fun_not_pair Hs).
  - pose proof (Tau_Sub_pair_label Hs) as E. subst a.
    left. exists y, z. split; reflexivity.
  - pose proof (Tau_Sub_pair_label Hs) as E. subst a.
    right. exists y0, T1. split; reflexivity.
Qed.

(** Runtime equations are typing-valid for a structurally typed store when
    they transport every structural path check in both directions. *)
Definition Store_StructTy_RuntimePathValid {n : nat}
    (G : Ctx n) (s : Store n) : Prop :=
  forall (k : Kind) (p q : Path n) (d : Tau n k),
    Path_RuntimeEq s p q ->
    (Path_StructCheck G (Path_RuntimeEq s) p d <->
      Path_StructCheck G (Path_RuntimeEq s) q d).

Print Assumptions Tm_StructPrecise_renameExact.
Print Assumptions Tm_StructPrecise_weaken_runtime.
Print Assumptions Tm_StructCheck_value_inversion.
Print Assumptions Store_StructTy_lookup_exists.
Print Assumptions Store_StructTy_of_store_binds.
Print Assumptions Store_StructTy_of_ctx_binds.
Print Assumptions Tm_StructPrecise_fun_canonical_source.
Print Assumptions Tm_StructPrecise_pair_canonical_source.
