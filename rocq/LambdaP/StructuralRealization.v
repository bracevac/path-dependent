From Equations Require Import Equations.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store RuntimeConversion ScopedRuntimeEq
  StructuralRuntimeTyping StructuralTermTyping StructuralValueInversion
  StructuralResolution StructuralPreciseStore StructuralRefinedProgress.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** View a stored definition as a generalized path-resolution endpoint. *)
Definition Def_endpoint {n : nat} {k : Kind} (d : Def n k) :
    Path_Endpoint n :=
  match d with
  | def_val x => endpoint_val x
  | def_type T => endpoint_type T
  end.

(** A store location is a possible inhabitant of a proper type.  Function
    and pair cases retain exactly the syntactic residues needed by progress
    and beta preservation. *)
Inductive Store_Possible : forall {n : nat},
    Ctx n -> Store n -> Fin.t n -> Ty n -> Prop :=
| store_possible_top {n : nat} (G : Ctx n) (s : Store n)
    (x : Fin.t n) :
    Store_Possible G s x ty_top
| store_possible_fun {n : nat} (G : Ctx n) (s : Store n)
    (x : Fin.t n) (A : Ty n) (body : Tm (S n))
    (B : Ty (S n)) (S0 : Ty n) (U : Ty (S n)) :
    Store_Binds s x (tm_abs A body) ->
    Ctx_Binds G x (ty_fun A B) ->
    Tm_StructPrecise G (Path_RuntimeEq s)
      (tm_abs A body) (ty_fun A B) ->
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S0) (tau_ty A) ->
    Tau_StructSub (ctx_snoc G S0)
      (Path_ScopedLift (Path_RuntimeEq s)) (tau_ty B) (tau_ty U) ->
    Store_Possible G s x (ty_fun S0 U)
| store_possible_pair {n : nat} {k : Kind}
    (G : Ctx n) (s : Store n) (x y : Fin.t n) (a : Name)
    (delta : Def n k) (S0 : Ty n) (d : Tau (S n) k) :
    Store_Binds s x (tm_pair y a delta) ->
    Path_StructCheck G (Path_RuntimeEq s) (path_var y) (tau_ty S0) ->
    Store_Possible G s y S0 ->
    Path_Endpoint_Realizes G s (Def_endpoint delta)
      (Tau_open d (path_var y)) ->
    Store_Possible G s x (ty_pair S0 a d)
| store_possible_single {n : nat} (G : Ctx n) (s : Store n)
    (x : Fin.t n) (p : Path n) :
    Path_Resolve p s (endpoint_val x) ->
    Store_Possible G s x (ty_single p)
| store_possible_tsel {n : nat} (G : Ctx n) (s : Store n)
    (x : Fin.t n) (p : Path n) (A : Name) (W : Ty n) :
    Path_Resolve (path_sel p A) s (endpoint_type W) ->
    Store_Possible G s x W ->
    Store_Possible G s x (ty_tsel p A)
| store_possible_conv {n : nat} (G : Ctx n) (s : Store n)
    (x : Fin.t n) (S0 T : Ty n) :
    Store_Possible G s x S0 ->
    Tau_StructConv (Path_RuntimeEq s) (tau_ty S0) (tau_ty T) ->
    Store_Possible G s x T

(** A generalized resolution endpoint realizes a generalized type.  At
    proper kind this delegates to [Store_Possible]; at interval kind the
    stored definition is sandwiched between the advertised bounds. *)
with Path_Endpoint_Realizes : forall {n : nat} {k : Kind},
    Ctx n -> Store n -> Path_Endpoint n -> Tau n k -> Prop :=
| endpoint_realizes_val {n : nat} (G : Ctx n) (s : Store n)
    (x : Fin.t n) (T : Ty n) :
    Store_Possible G s x T ->
    Path_Endpoint_Realizes G s (endpoint_val x) (tau_ty T)
| endpoint_realizes_type {n : nat} (G : Ctx n) (s : Store n)
    (L W U : Ty n) :
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty L) (tau_ty W) ->
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty W) (tau_ty U) ->
    Path_Endpoint_Realizes G s (endpoint_type W) (tau_intv L U)
| endpoint_realizes_conv {n : nat} {k : Kind}
    (G : Ctx n) (s : Store n) (endpoint : Path_Endpoint n)
    (d1 d2 : Tau n k) :
    Path_Endpoint_Realizes G s endpoint d1 ->
    Tau_StructConv (Path_RuntimeEq s) d1 d2 ->
    Path_Endpoint_Realizes G s endpoint d2.

Arguments store_possible_top {n} G s x.
Arguments store_possible_fun {n} G s x A body B S0 U _ _ _ _ _.
Arguments store_possible_pair {n k} G s x y a delta S0 d _ _ _ _.
Arguments store_possible_single {n} G s x p _.
Arguments store_possible_tsel {n} G s x p A W _ _.
Arguments store_possible_conv {n} G s x S0 T _ _.
Arguments endpoint_realizes_val {n} G s x T _.
Arguments endpoint_realizes_type {n} G s L W U _ _.
Arguments endpoint_realizes_conv {n k} G s endpoint d1 d2 _ _.

(** The lower and upper components of an interval. *)
Local Definition Tau_intv_lower {n : nat} (d : Tau n iota) : Ty n :=
  match d with tau_intv L _ => L end.

Local Definition Tau_intv_upper {n : nat} (d : Tau n iota) : Ty n :=
  match d with tau_intv _ U => U end.

Local Definition Tau_StructConv_intv_motive {n : nat} {k : Kind}
    (R : Path n -> Path n -> Prop) (d1 d2 : Tau n k) : Prop :=
  match k as k' return Tau n k' -> Tau n k' -> Prop with
  | star => fun _ _ => True
  | iota => fun e1 e2 =>
      Tau_StructConv R (tau_ty (Tau_intv_lower e1))
        (tau_ty (Tau_intv_lower e2)) /\
      Tau_StructConv R (tau_ty (Tau_intv_upper e1))
        (tau_ty (Tau_intv_upper e2))
  end d1 d2.

(** Runtime conversion of intervals acts componentwise. *)
Local Theorem Tau_StructConv_intv_parts_aux {n : nat} {k : Kind}
    {R : Path n -> Path n -> Prop} {d1 d2 : Tau n k}
    (h : Tau_StructConv R d1 d2) :
    Tau_StructConv_intv_motive R d1 d2.
Proof.
  induction h.
  - destruct k; cbn [Tau_StructConv_intv_motive].
    + exact I.
    + split; apply tau_struct_conv_refl.
  - destruct k; cbn [Tau_StructConv_intv_motive] in *.
    + exact I.
    + destruct IHh as [Hlo Hhi].
      split; apply tau_struct_conv_symm; assumption.
  - destruct k; cbn [Tau_StructConv_intv_motive] in *.
    + exact I.
    + destruct IHh1 as [Hlo1 Hhi1].
      destruct IHh2 as [Hlo2 Hhi2].
      split; eapply tau_struct_conv_trans; eassumption.
  - destruct k; cbn [Tau_StructConv_intv_motive] in *.
    + exact I.
    + dependent elimination template.
      cbn [Tau_intv_lower Tau_intv_upper Tau_open Tau_subst].
      split.
      * exact (tau_struct_conv_replace (tau_ty t0) H).
      * exact (tau_struct_conv_replace (tau_ty t1) H).
Qed.

Theorem Tau_StructConv_intv_parts {n : nat}
    {R : Path n -> Path n -> Prop} {L1 U1 L2 U2 : Ty n}
    (h : Tau_StructConv R (tau_intv L1 U1) (tau_intv L2 U2)) :
    Tau_StructConv R (tau_ty L1) (tau_ty L2) /\
    Tau_StructConv R (tau_ty U1) (tau_ty U2).
Proof.
  exact (Tau_StructConv_intv_parts_aux h).
Qed.

Theorem Tau_StructConv_intv_lo {n : nat}
    {R : Path n -> Path n -> Prop} {L1 U1 L2 U2 : Ty n}
    (h : Tau_StructConv R (tau_intv L1 U1) (tau_intv L2 U2)) :
    Tau_StructConv R (tau_ty L1) (tau_ty L2).
Proof. exact (proj1 (Tau_StructConv_intv_parts h)). Qed.

Theorem Tau_StructConv_intv_hi {n : nat}
    {R : Path n -> Path n -> Prop} {L1 U1 L2 U2 : Ty n}
    (h : Tau_StructConv R (tau_intv L1 U1) (tau_intv L2 U2)) :
    Tau_StructConv R (tau_ty U1) (tau_ty U2).
Proof. exact (proj2 (Tau_StructConv_intv_parts h)). Qed.

(** The two endpoint-specific inversions packaged as one motive. *)
Local Definition Tau_star_type {n : nat} (d : Tau n star) : Ty n :=
  match d with tau_ty T => T end.

Local Definition Path_Endpoint_Realizes_Invariant {n : nat} {k : Kind}
    (G : Ctx n) (s : Store n) (endpoint : Path_Endpoint n)
    (d : Tau n k) : Prop :=
  match k as k' return Tau n k' -> Prop with
  | star => fun d0 => forall x : Fin.t n,
      endpoint = endpoint_val x ->
      Store_Possible G s x (Tau_star_type d0)
  | iota => fun d0 => forall W : Ty n,
      endpoint = endpoint_type W ->
      Tau_StructSub G (Path_RuntimeEq s)
        (tau_ty (Tau_intv_lower d0)) (tau_ty W) /\
      Tau_StructSub G (Path_RuntimeEq s)
        (tau_ty W) (tau_ty (Tau_intv_upper d0))
  end d.

Local Theorem Path_Endpoint_Realizes_invariant {n : nat} {k : Kind}
    {G : Ctx n} {s : Store n} {endpoint : Path_Endpoint n}
    {d : Tau n k} (h : Path_Endpoint_Realizes G s endpoint d) :
    Path_Endpoint_Realizes_Invariant G s endpoint d.
Proof.
  refine (Path_Endpoint_Realizes_ind
    (P := fun n0 k0 G0 s0 endpoint0 d0 =>
      Path_Endpoint_Realizes_Invariant G0 s0 endpoint0 d0)
    _ _ _ h).
  - intros n0 G0 s0 x T Hp x' E.
    injection E as Ex. subst x'. exact Hp.
  - intros n0 G0 s0 L W U Hlo Hhi W' E.
    injection E as EW. subst W'. exact (conj Hlo Hhi).
  - intros n0 k0 G0 s0 endpoint0 d1 d2 Hr IH Hconv.
    destruct k0.
    + dependent elimination d1. dependent elimination d2.
      cbn [Path_Endpoint_Realizes_Invariant] in *.
      intros x E.
      eapply store_possible_conv.
      * exact (IH x E).
      * exact Hconv.
    + dependent elimination d1. dependent elimination d2.
      cbn [Path_Endpoint_Realizes_Invariant] in *.
      intros W E.
      destruct (IH W E) as [Hlo Hhi].
      destruct (Tau_StructConv_intv_parts Hconv) as [Hconvlo Hconvhi].
      split.
      * eapply tau_struct_sub_trans.
        -- apply tau_struct_sub_conv.
           apply tau_struct_conv_symm. exact Hconvlo.
        -- exact Hlo.
      * eapply tau_struct_sub_trans.
        -- exact Hhi.
        -- apply tau_struct_sub_conv. exact Hconvhi.
Qed.

Theorem Path_Endpoint_Realizes_val_possible {n : nat}
    {G : Ctx n} {s : Store n} {x : Fin.t n} {T : Ty n}
    (h : Path_Endpoint_Realizes G s (endpoint_val x) (tau_ty T)) :
    Store_Possible G s x T.
Proof.
  exact (Path_Endpoint_Realizes_invariant h x eq_refl).
Qed.

(** Inversion of a realized type-definition endpoint, including trailing
    runtime conversion. *)
Theorem Path_Endpoint_Realizes_type_bounds {n : nat}
    {G : Ctx n} {s : Store n} {W L U : Ty n}
    (h : Path_Endpoint_Realizes G s (endpoint_type W) (tau_intv L U)) :
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty L) (tau_ty W) /\
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty W) (tau_ty U).
Proof.
  exact (Path_Endpoint_Realizes_invariant h W eq_refl).
Qed.

(** A syntax-directed value in an exact store inhabits its precise
    introduction type. *)
Theorem Tm_StructPrecise_possible_of_binds {n : nat}
    {G : Ctx n} {s : Store n} {v : Tm n} {P : Ty n}
    {x : Fin.t n}
    (hprecise : Tm_StructPrecise G (Path_RuntimeEq s) v P)
    (hbind : Store_Binds s x v)
    (hctx : Ctx_Binds G x P) :
    Store_Possible G s x P.
Proof.
  dependent elimination hprecise.
  - eapply store_possible_fun.
    + exact hbind.
    + exact hctx.
    + now apply tm_struct_precise_abs.
    + apply tau_struct_sub_refl.
    + apply tau_struct_sub_refl.
  - eapply store_possible_pair.
    + exact hbind.
    + eapply path_struct_check_promote.
      * eapply path_struct_check_var; eassumption.
      * apply tau_struct_sub_refl.
    + apply store_possible_single. apply path_resolve_var.
    + cbn [Def_endpoint].
      change (Path_Endpoint_Realizes G1 s (endpoint_val z)
        (Tau_open (Tau_weaken (tau_ty (ty_single (path_var z))))
          (path_var y))).
      rewrite Tau_weaken_open.
      apply endpoint_realizes_val.
      apply store_possible_single. apply path_resolve_var.
  - eapply store_possible_pair.
    + exact hbind.
    + eapply path_struct_check_promote.
      * eapply path_struct_check_var; eassumption.
      * apply tau_struct_sub_refl.
    + apply store_possible_single. apply path_resolve_var.
    + cbn [Def_endpoint].
      rewrite Tau_weaken_open.
      apply endpoint_realizes_type;
        apply tau_struct_sub_refl.
Qed.

(** Every exact context entry is a possible inhabitant at the aligned store
    location. *)
Theorem Store_StructPreciseTy_possible_of_ctx_binds {n : nat}
    {G : Ctx n} {s : Store n} {x : Fin.t n} {P : Ty n}
    (hstore : Store_StructPreciseTy G s)
    (hctx : Ctx_Binds G x P) :
    Store_Possible G s x P.
Proof.
  destruct (Store_StructPreciseTy_of_ctx_binds hstore hctx)
    as (v & hbind & hprecise).
  exact (Tm_StructPrecise_possible_of_binds hprecise hbind hctx).
Qed.

Print Assumptions Tau_StructConv_intv_parts.
Print Assumptions Path_Endpoint_Realizes_val_possible.
Print Assumptions Path_Endpoint_Realizes_type_bounds.
Print Assumptions Tm_StructPrecise_possible_of_binds.
Print Assumptions Store_StructPreciseTy_possible_of_ctx_binds.
