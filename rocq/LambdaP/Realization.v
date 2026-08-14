From Equations Require Import Equations.
From PathDependent.LambdaP Require Import
  FinFun Syntax Context Typing Store PathReduction RuntimeConversion ScopedRuntimeEq
  StructuralRuntimeTyping StructuralTermTyping StructuralValueInversion
  StructuralResolution StructuralPreciseStore StructuralRefinedProgress
  StructuralRealization StructuralPathSubstitution
  StructuralConversionInversion StructuralNarrowing.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

Local Coercion FinFun.apply : FinFun.t >-> Funclass.

(** Canonical, conversion-normalized evidence that a store location
    inhabits a proper type. *)
Inductive Store_MappedPossible : forall {n : nat},
    Ctx n -> Store n -> Fin.t n -> Ty n -> Prop :=
| store_mapped_possible_top {n : nat} (G : Ctx n) (s : Store n)
    (x : Fin.t n) :
    Store_MappedPossible G s x ty_top
| store_mapped_possible_fun {n : nat} (G : Ctx n) (s : Store n)
    (x : Fin.t n) (A : Ty n) (body : Tm (S n))
    (B : Ty (S n)) (S0 : Ty n) (U : Ty (S n)) :
    Store_Binds s x (tm_abs A body) ->
    Ctx_Binds G x (ty_fun A B) ->
    Tm_StructPrecise G (Path_RuntimeEq s)
      (tm_abs A body) (ty_fun A B) ->
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S0) (tau_ty A) ->
    Tau_StructSub (ctx_snoc G S0)
      (Path_ScopedLift (Path_RuntimeEq s)) (tau_ty B) (tau_ty U) ->
    Store_MappedPossible G s x (ty_fun S0 U)
| store_mapped_possible_pair {n : nat} {k : Kind}
    (G : Ctx n) (s : Store n) (x y : Fin.t n) (a : Name)
    (delta : Def n k) (S0 : Ty n) (d : Tau (S n) k) :
    Store_Binds s x (tm_pair y a delta) ->
    Path_StructCheck G (Path_RuntimeEq s) (path_var y) (tau_ty S0) ->
    Store_MappedPossible G s y S0 ->
    Path_Endpoint_MappedRealizes G s (Def_endpoint delta)
      (Tau_open d (path_var y)) ->
    Store_MappedPossible G s x (ty_pair S0 a d)
| store_mapped_possible_single {n : nat} (G : Ctx n) (s : Store n)
    (x : Fin.t n) (p : Path n) :
    Path_Resolve p s (endpoint_val x) ->
    Store_MappedPossible G s x (ty_single p)
| store_mapped_possible_tsel {n : nat} (G : Ctx n) (s : Store n)
    (x : Fin.t n) (p : Path n) (A : Name) (W : Ty n) :
    Path_Resolve (path_sel p A) s (endpoint_type W) ->
    Store_MappedPossible G s x W ->
    Store_MappedPossible G s x (ty_tsel p A)

(** Endpoint realization whose interval bounds are semantic-map codes. *)
with Path_Endpoint_MappedRealizes : forall {n : nat} {k : Kind},
    Ctx n -> Store n -> Path_Endpoint n -> Tau n k -> Prop :=
| endpoint_mapped_realizes_val {n : nat} (G : Ctx n) (s : Store n)
    (x : Fin.t n) (T : Ty n) :
    Store_MappedPossible G s x T ->
    Path_Endpoint_MappedRealizes G s (endpoint_val x) (tau_ty T)
| endpoint_mapped_realizes_type {n : nat} (G : Ctx n) (s : Store n)
    (L W U : Ty n) :
    Tau_SemMap G s (tau_ty L) (tau_ty W) ->
    Tau_SemMap G s (tau_ty W) (tau_ty U) ->
    Path_Endpoint_MappedRealizes G s (endpoint_type W) (tau_intv L U)

(** A finite code for a semantic map.  Static premises are retained so
    erasure yields the exact structural-subtyping derivation used by typing
    and preservation. *)
with Tau_SemMap : forall {n : nat} {k : Kind},
    Ctx n -> Store n -> Tau n k -> Tau n k -> Prop :=
| tau_sem_map_refl {n : nat} {k : Kind} (G : Ctx n) (s : Store n)
    (d : Tau n k) :
    Tau_SemMap G s d d
| tau_sem_map_trans {n : nat} {k : Kind} (G : Ctx n) (s : Store n)
    (d1 d2 d3 : Tau n k) :
    Tau_SemMap G s d1 d2 ->
    Tau_SemMap G s d2 d3 ->
    Tau_StructSub G (Path_RuntimeEq s) d1 d3 ->
    Tau_SemMap G s d1 d3
| tau_sem_map_conv {n : nat} {k : Kind} (G : Ctx n) (s : Store n)
    (d1 d2 : Tau n k) :
    Tau_StructConv (Path_RuntimeEq s) d1 d2 ->
    Tau_SemMap G s d1 d2
| tau_sem_map_bot {n : nat} (G : Ctx n) (s : Store n) (T : Ty n) :
    Tau_SemMap G s (tau_ty ty_bot) (tau_ty T)
| tau_sem_map_top {n : nat} (G : Ctx n) (s : Store n) (T : Ty n) :
    Tau_SemMap G s (tau_ty T) (tau_ty ty_top)
| tau_sem_map_widen {n : nat} (G : Ctx n) (s : Store n)
    (p : Path n) (T : Ty n) (x : Fin.t n) :
    Path_StructCheck G (Path_RuntimeEq s) p (tau_ty T) ->
    Path_Resolve p s (endpoint_val x) ->
    Store_MappedPossible G s x T ->
    Tau_SemMap G s (tau_ty (ty_single p)) (tau_ty T)
| tau_sem_map_single_alias {n : nat} (G : Ctx n) (s : Store n)
    (p q : Path n) (x : Fin.t n) :
    Path_StructCheck G (Path_RuntimeEq s) p
      (tau_ty (ty_single q)) ->
    Path_Resolve p s (endpoint_val x) ->
    Path_Resolve q s (endpoint_val x) ->
    Tau_SemMap G s (tau_ty (ty_single q)) (tau_ty (ty_single p))
| tau_sem_map_sel_hi {n : nat} (G : Ctx n) (s : Store n)
    (p : Path n) (A : Name) (S0 T W : Ty n) :
    Path_StructCheck G (Path_RuntimeEq s) (path_sel p A)
      (tau_intv S0 T) ->
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S0) (tau_ty T) ->
    Path_Resolve (path_sel p A) s (endpoint_type W) ->
    Tau_SemMap G s (tau_ty W) (tau_ty T) ->
    Tau_SemMap G s (tau_ty (ty_tsel p A)) (tau_ty T)
| tau_sem_map_sel_lo {n : nat} (G : Ctx n) (s : Store n)
    (p : Path n) (A : Name) (S0 T W : Ty n) :
    Path_StructCheck G (Path_RuntimeEq s) (path_sel p A)
      (tau_intv S0 T) ->
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S0) (tau_ty T) ->
    Path_Resolve (path_sel p A) s (endpoint_type W) ->
    Tau_SemMap G s (tau_ty S0) (tau_ty W) ->
    Tau_SemMap G s (tau_ty S0) (tau_ty (ty_tsel p A))
| tau_sem_map_fun {n : nat} (G : Ctx n) (s : Store n)
    (S' S0 : Ty n) (T T' : Ty (S n)) :
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S') (tau_ty S0) ->
    Tau_StructSub (ctx_snoc G S')
      (Path_ScopedLift (Path_RuntimeEq s)) (tau_ty T) (tau_ty T') ->
    Tau_SemMap G s (tau_ty (ty_fun S0 T)) (tau_ty (ty_fun S' T'))
| tau_sem_map_pair_fst {n : nat} {k : Kind}
    (G : Ctx n) (s : Store n) (S0 S' : Ty n)
    (a : Name) (d : Tau (S n) k) :
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S0) (tau_ty S') ->
    Tau_SemMap G s (tau_ty S0) (tau_ty S') ->
    Tau_SemMap G s (tau_ty (ty_pair S0 a d))
      (tau_ty (ty_pair S' a d))
| tau_sem_map_pair_single_member {n : nat} {k : Kind}
    (G : Ctx n) (s : Store n) (p : Path n) (P : Ty n)
    (a : Name) (d d' : Tau (S n) k) :
    Path_StructCheck G (Path_RuntimeEq s) p (tau_ty P) ->
    Tau_StructSub (ctx_snoc G (ty_single p))
      (Path_ScopedLift (Path_RuntimeEq s)) d d' ->
    Tau_StructSub G (Path_RuntimeEq s)
      (Tau_open d p) (Tau_open d' p) ->
    Tau_SemMap G s (Tau_open d p) (Tau_open d' p) ->
    Tau_SemMap G s
      (tau_ty (ty_pair (ty_single p) a d))
      (tau_ty (ty_pair (ty_single p) a d'))
| tau_sem_map_bounds {n : nat} (G : Ctx n) (s : Store n)
    (S' S0 T T' : Ty n) :
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S') (tau_ty S0) ->
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty T) (tau_ty T') ->
    Tau_StructSub G (Path_RuntimeEq s) (tau_ty S0) (tau_ty T) ->
    Tau_SemMap G s (tau_ty S') (tau_ty S0) ->
    Tau_SemMap G s (tau_ty T) (tau_ty T') ->
    Tau_SemMap G s (tau_intv S0 T) (tau_intv S' T').

Scheme Store_MappedPossible_mut := Induction for Store_MappedPossible Sort Prop
with Path_Endpoint_MappedRealizes_mut :=
  Induction for Path_Endpoint_MappedRealizes Sort Prop
with Tau_SemMap_mut := Induction for Tau_SemMap Sort Prop.

(** Forget semantic evidence and recover the structural derivation denoted
    by a finite map code. *)
Theorem Tau_SemMap_erase {n : nat} {k : Kind} {G : Ctx n}
    {s : Store n} {d1 d2 : Tau n k}
    (h : Tau_SemMap G s d1 d2) :
    Tau_StructSub G (Path_RuntimeEq s) d1 d2.
Proof.
  destruct h.
  - apply tau_struct_sub_refl.
  - assumption.
  - apply tau_struct_sub_conv. assumption.
  - apply tau_struct_sub_bot.
  - apply tau_struct_sub_top.
  - apply tau_struct_sub_widen. assumption.
  - apply tau_struct_sub_symm. assumption.
  - eapply tau_struct_sub_sel_hi; eassumption.
  - eapply tau_struct_sub_sel_lo; eassumption.
  - eapply tau_struct_sub_fun; eassumption.
  - apply tau_struct_sub_pair_fst. assumption.
  - eapply tau_struct_sub_pair_single_member; eassumption.
  - eapply tau_struct_sub_bounds; eassumption.
Qed.

(** A syntax-directed value in an exact store inhabits its precise
    introduction type. *)
Theorem Tm_StructPrecise_mappedPossible_of_binds {n : nat}
    {G : Ctx n} {s : Store n} {v : Tm n} {P : Ty n} {x : Fin.t n}
    (hprecise : Tm_StructPrecise G (Path_RuntimeEq s) v P)
    (hbind : Store_Binds s x v)
    (hctx : Ctx_Binds G x P) :
    Store_MappedPossible G s x P.
Proof.
  dependent elimination hprecise.
  - eapply store_mapped_possible_fun.
    + exact hbind.
    + exact hctx.
    + now apply tm_struct_precise_abs.
    + apply tau_struct_sub_refl.
    + apply tau_struct_sub_refl.
  - eapply store_mapped_possible_pair.
    + exact hbind.
    + eapply path_struct_check_promote.
      * eapply path_struct_check_var; eassumption.
      * apply tau_struct_sub_refl.
    + apply store_mapped_possible_single. apply path_resolve_var.
    + cbn [Def_endpoint].
      change (Path_Endpoint_MappedRealizes G1 s (endpoint_val z)
        (Tau_open (Tau_weaken (tau_ty (ty_single (path_var z))))
          (path_var y))).
      rewrite Tau_weaken_open.
      apply endpoint_mapped_realizes_val.
      apply store_mapped_possible_single. apply path_resolve_var.
  - eapply store_mapped_possible_pair.
    + exact hbind.
    + eapply path_struct_check_promote.
      * eapply path_struct_check_var; eassumption.
      * apply tau_struct_sub_refl.
    + apply store_mapped_possible_single. apply path_resolve_var.
    + cbn [Def_endpoint]. rewrite Tau_weaken_open.
      apply endpoint_mapped_realizes_type;
        apply tau_sem_map_refl.
Qed.

Theorem Store_StructPreciseTy_mappedPossible_of_ctx_binds {n : nat}
    {G : Ctx n} {s : Store n} {x : Fin.t n} {P : Ty n}
    (hstore : Store_StructPreciseTy G s)
    (hctx : Ctx_Binds G x P) :
    Store_MappedPossible G s x P.
Proof.
  destruct (Store_StructPreciseTy_of_ctx_binds hstore hctx)
    as (v & hbind & hprecise).
  exact (Tm_StructPrecise_mappedPossible_of_binds hprecise hbind hctx).
Qed.

(** A mapped possible function exposes the exact stored abstraction and the
    domain/codomain residues used by application preservation. *)
Theorem Store_MappedPossible_function_signature {n : nat}
    {G : Ctx n} {s : Store n} {x : Fin.t n}
    {S0 : Ty n} {U : Ty (S n)}
    (h : Store_MappedPossible G s x (ty_fun S0 U)) :
    exists (A : Ty n) (body : Tm (S n)) (B : Ty (S n)),
      Store_Binds s x (tm_abs A body) /\
      Ctx_Binds G x (ty_fun A B) /\
      Tm_StructPrecise G (Path_RuntimeEq s)
        (tm_abs A body) (ty_fun A B) /\
      Tau_StructSub G (Path_RuntimeEq s) (tau_ty S0) (tau_ty A) /\
      Tau_StructSub (ctx_snoc G S0)
        (Path_ScopedLift (Path_RuntimeEq s)) (tau_ty B) (tau_ty U).
Proof.
  dependent elimination h.
  exists A, body, B. repeat split; assumption.
Qed.

(** In particular, a mapped possible function location stores an
    abstraction. *)
Theorem Store_MappedPossible_fun_binding {n : nat}
    {G : Ctx n} {s : Store n} {x : Fin.t n}
    {S0 : Ty n} {U : Ty (S n)}
    (h : Store_MappedPossible G s x (ty_fun S0 U)) :
    exists (A : Ty n) (body : Tm (S n)),
      Store_Binds s x (tm_abs A body).
Proof.
  destruct (Store_MappedPossible_function_signature h)
    as (A & body & B & hbind & _).
  now exists A, body.
Qed.

(** A mapped possible dependent pair stores a pair with the advertised
    label and member kind. *)
Theorem Store_MappedPossible_pair_binding {n : nat} {k : Kind}
    {G : Ctx n} {s : Store n} {x : Fin.t n} {S0 : Ty n}
    {a : Name} {d : Tau (S n) k}
    (h : Store_MappedPossible G s x (ty_pair S0 a d)) :
    exists (y : Fin.t n) (delta : Def n k),
      Store_Binds s x (tm_pair y a delta).
Proof.
  dependent elimination h.
  now exists y, delta.
Qed.

(** The action denoted by a semantic map on mapped realization. *)
Definition Tau_SemMap_Action {n : nat} {k : Kind}
    (G : Ctx n) (s : Store n) (d1 d2 : Tau n k) : Prop :=
  forall endpoint : Path_Endpoint n,
    Path_Endpoint_MappedRealizes G s endpoint d1 ->
    Path_Endpoint_MappedRealizes G s endpoint d2.

Definition Tau_SemMap_comp {n : nat} {k : Kind} {G : Ctx n}
    {s : Store n} {d1 d2 d3 : Tau n k}
    (h1 : Tau_SemMap G s d1 d2)
    (h2 : Tau_SemMap G s d2 d3) :
    Tau_SemMap G s d1 d3 :=
  tau_sem_map_trans h1 h2
    (tau_struct_sub_trans (Tau_SemMap_erase h1) (Tau_SemMap_erase h2)).

(** Mapped realization is invariant under runtime conversion.  Recursing on
    the realization makes dependent pair members genuine subproofs. *)
Local Theorem Path_Endpoint_MappedRealizes_convert {n : nat} {k : Kind}
    {G : Ctx n} {s : Store n} {endpoint : Path_Endpoint n}
    {d1 : Tau n k}
    (hrealizes : Path_Endpoint_MappedRealizes G s endpoint d1) :
    forall d2 : Tau n k,
      Tau_StructConv (Path_RuntimeEq s) d1 d2 ->
      Path_Endpoint_MappedRealizes G s endpoint d2.
Proof.
  refine (Path_Endpoint_MappedRealizes_mut
    (P := fun n0 G0 s0 x S0 _ => forall T,
      Tau_StructConv (Path_RuntimeEq s0) (tau_ty S0) (tau_ty T) ->
      Store_MappedPossible G0 s0 x T)
    (P0 := fun n0 k0 G0 s0 endpoint0 e _ => forall e',
      Tau_StructConv (Path_RuntimeEq s0) e e' ->
      Path_Endpoint_MappedRealizes G0 s0 endpoint0 e')
    (P1 := fun _ _ _ _ _ _ _ => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrealizes).
  - intros n0 G0 s0 x T hc.
    pose proof (Tau_StructConv_top_target_eq hc) as E. subst T.
    apply store_mapped_possible_top.
  - intros n0 G0 s0 x A body B S0 U
      hbind hctx hprecise hdom hcod T2 hc.
    pose proof (Tau_StructConv_convTag_eq hc) as Htag.
    dependent elimination T2;
      cbn [Tau_convTag Ty_convTag] in Htag; try discriminate Htag.
    destruct (Tau_StructConv_fun_parts hc) as [HdomConv HcodConv].
    eapply store_mapped_possible_fun.
    + exact hbind.
    + exact hctx.
    + exact hprecise.
    + eapply tau_struct_sub_trans.
      * apply tau_struct_sub_conv.
        apply tau_struct_conv_symm. exact HdomConv.
      * exact hdom.
    + eapply tau_struct_sub_trans.
      * eapply Tau_StructSub_narrow.
        -- exact hcod.
        -- apply tau_struct_sub_conv.
           apply tau_struct_conv_symm. exact HdomConv.
      * apply tau_struct_sub_conv. exact HcodConv.
  - intros n0 k0 G0 s0 x y a delta S0 d hbind hfirst
      hpossible ihFirst hmember ihMember T2 hc.
    pose proof (Tau_StructConv_convTag_eq hc) as Htag.
    dependent elimination T2;
      cbn [Tau_convTag Ty_convTag] in Htag; try discriminate Htag.
    destruct (Tau_StructConv_pair_label_kind hc) as [Elabel Ekind].
    dependent elimination Elabel. dependent elimination Ekind.
    destruct (Tau_StructConv_pair_components hc)
      as [HfirstConv HmemberConv].
    pose proof (Tau_StructConv_subst HmemberConv
      (Path_SubstRelHom_openAt (Path_RuntimeEq_isEquivCongr s0)
        (path_var y))) as HmemberOpened.
    change (Tau_StructConv (Path_RuntimeEq s0)
      (Tau_open d (path_var y)) (Tau_open t2 (path_var y)))
      in HmemberOpened.
    eapply store_mapped_possible_pair.
    + exact hbind.
    + eapply path_struct_check_sub.
      * exact hfirst.
      * apply tau_struct_sub_conv. exact HfirstConv.
    + exact (ihFirst _ HfirstConv).
    + exact (ihMember _ HmemberOpened).
  - intros n0 G0 s0 x p hr T hc.
    pose proof (Tau_StructConv_convTag_eq hc) as Htag.
    dependent elimination T;
      cbn [Tau_convTag Ty_convTag] in Htag; try discriminate Htag.
    pose proof (Tau_StructConv_single_paths
      (Path_RuntimeEq_isEquivCongr s0) hc) as Hpq.
    apply store_mapped_possible_single.
    exact (proj1 (Path_RuntimeEq_resolve_iff Hpq (endpoint_val x)) hr).
  - intros n0 G0 s0 x p A W hr hpossible ih T hc.
    pose proof (Tau_StructConv_convTag_eq hc) as Htag.
    dependent elimination T;
      cbn [Tau_convTag Ty_convTag] in Htag; try discriminate Htag.
    destruct (Tau_StructConv_tsel_parts
      (Path_RuntimeEq_isEquivCongr s0) hc) as [Elabel Hpq].
    dependent elimination Elabel.
    pose proof (path_equiv_sel (Path_RuntimeEq_isEquivCongr s0)
      Hpq A) as Hsel.
    eapply store_mapped_possible_tsel.
    + exact (proj1 (Path_RuntimeEq_resolve_iff Hsel
        (endpoint_type W)) hr).
    + exact hpossible.
  - intros n0 G0 s0 x T hpossible ih d2 hc.
    dependent elimination d2.
    apply endpoint_mapped_realizes_val. exact (ih _ hc).
  - intros n0 G0 s0 L W U hlo ihLo hhi ihHi d2 hc.
    dependent elimination d2.
    destruct (Tau_StructConv_interval_components hc)
      as [HloConv HhiConv].
    apply endpoint_mapped_realizes_type.
    + exact (Tau_SemMap_comp
        (tau_sem_map_conv G0 (tau_struct_conv_symm HloConv)) hlo).
    + exact (Tau_SemMap_comp hhi (tau_sem_map_conv G0 HhiConv)).
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

Theorem Tau_StructConv_mapped_action {n : nat} {k : Kind}
    {G : Ctx n} {s : Store n} {d1 d2 : Tau n k}
    (hc : Tau_StructConv (Path_RuntimeEq s) d1 d2) :
    Tau_SemMap_Action G s d1 d2.
Proof.
  intros endpoint hrealizes.
  exact (Path_Endpoint_MappedRealizes_convert hrealizes (d2 := d2) hc).
Qed.

Local Theorem Path_Endpoint_MappedRealizes_ty_inv {n : nat}
    {G : Ctx n} {s : Store n} {endpoint : Path_Endpoint n} {T : Ty n}
    (h : Path_Endpoint_MappedRealizes G s endpoint (tau_ty T)) :
    exists x : Fin.t n,
      endpoint = endpoint_val x /\ Store_MappedPossible G s x T.
Proof.
  dependent elimination h. exists x. split; [reflexivity | assumption].
Qed.

Local Theorem Path_Endpoint_MappedRealizes_intv_inv {n : nat}
    {G : Ctx n} {s : Store n} {endpoint : Path_Endpoint n}
    {L U : Ty n}
    (h : Path_Endpoint_MappedRealizes G s endpoint (tau_intv L U)) :
    exists W : Ty n,
      endpoint = endpoint_type W /\
      Tau_SemMap G s (tau_ty L) (tau_ty W) /\
      Tau_SemMap G s (tau_ty W) (tau_ty U).
Proof.
  dependent elimination h. exists W. repeat split; assumption.
Qed.

Local Theorem Store_MappedPossible_bot_absurd {n : nat}
    {G : Ctx n} {s : Store n} {x : Fin.t n}
    (h : Store_MappedPossible G s x ty_bot) : False.
Proof. dependent elimination h. Qed.

Local Theorem Store_MappedPossible_single_resolve {n : nat}
    {G : Ctx n} {s : Store n} {x : Fin.t n} {p : Path n}
    (h : Store_MappedPossible G s x (ty_single p)) :
    Path_Resolve p s (endpoint_val x).
Proof. dependent elimination h. assumption. Qed.

Local Theorem Store_MappedPossible_tsel_inv {n : nat}
    {G : Ctx n} {s : Store n} {x : Fin.t n}
    {p : Path n} {A : Name}
    (h : Store_MappedPossible G s x (ty_tsel p A)) :
    exists W : Ty n,
      Path_Resolve (path_sel p A) s (endpoint_type W) /\
      Store_MappedPossible G s x W.
Proof.
  dependent elimination h. exists W. split; assumption.
Qed.

Local Theorem Store_MappedPossible_pair_inv {n : nat} {k : Kind}
    {G : Ctx n} {s : Store n} {x : Fin.t n} {S0 : Ty n}
    {a : Name} {d : Tau (S n) k}
    (h : Store_MappedPossible G s x (ty_pair S0 a d)) :
    exists (y : Fin.t n) (delta : Def n k),
      Store_Binds s x (tm_pair y a delta) /\
      Path_StructCheck G (Path_RuntimeEq s) (path_var y) (tau_ty S0) /\
      Store_MappedPossible G s y S0 /\
      Path_Endpoint_MappedRealizes G s (Def_endpoint delta)
        (Tau_open d (path_var y)).
Proof.
  dependent elimination h. exists y, delta. repeat split; assumption.
Qed.

(** Every semantic code acts on mapped realization, provided runtime
    conversion acts on it. *)
Theorem Tau_SemMap_action_of_conv {n : nat} {G : Ctx n} {s : Store n}
    (hconv : forall {k : Kind} {d1 d2 : Tau n k},
      Tau_StructConv (Path_RuntimeEq s) d1 d2 ->
      Tau_SemMap_Action G s d1 d2)
    {k : Kind} {d1 d2 : Tau n k}
    (hmap : Tau_SemMap G s d1 d2) :
    Tau_SemMap_Action G s d1 d2.
Proof.
  refine ((Tau_SemMap_mut
    (P := fun _ _ _ _ _ _ => True)
    (P0 := fun _ _ _ _ _ _ _ => True)
    (P1 := fun n0 _ G0 s0 e1 e2 _ =>
      (forall {j : Kind} {u v : Tau n0 j},
        Tau_StructConv (Path_RuntimeEq s0) u v ->
        Tau_SemMap_Action G0 s0 u v) ->
      Tau_SemMap_Action G0 s0 e1 e2)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmap) hconv).
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros n0 k0 G0 s0 d hconv0 endpoint hsource. exact hsource.
  - intros n0 k0 G0 s0 e1 e2 e3 hm1 ih1 hm2 ih2 hstruct
      hconv0 endpoint hsource.
    exact (ih2 hconv0 endpoint (ih1 hconv0 endpoint hsource)).
  - intros n0 k0 G0 s0 e1 e2 hc hconv0.
    exact (@hconv0 k0 e1 e2 hc).
  - intros n0 G0 s0 T hconv0 endpoint hsource.
    destruct (Path_Endpoint_MappedRealizes_ty_inv hsource)
      as (x & Eendpoint & hpossible).
    subst endpoint. exfalso.
    exact (Store_MappedPossible_bot_absurd hpossible).
  - intros n0 G0 s0 T hconv0 endpoint hsource.
    destruct (Path_Endpoint_MappedRealizes_ty_inv hsource)
      as (x & Eendpoint & hpossible).
    subst endpoint. apply endpoint_mapped_realizes_val.
    apply store_mapped_possible_top.
  - intros n0 G0 s0 p T x hp hr hpossible ih
      hconv0 endpoint hsource.
    destruct (Path_Endpoint_MappedRealizes_ty_inv hsource)
      as (x' & Eendpoint & hsourcePossible).
    subst endpoint.
    pose proof (Store_MappedPossible_single_resolve hsourcePossible)
      as hr'.
    pose proof (Path_Resolve_deterministic hr hr') as Eresolve.
    pose proof (endpoint_val_inj Eresolve) as Eloc. subst x'.
    apply endpoint_mapped_realizes_val. exact hpossible.
  - intros n0 G0 s0 p q x hp hrp hrq hconv0 endpoint hsource.
    destruct (Path_Endpoint_MappedRealizes_ty_inv hsource)
      as (x' & Eendpoint & hsourcePossible).
    subst endpoint.
    pose proof (Store_MappedPossible_single_resolve hsourcePossible)
      as hrq'.
    pose proof (Path_Resolve_deterministic hrq hrq') as Eresolve.
    pose proof (endpoint_val_inj Eresolve) as Eloc. subst x'.
    apply endpoint_mapped_realizes_val.
    apply store_mapped_possible_single. exact hrp.
  - intros n0 G0 s0 p A S0 T W hp hbounds hr hupper ih
      hconv0 endpoint hsource.
    destruct (Path_Endpoint_MappedRealizes_ty_inv hsource)
      as (x & Eendpoint & hsourcePossible).
    subst endpoint.
    destruct (Store_MappedPossible_tsel_inv hsourcePossible)
      as (W' & hr' & hpossible').
    pose proof (Path_Resolve_deterministic hr hr') as Eresolve.
    injection Eresolve as EW. subst W'.
    exact (ih hconv0 (endpoint_val x)
      (endpoint_mapped_realizes_val hpossible')).
  - intros n0 G0 s0 p A S0 T W hp hbounds hr hlower ih
      hconv0 endpoint hsource.
    pose proof (ih hconv0 endpoint hsource) as htarget.
    destruct (Path_Endpoint_MappedRealizes_ty_inv htarget)
      as (x & Eendpoint & hpossible).
    subst endpoint. apply endpoint_mapped_realizes_val.
    eapply store_mapped_possible_tsel.
    + exact hr.
    + exact hpossible.
  - intros n0 G0 s0 S' S0 T T' hdom hcod hconv0 endpoint hsource.
    destruct (Path_Endpoint_MappedRealizes_ty_inv hsource)
      as (x & Eendpoint & hsourcePossible).
    subst endpoint.
    destruct (Store_MappedPossible_function_signature hsourcePossible)
      as (A & body & B & hbind & hctx & hprecise & hsourceDom &
        hsourceCod).
    apply endpoint_mapped_realizes_val.
    eapply store_mapped_possible_fun.
    + exact hbind.
    + exact hctx.
    + exact hprecise.
    + eapply tau_struct_sub_trans; [exact hdom | exact hsourceDom].
    + eapply tau_struct_sub_trans.
      * exact (Tau_StructSub_narrow hsourceCod hdom).
      * exact hcod.
  - intros n0 k0 G0 s0 S0 S' a d hdom hfirstMap ihFirst
      hconv0 endpoint hsource.
    destruct (Path_Endpoint_MappedRealizes_ty_inv hsource)
      as (x & Eendpoint & hsourcePossible).
    subst endpoint.
    destruct (Store_MappedPossible_pair_inv hsourcePossible)
      as (y & delta & hbind & hfirst & hfirstPossible & hmember).
    pose proof (ihFirst hconv0 (endpoint_val y)
      (endpoint_mapped_realizes_val hfirstPossible)) as hfirstTarget.
    destruct (Path_Endpoint_MappedRealizes_ty_inv hfirstTarget)
      as (y' & Efirst & hfirstPossible').
    pose proof (endpoint_val_inj Efirst) as Ey. subst y'.
    apply endpoint_mapped_realizes_val.
    eapply store_mapped_possible_pair.
    + exact hbind.
    + eapply path_struct_check_sub; [exact hfirst | exact hdom].
    + exact hfirstPossible'.
    + exact hmember.
  - intros n0 k0 G0 s0 p P a d d' hp hscoped hopen hopenMap
      ihOpened hconv0 endpoint hsource.
    destruct (Path_Endpoint_MappedRealizes_ty_inv hsource)
      as (x & Eendpoint & hsourcePossible).
    subst endpoint.
    destruct (Store_MappedPossible_pair_inv hsourcePossible)
      as (y & delta & hbind & hfirst & hfirstPossible & hmember).
    pose proof (Store_MappedPossible_single_resolve hfirstPossible)
      as hpResolve.
    pose proof (path_runtime_eq_coresolve
      (path_reduce_var y s0) (Path_Resolve_toReduce hpResolve)) as hyp.
    pose proof (tau_struct_conv_replace d hyp) as htoP.
    pose proof (tau_struct_conv_replace d'
      (path_runtime_eq_symm hyp)) as hfromP.
    pose proof (Path_Endpoint_MappedRealizes_convert hmember
      (d2 := Tau_open d p) htoP) as hmemberAtP.
    pose proof (ihOpened hconv0 _ hmemberAtP) as hmemberMapped.
    pose proof (Path_Endpoint_MappedRealizes_convert hmemberMapped
      (d2 := Tau_open d' (path_var y)) hfromP) as hmemberTarget.
    apply endpoint_mapped_realizes_val.
    eapply store_mapped_possible_pair.
    + exact hbind.
    + exact hfirst.
    + exact hfirstPossible.
    + exact hmemberTarget.
  - intros n0 G0 s0 S' S0 T T' hlo hhi hnonempty
      hmapLo ihLo hmapHi ihHi hconv0 endpoint hsource.
    destruct (Path_Endpoint_MappedRealizes_intv_inv hsource)
      as (W & Eendpoint & hsourceLo & hsourceHi).
    subst endpoint.
    apply endpoint_mapped_realizes_type.
    + exact (Tau_SemMap_comp hmapLo hsourceLo).
    + exact (Tau_SemMap_comp hsourceHi hmapHi).
Qed.

Theorem Tau_SemMap_action {n : nat} {k : Kind} {G : Ctx n}
    {s : Store n} {d1 d2 : Tau n k}
    (hmap : Tau_SemMap G s d1 d2) :
    Tau_SemMap_Action G s d1 d2.
Proof.
  exact (Tau_SemMap_action_of_conv
    (fun k0 e1 e2 hc => Tau_StructConv_mapped_action hc) hmap).
Qed.

(** A path substitution is semantically realized when every source context
    entry resolves to an endpoint realizing its substituted type. *)
Definition Path_MappedSubstitution {n m : nat}
    (G : Ctx n) (rho : PathSubst n m) (D : Ctx m) (s : Store m) : Prop :=
  forall (x : Fin.t n) (T : Ty n), Ctx_Binds G x T ->
    exists endpoint : Path_Endpoint m,
      Path_Resolve (rho x) s endpoint /\
      Path_Endpoint_MappedRealizes D s endpoint
        (tau_ty (Ty_subst T rho)).

(** The left-looking selection rule follows the first component of the same
    resolved pair before resuming lookup at the missed label. *)
Local Theorem Path_Resolve_sel_miss_fst {n : nat} {k : Kind}
    {s : Store n} {p : Path n} {x y : Fin.t n}
    {a b : Name} {delta : Def n k} {endpoint : Path_Endpoint n}
    (hp : Path_Resolve p s (endpoint_val x))
    (hbind : Store_Binds s x (tm_pair y b delta))
    (hne : a <> b)
    (htail : Path_Resolve (path_sel (path_fst p) a) s endpoint) :
    Path_Resolve (path_sel p a) s endpoint.
Proof.
  pose proof (path_resolve_fst hp hbind) as hfst.
  pose proof (Path_RuntimeEq_of_reduce (Path_Resolve_toReduce hfst))
    as hfstEq.
  pose proof (path_equiv_sel (Path_RuntimeEq_isEquivCongr s) hfstEq a)
    as htailEq.
  eapply path_resolve_sel_miss.
  - exact hp.
  - exact hbind.
  - exact hne.
  - exact (proj1 (Path_RuntimeEq_resolve_iff htailEq endpoint) htail).
Qed.

Local Definition PathMappedSubstMotive {n : nat}
    (G : Ctx n) (R : Path n -> Path n -> Prop) {k : Kind}
    (p : Path n) (d : Tau n k) (_ : Path_StructCheck G R p d) : Prop :=
  forall (m : nat) (rho : PathSubst n m) (D : Ctx m) (s : Store m),
    Path_StructSubstitution G rho D (Path_RuntimeEq s) ->
    Path_SubstRelHom R (Path_RuntimeEq s) rho ->
    Path_MappedSubstitution G rho D s ->
    exists endpoint : Path_Endpoint m,
      Path_Resolve (Path_subst p rho) s endpoint /\
      Path_Endpoint_MappedRealizes D s endpoint (Tau_subst d rho).

Local Definition SubMappedSubstMotive {n : nat}
    (G : Ctx n) (R : Path n -> Path n -> Prop) {k : Kind}
    (d1 d2 : Tau n k) (_ : Tau_StructSub G R d1 d2) : Prop :=
  forall (m : nat) (rho : PathSubst n m) (D : Ctx m) (s : Store m),
    Path_StructSubstitution G rho D (Path_RuntimeEq s) ->
    Path_SubstRelHom R (Path_RuntimeEq s) rho ->
    Path_MappedSubstitution G rho D s ->
    Tau_SemMap D s (Tau_subst d1 rho) (Tau_subst d2 rho).

Local Lemma Path_Sub_mapped_subst_mut :
    (forall n G R k p d (H : Path_StructCheck G R p d),
      @PathMappedSubstMotive n G R k p d H) /\
    (forall n G R k d1 d2 (H : Tau_StructSub G R d1 d2),
      @SubMappedSubstMotive n G R k d1 d2 H).
Proof.
  apply PathStruct_mutind;
    unfold PathMappedSubstMotive, SubMappedSubstMotive.
  - intros n G R x T Hb m rho D s hctx hrel henv.
    exact (henv x T Hb).
  - intros n k G R p d1 d2 hp ihp hs ihs
      m rho D s hctx hrel henv.
    destruct (ihp _ _ _ _ hctx hrel henv)
      as (endpoint & hresolve & hrealizes).
    exists endpoint. split; [exact hresolve |].
    exact (Tau_SemMap_action (ihs _ _ _ _ hctx hrel henv) hrealizes).
  - intros n G R p U T hp ihp hs ihs
      m rho D s hctx hrel henv.
    destruct (ihp _ _ _ _ hctx hrel henv)
      as (endpoint & hresolve & hrealizes).
    destruct (Path_Endpoint_MappedRealizes_ty_inv hrealizes)
      as (x & Eendpoint & hpossible). subst endpoint.
    exists (endpoint_val x). split; [exact hresolve |].
    cbn [Path_subst Ty_subst Tau_subst].
    exact (Tau_SemMap_action (ihs _ _ _ _ hctx hrel henv)
      (endpoint_mapped_realizes_val
        (store_mapped_possible_single D hresolve))).
  - intros n k G R p S0 a d hp ihp
      m rho D s hctx hrel henv.
    destruct (ihp _ _ _ _ hctx hrel henv)
      as (endpoint & hresolve & hrealizes).
    cbn [Ty_subst Tau_subst] in hrealizes.
    destruct (Path_Endpoint_MappedRealizes_ty_inv hrealizes)
      as (x & Eendpoint & hpossible). subst endpoint.
    destruct (Store_MappedPossible_pair_inv hpossible)
      as (y & delta & hbind & hfirst & hfirstPossible & hmember).
    exists (endpoint_val y). split.
    + cbn [Path_subst]. eapply path_resolve_fst; eassumption.
    + cbn [Tau_subst Ty_subst].
      apply endpoint_mapped_realizes_val. exact hfirstPossible.
  - intros n k G R p S0 a d hp ihp
      m rho D s hctx hrel henv.
    destruct (ihp _ _ _ _ hctx hrel henv)
      as (endpoint & hresolve & hrealizes).
    cbn [Ty_subst Tau_subst] in hrealizes.
    destruct (Path_Endpoint_MappedRealizes_ty_inv hrealizes)
      as (x & Eendpoint & hpossible). subst endpoint.
    destruct (Store_MappedPossible_pair_inv hpossible)
      as (y & delta & hbind & hfirst & hfirstPossible & hmember).
    pose proof (path_resolve_fst hresolve hbind) as hfst.
    pose proof (Path_RuntimeEq_of_reduce (Path_Resolve_toReduce hfst))
      as hfstEq.
    pose proof (tau_struct_conv_replace
      (Tau_subst d (PathSubst_lift rho))
      (path_runtime_eq_symm hfstEq)) as hopenConv.
    pose proof (Path_Endpoint_MappedRealizes_convert hmember
      (d2 := Tau_open (Tau_subst d (PathSubst_lift rho))
        (path_fst (Path_subst p rho))) hopenConv) as hmember'.
    destruct delta.
    + eexists. split.
      * cbn [Path_subst]. eapply path_resolve_sel_val; eassumption.
      * cbn [Path_subst Tau_subst Ty_subst].
        rewrite Tau_open_subst. exact hmember'.
    + eexists. split.
      * cbn [Path_subst]. eapply path_resolve_sel_type; eassumption.
      * cbn [Path_subst Tau_subst Ty_subst].
        rewrite Tau_open_subst. exact hmember'.
  - intros n k k' G R p S0 a b d d' hp ihp htail ihtail hne
      m rho D s hctx hrel henv.
    destruct (ihp _ _ _ _ hctx hrel henv)
      as (endpoint & hresolve & hrealizes).
    destruct (ihtail _ _ _ _ hctx hrel henv)
      as (tailEndpoint & htailResolve & htailRealizes).
    cbn [Ty_subst Tau_subst] in hrealizes.
    destruct (Path_Endpoint_MappedRealizes_ty_inv hrealizes)
      as (x & Eendpoint & hpossible). subst endpoint.
    destruct (Store_MappedPossible_pair_inv hpossible)
      as (y & delta & hbind & hfirst & hfirstPossible & hmember).
    exists tailEndpoint. split; [| exact htailRealizes].
    cbn [Path_subst] in htailResolve |- *.
    eapply Path_Resolve_sel_miss_fst; eassumption.
  - intros n k G R d m rho D s hctx hrel henv.
    apply tau_sem_map_refl.
  - intros n k G R d1 d2 d3 h1 ih1 h2 ih2
      m rho D s hctx hrel henv.
    exact (Tau_SemMap_comp
      (ih1 _ _ _ _ hctx hrel henv)
      (ih2 _ _ _ _ hctx hrel henv)).
  - intros n k G R d1 d2 hc m rho D s hctx hrel henv.
    apply tau_sem_map_conv. exact (Tau_StructConv_subst hc hrel).
  - intros n G R T m rho D s hctx hrel henv.
    cbn [Ty_subst Tau_subst]. apply tau_sem_map_bot.
  - intros n G R T m rho D s hctx hrel henv.
    cbn [Ty_subst Tau_subst]. apply tau_sem_map_top.
  - intros n G R p T hp ihp m rho D s hctx hrel henv.
    destruct (ihp _ _ _ _ hctx hrel henv)
      as (endpoint & hresolve & hrealizes).
    destruct (Path_Endpoint_MappedRealizes_ty_inv hrealizes)
      as (x & Eendpoint & hpossible). subst endpoint.
    cbn [Path_subst Ty_subst Tau_subst].
    eapply tau_sem_map_widen.
    + exact (Path_StructCheck_subst hp hctx hrel).
    + exact hresolve.
    + exact hpossible.
  - intros n G R p q hp ihp m rho D s hctx hrel henv.
    destruct (ihp _ _ _ _ hctx hrel henv)
      as (endpoint & hresolve & hrealizes).
    destruct (Path_Endpoint_MappedRealizes_ty_inv hrealizes)
      as (x & Eendpoint & hpossible). subst endpoint.
    pose proof (Store_MappedPossible_single_resolve hpossible)
      as hqresolve.
    cbn [Path_subst Ty_subst Tau_subst].
    eapply tau_sem_map_single_alias.
    + exact (Path_StructCheck_subst hp hctx hrel).
    + exact hresolve.
    + exact hqresolve.
  - intros n G R p A S0 T hp ihp hb ihb
      m rho D s hctx hrel henv.
    destruct (ihp _ _ _ _ hctx hrel henv)
      as (endpoint & hresolve & hrealizes).
    destruct (Path_Endpoint_MappedRealizes_intv_inv hrealizes)
      as (W & Eendpoint & hlower & hupper). subst endpoint.
    cbn [Path_subst Ty_subst Tau_subst].
    eapply tau_sem_map_sel_hi.
    + exact (Path_StructCheck_subst hp hctx hrel).
    + exact (Tau_StructSub_subst hb hctx hrel).
    + exact hresolve.
    + exact hupper.
  - intros n G R p A S0 T hp ihp hb ihb
      m rho D s hctx hrel henv.
    destruct (ihp _ _ _ _ hctx hrel henv)
      as (endpoint & hresolve & hrealizes).
    destruct (Path_Endpoint_MappedRealizes_intv_inv hrealizes)
      as (W & Eendpoint & hlower & hupper). subst endpoint.
    cbn [Path_subst Ty_subst Tau_subst].
    eapply tau_sem_map_sel_lo.
    + exact (Path_StructCheck_subst hp hctx hrel).
    + exact (Tau_StructSub_subst hb hctx hrel).
    + exact hresolve.
    + exact hlower.
  - intros n G R S0 S' T T' hdom ihdom hcod ihcod
      m rho D s hctx hrel henv.
    cbn [Ty_subst Tau_subst]. apply tau_sem_map_fun.
    + exact (Tau_StructSub_subst hdom hctx hrel).
    + exact (Tau_StructSub_subst hcod
        (Path_StructSubstitution_lift hctx)
        (Path_SubstRelHom_scoped hrel)).
  - intros n k G R S0 S' a d hdom ihdom
      m rho D s hctx hrel henv.
    cbn [Ty_subst Tau_subst]. eapply tau_sem_map_pair_fst.
    + exact (Tau_StructSub_subst hdom hctx hrel).
    + exact (ihdom _ _ _ _ hctx hrel henv).
  - intros n k G R p P a d d' hp ihp hscoped ihscoped
      hopen ihopen m rho D s hctx hrel henv.
    pose proof (Tau_StructSub_subst hopen hctx hrel) as hopen'.
    pose proof (ihopen _ _ _ _ hctx hrel henv) as hopenMap.
    rewrite !Tau_open_subst in hopen', hopenMap.
    cbn [Path_subst Ty_subst Tau_subst].
    eapply tau_sem_map_pair_single_member.
    + exact (Path_StructCheck_subst hp hctx hrel).
    + exact (Tau_StructSub_subst hscoped
        (Path_StructSubstitution_lift hctx)
        (Path_SubstRelHom_scoped hrel)).
    + exact hopen'.
    + exact hopenMap.
  - intros n G R S0 S' T T' hlo ihlo hhi ihhi hnon ihnon
      m rho D s hctx hrel henv.
    cbn [Tau_subst]. eapply tau_sem_map_bounds.
    + exact (Tau_StructSub_subst hlo hctx hrel).
    + exact (Tau_StructSub_subst hhi hctx hrel).
    + exact (Tau_StructSub_subst hnon hctx hrel).
    + exact (ihlo _ _ _ _ hctx hrel henv).
    + exact (ihhi _ _ _ _ hctx hrel henv).
Qed.

(** Fundamental theorem for generalized path checking under an arbitrary
    realized simultaneous path substitution. *)
Theorem Path_StructCheck_mapped_subst {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {k : Kind}
    {p : Path n} {d : Tau n k} (h : Path_StructCheck G R p d) :
    @PathMappedSubstMotive n G R k p d h.
Proof.
  exact (proj1 Path_Sub_mapped_subst_mut _ _ _ _ _ _ h).
Qed.

(** Fundamental theorem for structural generalized subtyping. *)
Theorem Tau_StructSub_mapped_subst {n : nat} {G : Ctx n}
    {R : Path n -> Path n -> Prop} {k : Kind}
    {d1 d2 : Tau n k} (h : Tau_StructSub G R d1 d2) :
    @SubMappedSubstMotive n G R k d1 d2 h.
Proof.
  exact (proj2 Path_Sub_mapped_subst_mut _ _ _ _ _ _ h).
Qed.

Local Theorem Store_StructPreciseTy_mapped_identity {n : nat}
    {G : Ctx n} {s : Store n}
    (hstore : Store_StructPreciseTy G s) :
    Path_MappedSubstitution G (PathSubst_id n) G s.
Proof.
  intros x T hb. exists (endpoint_val x). split.
  - rewrite PathSubst_id_apply. apply path_resolve_var.
  - rewrite Ty_subst_id. apply endpoint_mapped_realizes_val.
    exact (Store_StructPreciseTy_mappedPossible_of_ctx_binds hstore hb).
Qed.

(** Every structurally checked runtime path resolves to an endpoint realizing
    its checked generalized type. *)
Theorem Path_StructCheck_mapped_resolves {n : nat} {G : Ctx n}
    {s : Store n} {k : Kind} {p : Path n} {d : Tau n k}
    (hstore : Store_StructPreciseTy G s)
    (h : Path_StructCheck G (Path_RuntimeEq s) p d) :
    exists endpoint : Path_Endpoint n,
      Path_Resolve p s endpoint /\
      Path_Endpoint_MappedRealizes G s endpoint d.
Proof.
  pose proof (Path_StructCheck_mapped_subst h
    (m := n) (rho := PathSubst_id n) (D := G) (s := s)
    Path_StructSubstitution_id Path_SubstRelHom_id
    (Store_StructPreciseTy_mapped_identity hstore)) as Hmapped.
  rewrite Path_subst_id, Tau_subst_id in Hmapped. exact Hmapped.
Qed.

(** Structural runtime subtyping denotes a semantic map in every exact
    store. *)
Theorem Tau_StructSub_mapped {n : nat} {G : Ctx n} {s : Store n}
    {k : Kind} {d1 d2 : Tau n k}
    (hstore : Store_StructPreciseTy G s)
    (h : Tau_StructSub G (Path_RuntimeEq s) d1 d2) :
    Tau_SemMap G s d1 d2.
Proof.
  pose proof (Tau_StructSub_mapped_subst h
    (m := n) (rho := PathSubst_id n) (D := G) (s := s)
    Path_StructSubstitution_id Path_SubstRelHom_id
    (Store_StructPreciseTy_mapped_identity hstore)) as Hmapped.
  rewrite !Tau_subst_id in Hmapped. exact Hmapped.
Qed.

Print Assumptions Tau_SemMap_erase.
Print Assumptions Tm_StructPrecise_mappedPossible_of_binds.
Print Assumptions Store_MappedPossible_function_signature.
Print Assumptions Tau_StructConv_mapped_action.
Print Assumptions Tau_SemMap_action_of_conv.
Print Assumptions Tau_SemMap_action.
Print Assumptions Path_StructCheck_mapped_subst.
Print Assumptions Tau_StructSub_mapped_subst.
Print Assumptions Path_StructCheck_mapped_resolves.
Print Assumptions Tau_StructSub_mapped.
