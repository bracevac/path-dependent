From Equations Require Import Equations.
From PathDependent.LambdaPFC Require Import
  FinFun Syntax Context Typing Runtime RuntimeEquality Valuation.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Mutually positive finite semantic evidence. *)
Inductive Environment : forall {n m : nat},
    Ctx n -> Valuation n m -> Store m -> Type :=
| Env_intro {n m : nat} {Gamma : Ctx n} {rho : Valuation n m}
    {sigma : Store m} :
    (forall x : Fin n,
      StorePossible sigma (apply rho x)
        (ty_rename (ctx_lookup Gamma x) rho)) ->
    Environment Gamma rho sigma

with StorePossible : forall {m : nat}, Store m -> Fin m -> Ty m -> Type :=
| Possible_top {m : nat} {sigma : Store m} {x : Fin m} :
    StorePossible sigma x TyTop
| Possible_fun {m : nat} {sigma : Store m} {x : Fin m}
    {A S : Ty m} {body : Tm (Datatypes.S m)}
    {B U : Ty (Datatypes.S m)} :
    StoreBinds sigma x (TmAbs A body) ->
    BodyClosure sigma A body B ->
    Coercion sigma (TauTy S) (TauTy A) ->
    DeferredCoercion sigma S B U ->
    StorePossible sigma x (TyFun S U)
| Possible_pair {m : nat} {sigma : Store m} {x y : Fin m}
    {a : Name} {k : Kind} {delta : Def m k}
    {S : Ty m} {d : Tau (Datatypes.S m) k} :
    StoreBinds sigma x (TmPair y a delta) ->
    StorePossible sigma y S ->
    ReferentRealizes sigma (def_referent delta) (tau_open d (PVar y)) ->
    StorePossible sigma x (TyPair S a d)
| Possible_single {m : nat} {sigma : Store m} {x : Fin m}
    {p : Path m} :
    PathResolve p sigma (RefLoc x) ->
    StorePossible sigma x (TySingle p)
| Possible_selection {m : nat} {sigma : Store m} {x : Fin m}
    {p : Path m} {a : Name} {W : Ty m} :
    PathResolve (PSel p a) sigma (RefType W) ->
    StorePossible sigma x W ->
    StorePossible sigma x (TyTSel p a)

with ReferentRealizes : forall {m : nat} {k : Kind}, Store m ->
    PathReferent m -> Tau m k -> Type :=
| Realizes_loc {m : nat} {sigma : Store m} {x : Fin m} {T : Ty m} :
    StorePossible sigma x T ->
    ReferentRealizes sigma (RefLoc x) (TauTy T)
| Realizes_type {m : nat} {sigma : Store m} {L W U : Ty m} :
    Coercion sigma (TauTy L) (TauTy W) ->
    Coercion sigma (TauTy W) (TauTy U) ->
    ReferentRealizes sigma (RefType W) (TauIntv L U)

with Coercion : forall {m : nat} {k : Kind}, Store m ->
    Tau m k -> Tau m k -> Type :=
| Coercion_refl {m : nat} {k : Kind} {sigma : Store m}
    {d : Tau m k} : Coercion sigma d d
| Coercion_trans {m : nat} {k : Kind} {sigma : Store m}
    {d1 d2 d3 : Tau m k} :
    Coercion sigma d1 d2 -> Coercion sigma d2 d3 ->
    Coercion sigma d1 d3
| Coercion_runtime {m : nat} {k : Kind} {sigma : Store m}
    {d1 d2 : Tau m k} :
    TauRuntimeConv (PathRuntimeEq sigma) d1 d2 ->
    Coercion sigma d1 d2
| Coercion_bot {m : nat} {sigma : Store m} {T : Ty m} :
    Coercion sigma (TauTy TyBot) (TauTy T)
| Coercion_top {m : nat} {sigma : Store m} {T : Ty m} :
    Coercion sigma (TauTy T) (TauTy TyTop)
| Coercion_widen {m : nat} {sigma : Store m} {p : Path m}
    {x : Fin m} {T : Ty m} :
    PathResolve p sigma (RefLoc x) ->
    StorePossible sigma x T ->
    Coercion sigma (TauTy (TySingle p)) (TauTy T)
| Coercion_alias {m : nat} {sigma : Store m} {p q : Path m}
    {x : Fin m} :
    PathResolve p sigma (RefLoc x) ->
    PathResolve q sigma (RefLoc x) ->
    Coercion sigma (TauTy (TySingle q)) (TauTy (TySingle p))
| Coercion_sel_lo {m : nat} {sigma : Store m} {p : Path m}
    {a : Name} {L W : Ty m} :
    PathResolve (PSel p a) sigma (RefType W) ->
    Coercion sigma (TauTy L) (TauTy W) ->
    Coercion sigma (TauTy L) (TauTy (TyTSel p a))
| Coercion_sel_hi {m : nat} {sigma : Store m} {p : Path m}
    {a : Name} {W U : Ty m} :
    PathResolve (PSel p a) sigma (RefType W) ->
    Coercion sigma (TauTy W) (TauTy U) ->
    Coercion sigma (TauTy (TyTSel p a)) (TauTy U)
| Coercion_fun {m : nat} {sigma : Store m} {S S' : Ty m}
    {T T' : Ty (Datatypes.S m)} :
    Coercion sigma (TauTy S') (TauTy S) ->
    DeferredCoercion sigma S' T T' ->
    Coercion sigma (TauTy (TyFun S T)) (TauTy (TyFun S' T'))
| Coercion_pair {m : nat} {sigma : Store m} {S S' : Ty m}
    {a : Name} {k : Kind} {d d' : Tau (Datatypes.S m) k} :
    Coercion sigma (TauTy S) (TauTy S') ->
    MemberClosure sigma S d d' ->
    Coercion sigma (TauTy (TyPair S a d)) (TauTy (TyPair S' a d'))
| Coercion_bounds {m : nat} {sigma : Store m}
    {S S' T T' : Ty m} :
    Coercion sigma (TauTy S') (TauTy S) ->
    Coercion sigma (TauTy T) (TauTy T') ->
    Coercion sigma (TauIntv S T) (TauIntv S' T')

with DeferredCoercion : forall {m : nat}, Store m -> Ty m ->
    Ty (Datatypes.S m) -> Ty (Datatypes.S m) -> Type :=
| Deferred_refl {m : nat} {sigma : Store m} {S : Ty m}
    {T : Ty (Datatypes.S m)} : DeferredCoercion sigma S T T
| Deferred_trans {m : nat} {sigma : Store m} {S : Ty m}
    {T U V : Ty (Datatypes.S m)} :
    DeferredCoercion sigma S T U ->
    DeferredCoercion sigma S U V ->
    DeferredCoercion sigma S T V
| Deferred_runtime {m : nat} {sigma : Store m} {S : Ty m}
    {T U : Ty (Datatypes.S m)} :
    TauRuntimeConv (PathScopedLift (PathRuntimeEq sigma))
      (TauTy T) (TauTy U) ->
    DeferredCoercion sigma S T U
| Deferred_narrow {m : nat} {sigma : Store m} {S S' : Ty m}
    {T U : Ty (Datatypes.S m)} :
    Coercion sigma (TauTy S') (TauTy S) ->
    DeferredCoercion sigma S T U ->
    DeferredCoercion sigma S' T U
| Deferred_source {n m : nat} {Gamma : Ctx n}
    {rho : Valuation n m} {sigma : Store m} {S : Ty n}
    {T U : Ty (Datatypes.S n)} :
    Environment Gamma rho sigma ->
    TauSub (CtxSnoc Gamma S) (TauTy T) (TauTy U) ->
    DeferredCoercion sigma (ty_rename S rho)
      (ty_rename T (ext rho)) (ty_rename U (ext rho))

with MemberClosure : forall {m : nat}, Store m -> Ty m ->
    forall {k : Kind}, Tau (Datatypes.S m) k ->
      Tau (Datatypes.S m) k -> Type :=
| Member_source {n m : nat} {Gamma : Ctx n}
    {rho : Valuation n m} {sigma : Store m} {S : Ty n}
    {k : Kind} {d d' : Tau (Datatypes.S n) k} :
    Environment Gamma rho sigma ->
    TauSub (CtxSnoc Gamma S) d d' ->
    MemberClosure sigma (ty_rename S rho)
      (tau_rename d (ext rho)) (tau_rename d' (ext rho))

with BodyClosure : forall {m : nat}, Store m -> Ty m ->
    Tm (Datatypes.S m) -> Ty (Datatypes.S m) -> Type :=
| Body_source {n m : nat} {Gamma : Ctx n}
    {rho : Valuation n m} {sigma : Store m} {S : Ty n}
    {body : Tm (Datatypes.S n)} {T : Ty (Datatypes.S n)} :
    Environment Gamma rho sigma ->
    TmTy (CtxSnoc Gamma S) body T ->
    BodyClosure sigma (ty_rename S rho)
      (tm_rename body (ext rho)) (ty_rename T (ext rho)).

Derive Signature for Environment.
Derive NoConfusionHom for Environment.
Derive Signature for StorePossible.
Derive NoConfusionHom for StorePossible.
Derive Signature for ReferentRealizes.
Derive NoConfusionHom for ReferentRealizes.

Arguments Env_intro {n m Gamma rho sigma} _.

(** Retrieve the realization stored at a source variable. *)
Definition environment_lookup {n m : nat} {Gamma : Ctx n}
    {rho : Valuation n m} {sigma : Store m}
    (environment : Environment Gamma rho sigma) (x : Fin n) :
    StorePossible sigma (apply rho x)
      (ty_rename (ctx_lookup Gamma x) rho).
Proof.
  destruct environment as [n0 m0 Gamma0 rho0 sigma0 lookup].
  exact (lookup x).
Defined.

(** The empty source context has the initial semantic environment. *)
Definition environment_empty :
    Environment CtxNil (id 0) StoreEmpty.
Proof.
  apply Env_intro. intro x.
  exact (@fin_elim0 (fun z => StorePossible StoreEmpty
    (apply (id 0) z) (ty_rename (ctx_lookup CtxNil z) (id 0))) x).
Defined.

(** Extend an environment with a concrete newest binding. *)
Definition environment_snoc {n m : nat} {Gamma : Ctx n}
    {rho : Valuation n m} {sigma : Store m} {S : Ty n} {y : Fin m}
    (environment : Environment Gamma rho sigma)
    (argument : StorePossible sigma y (ty_rename S rho)) :
    Environment (CtxSnoc Gamma S) (valuation_snoc rho y) sigma.
Proof.
  apply Env_intro. intro x.
  assert (Hcomp : comp (weaken n) (valuation_snoc rho y) = rho).
  { apply finfun_ext. intro i.
    rewrite comp_apply, weaken_apply, valuation_snoc_succ. reflexivity. }
  refine (fin_case (P := fun x => StorePossible sigma
      (apply (valuation_snoc rho y) x)
      (ty_rename (ctx_lookup (CtxSnoc Gamma S) x)
        (valuation_snoc rho y))) _ _ x).
  - simp ctx_lookup. rewrite valuation_snoc_zero.
    unfold ty_weaken. rewrite ty_rename_rename, Hcomp.
    exact argument.
  - intro i. simp ctx_lookup. rewrite valuation_snoc_succ.
    unfold ty_weaken. rewrite ty_rename_rename, Hcomp.
    exact (environment_lookup environment i).
Defined.

Print Assumptions environment_snoc.
