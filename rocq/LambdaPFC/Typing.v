From PathDependent.LambdaPFC Require Import FinFun Syntax Context.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Precise typing for paths. *)
Inductive PathTy : forall {n : nat} {k : Kind},
    Ctx n -> Path n -> Tau n k -> Type :=
| PathTy_var {n : nat} (Gamma : Ctx n) (x : Fin n) :
    PathTy Gamma (PVar x) (TauTy (ctx_lookup Gamma x))
| PathTy_fst {n : nat} {Gamma : Ctx n} {p : Path n}
    {first : Ty n} {a : Name} {k : Kind} {member : Tau (S n) k} :
    PathTy Gamma p (TauTy (TyPair first a member)) ->
    PathTy Gamma (PFst p) (TauTy first)
| PathTy_sel_r {n : nat} {Gamma : Ctx n} {p : Path n}
    {first : Ty n} {a : Name} {k : Kind} {member : Tau (S n) k} :
    PathTy Gamma p (TauTy (TyPair first a member)) ->
    PathTy Gamma (PSel p a) (tau_open member (PFst p))
| PathTy_sel_l {n : nat} {Gamma : Ctx n} {p : Path n}
    {first : Ty n} {b : Name} {receiver_kind : Kind}
    {receiver_member : Tau (S n) receiver_kind}
    {a : Name} {k : Kind} {member : Tau n k} :
    PathTy Gamma p (TauTy (TyPair first b receiver_member)) ->
    PathTy Gamma (PSel (PFst p) a) member ->
    a <> b ->
    PathTy Gamma (PSel p a) member.

(** Proof-relevant subtyping for proper types and abstract intervals. *)
Inductive TauSub : forall {n : nat} {k : Kind},
    Ctx n -> Tau n k -> Tau n k -> Type :=
| TauSub_refl {n : nat} {k : Kind} {Gamma : Ctx n} {d : Tau n k} :
    TauSub Gamma d d
| TauSub_trans {n : nat} {k : Kind} {Gamma : Ctx n}
    {d1 d2 d3 : Tau n k} :
    TauSub Gamma d1 d2 -> TauSub Gamma d2 d3 -> TauSub Gamma d1 d3
| TauSub_bot {n : nat} {Gamma : Ctx n} {T : Ty n} :
    TauSub Gamma (TauTy TyBot) (TauTy T)
| TauSub_top {n : nat} {Gamma : Ctx n} {T : Ty n} :
    TauSub Gamma (TauTy T) (TauTy TyTop)
| TauSub_widen {n : nat} {Gamma : Ctx n} {p : Path n} {T : Ty n} :
    PathTy Gamma p (TauTy T) ->
    TauSub Gamma (TauTy (TySingle p)) (TauTy T)
| TauSub_symm {n : nat} {Gamma : Ctx n} {p q : Path n} :
    PathTy Gamma p (TauTy (TySingle q)) ->
    TauSub Gamma (TauTy (TySingle q)) (TauTy (TySingle p))
| TauSub_sel_hi {n : nat} {Gamma : Ctx n} {p : Path n} {A : Name}
    {lower upper : Ty n} :
    PathTy Gamma (PSel p A) (TauIntv lower upper) ->
    TauSub Gamma (TauTy lower) (TauTy upper) ->
    TauSub Gamma (TauTy (TyTSel p A)) (TauTy upper)
| TauSub_sel_lo {n : nat} {Gamma : Ctx n} {p : Path n} {A : Name}
    {lower upper : Ty n} :
    PathTy Gamma (PSel p A) (TauIntv lower upper) ->
    TauSub Gamma (TauTy lower) (TauTy upper) ->
    TauSub Gamma (TauTy lower) (TauTy (TyTSel p A))
| TauSub_fun {n : nat} {Gamma : Ctx n}
    {source source' : Ty n} {codomain codomain' : Ty (S n)} :
    TauSub Gamma (TauTy source') (TauTy source) ->
    TauSub (CtxSnoc Gamma source') (TauTy codomain) (TauTy codomain') ->
    TauSub Gamma (TauTy (TyFun source codomain))
      (TauTy (TyFun source' codomain'))
| TauSub_pair {n : nat} {Gamma : Ctx n} {source source' : Ty n}
    {a : Name} {k : Kind} {member member' : Tau (S n) k} :
    TauSub Gamma (TauTy source) (TauTy source') ->
    TauSub (CtxSnoc Gamma source) member member' ->
    TauSub Gamma (TauTy (TyPair source a member))
      (TauTy (TyPair source' a member'))
| TauSub_bounds {n : nat} {Gamma : Ctx n}
    {lower lower' upper upper' : Ty n} :
    TauSub Gamma (TauTy lower') (TauTy lower) ->
    TauSub Gamma (TauTy upper) (TauTy upper') ->
    TauSub Gamma (TauTy lower) (TauTy upper) ->
    TauSub Gamma (TauIntv lower upper) (TauIntv lower' upper').

(** Well-formed generalized types. *)
Inductive TauWf : forall {n : nat} {k : Kind},
    Ctx n -> Tau n k -> Type :=
| TauWf_bot {n : nat} {Gamma : Ctx n} : TauWf Gamma (TauTy TyBot)
| TauWf_top {n : nat} {Gamma : Ctx n} : TauWf Gamma (TauTy TyTop)
| TauWf_path {n : nat} {Gamma : Ctx n} {p : Path n} {T : Ty n} :
    PathTy Gamma p (TauTy T) -> TauWf Gamma (TauTy (TySingle p))
| TauWf_sel {n : nat} {Gamma : Ctx n} {p : Path n}
    {first : Ty n} {A : Name} {lower upper : Ty (S n)} :
    PathTy Gamma p (TauTy (TyPair first A (TauIntv lower upper))) ->
    TauWf Gamma (TauTy (TyTSel p A))
| TauWf_fun {n : nat} {Gamma : Ctx n} {source : Ty n}
    {codomain : Ty (S n)} :
    TauWf Gamma (TauTy source) ->
    TauWf (CtxSnoc Gamma source) (TauTy codomain) ->
    TauWf Gamma (TauTy (TyFun source codomain))
| TauWf_pair {n : nat} {Gamma : Ctx n} {source : Ty n}
    {a : Name} {k : Kind} {member : Tau (S n) k} :
    TauWf Gamma (TauTy source) ->
    TauWf (CtxSnoc Gamma source) member ->
    TauWf Gamma (TauTy (TyPair source a member))
| TauWf_bounds {n : nat} {Gamma : Ctx n} {lower upper : Ty n} :
    TauWf Gamma (TauTy lower) ->
    TauWf Gamma (TauTy upper) ->
    TauSub Gamma (TauTy lower) (TauTy upper) ->
    TauWf Gamma (TauIntv lower upper).

(** Typing for monadic-normal-form terms. *)
Inductive TmTy : forall {n : nat}, Ctx n -> Tm n -> Ty n -> Type :=
| TmTy_path {n : nat} {Gamma : Ctx n} {p : Path n} {T : Ty n} :
    PathTy Gamma p (TauTy T) ->
    TmTy Gamma (TmPath p) (TySingle p)
| TmTy_abs {n : nat} {Gamma : Ctx n} {source : Ty n}
    {body : Tm (S n)} {codomain : Ty (S n)} :
    TmTy (CtxSnoc Gamma source) body codomain ->
    TauWf Gamma (TauTy source) ->
    TmTy Gamma (TmAbs source body) (TyFun source codomain)
| TmTy_app {n : nat} {Gamma : Ctx n} {p q : Path n}
    {source : Ty n} {codomain : Ty (S n)} :
    TmTy Gamma (TmPath p) (TyFun source codomain) ->
    TmTy Gamma (TmPath q) source ->
    TmTy Gamma (TmApp p q) (ty_open codomain q)
| TmTy_pair {n : nat} {Gamma : Ctx n} {y z : Fin n} {a : Name} :
    TmTy Gamma (TmPair y a (DefVal z))
      (TyPair (TySingle (PVar y)) a
        (TauTy (TySingle (path_weaken (PVar z)))))
| TmTy_tpair {n : nat} {Gamma : Ctx n} {y : Fin n}
    {A : Name} {T : Ty n} :
    TauWf Gamma (TauTy T) ->
    TmTy Gamma (TmPair y A (DefType T))
      (TyPair (TySingle (PVar y)) A
        (tau_weaken (TauIntv T T)))
| TmTy_let {n : nat} {Gamma : Ctx n} {bound : Tm n}
    {body : Tm (S n)} {source result : Ty n} :
    TmTy Gamma bound source ->
    TauWf Gamma (TauTy result) ->
    TmTy (CtxSnoc Gamma source) body (ty_weaken result) ->
    TmTy Gamma (TmLet bound body) result
| TmTy_sub {n : nat} {Gamma : Ctx n} {term : Tm n}
    {source target : Ty n} :
    TmTy Gamma term source ->
    TauSub Gamma (TauTy source) (TauTy target) ->
    TauWf Gamma (TauTy target) ->
    TmTy Gamma term target.
