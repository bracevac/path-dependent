From PathDependent.LambdaP Require Import FinFun Syntax Context.

Set Implicit Arguments.
Unset Strict Implicit.
Set Default Proof Using "Type".

(** Precise typing for paths.  The kind records whether a path selection
    denotes a term member ([star]) or an abstract type member ([iota]). *)
Inductive Path_Ty : forall {n k : _}, Ctx n -> Path n -> Tau n k -> Prop :=
| path_ty_var {n : nat} (G : Ctx n) (x : Fin.t n) (T : Ty n) :
    Ctx_Binds G x T ->
    Path_Ty G (path_var x) (tau_ty T)
| path_ty_fst {n : nat} {k : Kind} (G : Ctx n) (p : Path n)
    (S : Ty n) (a : Name) (d : Tau (Datatypes.S n) k) :
    Path_Ty G p (tau_ty (ty_pair S a d)) ->
    Path_Ty G (path_fst p) (tau_ty S)
| path_ty_sel_r {n : nat} {k : Kind} (G : Ctx n) (p : Path n)
    (S : Ty n) (a : Name) (d : Tau (Datatypes.S n) k) :
    Path_Ty G p (tau_ty (ty_pair S a d)) ->
    Path_Ty G (path_sel p a) (Tau_open d (path_fst p))
| path_ty_sel_l {n : nat} {k k' : Kind} (G : Ctx n) (p : Path n)
    (S : Ty n) (a b : Name) (d : Tau n k)
    (d' : Tau (Datatypes.S n) k') :
    Path_Ty G p (tau_ty (ty_pair S b d')) ->
    Path_Ty G (path_sel (path_fst p) a) d ->
    a <> b ->
    Path_Ty G (path_sel p a) d.

Arguments path_ty_var {n} G x T _.
Arguments path_ty_fst {n k} G p S a d _.
Arguments path_ty_sel_r {n k} G p S a d _.
Arguments path_ty_sel_l {n k k'} G p S a b d d' _ _ _.

(** Subtyping for proper types and abstract intervals.  The explicit
    [S <: T] premises on selection and interval formation are the
    non-emptiness guards of the Lean development. *)
Inductive Tau_Sub : forall {n k : _}, Ctx n -> Tau n k -> Tau n k -> Prop :=
| sub_refl {n : nat} {k : Kind} (G : Ctx n) (d : Tau n k) :
    Tau_Sub G d d
| sub_trans {n : nat} {k : Kind} (G : Ctx n)
    (d1 d2 d3 : Tau n k) :
    Tau_Sub G d1 d2 ->
    Tau_Sub G d2 d3 ->
    Tau_Sub G d1 d3
| sub_bot {n : nat} (G : Ctx n) (T : Ty n) :
    Tau_Sub G (tau_ty ty_bot) (tau_ty T)
| sub_top {n : nat} (G : Ctx n) (T : Ty n) :
    Tau_Sub G (tau_ty T) (tau_ty ty_top)
| sub_widen {n : nat} (G : Ctx n) (p : Path n) (T : Ty n) :
    Path_Ty G p (tau_ty T) ->
    Tau_Sub G (tau_ty (ty_single p)) (tau_ty T)
| sub_symm {n : nat} (G : Ctx n) (p q : Path n) :
    Path_Ty G p (tau_ty (ty_single q)) ->
    Tau_Sub G (tau_ty (ty_single q)) (tau_ty (ty_single p))
| sub_sel_hi {n : nat} (G : Ctx n) (p : Path n) (A : Name)
    (S T : Ty n) :
    Path_Ty G (path_sel p A) (tau_intv S T) ->
    Tau_Sub G (tau_ty S) (tau_ty T) ->
    Tau_Sub G (tau_ty (ty_tsel p A)) (tau_ty T)
| sub_sel_lo {n : nat} (G : Ctx n) (p : Path n) (A : Name)
    (S T : Ty n) :
    Path_Ty G (path_sel p A) (tau_intv S T) ->
    Tau_Sub G (tau_ty S) (tau_ty T) ->
    Tau_Sub G (tau_ty S) (tau_ty (ty_tsel p A))
| sub_fun {n : nat} (G : Ctx n) (S S' : Ty n)
    (T T' : Ty (Datatypes.S n)) :
    Tau_Sub G (tau_ty S') (tau_ty S) ->
    Tau_Sub (ctx_snoc G S') (tau_ty T) (tau_ty T') ->
    Tau_Sub G (tau_ty (ty_fun S T)) (tau_ty (ty_fun S' T'))
| sub_pair_fst {n : nat} {k : Kind} (G : Ctx n) (S S' : Ty n)
    (a : Name) (d : Tau (Datatypes.S n) k) :
    Tau_Sub G (tau_ty S) (tau_ty S') ->
    Tau_Sub G (tau_ty (ty_pair S a d)) (tau_ty (ty_pair S' a d))
| sub_pair_single_member {n : nat} {k : Kind} (G : Ctx n)
    (p : Path n) (P : Ty n) (a : Name)
    (d d' : Tau (Datatypes.S n) k) :
    Path_Ty G p (tau_ty P) ->
    Tau_Sub (ctx_snoc G (ty_single p)) d d' ->
    Tau_Sub G (Tau_open d p) (Tau_open d' p) ->
    Tau_Sub G
      (tau_ty (ty_pair (ty_single p) a d))
      (tau_ty (ty_pair (ty_single p) a d'))
| sub_bounds {n : nat} (G : Ctx n) (S S' T T' : Ty n) :
    Tau_Sub G (tau_ty S') (tau_ty S) ->
    Tau_Sub G (tau_ty T) (tau_ty T') ->
    Tau_Sub G (tau_ty S) (tau_ty T) ->
    Tau_Sub G (tau_intv S T) (tau_intv S' T').

Arguments sub_refl {n k} G d.
Arguments sub_trans {n k} G d1 d2 d3 _ _.
Arguments sub_bot {n} G T.
Arguments sub_top {n} G T.
Arguments sub_widen {n} G p T _.
Arguments sub_symm {n} G p q _.
Arguments sub_sel_hi {n} G p A S T _ _.
Arguments sub_sel_lo {n} G p A S T _ _.
Arguments sub_fun {n} G S S' T T' _ _.
Arguments sub_pair_fst {n k} G S S' a d _.
Arguments sub_pair_single_member {n k} G p P a d d' _ _ _.
Arguments sub_bounds {n} G S S' T T' _ _ _.

(** Well-formed generalized types. *)
Inductive Tau_Wf : forall {n k : _}, Ctx n -> Tau n k -> Prop :=
| wf_bot {n : nat} (G : Ctx n) :
    Tau_Wf G (tau_ty ty_bot)
| wf_top {n : nat} (G : Ctx n) :
    Tau_Wf G (tau_ty ty_top)
| wf_path {n : nat} (G : Ctx n) (p : Path n) (T : Ty n) :
    Path_Ty G p (tau_ty T) ->
    Tau_Wf G (tau_ty (ty_single p))
| wf_sel {n : nat} (G : Ctx n) (p : Path n) (S : Ty n)
    (T U : Ty (Datatypes.S n)) (A : Name) :
    Path_Ty G p (tau_ty (ty_pair S A (tau_intv T U))) ->
    Tau_Wf G (tau_ty (ty_tsel p A))
| wf_fun {n : nat} (G : Ctx n) (S : Ty n)
    (T : Ty (Datatypes.S n)) :
    Tau_Wf G (tau_ty S) ->
    Tau_Wf (ctx_snoc G S) (tau_ty T) ->
    Tau_Wf G (tau_ty (ty_fun S T))
| wf_pair {n : nat} {k : Kind} (G : Ctx n) (S : Ty n)
    (a : Name) (d : Tau (Datatypes.S n) k) :
    Tau_Wf G (tau_ty S) ->
    Tau_Wf (ctx_snoc G S) d ->
    Tau_Wf G (tau_ty (ty_pair S a d))
| wf_bounds {n : nat} (G : Ctx n) (S T : Ty n) :
    Tau_Wf G (tau_ty S) ->
    Tau_Wf G (tau_ty T) ->
    Tau_Sub G (tau_ty S) (tau_ty T) ->
    Tau_Wf G (tau_intv S T).

Arguments wf_bot {n} G.
Arguments wf_top {n} G.
Arguments wf_path {n} G p T _.
Arguments wf_sel {n} G p S T U A _.
Arguments wf_fun {n} G S T _ _.
Arguments wf_pair {n k} G S a d _ _.
Arguments wf_bounds {n} G S T _ _ _.

(** Typing for monadic-normal-form terms. *)
Inductive Tm_Ty : forall {n : nat}, Ctx n -> Tm n -> Ty n -> Prop :=
| tm_ty_path {n : nat} (G : Ctx n) (p : Path n) (T : Ty n) :
    Path_Ty G p (tau_ty T) ->
    Tm_Ty G (tm_path p) (ty_single p)
| tm_ty_abs {n : nat} (G : Ctx n) (S : Ty n)
    (t : Tm (Datatypes.S n)) (T : Ty (Datatypes.S n)) :
    Tm_Ty (ctx_snoc G S) t T ->
    Tau_Wf G (tau_ty S) ->
    Tm_Ty G (tm_abs S t) (ty_fun S T)
| tm_ty_app {n : nat} (G : Ctx n) (p q : Path n)
    (S : Ty n) (T : Ty (Datatypes.S n)) :
    Tm_Ty G (tm_path p) (ty_fun S T) ->
    Tm_Ty G (tm_path q) S ->
    Tm_Ty G (tm_app p q) (Ty_open T q)
| tm_ty_pair {n : nat} (G : Ctx n) (y z : Fin.t n)
    (S T : Ty n) (a : Name) :
    Ctx_Binds G y S ->
    Ctx_Binds G z T ->
    Tm_Ty G (tm_pair y a (def_val z))
      (ty_pair (ty_single (path_var y)) a
        (tau_ty (ty_single (Path_weaken (path_var z)))))
| tm_ty_tpair {n : nat} (G : Ctx n) (y : Fin.t n)
    (S T : Ty n) (A : Name) :
    Ctx_Binds G y S ->
    Tau_Wf G (tau_ty T) ->
    Tm_Ty G (tm_pair y A (def_type T))
      (ty_pair (ty_single (path_var y)) A
        (Tau_weaken (tau_intv T T)))
| tm_ty_let {n : nat} (G : Ctx n) (s : Tm n) (S T : Ty n)
    (t : Tm (Datatypes.S n)) :
    Tm_Ty G s S ->
    Tau_Wf G (tau_ty T) ->
    Tm_Ty (ctx_snoc G S) t (Ty_weaken T) ->
    Tm_Ty G (tm_let s t) T
| tm_ty_typed {n : nat} (G : Ctx n) (t : Tm n) (T : Ty n) :
    Tm_Ty G t T ->
    Tau_Wf G (tau_ty T) ->
    Tm_Ty G (tm_typed t T) T
| tm_ty_sub {n : nat} (G : Ctx n) (t : Tm n) (S T : Ty n) :
    Tm_Ty G t S ->
    Tau_Sub G (tau_ty S) (tau_ty T) ->
    Tau_Wf G (tau_ty T) ->
    Tm_Ty G t T.

Arguments tm_ty_path {n} G p T _.
Arguments tm_ty_abs {n} G S t T _ _.
Arguments tm_ty_app {n} G p q S T _ _.
Arguments tm_ty_pair {n} G y z S T a _ _.
Arguments tm_ty_tpair {n} G y S T A _ _.
Arguments tm_ty_let {n} G s S T t _ _ _.
Arguments tm_ty_typed {n} G t T _ _.
Arguments tm_ty_sub {n} G t S T _ _ _.
