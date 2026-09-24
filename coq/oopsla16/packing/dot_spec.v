(*
DOT
T ::= Bot | Top | T1 /\ T2 | T1 \/ T2 |
      { def m(x: S): U^x } | { type A: S..U } | x.A | { z => T^z }
t ::= x | { y => d^y... } | t.m(t)
d ::= { def m(x: S): U^x = t^x } | { type A = T }
*)

(* in small-step *)
(* Minimal preamble replacing [Require Export SfLib] and the Arith requires of
   the original dot.v: we need lists (for [], ::, ++, length) and beq_nat,
   which was in Arith.EqNat in Coq 8.4 but is gone in Coq 8.19. Defining it
   here keeps every definition below character-identical to dot.v. *)
Require Export List.
Export ListNotations.

Fixpoint beq_nat (n m : nat) : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n', S m' => beq_nat n' m'
  end.


(*# Syntax #*)

Definition id := nat. (* identifiers for variables: x,y,z *)
Definition lb := nat. (* labels for records: L, m *)

Inductive vr : Type :=
  | TVar   : bool(*true for concrete context, false for abstract context *) ->
             id(*absolute position in context, from origin, invariant under context extension*) -> vr
  | TVarB  : id(*bound variable, de Bruijn, locally nameless style -- see open *) -> vr
.

Inductive ty : Type :=
  | TBot   : ty (* bottom type *)
  | TTop   : ty (* top type *)
  | TFun   : lb -> ty -> ty -> ty (* dependent function / method member type:
                                     { def m(x: S): U^x },
                                     where x is locally bound in U *)
  | TTyp   : lb -> ty -> ty -> ty (* type member type: { type L: S..U } *)
  | TSel   : vr -> lb -> ty (* type selection: x.L *)
  | TBind  : ty -> ty (* Recursive binder: { z => T^z },
                         where z is locally bound in T *)
  | TAnd   : ty -> ty -> ty (* Intersection Type: T1 /\ T2 *)
  | TOr    : ty -> ty -> ty (* Union Type: T1 \/ T2 *)
.

Inductive tm : Type :=
  | tvar  : bool(*like TVar: true for concrete, false for hypothetical *) -> id -> tm (* variable: x *)
  (* N.B.: no varB -- terms just use absolute identifers directly *)
  | tobj  : dms(*self is next slot in abstract context -- see subst_tm*) -> tm (* new object instance: { z => d... } *)
  | tapp  : tm -> lb -> tm -> tm (* method invocation: t.m(t) *)

with dm : Type := (* initialization / member definition --
                     the labels, e.g. m & A, are determined from the position in member list, dms *)
  | dfun : option ty -> option ty -> tm -> dm (* method: { def m(x[: S])[: U] = t }, where the types [: S] and [: U] are optional *)
  (* Church vs Curry: we show that all options work, by making parameter and return types optional,
     when defining a method. *)
  | dty  : ty -> dm (* type: { type L = T } *)

(* we use our own list-like structure for easy recursion, e.g. in subst_tm *)
with dms : Type := (* list of member defs *)
  | dnil : dms
  | dcons : dm -> dms -> dms
.

Fixpoint dms_to_list (ds: dms) : list dm :=
  match ds with
    | dnil => []
    | dcons d ds => d :: dms_to_list ds
  end.

Inductive vl : Type :=
  | vobj  : dms -> vl
.

Definition venv := list vl. (*rho G*)
Definition tenv := list ty. (*Gamma GH*)

Hint Unfold venv.
Hint Unfold tenv.

(*# Variable Binding #*)

Fixpoint index {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l'  => if beq_nat n (length l') then Some a else index n l'
  end.

(*
   closed i j k -- well-bound in
   an abstract environment GH of size >= i
   a concrete environment G of size >= j
   under >= k binders/de Bruijn levels
*)
Inductive vr_closed: nat(*abstract, TVar false i*) -> nat(*concrete, TVar true j*) -> nat(*bound, TVarB k*) -> vr -> Prop :=
| cl_var0: forall i j k x,
    i > x ->
    vr_closed i j k (TVar false x)
| cl_var1: forall i j k x,
    j > x ->
    vr_closed i j k (TVar true x)
| cl_varB: forall i j k x,
    k > x ->
    vr_closed i j k (TVarB x).

Inductive closed: nat(*abstract, TVar false i*) -> nat(*concrete, TVar true j*) -> nat(*bound, TVarB k*) -> ty -> Prop :=
| cl_bot: forall i j k,
    closed i j k TBot
| cl_top: forall i j k,
    closed i j k TTop
| cl_fun: forall i j k l T1 T2,
    closed i j k T1 ->
    closed i j (S k) T2 ->
    closed i j k (TFun l T1 T2)
| cl_typ: forall i j k l T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TTyp l T1 T2)
| cl_sel: forall i j k p1 l,
    vr_closed i j k p1 ->
    closed i j k (TSel p1 l)
| cl_bind: forall i j k T1,
    closed i j (S k) T1 ->
    closed i j k (TBind T1)
| cl_and: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TAnd T1 T2)
| cl_or: forall i j k T1 T2,
    closed i j k T1 ->
    closed i j k T2 ->
    closed i j k (TOr T1 T2)
.

(* substitute a locally bound variable at de Brujin level k with variable u in type T *)
Definition vr_open (k: nat) (u: vr) (p: vr) : vr :=
  match p with
    | TVar b x => TVar b x (* free var remains free. functional, so we can't check for conflict *)
    | TVarB x => if beq_nat k x then u else TVarB x
  end.
Fixpoint open (k: nat) (u: vr) (T: ty) { struct T }: ty :=
  match T with
    | TTop        => TTop
    | TBot        => TBot
    | TSel p1 l     => TSel (vr_open k u p1) l
    | TFun l T1 T2  => TFun l (open k u T1) (open (S k) u T2)
    | TTyp l T1 T2  => TTyp l (open k u T1) (open k u T2)
    | TBind T1    => TBind (open (S k) u T1)
    | TAnd T1 T2  => TAnd (open k u T1) (open k u T2)
    | TOr T1 T2   => TOr (open k u T1) (open k u T2)
  end.

(* substitute the first abstract variable (id 0) with variable u in type T --
   all other abstract variables are shifted (id decremented) to fit the shrinked abstract context
*)
Definition vr_subst (u : vr) (X : vr): vr :=
  match X with
    | TVarB i      => TVarB i
    | TVar true i  => TVar true i
    (* subst the _first_ aka _oldest_ abstract variables,
       the other abstract variables are shifted to resolve in the shrinked context *)
    | TVar false i => if beq_nat i 0 then u else TVar false (i-1)
  end.
Fixpoint subst (u : vr) (T : ty) {struct T} : ty :=
  match T with
    | TTop         => TTop
    | TBot         => TBot
    | TTyp l T1 T2 => TTyp l (subst u T1) (subst u T2)
    | TSel p1 l    => TSel (vr_subst u p1) l
    | TFun l T1 T2 => TFun l (subst u T1) (subst u T2)
    | TBind T2     => TBind (subst u T2)
    | TAnd T1 T2   => TAnd (subst u T1) (subst u T2)
    | TOr T1 T2    => TOr (subst u T1) (subst u T2)
  end.

(* substitute the first hypothetical variable with term u in term t --
   like subst, shifts other hypothetical variables *)
Fixpoint subst_tm (u:nat) (t : tm) {struct t} : tm :=
  match t with
    | tvar true i         => tvar true i
    | tvar false i        => if beq_nat i 0 then (tvar true u) else tvar false (i-1)
    | tobj ds             => tobj (subst_dms u ds)
    | tapp t1 l t2          => tapp (subst_tm u t1) l (subst_tm u t2)
  end
with subst_dm (u:nat) (d: dm) {struct d} : dm :=
  match d with
    | dty T        => dty (subst (TVar true u) T)
    | dfun T1 T2 t => dfun (option_map (subst (TVar true u)) T1) (option_map (subst (TVar true u)) T2) (subst_tm u t)
  end
with subst_dms (u:nat) (ds: dms) {struct ds} : dms :=
  match ds with
    | dnil        => dnil
    | dcons d ds1  => dcons (subst_dm u d) (subst_dms u ds1)
  end.

(* Shortcut for the common case of replacing abstract with concrete. *)
Definition substt x T := (subst (TVar true x) T).
Hint Immediate substt.

(*# Operational Semantics #*)

(* Reduction semantics  *)
Inductive step : venv -> tm -> venv -> tm -> Prop :=
(* Computation Rules *)
| ST_Obj : forall G1 D,
    step G1 (tobj D) (vobj (subst_dms (length G1) D)::G1) (tvar true (length G1))
| ST_AppAbs : forall G1 f l x ds T1 T2 t12,
    index f G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dfun T1 T2 t12) ->
    step G1 (tapp (tvar true f) l (tvar true x)) G1 (subst_tm x t12)
(* Congruence Rules *)
| ST_App1 : forall G1 G1' t1 t1' l t2,
    step G1 t1 G1' t1' ->
    step G1 (tapp t1 l t2) G1' (tapp t1' l t2)
| ST_App2 : forall G1 G1' f t2 l t2',
    step G1 t2 G1' t2' ->
    step G1 (tapp (tvar true f) l t2) G1' (tapp (tvar true f) l t2')
.

(*# Static Semantics #*)

Definition eq_some {X} (OT:option X) (T:X) := OT=None \/ OT=Some T.

(* : -- typing *)
Inductive has_type : tenv -> venv -> tm -> ty -> nat -> Prop :=
  | T_Vary : forall GH G1 x ds ds' T T' n1,
      index x G1 = Some (vobj ds) ->
      dms_has_type [T'] G1 ds' T' n1 ->
      subst_dms x ds' = ds ->
      substt x T' = T ->
      closed 0 (length G1) 0 T ->
      has_type GH G1 (tvar true x) T (S n1)
  | T_Varz : forall G1 GH x T n1,
      index x GH = Some T ->
      closed (length GH) (length G1) 0 T ->
      has_type GH G1 (tvar false x) T (S n1)
  | T_VarPack : forall GH G1 b x T1 T1' n1,
      has_type GH G1 (tvar b x) T1' n1 ->
      T1' = (open 0 (TVar b x) T1) ->
      closed (length GH) (length G1) 1 T1 ->
      has_type GH G1 (tvar b x) (TBind T1) (S n1)
  | T_VarUnpack : forall GH G1 b x T1 T1' n1,
      has_type GH G1 (tvar b x) (TBind T1) n1 ->
      T1' = (open 0 (TVar b x) T1) ->
      closed (length GH) (length G1) 0 T1' ->
      has_type GH G1 (tvar b x) T1' (S n1)
  | T_Obj : forall GH G1 ds T T' n1,
      dms_has_type (T'::GH) G1 ds T' n1 ->
      T' = open 0 (TVar false (length GH)) T ->
      closed (length GH) (length G1) 1 T ->
      has_type GH G1 (tobj ds) (TBind T) (S n1)
  | T_App : forall l T1 T2 GH G1 t1 t2 n1 n2,
      has_type GH G1 t1 (TFun l T1 T2) n1 ->
      has_type GH G1 t2 T1 n2 ->
      closed (length GH) (length G1) 0 T2 ->
      has_type GH G1 (tapp t1 l t2) T2 (S (n1+n2))
  | T_AppVar : forall l T1 T2 T2' GH G1 t1 b2 x2 n1 n2,
      has_type GH G1 t1 (TFun l T1 T2) n1 ->
      has_type GH G1 (tvar b2 x2) T1 n2 ->
      T2' = (open 0 (TVar b2 x2) T2) ->
      closed (length GH) (length G1) 0 T2' ->
      has_type GH G1 (tapp t1 l (tvar b2 x2)) T2' (S (n1+n2))
  | T_Sub : forall GH G1 t T1 T2 n1 n2,
      has_type GH G1 t T1 n1 ->
      stp GH G1 T1 T2 n2 ->
      has_type GH G1 t T2 (S (n1 + n2))

(* : -- member initialization *)
with dms_has_type: tenv -> venv -> dms -> ty -> nat -> Prop :=
  | D_Nil : forall GH G1 n1,
      dms_has_type GH G1 dnil TTop (S n1)
  | D_Typ : forall GH G1 l T11 ds TS T n1,
      dms_has_type GH G1 ds TS n1 ->
      closed (length GH) (length G1) 0 T11 ->
      l = length (dms_to_list ds) ->
      T = TAnd (TTyp l T11 T11) TS ->
      dms_has_type GH G1 (dcons (dty T11) ds) T (S n1)
  | D_Fun : forall GH G1 l OT11 T11 OT12 T12 T12' t12 ds TS T n1 n2,
      dms_has_type GH G1 ds TS n1 ->
      has_type (T11::GH) G1 t12 T12' n2 ->
      T12' = (open 0 (TVar false (length GH)) T12) ->
      closed (length GH) (length G1) 0 T11 ->
      closed (length GH) (length G1) 1 T12 ->
      l = length (dms_to_list ds) ->
      T = TAnd (TFun l T11 T12) TS ->
      eq_some OT11 T11 ->
      eq_some OT12 T12 ->
      dms_has_type GH G1 (dcons (dfun OT11 OT12 t12) ds) T (S (n1+n2))

(* <: -- subtyping *)
with stp: tenv -> venv -> ty -> ty -> nat -> Prop :=
| stp_bot: forall GH G1 T n1,
    closed (length GH) (length G1) 0  T ->
    stp GH G1 TBot T (S n1)
| stp_top: forall GH G1 T n1,
    closed (length GH) (length G1) 0 T ->
    stp GH G1 T  TTop (S n1)
| stp_fun: forall GH G1 l T1 T2 T3 T4 T2' T4' n1 n2,
    T2' = (open 0 (TVar false (length GH)) T2) ->
    T4' = (open 0 (TVar false (length GH)) T4) ->
    closed (length GH) (length G1) 1 T2 ->
    closed (length GH) (length G1) 1 T4 ->
    stp GH G1 T3 T1 n1 ->
    stp (T3::GH) G1 T2' T4' n2 ->
    stp GH G1 (TFun l T1 T2) (TFun l T3 T4) (S (n1+n2))
| stp_typ: forall GH G1 l T1 T2 T3 T4 n1 n2,
    stp GH G1 T3 T1 n2 ->
    stp GH G1 T2 T4 n1 ->
    stp GH G1 (TTyp l T1 T2) (TTyp l T3 T4) (S (n1+n2))

| stp_strong_sel1: forall GH G1 l T2 ds TX x n1,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    stp [] G1 TX T2 n1 ->
    stp GH G1 (TSel (TVar true x) l) T2 (S n1)
| stp_strong_sel2: forall GH G1 l T1 ds TX x n1,
    index x G1 = Some (vobj ds) ->
    index l (dms_to_list ds) = Some (dty TX) ->
    stp [] G1 T1 TX n1 ->
    stp GH G1 T1 (TSel (TVar true x) l) (S n1)

| stp_sel1: forall GH G1 l T2 x n1,
    htp  GH G1 x (TTyp l TBot T2) n1 ->
    stp GH G1 (TSel (TVar false x) l) T2 (S n1)

| stp_sel2: forall GH G1 l T1 x n1,
    htp  GH G1 x (TTyp l T1 TTop) n1 ->
    stp GH G1 T1 (TSel (TVar false x) l) (S n1)

| stp_selx: forall GH G1 l p1 n1,
    vr_closed (length GH) (length G1) 0 p1 ->
    stp GH G1 (TSel p1 l) (TSel p1 l) (S n1)

| stp_bind1: forall GH G1 T1 T1' T2 n1,
    stp (T1'::GH) G1 T1' T2 n1 ->
    T1' = (open 0 (TVar false (length GH)) T1) ->
    closed (length GH) (length G1) 1 T1 ->
    closed (length GH) (length G1) 0 T2 ->
    stp GH G1 (TBind T1) T2 (S n1)

| stp_bindx: forall GH G1 T1 T1' T2 T2' n1,
    stp (T1'::GH) G1 T1' T2' n1 ->
    T1' = (open 0 (TVar false (length GH)) T1) ->
    T2' = (open 0 (TVar false (length GH)) T2) ->
    closed (length GH) (length G1) 1 T1 ->
    closed (length GH) (length G1) 1 T2 ->
    stp GH G1 (TBind T1) (TBind T2) (S n1)

| stp_and11: forall GH G1 T1 T2 T n1,
    stp GH G1 T1 T n1 ->
    closed (length GH) (length G1) 0 T2 ->
    stp GH G1 (TAnd T1 T2) T (S n1)
| stp_and12: forall GH G1 T1 T2 T n1,
    stp GH G1 T2 T n1 ->
    closed (length GH) (length G1) 0 T1 ->
    stp GH G1 (TAnd T1 T2) T (S n1)
| stp_and2: forall GH G1 T1 T2 T n1 n2,
    stp GH G1 T T1 n1 ->
    stp GH G1 T T2 n2 ->
    stp GH G1 T (TAnd T1 T2) (S (n1+n2))

| stp_or21: forall GH G1 T1 T2 T n1,
    stp GH G1 T T1 n1 ->
    closed (length GH) (length G1) 0 T2 ->
    stp GH G1 T (TOr T1 T2) (S n1)
| stp_or22: forall GH G1 T1 T2 T n1,
    stp GH G1 T T2 n1 ->
    closed (length GH) (length G1) 0 T1 ->
    stp GH G1 T (TOr T1 T2) (S n1)
| stp_or1: forall GH G1 T1 T2 T n1 n2,
    stp GH G1 T1 T n1 ->
    stp GH G1 T2 T n2 ->
    stp GH G1 (TOr T1 T2) T (S (n1+n2))

| stp_trans: forall GH G1 T1 T2 T3 n1 n2,
    stp GH G1 T1 T2 n1 ->
    stp GH G1 T2 T3 n2 ->
    stp GH G1 T1 T3 (S (n1+n2))

(* :! -- typing for type selection in subtyping *)
with htp: tenv -> venv -> id -> ty -> nat -> Prop :=
| htp_var: forall GH G1 x TX n1,
    index x GH = Some TX ->
    closed (S x) (length G1) 0 TX ->
    htp GH G1 x TX (S n1)
| htp_unpack: forall GH G1 x TX n1,
    htp GH G1 x (TBind TX) n1 ->
    closed (S x) (length G1) 1 TX ->
    htp GH G1 x (open 0 (TVar false x) TX) (S n1)
| htp_sub: forall GH GU GL G1 x T1 T2 n1 n2,
    (* use restricted GH. note: this is slightly different
    from the big-step version b/c here we do not distinguish
    if variables are bound in terms vs types. it would be easy
    to do exactly the same thing by adding this distinction. *)
    htp GH G1 x T1 n1 ->
    stp GL G1 T1 T2 n2 ->
    length GL = S x ->
    GH = GU ++ GL ->
    htp GH G1 x T2 (S (n1+n2)).

Definition has_typed GH G1 x T1 := exists n, has_type GH G1 x T1 n.

Definition stpd GH G1 T1 T2 := exists n, stp GH G1 T1 T2 n.

Definition htpd GH G1 x T1 := exists n, htp GH G1 x T1 n.
