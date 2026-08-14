From Equations Require Import Equations.
From PathDependent.LambdaPFC Require Import FinFun.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

Definition Name : Type := nat.

Inductive Kind : Type :=
| KStar
| KIota.

Definition kind_eq_dec (x y : Kind) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Inductive Path : nat -> Type :=
| PVar {n : nat} : Fin n -> Path n
| PFst {n : nat} : Path n -> Path n
| PSel {n : nat} : Path n -> Name -> Path n.

Arguments PVar {n} _.
Arguments PFst {n} _.
Arguments PSel {n} _ _.

Derive Signature for Path.
Derive NoConfusionHom for Path.
Derive EqDec for Path.

Definition path_eq_dec {n : nat} (p q : Path n) : {p = q} + {p <> q} :=
  eq_dec p q.

Inductive Tau : nat -> Kind -> Type :=
| TauTy {n : nat} : Ty n -> Tau n KStar
| TauIntv {n : nat} : Ty n -> Ty n -> Tau n KIota
with Def : nat -> Kind -> Type :=
| DefVal {n : nat} : Fin n -> Def n KStar
| DefType {n : nat} : Ty n -> Def n KIota
with Ty : nat -> Type :=
| TyTop {n : nat} : Ty n
| TyBot {n : nat} : Ty n
| TyFun {n : nat} : Ty n -> Ty (S n) -> Ty n
| TyPair {n : nat} {k : Kind} : Ty n -> Name -> Tau (S n) k -> Ty n
| TySingle {n : nat} : Path n -> Ty n
| TyTSel {n : nat} : Path n -> Name -> Ty n
with Tm : nat -> Type :=
| TmPath {n : nat} : Path n -> Tm n
| TmAbs {n : nat} : Ty n -> Tm (S n) -> Tm n
| TmPair {n : nat} {k : Kind} : Fin n -> Name -> Def n k -> Tm n
| TmApp {n : nat} : Path n -> Path n -> Tm n
| TmLet {n : nat} : Tm n -> Tm (S n) -> Tm n.

Arguments TauTy {n} _.
Arguments TauIntv {n} _ _.
Arguments DefVal {n} _.
Arguments DefType {n} _.
Arguments TyTop {n}.
Arguments TyBot {n}.
Arguments TyFun {n} _ _.
Arguments TyPair {n k} _ _ _.
Arguments TySingle {n} _.
Arguments TyTSel {n} _ _.
Arguments TmPath {n} _.
Arguments TmAbs {n} _ _.
Arguments TmPair {n k} _ _ _.
Arguments TmApp {n} _ _.
Arguments TmLet {n} _ _.

(** Syntactic variables and values. *)
Inductive Path_IsVar {n : nat} : Path n -> Prop :=
| IsVar_var (x : Fin n) : Path_IsVar (PVar x).

Inductive Tm_IsValue {n : nat} : Tm n -> Prop :=
| IsValue_abs (A : Ty n) (body : Tm (S n)) :
    Tm_IsValue (TmAbs A body)
| IsValue_pair {k : Kind} (y : Fin n) (a : Name) (d : Def n k) :
    Tm_IsValue (TmPair y a d).

(** Renaming. *)
Equations path_rename {n m : nat} (p : Path n) (f : FinFun n m) : Path m :=
path_rename (PVar x) f := PVar (apply f x);
path_rename (PFst p) f := PFst (path_rename p f);
path_rename (PSel p a) f := PSel (path_rename p f) a.

Equations ty_rename {n m : nat} (T : Ty n) (f : FinFun n m) : Ty m
    by struct T :=
ty_rename TyTop f := TyTop;
ty_rename TyBot f := TyBot;
ty_rename (TyFun dom cod) f :=
  TyFun (ty_rename dom f) (ty_rename cod (ext f));
ty_rename (TyPair first a member) f :=
  TyPair (ty_rename first f) a (tau_rename member (ext f));
ty_rename (TySingle p) f := TySingle (path_rename p f);
ty_rename (TyTSel p A) f := TyTSel (path_rename p f) A
with tau_rename {n m : nat} {k : Kind}
    (d : Tau n k) (f : FinFun n m) : Tau m k
    by struct d :=
tau_rename (TauTy ty) f := TauTy (ty_rename ty f);
tau_rename (TauIntv lower upper) f :=
  TauIntv (ty_rename lower f) (ty_rename upper f)
with def_rename {n m : nat} {k : Kind}
    (d : Def n k) (f : FinFun n m) : Def m k
    by struct d :=
def_rename (DefVal x) f := DefVal (apply f x);
def_rename (DefType ty) f := DefType (ty_rename ty f)
with tm_rename {n m : nat} (t : Tm n) (f : FinFun n m) : Tm m
    by struct t :=
tm_rename (TmPath p) f := TmPath (path_rename p f);
tm_rename (TmAbs ty body) f := TmAbs (ty_rename ty f) (tm_rename body (ext f));
tm_rename (TmPair x a d) f := TmPair (apply f x) a (def_rename d f);
tm_rename (TmApp p q) f := TmApp (path_rename p f) (path_rename q f);
tm_rename (TmLet s body) f :=
  TmLet (tm_rename s f) (tm_rename body (ext f)).

Definition path_weaken {n : nat} (p : Path n) : Path (S n) :=
  path_rename p (weaken n).
Definition ty_weaken {n : nat} (T : Ty n) : Ty (S n) :=
  ty_rename T (weaken n).
Definition tau_weaken {n : nat} {k : Kind} (d : Tau n k) : Tau (S n) k :=
  tau_rename d (weaken n).
Definition tm_weaken {n : nat} (t : Tm n) : Tm (S n) :=
  tm_rename t (weaken n).

(** Simultaneous path substitutions are also first-order finite tables. *)
Definition PathSubst (n m : nat) : Type := Vec (Path m) n.

Definition subst_apply {n m : nat} (s : PathSubst n m) (x : Fin n) : Path m :=
  vec_lookup s x.

Definition finfun_as_subst {n m : nat} (f : FinFun n m) : PathSubst n m :=
  vec_map PVar f.

Definition path_subst_id (n : nat) : PathSubst n n :=
  finfun_as_subst (id n).

Definition path_subst_lift {n m : nat}
    (s : PathSubst n m) : PathSubst (S n) (S m) :=
  VCons (PVar FZ) (vec_map path_weaken s).

Definition path_subst_openAt {n : nat} (p : Path n) : PathSubst (S n) n :=
  VCons p (path_subst_id n).

Equations path_subst {n m : nat} (p : Path n) (s : PathSubst n m) : Path m :=
path_subst (PVar x) s := subst_apply s x;
path_subst (PFst p) s := PFst (path_subst p s);
path_subst (PSel p a) s := PSel (path_subst p s) a.

Definition path_subst_comp {n m l : nat}
    (s : PathSubst n m) (t : PathSubst m l) : PathSubst n l :=
  vec_map (fun p => path_subst p t) s.

Equations ty_subst {n m : nat} (T : Ty n) (s : PathSubst n m) : Ty m
    by struct T :=
ty_subst TyTop s := TyTop;
ty_subst TyBot s := TyBot;
ty_subst (TyFun dom cod) s :=
  TyFun (ty_subst dom s) (ty_subst cod (path_subst_lift s));
ty_subst (TyPair first a member) s :=
  TyPair (ty_subst first s) a
    (tau_subst member (path_subst_lift s));
ty_subst (TySingle p) s := TySingle (path_subst p s);
ty_subst (TyTSel p A) s := TyTSel (path_subst p s) A
with tau_subst {n m : nat} {k : Kind}
    (d : Tau n k) (s : PathSubst n m) : Tau m k
    by struct d :=
tau_subst (TauTy ty) s := TauTy (ty_subst ty s);
tau_subst (TauIntv lower upper) s :=
  TauIntv (ty_subst lower s) (ty_subst upper s).

Definition path_open {n : nat} (q : Path (S n)) (p : Path n) : Path n :=
  path_subst q (path_subst_openAt p).
Definition ty_open {n : nat} (T : Ty (S n)) (p : Path n) : Ty n :=
  ty_subst T (path_subst_openAt p).
Definition tau_open {n : nat} {k : Kind}
    (d : Tau (S n) k) (p : Path n) : Tau n k :=
  tau_subst d (path_subst_openAt p).
Definition tm_open {n : nat} (t : Tm (S n)) (x : Fin n) : Tm n :=
  tm_rename t (openAt x).

(** Renaming algebra. *)
Lemma path_rename_id {n : nat} (p : Path n) :
    path_rename p (id n) = p.
Proof.
  induction p as [n x|n p IH|n p IH a]; simp path_rename.
  - rewrite id_apply. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma path_rename_rename {n m l : nat}
    (p : Path n) (f : FinFun n m) (g : FinFun m l) :
    path_rename (path_rename p f) g = path_rename p (comp f g).
Proof.
  induction p as [n x|n p IH|n p IH a]; simp path_rename.
  - rewrite comp_apply. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Equations ty_rename_id {n : nat} (T : Ty n) : ty_rename T (id n) = T
    by struct T :=
ty_rename_id TyTop := eq_refl;
ty_rename_id TyBot := eq_refl;
ty_rename_id (TyFun dom cod) :=
  f_equal2 (fun x y => TyFun x y)
    (ty_rename_id dom) (ty_rename_id cod);
ty_rename_id (TyPair first a member) :=
  f_equal2 (fun x y => TyPair x a y)
    (ty_rename_id first) (tau_rename_id member);
ty_rename_id (TySingle p) := f_equal TySingle (path_rename_id p);
ty_rename_id (TyTSel p a) :=
  f_equal (fun q => TyTSel q a) (path_rename_id p)
with tau_rename_id {n : nat} {k : Kind} (d : Tau n k) :
    tau_rename d (id n) = d by struct d :=
tau_rename_id (TauTy ty) := f_equal TauTy (ty_rename_id ty);
tau_rename_id (TauIntv lower upper) :=
  f_equal2 (fun x y => TauIntv x y)
    (ty_rename_id lower) (ty_rename_id upper)
with def_rename_id {n : nat} {k : Kind} (d : Def n k) :
    def_rename d (id n) = d by struct d :=
def_rename_id (DefVal x) := f_equal DefVal (id_apply x);
def_rename_id (DefType ty) := f_equal DefType (ty_rename_id ty)
with tm_rename_id {n : nat} (t : Tm n) : tm_rename t (id n) = t
    by struct t :=
tm_rename_id (TmPath p) := f_equal TmPath (path_rename_id p);
tm_rename_id (TmAbs ty body) :=
  f_equal2 (fun x y => TmAbs x y)
    (ty_rename_id ty) (tm_rename_id body);
tm_rename_id (TmPair x a d) :=
  f_equal2 (fun y e => TmPair y a e)
    (id_apply x) (def_rename_id d);
tm_rename_id (TmApp p q) :=
  f_equal2 (fun x y => TmApp x y)
    (path_rename_id p) (path_rename_id q);
tm_rename_id (TmLet s body) :=
  f_equal2 (fun x y => TmLet x y)
    (tm_rename_id s) (tm_rename_id body).

Equations ty_rename_rename {n m l : nat} (T : Ty n)
    (f : FinFun n m) (g : FinFun m l) :
    ty_rename (ty_rename T f) g = ty_rename T (comp f g)
    by struct T :=
ty_rename_rename TyTop f g := eq_refl;
ty_rename_rename TyBot f g := eq_refl;
ty_rename_rename (TyFun dom cod) f g :=
  f_equal2 (fun x y => TyFun x y)
    (ty_rename_rename dom f g)
    (eq_trans (ty_rename_rename cod (ext f) (ext g))
      (f_equal (fun h => ty_rename cod h) (ext_comp f g)));
ty_rename_rename (TyPair first a member) f g :=
  f_equal2 (fun x y => TyPair x a y)
    (ty_rename_rename first f g)
    (eq_trans (tau_rename_rename member (ext f) (ext g))
      (f_equal (fun h => tau_rename member h) (ext_comp f g)));
ty_rename_rename (TySingle p) f g :=
  f_equal TySingle (path_rename_rename p f g);
ty_rename_rename (TyTSel p a) f g :=
  f_equal (fun q => TyTSel q a) (path_rename_rename p f g)
with tau_rename_rename {n m l : nat} {k : Kind} (d : Tau n k)
    (f : FinFun n m) (g : FinFun m l) :
    tau_rename (tau_rename d f) g = tau_rename d (comp f g)
    by struct d :=
tau_rename_rename (TauTy ty) f g :=
  f_equal TauTy (ty_rename_rename ty f g);
tau_rename_rename (TauIntv lower upper) f g :=
  f_equal2 (fun x y => TauIntv x y)
    (ty_rename_rename lower f g) (ty_rename_rename upper f g)
with def_rename_rename {n m l : nat} {k : Kind} (d : Def n k)
    (f : FinFun n m) (g : FinFun m l) :
    def_rename (def_rename d f) g = def_rename d (comp f g)
    by struct d :=
def_rename_rename (DefVal x) f g :=
  f_equal DefVal (eq_sym (comp_apply f g x));
def_rename_rename (DefType ty) f g :=
  f_equal DefType (ty_rename_rename ty f g)
with tm_rename_rename {n m l : nat} (t : Tm n)
    (f : FinFun n m) (g : FinFun m l) :
    tm_rename (tm_rename t f) g = tm_rename t (comp f g)
    by struct t :=
tm_rename_rename (TmPath p) f g :=
  f_equal TmPath (path_rename_rename p f g);
tm_rename_rename (TmAbs ty body) f g :=
  f_equal2 (fun x y => TmAbs x y)
    (ty_rename_rename ty f g)
    (eq_trans (tm_rename_rename body (ext f) (ext g))
      (f_equal (fun h => tm_rename body h) (ext_comp f g)));
tm_rename_rename (TmPair x a d) f g :=
  f_equal2 (fun y e => TmPair y a e)
    (eq_sym (comp_apply f g x)) (def_rename_rename d f g);
tm_rename_rename (TmApp p q) f g :=
  f_equal2 (fun x y => TmApp x y)
    (path_rename_rename p f g) (path_rename_rename q f g);
tm_rename_rename (TmLet s body) f g :=
  f_equal2 (fun x y => TmLet x y)
    (tm_rename_rename s f g)
    (eq_trans (tm_rename_rename body (ext f) (ext g))
      (f_equal (fun h => tm_rename body h) (ext_comp f g))).

Lemma path_weaken_rename {n m : nat}
    (p : Path n) (f : FinFun n m) :
    path_weaken (path_rename p f) = path_rename (path_weaken p) (ext f).
Proof.
  unfold path_weaken.
  rewrite !path_rename_rename, comp_weaken. reflexivity.
Qed.

Lemma ty_weaken_rename {n m : nat} (T : Ty n) (f : FinFun n m) :
    ty_weaken (ty_rename T f) = ty_rename (ty_weaken T) (ext f).
Proof.
  unfold ty_weaken.
  rewrite !ty_rename_rename, comp_weaken. reflexivity.
Qed.

Lemma tau_weaken_rename {n m : nat} {k : Kind}
    (d : Tau n k) (f : FinFun n m) :
    tau_weaken (tau_rename d f) = tau_rename (tau_weaken d) (ext f).
Proof.
  unfold tau_weaken.
  rewrite !tau_rename_rename, comp_weaken. reflexivity.
Qed.

(** Path-substitution algebra. *)
Lemma pathsubst_ext {n m : nat} (s t : PathSubst n m) :
    (forall x, subst_apply s x = subst_apply t x) -> s = t.
Proof. apply vec_ext. Qed.

Lemma path_subst_lift_zero {n m : nat} (s : PathSubst n m) :
    subst_apply (path_subst_lift s) FZ = PVar FZ.
Proof.
  unfold subst_apply. rewrite vec_lookup_zero. simp vec_head. reflexivity.
Qed.

Lemma path_subst_lift_succ {n m : nat}
    (s : PathSubst n m) (x : Fin n) :
    subst_apply (path_subst_lift s) (FS x) =
      path_weaken (subst_apply s x).
Proof.
  unfold subst_apply at 1. rewrite vec_lookup_succ. simp vec_tail.
  unfold path_subst_lift. simp vec_tail.
  rewrite vec_lookup_map. reflexivity.
Qed.

Lemma path_subst_openAt_zero {n : nat} (p : Path n) :
    subst_apply (path_subst_openAt p) FZ = p.
Proof.
  unfold subst_apply. rewrite vec_lookup_zero. simp vec_head. reflexivity.
Qed.

Lemma finfun_as_subst_apply {n m : nat}
    (f : FinFun n m) (x : Fin n) :
    subst_apply (finfun_as_subst f) x = PVar (apply f x).
Proof. unfold subst_apply, finfun_as_subst. apply vec_lookup_map. Qed.

Lemma path_subst_id_apply {n : nat} (x : Fin n) :
    subst_apply (path_subst_id n) x = PVar x.
Proof.
  unfold path_subst_id. rewrite finfun_as_subst_apply, id_apply. reflexivity.
Qed.

Lemma path_subst_openAt_succ {n : nat} (p : Path n) (x : Fin n) :
    subst_apply (path_subst_openAt p) (FS x) = PVar x.
Proof.
  unfold subst_apply at 1. rewrite vec_lookup_succ. simp vec_tail.
  unfold path_subst_openAt. simp vec_tail.
  change (subst_apply (path_subst_id n) x = PVar x).
  apply path_subst_id_apply.
Qed.

Lemma path_subst_comp_apply {n m l : nat}
    (s : PathSubst n m) (t : PathSubst m l) (x : Fin n) :
    subst_apply (path_subst_comp s t) x = path_subst (subst_apply s x) t.
Proof.
  unfold subst_apply, path_subst_comp. rewrite vec_lookup_map. reflexivity.
Qed.

Lemma path_subst_lift_id {n : nat} :
    path_subst_lift (path_subst_id n) = path_subst_id (S n).
Proof.
  apply pathsubst_ext. intro x.
  refine (fin_case (P := fun x =>
    subst_apply (path_subst_lift (path_subst_id n)) x =
      subst_apply (path_subst_id (S n)) x) _ _ x).
  - rewrite path_subst_lift_zero, path_subst_id_apply. reflexivity.
  - intro i. rewrite path_subst_lift_succ, !path_subst_id_apply.
    unfold path_weaken. simp path_rename. rewrite weaken_apply. reflexivity.
Qed.

Lemma path_subst_identity {n : nat} (p : Path n) :
    path_subst p (path_subst_id n) = p.
Proof.
  induction p as [n x|n p IH|n p IH a]; simp path_subst.
  - apply path_subst_id_apply.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Equations ty_subst_id {n : nat} (T : Ty n) :
    ty_subst T (path_subst_id n) = T by struct T :=
ty_subst_id TyTop := eq_refl;
ty_subst_id TyBot := eq_refl;
ty_subst_id (TyFun dom cod) :=
  f_equal2 (fun x y => TyFun x y)
    (ty_subst_id dom)
    (eq_trans
      (f_equal (fun s => ty_subst cod s) path_subst_lift_id)
      (ty_subst_id cod));
ty_subst_id (TyPair first a member) :=
  f_equal2 (fun x y => TyPair x a y)
    (ty_subst_id first)
    (eq_trans
      (f_equal (fun s => tau_subst member s) path_subst_lift_id)
      (tau_subst_id member));
ty_subst_id (TySingle p) := f_equal TySingle (path_subst_identity p);
ty_subst_id (TyTSel p a) :=
  f_equal (fun q => TyTSel q a) (path_subst_identity p)
with tau_subst_id {n : nat} {k : Kind} (d : Tau n k) :
    tau_subst d (path_subst_id n) = d by struct d :=
tau_subst_id (TauTy ty) := f_equal TauTy (ty_subst_id ty);
tau_subst_id (TauIntv lower upper) :=
  f_equal2 (fun x y => TauIntv x y)
    (ty_subst_id lower) (ty_subst_id upper).

Lemma finfun_as_subst_ext {n m : nat} (f : FinFun n m) :
    finfun_as_subst (ext f) = path_subst_lift (finfun_as_subst f).
Proof.
  apply pathsubst_ext. intro x.
  refine (fin_case (P := fun x =>
    subst_apply (finfun_as_subst (ext f)) x =
      subst_apply (path_subst_lift (finfun_as_subst f)) x) _ _ x).
  - rewrite finfun_as_subst_apply, ext_zero, path_subst_lift_zero.
    reflexivity.
  - intro i. rewrite finfun_as_subst_apply, ext_succ,
      path_subst_lift_succ, finfun_as_subst_apply.
    unfold path_weaken. simp path_rename. rewrite weaken_apply. reflexivity.
Qed.

Lemma finfun_openAt_as_subst {n : nat} (x : Fin n) :
    finfun_as_subst (openAt x) = path_subst_openAt (PVar x).
Proof.
  apply pathsubst_ext. intro y.
  refine (fin_case (P := fun y =>
    subst_apply (finfun_as_subst (openAt x)) y =
      subst_apply (path_subst_openAt (PVar x)) y) _ _ y).
  - rewrite finfun_as_subst_apply, openAt_zero, path_subst_openAt_zero.
    reflexivity.
  - intro i. rewrite finfun_as_subst_apply, openAt_succ,
      path_subst_openAt_succ. reflexivity.
Qed.

Lemma path_subst_as_subst {n m : nat}
    (p : Path n) (f : FinFun n m) :
    path_subst p (finfun_as_subst f) = path_rename p f.
Proof.
  induction p as [n x|n p IH|n p IH a]; simp path_subst path_rename.
  - apply finfun_as_subst_apply.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Equations ty_subst_as_subst {n m : nat} (T : Ty n) (f : FinFun n m) :
    ty_subst T (finfun_as_subst f) = ty_rename T f by struct T :=
ty_subst_as_subst TyTop f := eq_refl;
ty_subst_as_subst TyBot f := eq_refl;
ty_subst_as_subst (TyFun dom cod) f :=
  f_equal2 (fun x y => TyFun x y)
    (ty_subst_as_subst dom f)
    (eq_trans
      (f_equal (fun s => ty_subst cod s) (eq_sym (finfun_as_subst_ext f)))
      (ty_subst_as_subst cod (ext f)));
ty_subst_as_subst (TyPair first a member) f :=
  f_equal2 (fun x y => TyPair x a y)
    (ty_subst_as_subst first f)
    (eq_trans
      (f_equal (fun s => tau_subst member s)
        (eq_sym (finfun_as_subst_ext f)))
      (tau_subst_as_subst member (ext f)));
ty_subst_as_subst (TySingle p) f :=
  f_equal TySingle (path_subst_as_subst p f);
ty_subst_as_subst (TyTSel p a) f :=
  f_equal (fun q => TyTSel q a) (path_subst_as_subst p f)
with tau_subst_as_subst {n m : nat} {k : Kind}
    (d : Tau n k) (f : FinFun n m) :
    tau_subst d (finfun_as_subst f) = tau_rename d f by struct d :=
tau_subst_as_subst (TauTy ty) f :=
  f_equal TauTy (ty_subst_as_subst ty f);
tau_subst_as_subst (TauIntv lower upper) f :=
  f_equal2 (fun x y => TauIntv x y)
    (ty_subst_as_subst lower f) (ty_subst_as_subst upper f).

Lemma path_subst_openAt_rename {n m : nat}
    (p : Path n) (f : FinFun n m) :
    path_subst_comp (path_subst_openAt p) (finfun_as_subst f) =
      path_subst_comp (finfun_as_subst (ext f))
        (path_subst_openAt (path_rename p f)).
Proof.
  apply pathsubst_ext. intro x.
  refine (fin_case (P := fun x =>
    subst_apply
      (path_subst_comp (path_subst_openAt p) (finfun_as_subst f)) x =
    subst_apply
      (path_subst_comp (finfun_as_subst (ext f))
        (path_subst_openAt (path_rename p f))) x) _ _ x).
  - rewrite !path_subst_comp_apply, path_subst_openAt_zero,
      path_subst_as_subst, finfun_as_subst_apply, ext_zero.
    simp path_subst. apply eq_sym. apply path_subst_openAt_zero.
  - intro i. rewrite !path_subst_comp_apply, path_subst_openAt_succ,
      finfun_as_subst_apply, ext_succ.
    simp path_subst.
    rewrite finfun_as_subst_apply, path_subst_openAt_succ. reflexivity.
Qed.

Lemma path_subst_openAt_weaken {n : nat} (p : Path n) :
    path_subst_comp (finfun_as_subst (weaken n))
      (path_subst_openAt p) = path_subst_id n.
Proof.
  apply pathsubst_ext. intro x.
  rewrite path_subst_comp_apply, finfun_as_subst_apply, weaken_apply.
  simp path_subst. rewrite path_subst_openAt_succ, path_subst_id_apply.
  reflexivity.
Qed.

Lemma path_weaken_subst_lift {n m : nat}
    (p : Path n) (s : PathSubst n m) :
    path_subst (path_weaken p) (path_subst_lift s) =
      path_weaken (path_subst p s).
Proof.
  induction p as [n x|n p IH|n p IH a];
    unfold path_weaken in *; simp path_rename path_subst in *.
  - rewrite weaken_apply, path_subst_lift_succ. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma path_subst_comp_lift {n m l : nat}
    (s : PathSubst n m) (t : PathSubst m l) :
    path_subst_lift (path_subst_comp s t) =
      path_subst_comp (path_subst_lift s) (path_subst_lift t).
Proof.
  apply pathsubst_ext. intro x.
  refine (fin_case (P := fun x =>
    subst_apply (path_subst_lift (path_subst_comp s t)) x =
      subst_apply
        (path_subst_comp (path_subst_lift s) (path_subst_lift t)) x)
      _ _ x).
  - rewrite path_subst_lift_zero, path_subst_comp_apply,
      path_subst_lift_zero. simp path_subst.
    apply eq_sym. apply path_subst_lift_zero.
  - intro i. rewrite path_subst_comp_apply.
    rewrite !path_subst_lift_succ.
    rewrite path_subst_comp_apply.
    apply eq_sym. apply path_weaken_subst_lift.
Qed.

Lemma path_subst_compose {n m l : nat} (p : Path n)
    (s : PathSubst n m) (t : PathSubst m l) :
    path_subst (path_subst p s) t = path_subst p (path_subst_comp s t).
Proof.
  induction p as [n x|n p IH|n p IH a]; simp path_subst.
  - apply eq_sym. apply path_subst_comp_apply.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Equations ty_subst_compose {n m l : nat} (T : Ty n)
    (s : PathSubst n m) (t : PathSubst m l) :
    ty_subst (ty_subst T s) t = ty_subst T (path_subst_comp s t)
    by struct T :=
ty_subst_compose TyTop s t := eq_refl;
ty_subst_compose TyBot s t := eq_refl;
ty_subst_compose (TyFun dom cod) s t :=
  f_equal2 (fun x y => TyFun x y)
    (ty_subst_compose dom s t)
    (eq_trans (ty_subst_compose cod (path_subst_lift s)
      (path_subst_lift t))
      (f_equal (fun u => ty_subst cod u)
        (eq_sym (path_subst_comp_lift s t))));
ty_subst_compose (TyPair first a member) s t :=
  f_equal2 (fun x y => TyPair x a y)
    (ty_subst_compose first s t)
    (eq_trans (tau_subst_compose member (path_subst_lift s)
      (path_subst_lift t))
      (f_equal (fun u => tau_subst member u)
        (eq_sym (path_subst_comp_lift s t))));
ty_subst_compose (TySingle p) s t :=
  f_equal TySingle (path_subst_compose p s t);
ty_subst_compose (TyTSel p a) s t :=
  f_equal (fun q => TyTSel q a) (path_subst_compose p s t)
with tau_subst_compose {n m l : nat} {k : Kind} (d : Tau n k)
    (s : PathSubst n m) (t : PathSubst m l) :
    tau_subst (tau_subst d s) t = tau_subst d (path_subst_comp s t)
    by struct d :=
tau_subst_compose (TauTy ty) s t :=
  f_equal TauTy (ty_subst_compose ty s t);
tau_subst_compose (TauIntv lower upper) s t :=
  f_equal2 (fun x y => TauIntv x y)
    (ty_subst_compose lower s t) (ty_subst_compose upper s t).

Lemma path_subst_openAt_comp {n m : nat}
    (p : Path n) (s : PathSubst n m) :
    path_subst_comp (path_subst_openAt p) s =
      path_subst_comp (path_subst_lift s)
        (path_subst_openAt (path_subst p s)).
Proof.
  apply pathsubst_ext. intro x.
  refine (fin_case (P := fun x =>
    subst_apply (path_subst_comp (path_subst_openAt p) s) x =
      subst_apply (path_subst_comp (path_subst_lift s)
        (path_subst_openAt (path_subst p s))) x) _ _ x).
  - rewrite !path_subst_comp_apply, path_subst_openAt_zero,
      path_subst_lift_zero. simp path_subst.
    apply eq_sym. apply path_subst_openAt_zero.
  - intro i. rewrite !path_subst_comp_apply, path_subst_openAt_succ,
      path_subst_lift_succ. simp path_subst.
    apply eq_sym. unfold path_weaken.
    rewrite <- path_subst_as_subst, path_subst_compose,
      path_subst_openAt_weaken. apply path_subst_identity.
Qed.

Lemma tau_open_subst {n m : nat} {k : Kind}
    (d : Tau (S n) k) (p : Path n) (s : PathSubst n m) :
    tau_subst (tau_open d p) s =
      tau_open (tau_subst d (path_subst_lift s)) (path_subst p s).
Proof.
  unfold tau_open.
  rewrite !tau_subst_compose, path_subst_openAt_comp. reflexivity.
Qed.

Lemma ty_rename_openAt_eq_open_var {n : nat}
    (T : Ty (S n)) (x : Fin n) :
    ty_rename T (openAt x) = ty_open T (PVar x).
Proof.
  unfold ty_open.
  rewrite <- ty_subst_as_subst, finfun_openAt_as_subst. reflexivity.
Qed.

Lemma tau_rename_openAt_eq_open_var {n : nat} {k : Kind}
    (d : Tau (S n) k) (x : Fin n) :
    tau_rename d (openAt x) = tau_open d (PVar x).
Proof.
  unfold tau_open.
  rewrite <- tau_subst_as_subst, finfun_openAt_as_subst. reflexivity.
Qed.

Lemma path_open_rename {n m : nat} (p : Path (S n))
    (q : Path n) (f : FinFun n m) :
    path_rename (path_open p q) f =
      path_open (path_rename p (ext f)) (path_rename q f).
Proof.
  unfold path_open.
  rewrite <- path_subst_as_subst, path_subst_compose,
    path_subst_openAt_rename, <- path_subst_compose,
    path_subst_as_subst. reflexivity.
Qed.

Lemma ty_open_rename {n m : nat} (T : Ty (S n))
    (p : Path n) (f : FinFun n m) :
    ty_rename (ty_open T p) f =
      ty_open (ty_rename T (ext f)) (path_rename p f).
Proof.
  unfold ty_open.
  rewrite <- ty_subst_as_subst, ty_subst_compose,
    path_subst_openAt_rename, <- ty_subst_compose,
    ty_subst_as_subst. reflexivity.
Qed.

Lemma tau_open_rename {n m : nat} {k : Kind} (d : Tau (S n) k)
    (p : Path n) (f : FinFun n m) :
    tau_rename (tau_open d p) f =
      tau_open (tau_rename d (ext f)) (path_rename p f).
Proof.
  unfold tau_open.
  rewrite <- tau_subst_as_subst, tau_subst_compose,
    path_subst_openAt_rename, <- tau_subst_compose,
    tau_subst_as_subst. reflexivity.
Qed.

Lemma path_weaken_open {n : nat} (p q : Path n) :
    path_open (path_weaken p) q = p.
Proof.
  unfold path_open, path_weaken.
  rewrite <- path_subst_as_subst, path_subst_compose,
    path_subst_openAt_weaken. apply path_subst_identity.
Qed.

Lemma ty_weaken_open {n : nat} (T : Ty n) (p : Path n) :
    ty_open (ty_weaken T) p = T.
Proof.
  unfold ty_open, ty_weaken.
  rewrite <- ty_subst_as_subst, ty_subst_compose,
    path_subst_openAt_weaken. apply ty_subst_id.
Qed.

Lemma tau_weaken_open {n : nat} {k : Kind}
    (d : Tau n k) (p : Path n) : tau_open (tau_weaken d) p = d.
Proof.
  unfold tau_open, tau_weaken.
  rewrite <- tau_subst_as_subst, tau_subst_compose,
    path_subst_openAt_weaken. apply tau_subst_id.
Qed.

Print Assumptions tau_weaken_open.
