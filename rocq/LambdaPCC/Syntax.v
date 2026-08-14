From Equations Require Import Equations.
From PathDependent.LambdaPCC Require Import FinFun.

Set Implicit Arguments.
Set Universe Polymorphism.
Unset Strict Implicit.

(** Intrinsically scoped syntax for the capture-checking calculus. *)

Definition Name : Type := nat.

Inductive Kind : Type :=
| KTerm
| KType
| KCapture.

Inductive Path : nat -> Type :=
| PVar {n : nat} : Fin n -> Path n
| PFst {n : nat} : Path n -> Path n
| PSel {n : nat} : Path n -> Name -> Path n.

Arguments PVar {n} _.
Arguments PFst {n} _.
Arguments PSel {n} _ _.

Derive NoConfusionHom for Path.

Inductive CaptureSet : nat -> Type :=
| CEmpty {n : nat} : CaptureSet n
| CUnion {n : nat} : CaptureSet n -> CaptureSet n -> CaptureSet n
| CSingleton {n : nat} : Path n -> CaptureSet n
| CSelect {n : nat} : Path n -> Name -> CaptureSet n.

Arguments CEmpty {n}.
Arguments CUnion {n} _ _.
Arguments CSingleton {n} _.
Arguments CSelect {n} _ _.

Inductive Ty : nat -> Type :=
| TyCapt {n : nat} : CaptureSet n -> Shape n -> Ty n
with Shape : nat -> Type :=
| ShTop {n : nat} : Shape n
| ShBot {n : nat} : Shape n
| ShFun {n : nat} : Ty n -> Ty (S n) -> Shape n
| ShPair {n : nat} {k : Kind} : Ty n -> Name -> Tau (S n) k -> Shape n
| ShSingle {n : nat} : Path n -> Shape n
| ShTSel {n : nat} : Path n -> Name -> Shape n
with Tau : nat -> Kind -> Type :=
| TauTerm {n : nat} : Ty n -> Tau n KTerm
| TauType {n : nat} : Shape n -> Shape n -> Tau n KType
| TauCapture {n : nat} : CaptureSet n -> CaptureSet n -> Tau n KCapture.

Arguments TyCapt {n} _ _.
Arguments ShTop {n}.
Arguments ShBot {n}.
Arguments ShFun {n} _ _.
Arguments ShPair {n k} _ _ _.
Arguments ShSingle {n} _.
Arguments ShTSel {n} _ _.
Arguments TauTerm {n} _.
Arguments TauType {n} _ _.
Arguments TauCapture {n} _ _.

Definition ty_capture_set {n : nat} (T : Ty n) : CaptureSet n :=
  match T with TyCapt C _ => C end.

Inductive Def : nat -> Kind -> Type :=
| DefVal {n : nat} : Fin n -> Def n KTerm
| DefType {n : nat} : Shape n -> Def n KType
| DefCapture {n : nat} : CaptureSet n -> Def n KCapture.

Arguments DefVal {n} _.
Arguments DefType {n} _.
Arguments DefCapture {n} _.

Inductive Tm : nat -> Type :=
| TmPath {n : nat} : Path n -> Tm n
| TmAbs {n : nat} : Ty n -> Tm (S n) -> Tm n
| TmPair {n : nat} {k : Kind} : Fin n -> Name -> Def n k -> Tm n
| TmApp {n : nat} : Path n -> Path n -> Tm n
| TmLet {n : nat} : Tm n -> Tm (S n) -> Tm n.

Arguments TmPath {n} _.
Arguments TmAbs {n} _ _.
Arguments TmPair {n k} _ _ _.
Arguments TmApp {n} _ _.
Arguments TmLet {n} _ _.

Inductive Path_IsVar {n : nat} : Path n -> Prop :=
| IsVar_var (x : Fin n) : Path_IsVar (PVar x).

Inductive Tm_IsValue {n : nat} : Tm n -> Prop :=
| IsValue_abs (A : Ty n) (body : Tm (S n)) :
    Tm_IsValue (TmAbs A body)
| IsValue_pair {k : Kind} (y : Fin n) (a : Name) (d : Def n k) :
    Tm_IsValue (TmPair y a d).

(** Renaming. *)
Equations path_rename {n m : nat}
    (p : Path n) (f : FinFun n m) : Path m :=
path_rename (PVar x) f := PVar (apply f x);
path_rename (PFst p) f := PFst (path_rename p f);
path_rename (PSel p a) f := PSel (path_rename p f) a.

Equations capture_rename {n m : nat}
    (C : CaptureSet n) (f : FinFun n m) : CaptureSet m :=
capture_rename CEmpty f := CEmpty;
capture_rename (CUnion C D) f :=
  CUnion (capture_rename C f) (capture_rename D f);
capture_rename (CSingleton p) f := CSingleton (path_rename p f);
capture_rename (CSelect p a) f := CSelect (path_rename p f) a.

Equations ty_rename {n m : nat} (T : Ty n) (f : FinFun n m) : Ty m
    by struct T :=
ty_rename (TyCapt C shape) f :=
  TyCapt (capture_rename C f) (shape_rename shape f)
with shape_rename {n m : nat}
    (shape : Shape n) (f : FinFun n m) : Shape m
    by struct shape :=
shape_rename ShTop f := ShTop;
shape_rename ShBot f := ShBot;
shape_rename (ShFun dom cod) f :=
  ShFun (ty_rename dom f) (ty_rename cod (ext f));
shape_rename (ShPair first a member) f :=
  ShPair (ty_rename first f) a (tau_rename member (ext f));
shape_rename (ShSingle p) f := ShSingle (path_rename p f);
shape_rename (ShTSel p a) f := ShTSel (path_rename p f) a
with tau_rename {n m : nat} {k : Kind}
    (d : Tau n k) (f : FinFun n m) : Tau m k
    by struct d :=
tau_rename (TauTerm T) f := TauTerm (ty_rename T f);
tau_rename (TauType lower upper) f :=
  TauType (shape_rename lower f) (shape_rename upper f);
tau_rename (TauCapture lower upper) f :=
  TauCapture (capture_rename lower f) (capture_rename upper f).

Equations def_rename {n m : nat} {k : Kind}
    (d : Def n k) (f : FinFun n m) : Def m k :=
def_rename (DefVal x) f := DefVal (apply f x);
def_rename (DefType shape) f := DefType (shape_rename shape f);
def_rename (DefCapture C) f := DefCapture (capture_rename C f).

Equations tm_rename {n m : nat} (t : Tm n) (f : FinFun n m) : Tm m :=
tm_rename (TmPath p) f := TmPath (path_rename p f);
tm_rename (TmAbs T body) f :=
  TmAbs (ty_rename T f) (tm_rename body (ext f));
tm_rename (TmPair x a d) f := TmPair (apply f x) a (def_rename d f);
tm_rename (TmApp p q) f := TmApp (path_rename p f) (path_rename q f);
tm_rename (TmLet bound body) f :=
  TmLet (tm_rename bound f) (tm_rename body (ext f)).

Definition path_weaken {n : nat} (p : Path n) : Path (S n) :=
  path_rename p (weaken n).
Definition capture_weaken {n : nat} (C : CaptureSet n) : CaptureSet (S n) :=
  capture_rename C (weaken n).
Definition ty_weaken {n : nat} (T : Ty n) : Ty (S n) :=
  ty_rename T (weaken n).
Definition shape_weaken {n : nat} (shape : Shape n) : Shape (S n) :=
  shape_rename shape (weaken n).
Definition tau_weaken {n : nat} {k : Kind} (d : Tau n k) : Tau (S n) k :=
  tau_rename d (weaken n).
Definition def_weaken {n : nat} {k : Kind} (d : Def n k) : Def (S n) k :=
  def_rename d (weaken n).
Definition tm_weaken {n : nat} (t : Tm n) : Tm (S n) :=
  tm_rename t (weaken n).

(** Simultaneous path substitutions are first-order finite tables. *)
Definition PathSubst (n m : nat) : Type := Vec (Path m) n.

Definition subst_apply {n m : nat}
    (s : PathSubst n m) (x : Fin n) : Path m := vec_lookup s x.

Lemma path_subst_ext {n m : nat} (s t : PathSubst n m) :
    (forall x, subst_apply s x = subst_apply t x) -> s = t.
Proof. apply vec_ext. Qed.

Definition finfun_as_subst {n m : nat} (f : FinFun n m) : PathSubst n m :=
  vec_map PVar f.

Definition path_subst_id (n : nat) : PathSubst n n :=
  finfun_as_subst (id n).

Definition path_subst_lift {n m : nat}
    (s : PathSubst n m) : PathSubst (S n) (S m) :=
  VCons (PVar FZ) (vec_map path_weaken s).

Definition path_subst_openAt {n : nat}
    (p : Path n) : PathSubst (S n) n :=
  VCons p (path_subst_id n).

Equations path_subst {n m : nat}
    (p : Path n) (s : PathSubst n m) : Path m :=
path_subst (PVar x) s := subst_apply s x;
path_subst (PFst p) s := PFst (path_subst p s);
path_subst (PSel p a) s := PSel (path_subst p s) a.

Definition path_subst_comp {n m l : nat}
    (s : PathSubst n m) (t : PathSubst m l) : PathSubst n l :=
  vec_map (fun p => path_subst p t) s.

Equations capture_subst {n m : nat}
    (C : CaptureSet n) (s : PathSubst n m) : CaptureSet m :=
capture_subst CEmpty s := CEmpty;
capture_subst (CUnion C D) s :=
  CUnion (capture_subst C s) (capture_subst D s);
capture_subst (CSingleton p) s := CSingleton (path_subst p s);
capture_subst (CSelect p a) s := CSelect (path_subst p s) a.

Equations ty_subst {n m : nat} (T : Ty n) (s : PathSubst n m) : Ty m
    by struct T :=
ty_subst (TyCapt C shape) s :=
  TyCapt (capture_subst C s) (shape_subst shape s)
with shape_subst {n m : nat}
    (shape : Shape n) (s : PathSubst n m) : Shape m
    by struct shape :=
shape_subst ShTop s := ShTop;
shape_subst ShBot s := ShBot;
shape_subst (ShFun dom cod) s :=
  ShFun (ty_subst dom s) (ty_subst cod (path_subst_lift s));
shape_subst (ShPair first a member) s :=
  ShPair (ty_subst first s) a
    (tau_subst member (path_subst_lift s));
shape_subst (ShSingle p) s := ShSingle (path_subst p s);
shape_subst (ShTSel p a) s := ShTSel (path_subst p s) a
with tau_subst {n m : nat} {k : Kind}
    (d : Tau n k) (s : PathSubst n m) : Tau m k
    by struct d :=
tau_subst (TauTerm T) s := TauTerm (ty_subst T s);
tau_subst (TauType lower upper) s :=
  TauType (shape_subst lower s) (shape_subst upper s);
tau_subst (TauCapture lower upper) s :=
  TauCapture (capture_subst lower s) (capture_subst upper s).

Definition path_open {n : nat} (q : Path (S n)) (p : Path n) : Path n :=
  path_subst q (path_subst_openAt p).
Definition capture_open {n : nat}
    (C : CaptureSet (S n)) (p : Path n) : CaptureSet n :=
  capture_subst C (path_subst_openAt p).
Definition ty_open {n : nat} (T : Ty (S n)) (p : Path n) : Ty n :=
  ty_subst T (path_subst_openAt p).
Definition shape_open {n : nat}
    (shape : Shape (S n)) (p : Path n) : Shape n :=
  shape_subst shape (path_subst_openAt p).
Definition tau_open {n : nat} {k : Kind}
    (d : Tau (S n) k) (p : Path n) : Tau n k :=
  tau_subst d (path_subst_openAt p).
Definition tm_open {n : nat} (t : Tm (S n)) (x : Fin n) : Tm n :=
  tm_rename t (openAt x).

(** Algebra of renaming. *)

Lemma path_rename_id {n : nat} (p : Path n) :
    path_rename p (id n) = p.
Proof.
  induction p as [n x|n p IH|n p IH a].
  - simp path_rename. rewrite id_apply. reflexivity.
  - simp path_rename. now rewrite IH.
  - simp path_rename. now rewrite IH.
Qed.

Lemma capture_rename_id {n : nat} (C : CaptureSet n) :
    capture_rename C (id n) = C.
Proof.
  induction C as [n|n C IHC D IHD|n p|n p a];
    simp capture_rename; try rewrite path_rename_id;
    try rewrite IHC; try rewrite IHD; reflexivity.
Qed.

Equations ty_rename_id {n : nat} (T : Ty n) :
    ty_rename T (id n) = T by struct T :=
ty_rename_id (TyCapt C shape) :=
  f_equal2 TyCapt (capture_rename_id C) (shape_rename_id shape)
with shape_rename_id {n : nat} (shape : Shape n) :
    shape_rename shape (id n) = shape by struct shape :=
shape_rename_id ShTop := eq_refl;
shape_rename_id ShBot := eq_refl;
shape_rename_id (ShFun dom cod) :=
  f_equal2 ShFun (ty_rename_id dom)
    (eq_rect _ (fun f => ty_rename cod f = cod)
      (ty_rename_id cod) _ (eq_sym ext_id));
shape_rename_id (ShPair first a member) :=
  f_equal2 (fun first member => ShPair first a member)
    (ty_rename_id first)
    (eq_rect _ (fun f => tau_rename member f = member)
      (tau_rename_id member) _ (eq_sym ext_id));
shape_rename_id (ShSingle p) := f_equal ShSingle (path_rename_id p);
shape_rename_id (ShTSel p a) :=
  f_equal (fun p => ShTSel p a) (path_rename_id p)
with tau_rename_id {n : nat} {k : Kind} (d : Tau n k) :
    tau_rename d (id n) = d by struct d :=
tau_rename_id (TauTerm T) := f_equal TauTerm (ty_rename_id T);
tau_rename_id (TauType lower upper) :=
  f_equal2 TauType (shape_rename_id lower) (shape_rename_id upper);
tau_rename_id (TauCapture lower upper) :=
  f_equal2 TauCapture (capture_rename_id lower) (capture_rename_id upper).

Lemma def_rename_id {n : nat} {k : Kind} (d : Def n k) :
    def_rename d (id n) = d.
Proof.
  destruct d as [n x|n shape|n C]; simp def_rename.
  - rewrite id_apply. reflexivity.
  - rewrite shape_rename_id. reflexivity.
  - rewrite capture_rename_id. reflexivity.
Qed.

Lemma tm_rename_id {n : nat} (t : Tm n) :
    tm_rename t (id n) = t.
Proof.
  induction t as [n p|n T body IH|n k x a d|n p q|n bound IHb body IHbody];
    simp tm_rename.
  - now rewrite path_rename_id.
  - rewrite ty_rename_id, ext_id, IH. reflexivity.
  - rewrite id_apply, def_rename_id. reflexivity.
  - now rewrite !path_rename_id.
  - rewrite IHb, ext_id, IHbody. reflexivity.
Qed.

Lemma path_rename_rename {n m l : nat}
    (p : Path n) (f : FinFun n m) (g : FinFun m l) :
    path_rename (path_rename p f) g = path_rename p (comp f g).
Proof.
  induction p as [n x|n p IH|n p IH a]; simp path_rename.
  - now rewrite !comp_apply.
  - now rewrite IH.
  - now rewrite IH.
Qed.

Lemma capture_rename_rename {n m l : nat}
    (C : CaptureSet n) (f : FinFun n m) (g : FinFun m l) :
    capture_rename (capture_rename C f) g =
      capture_rename C (comp f g).
Proof.
  induction C as [n|n C IHC D IHD|n p|n p a];
    simp capture_rename; try rewrite path_rename_rename;
    try rewrite IHC; try rewrite IHD; reflexivity.
Qed.

Equations ty_rename_rename {n m l : nat}
    (T : Ty n) (f : FinFun n m) (g : FinFun m l) :
    ty_rename (ty_rename T f) g = ty_rename T (comp f g)
    by struct T :=
ty_rename_rename (TyCapt C shape) f g :=
  f_equal2 TyCapt (capture_rename_rename C f g)
    (shape_rename_rename shape f g)
with shape_rename_rename {n m l : nat}
    (shape : Shape n) (f : FinFun n m) (g : FinFun m l) :
    shape_rename (shape_rename shape f) g =
      shape_rename shape (comp f g) by struct shape :=
shape_rename_rename ShTop f g := eq_refl;
shape_rename_rename ShBot f g := eq_refl;
shape_rename_rename (ShFun dom cod) f g :=
  f_equal2 ShFun (ty_rename_rename dom f g)
    (eq_trans (ty_rename_rename cod (ext f) (ext g))
      (f_equal (ty_rename cod) (ext_comp f g)));
shape_rename_rename (ShPair first a member) f g :=
  f_equal2 (fun first member => ShPair first a member)
    (ty_rename_rename first f g)
    (eq_trans (tau_rename_rename member (ext f) (ext g))
      (f_equal (tau_rename member) (ext_comp f g)));
shape_rename_rename (ShSingle p) f g :=
  f_equal ShSingle (path_rename_rename p f g);
shape_rename_rename (ShTSel p a) f g :=
  f_equal (fun p => ShTSel p a) (path_rename_rename p f g)
with tau_rename_rename {n m l : nat} {k : Kind}
    (d : Tau n k) (f : FinFun n m) (g : FinFun m l) :
    tau_rename (tau_rename d f) g = tau_rename d (comp f g)
    by struct d :=
tau_rename_rename (TauTerm T) f g :=
  f_equal TauTerm (ty_rename_rename T f g);
tau_rename_rename (TauType lower upper) f g :=
  f_equal2 TauType (shape_rename_rename lower f g)
    (shape_rename_rename upper f g);
tau_rename_rename (TauCapture lower upper) f g :=
  f_equal2 TauCapture (capture_rename_rename lower f g)
    (capture_rename_rename upper f g).

Lemma def_rename_rename {n m l : nat} {k : Kind}
    (d : Def n k) (f : FinFun n m) (g : FinFun m l) :
    def_rename (def_rename d f) g = def_rename d (comp f g).
Proof.
  destruct d as [n x|n shape|n C]; simp def_rename.
  - rewrite comp_apply. reflexivity.
  - apply f_equal. apply shape_rename_rename.
  - apply f_equal. apply capture_rename_rename.
Qed.

Lemma tm_rename_rename {n m l : nat}
    (t : Tm n) (f : FinFun n m) (g : FinFun m l) :
    tm_rename (tm_rename t f) g = tm_rename t (comp f g).
Proof.
  revert m l f g.
  induction t as [n p|n T body IH|n k x a d|n p q|n bound IHb body IHbody];
    intros m l f g; simp tm_rename.
  - now rewrite path_rename_rename.
  - rewrite ty_rename_rename, IH, ext_comp. reflexivity.
  - rewrite comp_apply, def_rename_rename. reflexivity.
  - now rewrite !path_rename_rename.
  - rewrite IHb, IHbody, ext_comp. reflexivity.
Qed.

Lemma path_weaken_rename {n m : nat}
    (p : Path n) (f : FinFun n m) :
    path_weaken (path_rename p f) =
      path_rename (path_weaken p) (ext f).
Proof.
  unfold path_weaken. rewrite !path_rename_rename, comp_weaken.
  reflexivity.
Qed.

Lemma capture_weaken_rename {n m : nat}
    (C : CaptureSet n) (f : FinFun n m) :
    capture_weaken (capture_rename C f) =
      capture_rename (capture_weaken C) (ext f).
Proof.
  unfold capture_weaken. rewrite !capture_rename_rename, comp_weaken.
  reflexivity.
Qed.

Lemma ty_weaken_rename {n m : nat}
    (T : Ty n) (f : FinFun n m) :
    ty_weaken (ty_rename T f) = ty_rename (ty_weaken T) (ext f).
Proof.
  unfold ty_weaken. rewrite !ty_rename_rename, comp_weaken.
  reflexivity.
Qed.

Lemma shape_weaken_rename {n m : nat}
    (shape : Shape n) (f : FinFun n m) :
    shape_weaken (shape_rename shape f) =
      shape_rename (shape_weaken shape) (ext f).
Proof.
  unfold shape_weaken. rewrite !shape_rename_rename, comp_weaken.
  reflexivity.
Qed.

Lemma tau_weaken_rename {n m : nat} {k : Kind}
    (d : Tau n k) (f : FinFun n m) :
    tau_weaken (tau_rename d f) = tau_rename (tau_weaken d) (ext f).
Proof.
  unfold tau_weaken. rewrite !tau_rename_rename, comp_weaken.
  reflexivity.
Qed.

(** Algebra of path substitution and opening. *)

Lemma subst_apply_finfun_as_subst {n m : nat}
    (f : FinFun n m) (x : Fin n) :
    subst_apply (finfun_as_subst f) x = PVar (apply f x).
Proof. unfold subst_apply, finfun_as_subst. apply vec_lookup_map. Qed.

Lemma subst_lift_zero {n m : nat} (s : PathSubst n m) :
    subst_apply (path_subst_lift s) FZ = PVar FZ.
Proof.
  unfold path_subst_lift, subst_apply, vec_lookup. simp fin_case.
  reflexivity.
Qed.

Lemma subst_lift_succ {n m : nat}
    (s : PathSubst n m) (x : Fin n) :
    subst_apply (path_subst_lift s) (FS x) =
      path_weaken (subst_apply s x).
Proof.
  unfold path_subst_lift, subst_apply at 1. unfold vec_lookup.
  simp fin_case. apply vec_lookup_map.
Qed.

Lemma subst_openAt_zero {n : nat} (p : Path n) :
    subst_apply (path_subst_openAt p) FZ = p.
Proof.
  unfold path_subst_openAt, subst_apply, vec_lookup. simp fin_case.
  reflexivity.
Qed.

Lemma subst_openAt_succ {n : nat} (p : Path n) (x : Fin n) :
    subst_apply (path_subst_openAt p) (FS x) = PVar x.
Proof.
  unfold path_subst_openAt, subst_apply at 1. unfold vec_lookup.
  simp fin_case. unfold path_subst_id, finfun_as_subst.
  rewrite vec_lookup_map.
  change (PVar (apply (id n) x) = PVar x).
  rewrite id_apply. reflexivity.
Qed.

Lemma subst_comp_apply {n m l : nat}
    (s : PathSubst n m) (t : PathSubst m l) (x : Fin n) :
    subst_apply (path_subst_comp s t) x =
      path_subst (subst_apply s x) t.
Proof.
  unfold path_subst_comp, subst_apply.
  exact (vec_lookup_map (fun p : Path m => path_subst p t) s x).
Qed.

Lemma path_subst_lift_id {n : nat} :
    path_subst_lift (path_subst_id n) = path_subst_id (S n).
Proof.
  apply path_subst_ext. intro x.
  refine (fin_case (P := fun x =>
      subst_apply (path_subst_lift (path_subst_id n)) x =
        subst_apply (path_subst_id (S n)) x) _ _ x).
  - rewrite subst_lift_zero. unfold path_subst_id.
    rewrite subst_apply_finfun_as_subst, id_apply. reflexivity.
  - intro i. rewrite subst_lift_succ.
    unfold path_subst_id at 1 2.
    rewrite !subst_apply_finfun_as_subst, !id_apply.
    unfold path_weaken. simp path_rename. rewrite weaken_apply.
    reflexivity.
Qed.

Lemma path_subst_identity {n : nat} (p : Path n) :
    path_subst p (path_subst_id n) = p.
Proof.
  induction p as [n x|n p IH|n p IH a]; simp path_subst.
  - unfold path_subst_id. rewrite subst_apply_finfun_as_subst, id_apply.
    reflexivity.
  - now rewrite IH.
  - now rewrite IH.
Qed.

Lemma capture_subst_identity {n : nat} (C : CaptureSet n) :
    capture_subst C (path_subst_id n) = C.
Proof.
  induction C as [n|n C IHC D IHD|n p|n p a];
    simp capture_subst; try rewrite path_subst_identity;
    try rewrite IHC; try rewrite IHD; reflexivity.
Qed.

Equations ty_subst_identity {n : nat} (T : Ty n) :
    ty_subst T (path_subst_id n) = T by struct T :=
ty_subst_identity (TyCapt C shape) :=
  f_equal2 TyCapt (capture_subst_identity C) (shape_subst_identity shape)
with shape_subst_identity {n : nat} (shape : Shape n) :
    shape_subst shape (path_subst_id n) = shape by struct shape :=
shape_subst_identity ShTop := eq_refl;
shape_subst_identity ShBot := eq_refl;
shape_subst_identity (ShFun dom cod) :=
  f_equal2 ShFun (ty_subst_identity dom)
    (eq_rect _ (fun s => ty_subst cod s = cod)
      (ty_subst_identity cod) _ (eq_sym path_subst_lift_id));
shape_subst_identity (ShPair first a member) :=
  f_equal2 (fun first member => ShPair first a member)
    (ty_subst_identity first)
    (eq_rect _ (fun s => tau_subst member s = member)
      (tau_subst_identity member) _ (eq_sym path_subst_lift_id));
shape_subst_identity (ShSingle p) :=
  f_equal ShSingle (path_subst_identity p);
shape_subst_identity (ShTSel p a) :=
  f_equal (fun p => ShTSel p a) (path_subst_identity p)
with tau_subst_identity {n : nat} {k : Kind} (d : Tau n k) :
    tau_subst d (path_subst_id n) = d by struct d :=
tau_subst_identity (TauTerm T) := f_equal TauTerm (ty_subst_identity T);
tau_subst_identity (TauType lower upper) :=
  f_equal2 TauType (shape_subst_identity lower)
    (shape_subst_identity upper);
tau_subst_identity (TauCapture lower upper) :=
  f_equal2 TauCapture (capture_subst_identity lower)
    (capture_subst_identity upper).

Lemma finfun_as_subst_ext {n m : nat} (f : FinFun n m) :
    finfun_as_subst (ext f) = path_subst_lift (finfun_as_subst f).
Proof.
  apply path_subst_ext. intro x.
  refine (fin_case (P := fun x =>
      subst_apply (finfun_as_subst (ext f)) x =
        subst_apply (path_subst_lift (finfun_as_subst f)) x) _ _ x).
  - rewrite subst_apply_finfun_as_subst, ext_zero, subst_lift_zero.
    reflexivity.
  - intro i.
    rewrite subst_apply_finfun_as_subst, ext_succ, subst_lift_succ.
    rewrite subst_apply_finfun_as_subst.
    unfold path_weaken. simp path_rename. rewrite weaken_apply.
    reflexivity.
Qed.

Lemma finfun_openAt_as_subst {n : nat} (x : Fin n) :
    finfun_as_subst (openAt x) = path_subst_openAt (PVar x).
Proof.
  apply path_subst_ext. intro y.
  refine (fin_case (P := fun y =>
      subst_apply (finfun_as_subst (openAt x)) y =
        subst_apply (path_subst_openAt (PVar x)) y) _ _ y).
  - rewrite subst_apply_finfun_as_subst, openAt_zero, subst_openAt_zero.
    reflexivity.
  - intro i.
    rewrite subst_apply_finfun_as_subst, openAt_succ, subst_openAt_succ.
    reflexivity.
Qed.

Lemma path_subst_as_rename {n m : nat}
    (p : Path n) (f : FinFun n m) :
    path_subst p (finfun_as_subst f) = path_rename p f.
Proof.
  induction p as [n x|n p IH|n p IH a]; simp path_subst path_rename.
  - apply subst_apply_finfun_as_subst.
  - now rewrite IH.
  - now rewrite IH.
Qed.

Lemma capture_subst_as_rename {n m : nat}
    (C : CaptureSet n) (f : FinFun n m) :
    capture_subst C (finfun_as_subst f) = capture_rename C f.
Proof.
  induction C as [n|n C IHC D IHD|n p|n p a];
    simp capture_subst capture_rename;
    try rewrite path_subst_as_rename;
    try rewrite IHC; try rewrite IHD; reflexivity.
Qed.

Equations ty_subst_as_rename {n m : nat}
    (T : Ty n) (f : FinFun n m) :
    ty_subst T (finfun_as_subst f) = ty_rename T f by struct T :=
ty_subst_as_rename (TyCapt C shape) f :=
  f_equal2 TyCapt (capture_subst_as_rename C f)
    (shape_subst_as_rename shape f)
with shape_subst_as_rename {n m : nat}
    (shape : Shape n) (f : FinFun n m) :
    shape_subst shape (finfun_as_subst f) = shape_rename shape f
    by struct shape :=
shape_subst_as_rename ShTop f := eq_refl;
shape_subst_as_rename ShBot f := eq_refl;
shape_subst_as_rename (ShFun dom cod) f :=
  f_equal2 ShFun (ty_subst_as_rename dom f)
    (eq_rect _
      (fun s => ty_subst cod s = ty_rename cod (ext f))
      (ty_subst_as_rename cod (ext f)) _ (finfun_as_subst_ext f));
shape_subst_as_rename (ShPair first a member) f :=
  f_equal2 (fun first member => ShPair first a member)
    (ty_subst_as_rename first f)
    (eq_rect _
      (fun s => tau_subst member s = tau_rename member (ext f))
      (tau_subst_as_rename member (ext f)) _ (finfun_as_subst_ext f));
shape_subst_as_rename (ShSingle p) f :=
  f_equal ShSingle (path_subst_as_rename p f);
shape_subst_as_rename (ShTSel p a) f :=
  f_equal (fun p => ShTSel p a) (path_subst_as_rename p f)
with tau_subst_as_rename {n m : nat} {k : Kind}
    (d : Tau n k) (f : FinFun n m) :
    tau_subst d (finfun_as_subst f) = tau_rename d f by struct d :=
tau_subst_as_rename (TauTerm T) f :=
  f_equal TauTerm (ty_subst_as_rename T f);
tau_subst_as_rename (TauType lower upper) f :=
  f_equal2 TauType (shape_subst_as_rename lower f)
    (shape_subst_as_rename upper f);
tau_subst_as_rename (TauCapture lower upper) f :=
  f_equal2 TauCapture (capture_subst_as_rename lower f)
    (capture_subst_as_rename upper f).

Lemma path_weaken_subst_lift {n m : nat}
    (p : Path n) (s : PathSubst n m) :
    path_subst (path_weaken p) (path_subst_lift s) =
      path_weaken (path_subst p s).
Proof.
  induction p as [n x|n p IH|n p IH a].
  - unfold path_weaken at 1. simp path_rename. rewrite weaken_apply.
    simp path_subst. rewrite subst_lift_succ. reflexivity.
  - change (PFst (path_subst (path_weaken p) (path_subst_lift s)) =
      PFst (path_weaken (path_subst p s))).
    now rewrite IH.
  - change (PSel (path_subst (path_weaken p) (path_subst_lift s)) a =
      PSel (path_weaken (path_subst p s)) a).
    now rewrite IH.
Qed.

Lemma path_subst_comp_lift {n m l : nat}
    (s : PathSubst n m) (t : PathSubst m l) :
    path_subst_lift (path_subst_comp s t) =
      path_subst_comp (path_subst_lift s) (path_subst_lift t).
Proof.
  apply path_subst_ext. intro x.
  refine (fin_case (P := fun x =>
      subst_apply (path_subst_lift (path_subst_comp s t)) x =
        subst_apply
          (path_subst_comp (path_subst_lift s) (path_subst_lift t)) x)
      _ _ x).
  - rewrite subst_lift_zero, subst_comp_apply, subst_lift_zero.
    simp path_subst. rewrite subst_lift_zero. reflexivity.
  - intro i.
    rewrite subst_lift_succ, !subst_comp_apply, !subst_lift_succ.
    rewrite path_weaken_subst_lift. reflexivity.
Qed.

Lemma path_subst_compose {n m l : nat}
    (p : Path n) (s : PathSubst n m) (t : PathSubst m l) :
    path_subst (path_subst p s) t =
      path_subst p (path_subst_comp s t).
Proof.
  induction p as [n x|n p IH|n p IH a]; simp path_subst.
  - rewrite subst_comp_apply. reflexivity.
  - now rewrite IH.
  - now rewrite IH.
Qed.

Lemma capture_subst_compose {n m l : nat}
    (C : CaptureSet n) (s : PathSubst n m) (t : PathSubst m l) :
    capture_subst (capture_subst C s) t =
      capture_subst C (path_subst_comp s t).
Proof.
  induction C as [n|n C IHC D IHD|n p|n p a];
    simp capture_subst; try rewrite path_subst_compose;
    try rewrite IHC; try rewrite IHD; reflexivity.
Qed.

Equations ty_subst_compose {n m l : nat}
    (T : Ty n) (s : PathSubst n m) (t : PathSubst m l) :
    ty_subst (ty_subst T s) t =
      ty_subst T (path_subst_comp s t) by struct T :=
ty_subst_compose (TyCapt C shape) s t :=
  f_equal2 TyCapt (capture_subst_compose C s t)
    (shape_subst_compose shape s t)
with shape_subst_compose {n m l : nat}
    (shape : Shape n) (s : PathSubst n m) (t : PathSubst m l) :
    shape_subst (shape_subst shape s) t =
      shape_subst shape (path_subst_comp s t) by struct shape :=
shape_subst_compose ShTop s t := eq_refl;
shape_subst_compose ShBot s t := eq_refl;
shape_subst_compose (ShFun dom cod) s t :=
  f_equal2 ShFun (ty_subst_compose dom s t)
    (eq_trans (ty_subst_compose cod (path_subst_lift s)
      (path_subst_lift t))
      (f_equal (ty_subst cod) (eq_sym (path_subst_comp_lift s t))));
shape_subst_compose (ShPair first a member) s t :=
  f_equal2 (fun first member => ShPair first a member)
    (ty_subst_compose first s t)
    (eq_trans (tau_subst_compose member (path_subst_lift s)
      (path_subst_lift t))
      (f_equal (tau_subst member) (eq_sym (path_subst_comp_lift s t))));
shape_subst_compose (ShSingle p) s t :=
  f_equal ShSingle (path_subst_compose p s t);
shape_subst_compose (ShTSel p a) s t :=
  f_equal (fun p => ShTSel p a) (path_subst_compose p s t)
with tau_subst_compose {n m l : nat} {k : Kind}
    (d : Tau n k) (s : PathSubst n m) (t : PathSubst m l) :
    tau_subst (tau_subst d s) t =
      tau_subst d (path_subst_comp s t) by struct d :=
tau_subst_compose (TauTerm T) s t :=
  f_equal TauTerm (ty_subst_compose T s t);
tau_subst_compose (TauType lower upper) s t :=
  f_equal2 TauType (shape_subst_compose lower s t)
    (shape_subst_compose upper s t);
tau_subst_compose (TauCapture lower upper) s t :=
  f_equal2 TauCapture (capture_subst_compose lower s t)
    (capture_subst_compose upper s t).

Lemma path_subst_openAt_rename {n m : nat}
    (p : Path n) (f : FinFun n m) :
    path_subst_comp (path_subst_openAt p) (finfun_as_subst f) =
      path_subst_comp (finfun_as_subst (ext f))
        (path_subst_openAt (path_rename p f)).
Proof.
  apply path_subst_ext. intro x.
  refine (fin_case (P := fun x =>
      subst_apply
        (path_subst_comp (path_subst_openAt p) (finfun_as_subst f)) x =
      subst_apply
        (path_subst_comp (finfun_as_subst (ext f))
          (path_subst_openAt (path_rename p f))) x) _ _ x).
  - rewrite !subst_comp_apply, subst_openAt_zero,
      path_subst_as_rename, subst_apply_finfun_as_subst, ext_zero.
    simp path_subst. rewrite subst_openAt_zero. reflexivity.
  - intro i.
    rewrite !subst_comp_apply, subst_openAt_succ.
    rewrite subst_apply_finfun_as_subst, ext_succ.
    simp path_subst.
    rewrite subst_apply_finfun_as_subst, subst_openAt_succ.
    reflexivity.
Qed.

Lemma path_subst_openAt_weaken {n : nat} (p : Path n) :
    path_subst_comp (finfun_as_subst (weaken n))
      (path_subst_openAt p) = path_subst_id n.
Proof.
  apply path_subst_ext. intro x.
  rewrite subst_comp_apply, subst_apply_finfun_as_subst, weaken_apply.
  simp path_subst. rewrite subst_openAt_succ.
  unfold path_subst_id. rewrite subst_apply_finfun_as_subst, id_apply.
  reflexivity.
Qed.

Lemma path_weaken_open {n : nat} (p q : Path n) :
    path_open (path_weaken p) q = p.
Proof.
  induction p as [n x|n p IH|n p IH a].
  - unfold path_open, path_weaken. simp path_rename.
    rewrite weaken_apply. simp path_subst. rewrite subst_openAt_succ.
    reflexivity.
  - change (PFst (path_open (path_weaken p) q) = PFst p).
    now rewrite IH.
  - change (PSel (path_open (path_weaken p) q) a = PSel p a).
    now rewrite IH.
Qed.

Lemma path_subst_openAt_comp {n m : nat}
    (p : Path n) (s : PathSubst n m) :
    path_subst_comp (path_subst_openAt p) s =
      path_subst_comp (path_subst_lift s)
        (path_subst_openAt (path_subst p s)).
Proof.
  apply path_subst_ext. intro x.
  refine (fin_case (P := fun x =>
      subst_apply (path_subst_comp (path_subst_openAt p) s) x =
        subst_apply
          (path_subst_comp (path_subst_lift s)
            (path_subst_openAt (path_subst p s))) x) _ _ x).
  - rewrite !subst_comp_apply, subst_openAt_zero, subst_lift_zero.
    simp path_subst. rewrite subst_openAt_zero. reflexivity.
  - intro i.
    rewrite !subst_comp_apply, subst_openAt_succ, subst_lift_succ.
    change (subst_apply s i =
      path_open (path_weaken (subst_apply s i)) (path_subst p s)).
    symmetry. apply path_weaken_open.
Qed.

Lemma tau_open_subst {n m : nat} {k : Kind}
    (d : Tau (S n) k) (p : Path n) (s : PathSubst n m) :
    tau_subst (tau_open d p) s =
      tau_open (tau_subst d (path_subst_lift s)) (path_subst p s).
Proof.
  unfold tau_open.
  rewrite !tau_subst_compose, path_subst_openAt_comp. reflexivity.
Qed.

Lemma capture_open_subst {n m : nat}
    (C : CaptureSet (S n)) (p : Path n) (s : PathSubst n m) :
    capture_subst (capture_open C p) s =
      capture_open (capture_subst C (path_subst_lift s))
        (path_subst p s).
Proof.
  unfold capture_open.
  rewrite !capture_subst_compose, path_subst_openAt_comp. reflexivity.
Qed.

Lemma ty_open_subst {n m : nat}
    (T : Ty (S n)) (p : Path n) (s : PathSubst n m) :
    ty_subst (ty_open T p) s =
      ty_open (ty_subst T (path_subst_lift s)) (path_subst p s).
Proof.
  unfold ty_open.
  rewrite !ty_subst_compose, path_subst_openAt_comp. reflexivity.
Qed.

Lemma shape_open_subst {n m : nat}
    (shape : Shape (S n)) (p : Path n) (s : PathSubst n m) :
    shape_subst (shape_open shape p) s =
      shape_open (shape_subst shape (path_subst_lift s))
        (path_subst p s).
Proof.
  unfold shape_open.
  rewrite !shape_subst_compose, path_subst_openAt_comp. reflexivity.
Qed.

Lemma path_open_subst {n m : nat}
    (p : Path (S n)) (q : Path n) (s : PathSubst n m) :
    path_subst (path_open p q) s =
      path_open (path_subst p (path_subst_lift s)) (path_subst q s).
Proof.
  unfold path_open.
  rewrite !path_subst_compose, path_subst_openAt_comp. reflexivity.
Qed.

Lemma capture_rename_openAt_eq_open_var {n : nat}
    (C : CaptureSet (S n)) (x : Fin n) :
    capture_rename C (openAt x) = capture_open C (PVar x).
Proof.
  unfold capture_open.
  rewrite <- capture_subst_as_rename.
  rewrite finfun_openAt_as_subst. reflexivity.
Qed.

Lemma ty_rename_openAt_eq_open_var {n : nat}
    (T : Ty (S n)) (x : Fin n) :
    ty_rename T (openAt x) = ty_open T (PVar x).
Proof.
  unfold ty_open.
  rewrite <- ty_subst_as_rename.
  rewrite finfun_openAt_as_subst. reflexivity.
Qed.

Lemma shape_rename_openAt_eq_open_var {n : nat}
    (shape : Shape (S n)) (x : Fin n) :
    shape_rename shape (openAt x) = shape_open shape (PVar x).
Proof.
  unfold shape_open.
  rewrite <- shape_subst_as_rename.
  rewrite finfun_openAt_as_subst. reflexivity.
Qed.

Lemma tau_rename_openAt_eq_open_var {n : nat} {k : Kind}
    (d : Tau (S n) k) (x : Fin n) :
    tau_rename d (openAt x) = tau_open d (PVar x).
Proof.
  unfold tau_open.
  rewrite <- tau_subst_as_rename.
  rewrite finfun_openAt_as_subst. reflexivity.
Qed.

Lemma path_open_rename {n m : nat}
    (p : Path (S n)) (q : Path n) (f : FinFun n m) :
    path_rename (path_open p q) f =
      path_open (path_rename p (ext f)) (path_rename q f).
Proof.
  rewrite <- path_subst_as_rename.
  rewrite path_open_subst, <- finfun_as_subst_ext.
  rewrite !path_subst_as_rename. reflexivity.
Qed.

Lemma capture_open_rename {n m : nat}
    (C : CaptureSet (S n)) (p : Path n) (f : FinFun n m) :
    capture_rename (capture_open C p) f =
      capture_open (capture_rename C (ext f)) (path_rename p f).
Proof.
  rewrite <- capture_subst_as_rename.
  rewrite capture_open_subst, <- finfun_as_subst_ext.
  rewrite capture_subst_as_rename, path_subst_as_rename. reflexivity.
Qed.

Lemma ty_open_rename {n m : nat}
    (T : Ty (S n)) (p : Path n) (f : FinFun n m) :
    ty_rename (ty_open T p) f =
      ty_open (ty_rename T (ext f)) (path_rename p f).
Proof.
  rewrite <- ty_subst_as_rename.
  rewrite ty_open_subst, <- finfun_as_subst_ext.
  rewrite ty_subst_as_rename, path_subst_as_rename. reflexivity.
Qed.

Lemma shape_open_rename {n m : nat}
    (shape : Shape (S n)) (p : Path n) (f : FinFun n m) :
    shape_rename (shape_open shape p) f =
      shape_open (shape_rename shape (ext f)) (path_rename p f).
Proof.
  rewrite <- shape_subst_as_rename.
  rewrite shape_open_subst, <- finfun_as_subst_ext.
  rewrite shape_subst_as_rename, path_subst_as_rename. reflexivity.
Qed.

Lemma tau_open_rename {n m : nat} {k : Kind}
    (d : Tau (S n) k) (p : Path n) (f : FinFun n m) :
    tau_rename (tau_open d p) f =
      tau_open (tau_rename d (ext f)) (path_rename p f).
Proof.
  rewrite <- tau_subst_as_rename.
  rewrite tau_open_subst, <- finfun_as_subst_ext.
  rewrite tau_subst_as_rename, path_subst_as_rename. reflexivity.
Qed.

Lemma capture_weaken_open {n : nat}
    (C : CaptureSet n) (p : Path n) :
    capture_open (capture_weaken C) p = C.
Proof.
  unfold capture_open, capture_weaken.
  rewrite <- capture_subst_as_rename, capture_subst_compose.
  rewrite path_subst_openAt_weaken. apply capture_subst_identity.
Qed.

Lemma ty_weaken_open {n : nat} (T : Ty n) (p : Path n) :
    ty_open (ty_weaken T) p = T.
Proof.
  unfold ty_open, ty_weaken.
  rewrite <- ty_subst_as_rename, ty_subst_compose.
  rewrite path_subst_openAt_weaken. apply ty_subst_identity.
Qed.

Lemma shape_weaken_open {n : nat}
    (shape : Shape n) (p : Path n) :
    shape_open (shape_weaken shape) p = shape.
Proof.
  unfold shape_open, shape_weaken.
  rewrite <- shape_subst_as_rename, shape_subst_compose.
  rewrite path_subst_openAt_weaken. apply shape_subst_identity.
Qed.

Lemma tau_weaken_open {n : nat} {k : Kind}
    (d : Tau n k) (p : Path n) : tau_open (tau_weaken d) p = d.
Proof.
  unfold tau_open, tau_weaken.
  rewrite <- tau_subst_as_rename, tau_subst_compose.
  rewrite path_subst_openAt_weaken. apply tau_subst_identity.
Qed.

Print Assumptions tau_open_rename.
Print Assumptions tau_weaken_open.
