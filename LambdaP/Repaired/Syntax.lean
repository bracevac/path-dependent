import LambdaP.Repaired.FinFun

/-!
The intrinsically scoped syntax of the repaired pre-restart `lambda_p`
calculus. Term singleton types and abstract type selections are distinct;
all other syntax and binding operations remain faithful to the original.
-/

namespace LambdaP.Repaired

/-- Labels for term and type members. -/
abbrev Name : Type := Nat

/-- The kind of the dependent second component of a pair. -/
inductive Kind : Type where
| star
| iota
deriving DecidableEq

/-- Paths are variables, first projections, and named selections. -/
inductive Path : Nat -> Type where
| var : Fin n -> Path n
| fst : Path n -> Path n
| sel : Path n -> Name -> Path n
deriving DecidableEq

mutual

/-- Generalized types used as dependent pair components. -/
inductive Tau : Nat -> Kind -> Type where
| ty : Ty n -> Tau n .star
| intv : Ty n -> Ty n -> Tau n .iota

/-- Definitions stored in pair values. -/
inductive Def : Nat -> Kind -> Type where
| val : Fin n -> Def n .star
| «type» : Ty n -> Def n .iota

/-- Types of the original calculus. -/
inductive Ty : Nat -> Type where
| Top : Ty n
| Bot : Ty n
| Fun : Ty n -> Ty (n + 1) -> Ty n
| Pair : Ty n -> Name -> Tau (n + 1) k -> Ty n
| Single : Path n -> Ty n
/-- Abstract type-member selection `p.A`, distinct from the term singleton `{p}`. -/
| TSel : Path n -> Name -> Ty n

/-- Terms in monadic normal form. -/
inductive Tm : Nat -> Type where
| path : Path n -> Tm n
| abs : Ty n -> Tm (n + 1) -> Tm n
| pair : Fin n -> Name -> Def n k -> Tm n
| app : Path n -> Path n -> Tm n
| «let» : Tm n -> Tm (n + 1) -> Tm n
| typed : Tm n -> Ty n -> Tm n

end

instance : Coe (Path n) (Ty n) where
  coe := Ty.Single

instance : Coe (Path n) (Tm n) where
  coe := Tm.path

instance : Coe (Ty n) (Tau n .star) where
  coe := Tau.ty

instance : Coe (Ty n) (Def n .iota) where
  coe := Def.type

/-- An interval viewed as a pair of ordinary types. -/
abbrev Interval (n : Nat) := Ty n × Ty n

def Tau.interval (sig : Tau n .iota) : Interval n :=
  match sig with
  | .intv S T => (S, T)

/-- Syntactic variables, used by the tail-path reduction rule. -/
inductive Path.IsVar : Path n -> Prop where
| var : IsVar (.var x)

/-- Values of the original MNF calculus. -/
inductive Tm.IsValue : Tm n -> Prop where
| abs : IsValue (.abs T t)
| pair : IsValue (.pair y a d)

/-! ## Renaming -/

def Path.rename : Path n -> FinFun n m -> Path m
| .var x, f => .var (f x)
| .fst p, f => .fst (p.rename f)
| .sel p a, f => .sel (p.rename f) a

mutual

def Ty.rename : Ty n -> FinFun n m -> Ty m
| .Top, _ => .Top
| .Bot, _ => .Bot
| .Fun S T, f => .Fun (S.rename f) (T.rename f.ext)
| .Pair S a d, f => .Pair (S.rename f) a (d.rename f.ext)
| .Single p, f => .Single (p.rename f)
| .TSel p A, f => .TSel (p.rename f) A

def Tau.rename : Tau n k -> FinFun n m -> Tau m k
| .ty T, f => .ty (T.rename f)
| .intv S T, f => .intv (S.rename f) (T.rename f)

def Tm.rename : Tm n -> FinFun n m -> Tm m
| .path p, f => .path (p.rename f)
| .abs T t, f => .abs (T.rename f) (t.rename f.ext)
| .pair x a d, f => .pair (f x) a (d.rename f)
| .app p q, f => .app (p.rename f) (q.rename f)
| .let t u, f => .let (t.rename f) (u.rename f.ext)
| .typed t T, f => .typed (t.rename f) (T.rename f)

def Def.rename : Def n k -> FinFun n m -> Def m k
| .val x, f => .val (f x)
| .type T, f => .type (T.rename f)

end

def Path.weaken (p : Path n) : Path (n + 1) := p.rename FinFun.weaken
def Ty.weaken (T : Ty n) : Ty (n + 1) := T.rename FinFun.weaken
def Tau.weaken (d : Tau n k) : Tau (n + 1) k := d.rename FinFun.weaken
def Tm.weaken (t : Tm n) : Tm (n + 1) := t.rename FinFun.weaken
def Def.weaken (d : Def n k) : Def (n + 1) k := d.rename FinFun.weaken

/-! ## Path substitution and opening -/

/-- A simultaneous substitution of paths for variables. -/
abbrev PathSubst (n m : Nat) : Type := Fin n -> Path m

namespace PathSubst

/-- The identity path substitution. -/
def id : PathSubst n n := fun x => .var x

/-- Lift a path substitution through one binder. -/
def lift (σ : PathSubst n m) : PathSubst (n + 1) (m + 1) :=
  Fin.cases (.var 0) (fun i => (σ i).weaken)

/-- The single-binder substitution which replaces variable `0` by `p`. -/
def openAt (p : Path n) : PathSubst (n + 1) n :=
  Fin.cases p (fun i => .var i)

end PathSubst

/-- Simultaneous path substitution. -/
def Path.subst : Path n -> PathSubst n m -> Path m
| .var x, σ => σ x
| .fst p, σ => .fst (p.subst σ)
| .sel p a, σ => .sel (p.subst σ) a

mutual

/-- Capture-avoiding simultaneous path substitution in types. -/
def Ty.subst : Ty n -> PathSubst n m -> Ty m
| .Top, _ => .Top
| .Bot, _ => .Bot
| .Fun S T, σ => .Fun (S.subst σ) (T.subst σ.lift)
| .Pair S a d, σ => .Pair (S.subst σ) a (d.subst σ.lift)
| .Single p, σ => .Single (p.subst σ)
| .TSel p A, σ => .TSel (p.subst σ) A

/-- Capture-avoiding simultaneous path substitution in generalized types. -/
def Tau.subst : Tau n k -> PathSubst n m -> Tau m k
| .ty T, σ => .ty (T.subst σ)
| .intv S T, σ => .intv (S.subst σ) (T.subst σ)

end

/-- Replace the newest bound variable in a path by an arbitrary path. -/
def Path.open (q : Path (n + 1)) (p : Path n) : Path n :=
  q.subst (PathSubst.openAt p)

/-- Capture-avoiding replacement of the newest bound variable in a type. -/
def Ty.open (T : Ty (n + 1)) (p : Path n) : Ty n :=
  T.subst (PathSubst.openAt p)

/-- Capture-avoiding replacement in a generalized type. -/
def Tau.open (d : Tau (n + 1) k) (p : Path n) : Tau n k :=
  d.subst (PathSubst.openAt p)

/-- Term opening substitutes an existing variable for the newest binder. -/
def Tm.open (t : Tm (n + 1)) (x : Fin n) : Tm n :=
  t.rename (FinFun.openAt x)

/-- Definition opening substitutes an existing variable for the newest binder. -/
def Def.open (d : Def (n + 1) k) (x : Fin n) : Def n k :=
  d.rename (FinFun.openAt x)

/-! ## Algebra of renaming -/

theorem Path.rename_id (p : Path n) : p.rename FinFun.id = p := by
  induction p with
  | var x => rfl
  | fst p ih => simp only [Path.rename, ih]
  | sel p a ih => simp only [Path.rename, ih]

theorem Path.rename_rename (p : Path n) (f : FinFun n m) (g : FinFun m l) :
    (p.rename f).rename g = p.rename (g ∘ f) := by
  induction p with
  | var x => rfl
  | fst p ih => simp only [Path.rename, ih]
  | sel p a ih => simp only [Path.rename, ih]

mutual

theorem Ty.rename_id (T : Ty n) : T.rename FinFun.id = T :=
  match T with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Ty.rename, FinFun.ext_id, Ty.rename_id S, Ty.rename_id T]
  | .Pair S a d => by
      simp only [Ty.rename, FinFun.ext_id, Ty.rename_id S, Tau.rename_id d]
  | .Single p => by simp only [Ty.rename, Path.rename_id]
  | .TSel p A => by simp only [Ty.rename, Path.rename_id]

theorem Tau.rename_id (d : Tau n k) : d.rename FinFun.id = d :=
  match d with
  | .ty T => by simp only [Tau.rename, Ty.rename_id]
  | .intv S T => by simp only [Tau.rename, Ty.rename_id]

theorem Tm.rename_id (t : Tm n) : t.rename FinFun.id = t :=
  match t with
  | .path p => by simp only [Tm.rename, Path.rename_id]
  | .abs T t => by
      simp only [Tm.rename, FinFun.ext_id, Ty.rename_id, Tm.rename_id]
  | .pair x a d => by simp only [Tm.rename, FinFun.id_apply, Def.rename_id]
  | .app p q => by simp only [Tm.rename, Path.rename_id]
  | .let t u => by
      simp only [Tm.rename, FinFun.ext_id, Tm.rename_id]
  | .typed t T => by simp only [Tm.rename, Tm.rename_id, Ty.rename_id]

theorem Def.rename_id (d : Def n k) : d.rename FinFun.id = d :=
  match d with
  | .val x => by simp only [Def.rename, FinFun.id_apply]
  | .type T => by simp only [Def.rename, Ty.rename_id]

end

mutual

theorem Ty.rename_rename (T : Ty n) (f : FinFun n m) (g : FinFun m l) :
    (T.rename f).rename g = T.rename (g ∘ f) :=
  match T with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Ty.rename, Ty.rename_rename S f g,
        Ty.rename_rename T f.ext g.ext, FinFun.ext_comp_ext]
  | .Pair S a d => by
      simp only [Ty.rename, Ty.rename_rename S f g,
        Tau.rename_rename d f.ext g.ext, FinFun.ext_comp_ext]
  | .Single p => by simp only [Ty.rename, Path.rename_rename]
  | .TSel p A => by simp only [Ty.rename, Path.rename_rename]

theorem Tau.rename_rename (d : Tau n k) (f : FinFun n m) (g : FinFun m l) :
    (d.rename f).rename g = d.rename (g ∘ f) :=
  match d with
  | .ty T => by simp only [Tau.rename, Ty.rename_rename]
  | .intv S T => by simp only [Tau.rename, Ty.rename_rename]

theorem Tm.rename_rename (t : Tm n) (f : FinFun n m) (g : FinFun m l) :
    (t.rename f).rename g = t.rename (g ∘ f) :=
  match t with
  | .path p => by simp only [Tm.rename, Path.rename_rename]
  | .abs T t => by
      simp only [Tm.rename, Ty.rename_rename, Tm.rename_rename,
        FinFun.ext_comp_ext]
  | .pair x a d => by
      simp only [Tm.rename, Def.rename_rename]
      rfl
  | .app p q => by simp only [Tm.rename, Path.rename_rename]
  | .let t u => by
      simp only [Tm.rename, Tm.rename_rename, FinFun.ext_comp_ext]
  | .typed t T => by simp only [Tm.rename, Tm.rename_rename, Ty.rename_rename]

theorem Def.rename_rename (d : Def n k) (f : FinFun n m) (g : FinFun m l) :
    (d.rename f).rename g = d.rename (g ∘ f) :=
  match d with
  | .val x => rfl
  | .type T => by simp only [Def.rename, Ty.rename_rename]

end

theorem Path.weaken_rename (p : Path n) (f : FinFun n m) :
    (p.rename f).weaken = p.weaken.rename f.ext := by
  simp only [Path.weaken, Path.rename_rename, FinFun.comp_weaken]

theorem Ty.weaken_rename (T : Ty n) (f : FinFun n m) :
    (T.rename f).weaken = T.weaken.rename f.ext := by
  simp only [Ty.weaken, Ty.rename_rename, FinFun.comp_weaken]

theorem Tau.weaken_rename (d : Tau n k) (f : FinFun n m) :
    (d.rename f).weaken = d.weaken.rename f.ext := by
  simp only [Tau.weaken, Tau.rename_rename, FinFun.comp_weaken]

theorem Tm.weaken_rename (t : Tm n) (f : FinFun n m) :
    (t.rename f).weaken = t.weaken.rename f.ext := by
  simp only [Tm.weaken, Tm.rename_rename, FinFun.comp_weaken]

theorem Def.weaken_rename (d : Def n k) (f : FinFun n m) :
    (d.rename f).weaken = d.weaken.rename f.ext := by
  simp only [Def.weaken, Def.rename_rename, FinFun.comp_weaken]

/-! ## Algebra of path substitution and opening -/

namespace PathSubst

@[simp] theorem lift_zero (σ : PathSubst n m) : σ.lift 0 = .var 0 := rfl

@[simp] theorem lift_succ (σ : PathSubst n m) (x : Fin n) :
    σ.lift x.succ = (σ x).weaken := rfl

@[simp] theorem openAt_zero (p : Path n) : openAt p 0 = p := rfl

@[simp] theorem openAt_succ (p : Path n) (x : Fin n) :
    openAt p x.succ = .var x := rfl

theorem lift_id : (id (n := n)).lift = id := by
  apply _root_.funext
  intro x
  refine Fin.cases ?_ (fun i => ?_) x <;> rfl

/-- Post-renaming commutes with lifting a path substitution. -/
theorem lift_post_rename (σ : PathSubst n m) (f : FinFun m l) :
    (fun x => (σ.lift x).rename f.ext) =
      PathSubst.lift (fun x => (σ x).rename f) := by
  apply _root_.funext
  intro x
  refine Fin.cases ?_ (fun i => ?_) x
  · rfl
  · change (σ i).weaken.rename f.ext = ((σ i).rename f).weaken
    exact (Path.weaken_rename (σ i) f).symm

/-- Pre-renaming commutes with lifting a path substitution. -/
theorem lift_pre_rename (g : FinFun n m) (σ : PathSubst m l) :
    (fun x => σ.lift (g.ext x)) = PathSubst.lift (fun x => σ (g x)) := by
  apply _root_.funext
  intro x
  refine Fin.cases ?_ (fun i => ?_) x <;> rfl

/-- Opening is natural with respect to a subsequent renaming. -/
theorem openAt_rename (p : Path n) (f : FinFun n m) :
    (fun x => (openAt p x).rename f) =
      (fun x => openAt (p.rename f) (f.ext x)) := by
  apply _root_.funext
  intro x
  refine Fin.cases ?_ (fun i => ?_) x <;> rfl

/-- The opening substitution cancels weakening. -/
theorem openAt_weaken (p : Path n) :
    (fun x => openAt p (FinFun.weaken x)) = id := by
  apply _root_.funext
  intro x
  rfl

end PathSubst

theorem Path.subst_id (p : Path n) : p.subst PathSubst.id = p := by
  induction p with
  | var x => rfl
  | fst p ih => simp only [Path.subst, ih]
  | sel p a ih => simp only [Path.subst, ih]

theorem Path.subst_rename (p : Path n) (σ : PathSubst n m) (f : FinFun m l) :
    (p.subst σ).rename f = p.subst (fun x => (σ x).rename f) := by
  induction p with
  | var x => rfl
  | fst p ih => simp only [Path.subst, Path.rename, ih]
  | sel p a ih => simp only [Path.subst, Path.rename, ih]

theorem Path.rename_subst (p : Path n) (g : FinFun n m) (σ : PathSubst m l) :
    (p.rename g).subst σ = p.subst (fun x => σ (g x)) := by
  induction p with
  | var x => rfl
  | fst p ih => simp only [Path.rename, Path.subst, ih]
  | sel p a ih => simp only [Path.rename, Path.subst, ih]

mutual

theorem Ty.subst_id (T : Ty n) : T.subst PathSubst.id = T :=
  match T with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Ty.subst, PathSubst.lift_id, Ty.subst_id S, Ty.subst_id T]
  | .Pair S a d => by
      simp only [Ty.subst, PathSubst.lift_id, Ty.subst_id S, Tau.subst_id d]
  | .Single p => by simp only [Ty.subst, Path.subst_id]
  | .TSel p A => by simp only [Ty.subst, Path.subst_id]

theorem Tau.subst_id (d : Tau n k) : d.subst PathSubst.id = d :=
  match d with
  | .ty T => by simp only [Tau.subst, Ty.subst_id]
  | .intv S T => by simp only [Tau.subst, Ty.subst_id]

end

mutual

theorem Ty.subst_rename (T : Ty n) (σ : PathSubst n m) (f : FinFun m l) :
    (T.subst σ).rename f = T.subst (fun x => (σ x).rename f) :=
  match T with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Ty.subst, Ty.rename, Ty.subst_rename S σ f,
        Ty.subst_rename T σ.lift f.ext, PathSubst.lift_post_rename]
  | .Pair S a d => by
      simp only [Ty.subst, Ty.rename, Ty.subst_rename S σ f,
        Tau.subst_rename d σ.lift f.ext, PathSubst.lift_post_rename]
  | .Single p => by simp only [Ty.subst, Ty.rename, Path.subst_rename]
  | .TSel p A => by simp only [Ty.subst, Ty.rename, Path.subst_rename]

theorem Tau.subst_rename (d : Tau n k) (σ : PathSubst n m) (f : FinFun m l) :
    (d.subst σ).rename f = d.subst (fun x => (σ x).rename f) :=
  match d with
  | .ty T => by simp only [Tau.subst, Tau.rename, Ty.subst_rename]
  | .intv S T => by simp only [Tau.subst, Tau.rename, Ty.subst_rename]

end

mutual

theorem Ty.rename_subst (T : Ty n) (g : FinFun n m) (σ : PathSubst m l) :
    (T.rename g).subst σ = T.subst (fun x => σ (g x)) :=
  match T with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Ty.rename, Ty.subst, Ty.rename_subst S g σ,
        Ty.rename_subst T g.ext σ.lift, PathSubst.lift_pre_rename]
  | .Pair S a d => by
      simp only [Ty.rename, Ty.subst, Ty.rename_subst S g σ,
        Tau.rename_subst d g.ext σ.lift, PathSubst.lift_pre_rename]
  | .Single p => by simp only [Ty.rename, Ty.subst, Path.rename_subst]
  | .TSel p A => by simp only [Ty.rename, Ty.subst, Path.rename_subst]

theorem Tau.rename_subst (d : Tau n k) (g : FinFun n m) (σ : PathSubst m l) :
    (d.rename g).subst σ = d.subst (fun x => σ (g x)) :=
  match d with
  | .ty T => by simp only [Tau.rename, Tau.subst, Ty.rename_subst]
  | .intv S T => by simp only [Tau.rename, Tau.subst, Ty.rename_subst]

end

theorem Path.open_rename (p : Path (n + 1)) (q : Path n) (f : FinFun n m) :
    (p.open q).rename f = (p.rename f.ext).open (q.rename f) := by
  simp only [Path.open, Path.subst_rename, Path.rename_subst]
  rw [PathSubst.openAt_rename]

theorem Ty.open_rename (T : Ty (n + 1)) (p : Path n) (f : FinFun n m) :
    (T.open p).rename f = (T.rename f.ext).open (p.rename f) := by
  simp only [Ty.open, Ty.subst_rename, Ty.rename_subst]
  rw [PathSubst.openAt_rename]

theorem Tau.open_rename (d : Tau (n + 1) k) (p : Path n) (f : FinFun n m) :
    (d.open p).rename f = (d.rename f.ext).open (p.rename f) := by
  simp only [Tau.open, Tau.subst_rename, Tau.rename_subst]
  rw [PathSubst.openAt_rename]

theorem Path.weaken_open (p : Path n) (q : Path n) : p.weaken.open q = p := by
  simp only [Path.weaken, Path.open, Path.rename_subst,
    PathSubst.openAt_weaken, Path.subst_id]

theorem Ty.weaken_open (T : Ty n) (p : Path n) : T.weaken.open p = T := by
  simp only [Ty.weaken, Ty.open, Ty.rename_subst,
    PathSubst.openAt_weaken, Ty.subst_id]

theorem Tau.weaken_open (d : Tau n k) (p : Path n) : d.weaken.open p = d := by
  simp only [Tau.weaken, Tau.open, Tau.rename_subst,
    PathSubst.openAt_weaken, Tau.subst_id]

theorem Tm.open_rename (t : Tm (n + 1)) (x : Fin n) (f : FinFun n m) :
    (t.open x).rename f = (t.rename f.ext).open (f x) := by
  simp only [Tm.open, Tm.rename_rename, FinFun.openAt_comp]

theorem Def.open_rename (d : Def (n + 1) k) (x : Fin n) (f : FinFun n m) :
    (d.open x).rename f = (d.rename f.ext).open (f x) := by
  simp only [Def.open, Def.rename_rename, FinFun.openAt_comp]

theorem Tm.weaken_open (t : Tm n) (x : Fin n) : t.weaken.open x = t := by
  simp only [Tm.weaken, Tm.open, Tm.rename_rename, FinFun.openAt_weaken,
    Tm.rename_id]

theorem Def.weaken_open (d : Def n k) (x : Fin n) : d.weaken.open x = d := by
  simp only [Def.weaken, Def.open, Def.rename_rename, FinFun.openAt_weaken,
    Def.rename_id]

theorem Tm.IsValue.rename {t : Tm n} (hv : Tm.IsValue t) (f : FinFun n m) :
    Tm.IsValue (Tm.rename t f) := by
  cases hv <;> constructor

theorem Tm.IsValue.weaken {t : Tm n} (hv : Tm.IsValue t) : Tm.IsValue t.weaken :=
  hv.rename FinFun.weaken

end LambdaP.Repaired
