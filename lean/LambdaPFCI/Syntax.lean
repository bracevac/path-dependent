import LambdaPFCI.FinFun

/-!
Intrinsically scoped syntax for `lambda_p`.  Term singleton types and
abstract type selections are distinct constructors.  Function codomains and
pair members bind their first component.

Dependencies admit substitution of arbitrary paths.  Pair definitions store
variables, so terms and definitions support the corresponding variable-only
action through renaming; their one-binder opening operations reflect this
restriction.
-/

namespace LambdaPFCI

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

/-- Types. -/
inductive Ty : Nat -> Type where
| Top : Ty n
| Bot : Ty n
| Fun : Ty n -> Ty (n + 1) -> Ty n
| Pair : Ty n -> Name -> Tau (n + 1) k -> Ty n
| Inter : Ty n -> Ty n -> Ty n
| Union : Ty n -> Ty n -> Ty n
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

end

/-- Syntactic variables, used by the path-resolution transition. -/
inductive Path.IsVar : Path n -> Prop where
| var : IsVar (.var x)

/-- Values of the MNF calculus. -/
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
| .Inter S T, f => .Inter (S.rename f) (T.rename f)
| .Union S T, f => .Union (S.rename f) (T.rename f)
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

def Def.rename : Def n k -> FinFun n m -> Def m k
| .val x, f => .val (f x)
| .type T, f => .type (T.rename f)

end

def Path.weaken (p : Path n) : Path (n + 1) := p.rename FinFun.weaken
def Ty.weaken (T : Ty n) : Ty (n + 1) := T.rename FinFun.weaken
def Tau.weaken (d : Tau n k) : Tau (n + 1) k := d.rename FinFun.weaken
def Tm.weaken (t : Tm n) : Tm (n + 1) := t.rename FinFun.weaken

/-! ## Path substitution and opening -/

/-- A simultaneous substitution of paths for variables. -/
abbrev PathSubst (n m : Nat) : Type := Fin n -> Path m

/-- Regard a variable renaming as a path substitution. -/
def FinFun.asSubst (f : FinFun n m) : PathSubst n m :=
  fun x => .var (f x)

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

namespace PathSubst

/-- Composition of path substitutions, in diagrammatic order. -/
def comp (σ : PathSubst n m) (θ : PathSubst m l) : PathSubst n l :=
  fun x => (σ x).subst θ

end PathSubst

mutual

/-- Capture-avoiding simultaneous path substitution in types. -/
def Ty.subst : Ty n -> PathSubst n m -> Ty m
| .Top, _ => .Top
| .Bot, _ => .Bot
| .Fun S T, σ => .Fun (S.subst σ) (T.subst σ.lift)
| .Pair S a d, σ => .Pair (S.subst σ) a (d.subst σ.lift)
| .Inter S T, σ => .Inter (S.subst σ) (T.subst σ)
| .Union S T, σ => .Union (S.subst σ) (T.subst σ)
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

/-! ## Algebra of renaming -/

theorem Path.rename_id (p : Path n) : p.rename FinFun.id = p := by
  induction p with
  | var x => rfl
  | fst p ih => simp only [Path.rename, ih]
  | sel p a ih => simp only [Path.rename, ih]

theorem Path.rename_rename (p : Path n) (f : FinFun n m) (g : FinFun m l) :
    (p.rename f).rename g = p.rename (f.comp g) := by
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
  | .Inter S T => by
      simp only [Ty.rename, Ty.rename_id S, Ty.rename_id T]
  | .Union S T => by
      simp only [Ty.rename, Ty.rename_id S, Ty.rename_id T]
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

theorem Def.rename_id (d : Def n k) : d.rename FinFun.id = d :=
  match d with
  | .val x => by simp only [Def.rename, FinFun.id_apply]
  | .type T => by simp only [Def.rename, Ty.rename_id]

end

mutual

theorem Ty.rename_rename (T : Ty n) (f : FinFun n m) (g : FinFun m l) :
    (T.rename f).rename g = T.rename (f.comp g) :=
  match T with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Ty.rename, Ty.rename_rename S f g,
        Ty.rename_rename T f.ext g.ext, FinFun.ext_comp]
  | .Pair S a d => by
      simp only [Ty.rename, Ty.rename_rename S f g,
        Tau.rename_rename d f.ext g.ext, FinFun.ext_comp]
  | .Inter S T => by
      simp only [Ty.rename, Ty.rename_rename S f g, Ty.rename_rename T f g]
  | .Union S T => by
      simp only [Ty.rename, Ty.rename_rename S f g, Ty.rename_rename T f g]
  | .Single p => by simp only [Ty.rename, Path.rename_rename]
  | .TSel p A => by simp only [Ty.rename, Path.rename_rename]

theorem Tau.rename_rename (d : Tau n k) (f : FinFun n m) (g : FinFun m l) :
    (d.rename f).rename g = d.rename (f.comp g) :=
  match d with
  | .ty T => by simp only [Tau.rename, Ty.rename_rename]
  | .intv S T => by simp only [Tau.rename, Ty.rename_rename]

theorem Tm.rename_rename (t : Tm n) (f : FinFun n m) (g : FinFun m l) :
    (t.rename f).rename g = t.rename (f.comp g) :=
  match t with
  | .path p => by simp only [Tm.rename, Path.rename_rename]
  | .abs T t => by
      simp only [Tm.rename, Ty.rename_rename, Tm.rename_rename,
        FinFun.ext_comp]
  | .pair x a d => by
      simp only [Tm.rename, Def.rename_rename]
      rfl
  | .app p q => by simp only [Tm.rename, Path.rename_rename]
  | .let t u => by
      simp only [Tm.rename, Tm.rename_rename, FinFun.ext_comp]

theorem Def.rename_rename (d : Def n k) (f : FinFun n m) (g : FinFun m l) :
    (d.rename f).rename g = d.rename (f.comp g) :=
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

/-! ## Algebra of path substitution and opening -/

namespace PathSubst

@[simp] theorem lift_zero (σ : PathSubst n m) : σ.lift 0 = .var 0 := rfl

@[simp] theorem lift_succ (σ : PathSubst n m) (x : Fin n) :
    σ.lift x.succ = (σ x).weaken := rfl

@[simp] theorem openAt_zero (p : Path n) : openAt p 0 = p := rfl

@[simp] theorem openAt_succ (p : Path n) (x : Fin n) :
    openAt p x.succ = .var x := rfl

@[simp] theorem comp_apply (σ : PathSubst n m) (θ : PathSubst m l)
    (x : Fin n) : σ.comp θ x = (σ x).subst θ := rfl

theorem lift_id : (id (n := n)).lift = id := by
  funext x
  refine Fin.cases ?_ (fun i => ?_) x <;> rfl

end PathSubst

theorem Path.subst_id (p : Path n) : p.subst PathSubst.id = p := by
  induction p with
  | var x => rfl
  | fst p ih => simp only [Path.subst, ih]
  | sel p a ih => simp only [Path.subst, ih]

mutual

theorem Ty.subst_id (T : Ty n) : T.subst PathSubst.id = T :=
  match T with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Ty.subst, PathSubst.lift_id, Ty.subst_id S, Ty.subst_id T]
  | .Pair S a d => by
      simp only [Ty.subst, PathSubst.lift_id, Ty.subst_id S, Tau.subst_id d]
  | .Inter S T => by
      simp only [Ty.subst, Ty.subst_id S, Ty.subst_id T]
  | .Union S T => by
      simp only [Ty.subst, Ty.subst_id S, Ty.subst_id T]
  | .Single p => by simp only [Ty.subst, Path.subst_id]
  | .TSel p A => by simp only [Ty.subst, Path.subst_id]

theorem Tau.subst_id (d : Tau n k) : d.subst PathSubst.id = d :=
  match d with
  | .ty T => by simp only [Tau.subst, Ty.subst_id]
  | .intv S T => by simp only [Tau.subst, Ty.subst_id]

end

/-! ### Composition and renamings as substitutions -/

namespace FinFun

@[simp] theorem asSubst_apply (f : FinFun n m) (x : Fin n) :
    f.asSubst x = .var (f x) := rfl

theorem asSubst_ext (f : FinFun n m) :
    f.ext.asSubst = f.asSubst.lift := by
  funext x
  refine Fin.cases ?_ (fun i => ?_) x <;> rfl

theorem openAt_asSubst (x : Fin n) :
    (openAt x).asSubst = PathSubst.openAt (.var x) := by
  funext y
  refine Fin.cases ?_ (fun i => ?_) y <;> rfl

end FinFun

theorem Path.subst_asSubst (p : Path n) (f : FinFun n m) :
    p.subst f.asSubst = p.rename f := by
  induction p with
  | var x => rfl
  | fst p ih => simp only [Path.subst, Path.rename, ih]
  | sel p a ih => simp only [Path.subst, Path.rename, ih]

mutual

theorem Ty.subst_asSubst (T : Ty n) (f : FinFun n m) :
    T.subst f.asSubst = T.rename f :=
  match T with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Ty.subst, Ty.rename, Ty.subst_asSubst S f,
        ← FinFun.asSubst_ext, Ty.subst_asSubst T f.ext]
  | .Pair S a d => by
      simp only [Ty.subst, Ty.rename, Ty.subst_asSubst S f,
        ← FinFun.asSubst_ext, Tau.subst_asSubst d f.ext]
  | .Inter S T => by
      simp only [Ty.subst, Ty.rename, Ty.subst_asSubst S f,
        Ty.subst_asSubst T f]
  | .Union S T => by
      simp only [Ty.subst, Ty.rename, Ty.subst_asSubst S f,
        Ty.subst_asSubst T f]
  | .Single p => by simp only [Ty.subst, Ty.rename, Path.subst_asSubst]
  | .TSel p A => by simp only [Ty.subst, Ty.rename, Path.subst_asSubst]

theorem Tau.subst_asSubst (d : Tau n k) (f : FinFun n m) :
    d.subst f.asSubst = d.rename f :=
  match d with
  | .ty T => by simp only [Tau.subst, Tau.rename, Ty.subst_asSubst]
  | .intv S T => by simp only [Tau.subst, Tau.rename, Ty.subst_asSubst]

end

/-- Opening is natural with respect to a subsequent renaming. -/
theorem PathSubst.openAt_rename (p : Path n) (f : FinFun n m) :
    (openAt p).comp f.asSubst =
      f.ext.asSubst.comp (openAt (p.rename f)) := by
  funext x
  refine Fin.cases ?_ (fun i => ?_) x
  · exact Path.subst_asSubst p f
  · rfl

/-- The opening substitution cancels weakening. -/
theorem PathSubst.openAt_weaken (p : Path n) :
    FinFun.weaken.asSubst.comp (openAt p) = id := by
  funext x
  rfl

/-- Weakening commutes with a lifted path substitution. -/
theorem Path.weaken_subst_lift (p : Path n) (σ : PathSubst n m) :
    p.weaken.subst σ.lift = (p.subst σ).weaken := by
  induction p with
  | var x => rfl
  | fst p ih => exact congrArg Path.fst ih
  | sel p a ih => exact congrArg (Path.sel · a) ih

namespace PathSubst

/-- Composition of path substitutions commutes with lifting. -/
theorem comp_lift (σ : PathSubst n m) (θ : PathSubst m l) :
    (σ.comp θ).lift = σ.lift.comp θ.lift := by
  funext x
  refine Fin.cases ?_ (fun i => ?_) x
  · rfl
  · exact (Path.weaken_subst_lift (σ i) θ).symm

end PathSubst

theorem Path.subst_comp (p : Path n) (σ : PathSubst n m)
    (θ : PathSubst m l) :
    (p.subst σ).subst θ = p.subst (σ.comp θ) := by
  induction p with
  | var x => rfl
  | fst p ih => simp only [Path.subst, ih]
  | sel p a ih => simp only [Path.subst, ih]

mutual

theorem Ty.subst_comp (T : Ty n) (σ : PathSubst n m)
    (θ : PathSubst m l) :
    (T.subst σ).subst θ = T.subst (σ.comp θ) :=
  match T with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Ty.subst, Ty.subst_comp S σ θ,
        Ty.subst_comp T σ.lift θ.lift, PathSubst.comp_lift]
  | .Pair S a d => by
      simp only [Ty.subst, Ty.subst_comp S σ θ,
        Tau.subst_comp d σ.lift θ.lift, PathSubst.comp_lift]
  | .Inter S T => by
      simp only [Ty.subst, Ty.subst_comp S σ θ, Ty.subst_comp T σ θ]
  | .Union S T => by
      simp only [Ty.subst, Ty.subst_comp S σ θ, Ty.subst_comp T σ θ]
  | .Single p => by simp only [Ty.subst, Path.subst_comp]
  | .TSel p A => by simp only [Ty.subst, Path.subst_comp]

theorem Tau.subst_comp (d : Tau n k) (σ : PathSubst n m)
    (θ : PathSubst m l) :
    (d.subst σ).subst θ = d.subst (σ.comp θ) :=
  match d with
  | .ty T => by simp only [Tau.subst, Ty.subst_comp]
  | .intv S T => by simp only [Tau.subst, Ty.subst_comp]

end

/-- The two ways of composing a one-binder opening with a simultaneous
substitution agree. -/
theorem PathSubst.openAt_comp (p : Path n) (σ : PathSubst n m) :
    (PathSubst.openAt p).comp σ =
      σ.lift.comp (PathSubst.openAt (p.subst σ)) := by
  funext x
  refine Fin.cases ?_ (fun y => ?_) x
  · rfl
  · change σ y = (σ y).weaken.open (p.subst σ)
    simp only [Path.weaken, Path.open, ← Path.subst_asSubst, Path.subst_comp,
      PathSubst.openAt_weaken, Path.subst_id]

theorem Tau.open_subst (d : Tau (n + 1) k) (p : Path n)
    (σ : PathSubst n m) :
    (d.open p).subst σ = (d.subst σ.lift).open (p.subst σ) := by
  unfold Tau.open
  rw [Tau.subst_comp, Tau.subst_comp, PathSubst.openAt_comp]

theorem Ty.rename_openAt_eq_open_var (T : Ty (n + 1)) (x : Fin n) :
    T.rename (FinFun.openAt x) = T.open (.var x) := by
  rw [← Ty.subst_asSubst, FinFun.openAt_asSubst]
  rfl

theorem Tau.rename_openAt_eq_open_var (d : Tau (n + 1) k) (x : Fin n) :
    d.rename (FinFun.openAt x) = d.open (.var x) := by
  rw [← Tau.subst_asSubst, FinFun.openAt_asSubst]
  rfl

theorem Path.open_rename (p : Path (n + 1)) (q : Path n) (f : FinFun n m) :
    (p.open q).rename f = (p.rename f.ext).open (q.rename f) := by
  simp only [Path.open, ← Path.subst_asSubst, Path.subst_comp,
    PathSubst.openAt_rename]

theorem Ty.open_rename (T : Ty (n + 1)) (p : Path n) (f : FinFun n m) :
    (T.open p).rename f = (T.rename f.ext).open (p.rename f) := by
  simp only [Ty.open, ← Ty.subst_asSubst, Ty.subst_comp,
    PathSubst.openAt_rename]

theorem Tau.open_rename (d : Tau (n + 1) k) (p : Path n) (f : FinFun n m) :
    (d.open p).rename f = (d.rename f.ext).open (p.rename f) := by
  simp only [Tau.open, ← Tau.subst_asSubst, Tau.subst_comp,
    PathSubst.openAt_rename]

theorem Path.weaken_open (p : Path n) (q : Path n) : p.weaken.open q = p := by
  simp only [Path.weaken, Path.open, ← Path.subst_asSubst, Path.subst_comp,
    PathSubst.openAt_weaken, Path.subst_id]

theorem Ty.weaken_open (T : Ty n) (p : Path n) : T.weaken.open p = T := by
  simp only [Ty.weaken, Ty.open, ← Ty.subst_asSubst, Ty.subst_comp,
    PathSubst.openAt_weaken, Ty.subst_id]

theorem Tau.weaken_open (d : Tau n k) (p : Path n) : d.weaken.open p = d := by
  simp only [Tau.weaken, Tau.open, ← Tau.subst_asSubst, Tau.subst_comp,
    PathSubst.openAt_weaken, Tau.subst_id]

end LambdaPFCI
