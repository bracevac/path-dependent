import LambdaPCC.FinFun

/-!
Intrinsically scoped syntax for `lambda_p` with capture sets and
abstract capture-set members. Function codomains and pair members bind their
first component.

Dependencies, including paths in capture sets, admit substitution of arbitrary
paths. Pair definitions store variables, types, or capture sets, so terms and
definitions support the corresponding variable-only action through renaming.
-/

namespace LambdaPCC

/-- Labels for term, type, and capture-set members. -/
abbrev Name : Type := Nat

/-- The kind of the dependent second component of a pair. -/
inductive Kind : Type where
| term
| «type»
| capture
deriving DecidableEq

/-- Paths are variables, first projections, and named selections. -/
inductive Path : Nat -> Type where
| var : Fin n -> Path n
| fst : Path n -> Path n
| sel : Path n -> Name -> Path n
deriving DecidableEq

mutual

/-- Capture sets contain capability paths and selections of abstract
capture-set members. The two constructors are distinct: `singleton p` is the
capability `{p}`, whereas `select p a` denotes the member `p.a`. -/
inductive CaptureSet : Nat -> Type where
| empty : CaptureSet n
| union : CaptureSet n -> CaptureSet n -> CaptureSet n
| singleton : Path n -> CaptureSet n
| select : Path n -> Name -> CaptureSet n

/-- Capturing types. -/
inductive Ty : Nat -> Type where
| capt : CaptureSet n -> Shape n -> Ty n

/-- Shape types underlying capturing types. -/
inductive Shape : Nat -> Type where
| Top : Shape n
| Bot : Shape n
| Fun : Ty n -> Ty (n + 1) -> Shape n
| Pair : Ty n -> Name -> Tau (n + 1) k -> Shape n
| Single : Path n -> Shape n
/-- Abstract type-member selection `p.A`, distinct from the term singleton `{p}`. -/
| TSel : Path n -> Name -> Shape n

/-- Member signatures used as dependent pair components. -/
inductive Tau : Nat -> Kind -> Type where
| term : Ty n -> Tau n .term
| «type» : Shape n -> Shape n -> Tau n .type
| capture : CaptureSet n -> CaptureSet n -> Tau n .capture

end

/-- The capture set of a capturing type. -/
def Ty.captureSet : Ty n -> CaptureSet n
| .capt captures _ => captures

/-- Definitions stored in pair values. -/
inductive Def : Nat -> Kind -> Type where
| val : Fin n -> Def n .term
| «type» : Shape n -> Def n .type
| capture : CaptureSet n -> Def n .capture

/-- Terms in monadic normal form. -/
inductive Tm : Nat -> Type where
| path : Path n -> Tm n
| abs : Ty n -> Tm (n + 1) -> Tm n
| pair : Fin n -> Name -> Def n k -> Tm n
| app : Path n -> Path n -> Tm n
| «let» : Tm n -> Tm (n + 1) -> Tm n

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

def CaptureSet.rename : CaptureSet n -> FinFun n m -> CaptureSet m
| .empty, _ => .empty
| .union C D, f => .union (C.rename f) (D.rename f)
| .singleton p, f => .singleton (p.rename f)
| .select p a, f => .select (p.rename f) a

def Ty.rename : Ty n -> FinFun n m -> Ty m
| .capt C S, f => .capt (C.rename f) (S.rename f)

def Shape.rename : Shape n -> FinFun n m -> Shape m
| .Top, _ => .Top
| .Bot, _ => .Bot
| .Fun S T, f => .Fun (S.rename f) (T.rename f.ext)
| .Pair S a d, f => .Pair (S.rename f) a (d.rename f.ext)
| .Single p, f => .Single (p.rename f)
| .TSel p A, f => .TSel (p.rename f) A

def Tau.rename : Tau n k -> FinFun n m -> Tau m k
| .term T, f => .term (T.rename f)
| .type S T, f => .type (S.rename f) (T.rename f)
| .capture C D, f => .capture (C.rename f) (D.rename f)

end

def Def.rename : Def n k -> FinFun n m -> Def m k
| .val x, f => .val (f x)
| .type T, f => .type (T.rename f)
| .capture C, f => .capture (C.rename f)

def Tm.rename : Tm n -> FinFun n m -> Tm m
| .path p, f => .path (p.rename f)
| .abs T t, f => .abs (T.rename f) (t.rename f.ext)
| .pair x a d, f => .pair (f x) a (d.rename f)
| .app p q, f => .app (p.rename f) (q.rename f)
| .let t u, f => .let (t.rename f) (u.rename f.ext)

def Path.weaken (p : Path n) : Path (n + 1) := p.rename FinFun.weaken
def CaptureSet.weaken (C : CaptureSet n) : CaptureSet (n + 1) :=
  C.rename FinFun.weaken
def Ty.weaken (T : Ty n) : Ty (n + 1) := T.rename FinFun.weaken
def Shape.weaken (S : Shape n) : Shape (n + 1) := S.rename FinFun.weaken
def Tau.weaken (d : Tau n k) : Tau (n + 1) k := d.rename FinFun.weaken
def Def.weaken (d : Def n k) : Def (n + 1) k := d.rename FinFun.weaken
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

def CaptureSet.subst : CaptureSet n -> PathSubst n m -> CaptureSet m
| .empty, _ => .empty
| .union C D, σ => .union (C.subst σ) (D.subst σ)
| .singleton p, σ => .singleton (p.subst σ)
| .select p a, σ => .select (p.subst σ) a

/-- Capture-avoiding simultaneous path substitution in types. -/
def Ty.subst : Ty n -> PathSubst n m -> Ty m
| .capt C S, σ => .capt (C.subst σ) (S.subst σ)

def Shape.subst : Shape n -> PathSubst n m -> Shape m
| .Top, _ => .Top
| .Bot, _ => .Bot
| .Fun S T, σ => .Fun (S.subst σ) (T.subst σ.lift)
| .Pair S a d, σ => .Pair (S.subst σ) a (d.subst σ.lift)
| .Single p, σ => .Single (p.subst σ)
| .TSel p A, σ => .TSel (p.subst σ) A

/-- Capture-avoiding simultaneous path substitution in generalized types. -/
def Tau.subst : Tau n k -> PathSubst n m -> Tau m k
| .term T, σ => .term (T.subst σ)
| .type S T, σ => .type (S.subst σ) (T.subst σ)
| .capture C D, σ => .capture (C.subst σ) (D.subst σ)

end

/-- Replace the newest bound variable in a path by an arbitrary path. -/
def Path.open (q : Path (n + 1)) (p : Path n) : Path n :=
  q.subst (PathSubst.openAt p)

/-- Capture-avoiding replacement of the newest bound variable in a capture set. -/
def CaptureSet.open (C : CaptureSet (n + 1)) (p : Path n) : CaptureSet n :=
  C.subst (PathSubst.openAt p)

/-- Capture-avoiding replacement of the newest bound variable in a type. -/
def Ty.open (T : Ty (n + 1)) (p : Path n) : Ty n :=
  T.subst (PathSubst.openAt p)

/-- Capture-avoiding replacement of the newest bound variable in a shape. -/
def Shape.open (S : Shape (n + 1)) (p : Path n) : Shape n :=
  S.subst (PathSubst.openAt p)

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

theorem CaptureSet.rename_id (C : CaptureSet n) : C.rename FinFun.id = C :=
  match C with
  | .empty => rfl
  | .union C D => by
      simp only [CaptureSet.rename, CaptureSet.rename_id C, CaptureSet.rename_id D]
  | .singleton p => by simp only [CaptureSet.rename, Path.rename_id]
  | .select p a => by simp only [CaptureSet.rename, Path.rename_id]

theorem Ty.rename_id (T : Ty n) : T.rename FinFun.id = T :=
  match T with
  | .capt C S => by
      simp only [Ty.rename, CaptureSet.rename_id C, Shape.rename_id S]

theorem Shape.rename_id (S : Shape n) : S.rename FinFun.id = S :=
  match S with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Shape.rename, FinFun.ext_id, Ty.rename_id S, Ty.rename_id T]
  | .Pair S a d => by
      simp only [Shape.rename, FinFun.ext_id, Ty.rename_id S, Tau.rename_id d]
  | .Single p => by simp only [Shape.rename, Path.rename_id]
  | .TSel p A => by simp only [Shape.rename, Path.rename_id]

theorem Tau.rename_id (d : Tau n k) : d.rename FinFun.id = d :=
  match d with
  | .term T => by simp only [Tau.rename, Ty.rename_id]
  | .type S T => by simp only [Tau.rename, Shape.rename_id]
  | .capture C D => by simp only [Tau.rename, CaptureSet.rename_id]

end


theorem Def.rename_id (d : Def n k) : d.rename FinFun.id = d :=
  match d with
  | .val x => by simp only [Def.rename, FinFun.id_apply]
  | .type T => by simp only [Def.rename, Shape.rename_id]
  | .capture C => by simp only [Def.rename, CaptureSet.rename_id]

theorem Tm.rename_id (t : Tm n) : t.rename FinFun.id = t :=
  match t with
  | .path p => by simp only [Tm.rename, Path.rename_id]
  | .abs T t => by
      simp only [Tm.rename, FinFun.ext_id, Ty.rename_id, Tm.rename_id]
  | .pair x a d => by simp only [Tm.rename, FinFun.id_apply, Def.rename_id]
  | .app p q => by simp only [Tm.rename, Path.rename_id]
  | .let t u => by
      simp only [Tm.rename, FinFun.ext_id, Tm.rename_id]

mutual

theorem CaptureSet.rename_rename (C : CaptureSet n)
    (f : FinFun n m) (g : FinFun m l) :
    (C.rename f).rename g = C.rename (f.comp g) :=
  match C with
  | .empty => rfl
  | .union C D => by
      simp only [CaptureSet.rename, CaptureSet.rename_rename C f g,
        CaptureSet.rename_rename D f g]
  | .singleton p => by simp only [CaptureSet.rename, Path.rename_rename]
  | .select p a => by simp only [CaptureSet.rename, Path.rename_rename]

theorem Ty.rename_rename (T : Ty n) (f : FinFun n m) (g : FinFun m l) :
    (T.rename f).rename g = T.rename (f.comp g) :=
  match T with
  | .capt C S => by
      simp only [Ty.rename, CaptureSet.rename_rename C f g,
        Shape.rename_rename S f g]

theorem Shape.rename_rename (S : Shape n) (f : FinFun n m) (g : FinFun m l) :
    (S.rename f).rename g = S.rename (f.comp g) :=
  match S with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Shape.rename, Ty.rename_rename S f g,
        Ty.rename_rename T f.ext g.ext, FinFun.ext_comp]
  | .Pair S a d => by
      simp only [Shape.rename, Ty.rename_rename S f g,
        Tau.rename_rename d f.ext g.ext, FinFun.ext_comp]
  | .Single p => by simp only [Shape.rename, Path.rename_rename]
  | .TSel p A => by simp only [Shape.rename, Path.rename_rename]

theorem Tau.rename_rename (d : Tau n k) (f : FinFun n m) (g : FinFun m l) :
    (d.rename f).rename g = d.rename (f.comp g) :=
  match d with
  | .term T => by simp only [Tau.rename, Ty.rename_rename]
  | .type S T => by simp only [Tau.rename, Shape.rename_rename]
  | .capture C D => by simp only [Tau.rename, CaptureSet.rename_rename]

end


theorem Def.rename_rename (d : Def n k) (f : FinFun n m) (g : FinFun m l) :
    (d.rename f).rename g = d.rename (f.comp g) :=
  match d with
  | .val x => rfl
  | .type T => by simp only [Def.rename, Shape.rename_rename]
  | .capture C => by simp only [Def.rename, CaptureSet.rename_rename]

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

theorem Path.weaken_rename (p : Path n) (f : FinFun n m) :
    (p.rename f).weaken = p.weaken.rename f.ext := by
  simp only [Path.weaken, Path.rename_rename, FinFun.comp_weaken]

theorem CaptureSet.weaken_rename (C : CaptureSet n) (f : FinFun n m) :
    (C.rename f).weaken = C.weaken.rename f.ext := by
  simp only [CaptureSet.weaken, CaptureSet.rename_rename, FinFun.comp_weaken]

theorem Ty.weaken_rename (T : Ty n) (f : FinFun n m) :
    (T.rename f).weaken = T.weaken.rename f.ext := by
  simp only [Ty.weaken, Ty.rename_rename, FinFun.comp_weaken]

theorem Shape.weaken_rename (S : Shape n) (f : FinFun n m) :
    (S.rename f).weaken = S.weaken.rename f.ext := by
  simp only [Shape.weaken, Shape.rename_rename, FinFun.comp_weaken]

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

theorem CaptureSet.subst_id (C : CaptureSet n) : C.subst PathSubst.id = C :=
  match C with
  | .empty => rfl
  | .union C D => by
      simp only [CaptureSet.subst, CaptureSet.subst_id C, CaptureSet.subst_id D]
  | .singleton p => by simp only [CaptureSet.subst, Path.subst_id]
  | .select p a => by simp only [CaptureSet.subst, Path.subst_id]

theorem Ty.subst_id (T : Ty n) : T.subst PathSubst.id = T :=
  match T with
  | .capt C S => by
      simp only [Ty.subst, CaptureSet.subst_id C, Shape.subst_id S]

theorem Shape.subst_id (S : Shape n) : S.subst PathSubst.id = S :=
  match S with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Shape.subst, PathSubst.lift_id, Ty.subst_id S, Ty.subst_id T]
  | .Pair S a d => by
      simp only [Shape.subst, PathSubst.lift_id, Ty.subst_id S, Tau.subst_id d]
  | .Single p => by simp only [Shape.subst, Path.subst_id]
  | .TSel p A => by simp only [Shape.subst, Path.subst_id]

theorem Tau.subst_id (d : Tau n k) : d.subst PathSubst.id = d :=
  match d with
  | .term T => by simp only [Tau.subst, Ty.subst_id]
  | .type S T => by simp only [Tau.subst, Shape.subst_id]
  | .capture C D => by simp only [Tau.subst, CaptureSet.subst_id]

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

theorem CaptureSet.subst_asSubst (C : CaptureSet n) (f : FinFun n m) :
    C.subst f.asSubst = C.rename f :=
  match C with
  | .empty => rfl
  | .union C D => by
      simp only [CaptureSet.subst, CaptureSet.rename,
        CaptureSet.subst_asSubst C f, CaptureSet.subst_asSubst D f]
  | .singleton p => by
      simp only [CaptureSet.subst, CaptureSet.rename, Path.subst_asSubst]
  | .select p a => by
      simp only [CaptureSet.subst, CaptureSet.rename, Path.subst_asSubst]

theorem Ty.subst_asSubst (T : Ty n) (f : FinFun n m) :
    T.subst f.asSubst = T.rename f :=
  match T with
  | .capt C S => by
      simp only [Ty.subst, Ty.rename, CaptureSet.subst_asSubst C f,
        Shape.subst_asSubst S f]

theorem Shape.subst_asSubst (S : Shape n) (f : FinFun n m) :
    S.subst f.asSubst = S.rename f :=
  match S with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Shape.subst, Shape.rename, Ty.subst_asSubst S f,
        ← FinFun.asSubst_ext, Ty.subst_asSubst T f.ext]
  | .Pair S a d => by
      simp only [Shape.subst, Shape.rename, Ty.subst_asSubst S f,
        ← FinFun.asSubst_ext, Tau.subst_asSubst d f.ext]
  | .Single p => by simp only [Shape.subst, Shape.rename, Path.subst_asSubst]
  | .TSel p A => by simp only [Shape.subst, Shape.rename, Path.subst_asSubst]

theorem Tau.subst_asSubst (d : Tau n k) (f : FinFun n m) :
    d.subst f.asSubst = d.rename f :=
  match d with
  | .term T => by simp only [Tau.subst, Tau.rename, Ty.subst_asSubst]
  | .type S T => by simp only [Tau.subst, Tau.rename, Shape.subst_asSubst]
  | .capture C D => by
      simp only [Tau.subst, Tau.rename, CaptureSet.subst_asSubst]

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

theorem CaptureSet.subst_comp (C : CaptureSet n) (σ : PathSubst n m)
    (θ : PathSubst m l) :
    (C.subst σ).subst θ = C.subst (σ.comp θ) :=
  match C with
  | .empty => rfl
  | .union C D => by
      simp only [CaptureSet.subst, CaptureSet.subst_comp C σ θ,
        CaptureSet.subst_comp D σ θ]
  | .singleton p => by simp only [CaptureSet.subst, Path.subst_comp]
  | .select p a => by simp only [CaptureSet.subst, Path.subst_comp]

theorem Ty.subst_comp (T : Ty n) (σ : PathSubst n m)
    (θ : PathSubst m l) :
    (T.subst σ).subst θ = T.subst (σ.comp θ) :=
  match T with
  | .capt C S => by
      simp only [Ty.subst, CaptureSet.subst_comp C σ θ,
        Shape.subst_comp S σ θ]

theorem Shape.subst_comp (S : Shape n) (σ : PathSubst n m)
    (θ : PathSubst m l) :
    (S.subst σ).subst θ = S.subst (σ.comp θ) :=
  match S with
  | .Top => rfl
  | .Bot => rfl
  | .Fun S T => by
      simp only [Shape.subst, Ty.subst_comp S σ θ,
        Ty.subst_comp T σ.lift θ.lift, PathSubst.comp_lift]
  | .Pair S a d => by
      simp only [Shape.subst, Ty.subst_comp S σ θ,
        Tau.subst_comp d σ.lift θ.lift, PathSubst.comp_lift]
  | .Single p => by simp only [Shape.subst, Path.subst_comp]
  | .TSel p A => by simp only [Shape.subst, Path.subst_comp]

theorem Tau.subst_comp (d : Tau n k) (σ : PathSubst n m)
    (θ : PathSubst m l) :
    (d.subst σ).subst θ = d.subst (σ.comp θ) :=
  match d with
  | .term T => by simp only [Tau.subst, Ty.subst_comp]
  | .type S T => by simp only [Tau.subst, Shape.subst_comp]
  | .capture C D => by simp only [Tau.subst, CaptureSet.subst_comp]

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

theorem CaptureSet.open_subst (C : CaptureSet (n + 1)) (p : Path n)
    (σ : PathSubst n m) :
    (C.open p).subst σ = (C.subst σ.lift).open (p.subst σ) := by
  unfold CaptureSet.open
  rw [CaptureSet.subst_comp, CaptureSet.subst_comp, PathSubst.openAt_comp]

theorem Ty.open_subst (T : Ty (n + 1)) (p : Path n)
    (σ : PathSubst n m) :
    (T.open p).subst σ = (T.subst σ.lift).open (p.subst σ) := by
  unfold Ty.open
  rw [Ty.subst_comp, Ty.subst_comp, PathSubst.openAt_comp]

theorem Shape.open_subst (S : Shape (n + 1)) (p : Path n)
    (σ : PathSubst n m) :
    (S.open p).subst σ = (S.subst σ.lift).open (p.subst σ) := by
  unfold Shape.open
  rw [Shape.subst_comp, Shape.subst_comp, PathSubst.openAt_comp]

theorem CaptureSet.rename_openAt_eq_open_var (C : CaptureSet (n + 1))
    (x : Fin n) :
    C.rename (FinFun.openAt x) = C.open (.var x) := by
  rw [← CaptureSet.subst_asSubst, FinFun.openAt_asSubst]
  rfl

theorem Ty.rename_openAt_eq_open_var (T : Ty (n + 1)) (x : Fin n) :
    T.rename (FinFun.openAt x) = T.open (.var x) := by
  rw [← Ty.subst_asSubst, FinFun.openAt_asSubst]
  rfl

theorem Shape.rename_openAt_eq_open_var (S : Shape (n + 1)) (x : Fin n) :
    S.rename (FinFun.openAt x) = S.open (.var x) := by
  rw [← Shape.subst_asSubst, FinFun.openAt_asSubst]
  rfl

theorem Tau.rename_openAt_eq_open_var (d : Tau (n + 1) k) (x : Fin n) :
    d.rename (FinFun.openAt x) = d.open (.var x) := by
  rw [← Tau.subst_asSubst, FinFun.openAt_asSubst]
  rfl

theorem Path.open_rename (p : Path (n + 1)) (q : Path n) (f : FinFun n m) :
    (p.open q).rename f = (p.rename f.ext).open (q.rename f) := by
  simp only [Path.open, ← Path.subst_asSubst, Path.subst_comp,
    PathSubst.openAt_rename]

theorem CaptureSet.open_rename (C : CaptureSet (n + 1))
    (p : Path n) (f : FinFun n m) :
    (C.open p).rename f = (C.rename f.ext).open (p.rename f) := by
  simp only [CaptureSet.open, ← CaptureSet.subst_asSubst,
    CaptureSet.subst_comp, PathSubst.openAt_rename]

theorem Ty.open_rename (T : Ty (n + 1)) (p : Path n) (f : FinFun n m) :
    (T.open p).rename f = (T.rename f.ext).open (p.rename f) := by
  simp only [Ty.open, ← Ty.subst_asSubst, Ty.subst_comp,
    PathSubst.openAt_rename]

theorem Shape.open_rename (S : Shape (n + 1)) (p : Path n) (f : FinFun n m) :
    (S.open p).rename f = (S.rename f.ext).open (p.rename f) := by
  simp only [Shape.open, ← Shape.subst_asSubst, Shape.subst_comp,
    PathSubst.openAt_rename]

theorem Tau.open_rename (d : Tau (n + 1) k) (p : Path n) (f : FinFun n m) :
    (d.open p).rename f = (d.rename f.ext).open (p.rename f) := by
  simp only [Tau.open, ← Tau.subst_asSubst, Tau.subst_comp,
    PathSubst.openAt_rename]

theorem Path.weaken_open (p : Path n) (q : Path n) : p.weaken.open q = p := by
  simp only [Path.weaken, Path.open, ← Path.subst_asSubst, Path.subst_comp,
    PathSubst.openAt_weaken, Path.subst_id]

theorem CaptureSet.weaken_open (C : CaptureSet n) (p : Path n) :
    C.weaken.open p = C := by
  simp only [CaptureSet.weaken, CaptureSet.open, ← CaptureSet.subst_asSubst,
    CaptureSet.subst_comp, PathSubst.openAt_weaken, CaptureSet.subst_id]

theorem Ty.weaken_open (T : Ty n) (p : Path n) : T.weaken.open p = T := by
  simp only [Ty.weaken, Ty.open, ← Ty.subst_asSubst, Ty.subst_comp,
    PathSubst.openAt_weaken, Ty.subst_id]

theorem Shape.weaken_open (S : Shape n) (p : Path n) : S.weaken.open p = S := by
  simp only [Shape.weaken, Shape.open, ← Shape.subst_asSubst,
    Shape.subst_comp, PathSubst.openAt_weaken, Shape.subst_id]

theorem Tau.weaken_open (d : Tau n k) (p : Path n) : d.weaken.open p = d := by
  simp only [Tau.weaken, Tau.open, ← Tau.subst_asSubst, Tau.subst_comp,
    PathSubst.openAt_weaken, Tau.subst_id]

end LambdaPCC
