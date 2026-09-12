import Coercions.Paths.FCdot.Debruijn

namespace Paths

/-!
# DOT-MNF syntax

WadlerFest DOT in monadic normal form: `let` right-hand sides are arbitrary
terms, application and selection take variables.  The scoping discipline is
the one of `FCdot.Debruijn`, reused verbatim: signatures, bound variables,
renamings, and the label type are shared with the target so that the
translation of Plan III §8 is the identity on signatures.

A path is a variable followed by field selections.  Types mention paths.
Terms do not: `Tm.path` takes a variable, and a deep path in term position is
written with a `let`, which is monadic normal form.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Paths -/

/-- Paths.  A variable, or a path followed by a field selection. -/
inductive Path : Sig → Type where
  | var : BVar s .var → Path s
  | sel : Path s → Label → Path s
deriving DecidableEq

/-- The variable at the root of a path. -/
def Path.root : Path s → BVar s .var
  | .var x => x
  | .sel p _ => p.root

/-- The number of field steps of a path. -/
def Path.depth : Path s → Nat
  | .var _ => 0
  | .sel p _ => p.depth + 1

def Path.rename : Path s1 → Rename s1 s2 → Path s2
  | .var x, ρ => .var (ρ.var x)
  | .sel p a, ρ => .sel (p.rename ρ) a

def Path.weaken (p : Path s) : Path (s,,k) := p.rename Rename.succ

/-- Instantiate the innermost binder of a path by a variable. -/
def Path.substVar (p : Path (s,,k)) (y : BVar s k) : Path s := p.rename (Rename.subst y)

/-- Instantiate the innermost binder of a path by a path.  The root is
replaced and the field suffix is kept. -/
def Path.substPath : Path (s,x) → Path s → Path s
  | .var .here, q => q
  | .var (.there y), _ => .var y
  | .sel p a, q => .sel (p.substPath q) a

/-- Path substitutions: one path for each variable.  The shape of `Rename`,
with paths in place of variables.  It is what `Ty.subst` carries under a
binder, where a renaming cannot say that the substituted binder is a path. -/
structure PathSubst (s1 s2 : Sig) where
  var : BVar s1 .var → Path s2

namespace PathSubst

/-- The substitution induced by a renaming. -/
def ofRename (ρ : Rename s1 s2) : PathSubst s1 s2 where
  var := fun x => .var (ρ.var x)

/-- Lift under one binder: the new binder maps to itself. -/
def lift (σ : PathSubst s1 s2) : PathSubst (s1,x) (s2,x) where
  var := fun
    | .here => .var .here
    | .there x => (σ.var x).weaken

/-- Substitute the innermost binder by a path, and nothing else. -/
def one (q : Path s) : PathSubst (s,x) s where
  var := fun
    | .here => q
    | .there y => .var y

theorem funext' {σ τ : PathSubst s1 s2} (h : ∀ x, σ.var x = τ.var x) : σ = τ := by
  cases σ; cases τ
  simp only [PathSubst.mk.injEq]
  funext x
  exact h x

@[simp] theorem lift_ofRename (ρ : Rename s1 s2) : (ofRename ρ).lift = ofRename ρ.lift := by
  apply funext'; intro x; cases x <;> rfl

@[simp] theorem one_var (y : BVar s .var) : one (Path.var y) = ofRename (Rename.subst y) := by
  apply funext'; intro x; cases x <;> rfl

end PathSubst

/-- Apply a path substitution to a path. -/
def Path.subst : Path s1 → PathSubst s1 s2 → Path s2
  | .var x, σ => σ.var x
  | .sel p a, σ => .sel (p.subst σ) a

@[simp] theorem Path.subst_one (p : Path (s,x)) (q : Path s) :
    p.subst (PathSubst.one q) = p.substPath q := by
  induction p with
  | var x => cases x <;> rfl
  | sel p a ih => exact congrArg (Path.sel · a) ih

@[simp] theorem Path.subst_ofRename (p : Path s1) (ρ : Rename s1 s2) :
    p.subst (PathSubst.ofRename ρ) = p.rename ρ := by
  induction p with
  | var x => rfl
  | sel p a ih => exact congrArg (Path.sel · a) ih

@[simp] theorem Path.root_rename (p : Path s1) (ρ : Rename s1 s2) :
    (p.rename ρ).root = ρ.var p.root := by
  induction p with
  | var x => rfl
  | sel p a ih => exact ih

@[simp] theorem Path.depth_rename (p : Path s1) (ρ : Rename s1 s2) :
    (p.rename ρ).depth = p.depth := by
  induction p with
  | var x => rfl
  | sel p a ih => exact congrArg (· + 1) ih

/-- Substituting a variable path is the renaming `Path.substVar`. -/
@[simp] theorem Path.substPath_var (p : Path (s,x)) (y : BVar s .var) :
    p.substPath (.var y) = p.substVar y := by
  induction p with
  | var x => cases x <;> rfl
  | sel p a ih => exact congrArg (Path.sel · a) ih

/-! ## Types -/

/-- Types of DOT-MNF. -/
inductive Ty : Sig → Type where
  | top : Ty s
  | bot : Ty s
  /-- Type declaration `{A : S..T}`.  Bad bounds are allowed. -/
  | typ : Label → Ty s → Ty s → Ty s
  /-- Field declaration `{a : T}`, a computation member. -/
  | fld : Label → Ty s → Ty s
  /-- Stable field declaration `{val a : T}`, a member whose body is stable. -/
  | vfld : Label → Ty s → Ty s
  /-- Singleton type `p.type`: the values of `p`. -/
  | sngl : Path s → Ty s
  /-- Type selection `p.A`. -/
  | sel : Path s → Label → Ty s
  /-- Recursive self type `μ(x. T)`. -/
  | mu : Ty (s,x) → Ty s
  /-- Dependent function type `∀(x : S) T`. -/
  | all : Ty s → Ty (s,x) → Ty s
  /-- Intersection `S ∧ T`; restricted to declarations by `Ty.Wf`. -/
  | and : Ty s → Ty s → Ty s
deriving DecidableEq

def Ty.rename : Ty s1 → Rename s1 s2 → Ty s2
  | .top, _ => .top
  | .bot, _ => .bot
  | .typ A S T, ρ => .typ A (S.rename ρ) (T.rename ρ)
  | .fld a T, ρ => .fld a (T.rename ρ)
  | .vfld a T, ρ => .vfld a (T.rename ρ)
  | .sngl p, ρ => .sngl (p.rename ρ)
  | .sel p A, ρ => .sel (p.rename ρ) A
  | .mu T, ρ => .mu (T.rename ρ.lift)
  | .all S T, ρ => .all (S.rename ρ) (T.rename ρ.lift)
  | .and S T, ρ => .and (S.rename ρ) (T.rename ρ)

/-- Apply a path substitution to a type.  The shape of `Ty.rename`. -/
def Ty.subst : Ty s1 → PathSubst s1 s2 → Ty s2
  | .top, _ => .top
  | .bot, _ => .bot
  | .typ A S T, σ => .typ A (S.subst σ) (T.subst σ)
  | .fld a T, σ => .fld a (T.subst σ)
  | .vfld a T, σ => .vfld a (T.subst σ)
  | .sngl p, σ => .sngl (p.subst σ)
  | .sel p A, σ => .sel (p.subst σ) A
  | .mu T, σ => .mu (T.subst σ.lift)
  | .all S T, σ => .all (S.subst σ) (T.subst σ.lift)
  | .and S T, σ => .and (S.subst σ) (T.subst σ)

def Ty.weaken (T : Ty s) : Ty (s,,k) := T.rename Rename.succ

/-- Instantiate the innermost binder of a type by a variable. -/
def Ty.substVar (T : Ty (s,,k)) (y : BVar s k) : Ty s := T.rename (Rename.subst y)

/-- Instantiate the innermost binder of a type by a path.  It is the
parallel substitution `PathSubst.one q`, which reads as `Path.substPath` at
every leaf and lifts under a binder. -/
def Ty.substPath (T : Ty (s,x)) (q : Path s) : Ty s := T.subst (PathSubst.one q)

@[simp] theorem Ty.substPath_top (q : Path s) : (Ty.top (s := s,x)).substPath q = .top := rfl
@[simp] theorem Ty.substPath_bot (q : Path s) : (Ty.bot (s := s,x)).substPath q = .bot := rfl
@[simp] theorem Ty.substPath_typ (A : Label) (S T : Ty (s,x)) (q : Path s) :
    (Ty.typ A S T).substPath q = .typ A (S.substPath q) (T.substPath q) := rfl
@[simp] theorem Ty.substPath_fld (a : Label) (T : Ty (s,x)) (q : Path s) :
    (Ty.fld a T).substPath q = .fld a (T.substPath q) := rfl
@[simp] theorem Ty.substPath_vfld (a : Label) (T : Ty (s,x)) (q : Path s) :
    (Ty.vfld a T).substPath q = .vfld a (T.substPath q) := rfl
@[simp] theorem Ty.substPath_sngl (p : Path (s,x)) (q : Path s) :
    (Ty.sngl p).substPath q = .sngl (p.substPath q) := by
  simp only [Ty.substPath, Ty.subst, Path.subst_one]
@[simp] theorem Ty.substPath_sel (p : Path (s,x)) (A : Label) (q : Path s) :
    (Ty.sel p A).substPath q = .sel (p.substPath q) A := by
  simp only [Ty.substPath, Ty.subst, Path.subst_one]
@[simp] theorem Ty.substPath_and (S T : Ty (s,x)) (q : Path s) :
    (Ty.and S T).substPath q = .and (S.substPath q) (T.substPath q) := rfl

/-- A path substitution built from a renaming acts as that renaming. -/
theorem Ty.subst_ofRename : ∀ {s1 s2 : Sig} (T : Ty s1) (ρ : Rename s1 s2),
    T.subst (PathSubst.ofRename ρ) = T.rename ρ
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | _, _, .typ A S T, ρ => by
      simp only [Ty.subst, Ty.rename, Ty.subst_ofRename S ρ, Ty.subst_ofRename T ρ]
  | _, _, .fld a T, ρ => by simp only [Ty.subst, Ty.rename, Ty.subst_ofRename T ρ]
  | _, _, .vfld a T, ρ => by simp only [Ty.subst, Ty.rename, Ty.subst_ofRename T ρ]
  | _, _, .sngl p, ρ => by simp only [Ty.subst, Ty.rename, Path.subst_ofRename p ρ]
  | _, _, .sel p A, ρ => by simp only [Ty.subst, Ty.rename, Path.subst_ofRename p ρ]
  | _, _, .mu T, ρ => by
      simp only [Ty.subst, Ty.rename, PathSubst.lift_ofRename, Ty.subst_ofRename T ρ.lift]
  | _, _, .all S T, ρ => by
      simp only [Ty.subst, Ty.rename, PathSubst.lift_ofRename,
        Ty.subst_ofRename S ρ, Ty.subst_ofRename T ρ.lift]
  | _, _, .and S T, ρ => by
      simp only [Ty.subst, Ty.rename, Ty.subst_ofRename S ρ, Ty.subst_ofRename T ρ]

/-- Substituting a variable path is the renaming `Ty.substVar`. -/
@[simp] theorem Ty.substPath_var (T : Ty (s,x)) (y : BVar s .var) :
    T.substPath (.var y) = T.substVar y := by
  rw [Ty.substPath, PathSubst.one_var, Ty.subst_ofRename, Ty.substVar]

/-! ## Terms, values, definitions -/

mutual

/-- Terms.  Application, projection and the path term take variables, which
is monadic normal form.  A deep path in term position is written with a
`let`. -/
inductive Tm : Sig → Type where
  | path : BVar s .var → Tm s
  | val : Value s → Tm s
  | app : BVar s .var → BVar s .var → Tm s
  | proj : BVar s .var → Label → Tm s
  | «let» : Tm s → Tm (s,x) → Tm s

/-- Values.  Object literals carry no type annotation. -/
inductive Value : Sig → Type where
  | obj : Defs (s,x) → Value s
  | lam : Ty s → Tm (s,x) → Value s

/-- Definitions of an object literal. -/
inductive Defs : Sig → Type where
  | typ : Label → Ty s → Defs s
  | trm : Label → Tm s → Defs s
  | and : Defs s → Defs s → Defs s

end

deriving instance DecidableEq for Tm, Value, Defs

mutual

def Tm.rename : Tm s1 → Rename s1 s2 → Tm s2
  | .path x, ρ => .path (ρ.var x)
  | .val v, ρ => .val (v.rename ρ)
  | .app x y, ρ => .app (ρ.var x) (ρ.var y)
  | .proj x a, ρ => .proj (ρ.var x) a
  | .let t u, ρ => .let (t.rename ρ) (u.rename ρ.lift)

def Value.rename : Value s1 → Rename s1 s2 → Value s2
  | .obj d, ρ => .obj (d.rename ρ.lift)
  | .lam S t, ρ => .lam (S.rename ρ) (t.rename ρ.lift)

def Defs.rename : Defs s1 → Rename s1 s2 → Defs s2
  | .typ A T, ρ => .typ A (T.rename ρ)
  | .trm a t, ρ => .trm a (t.rename ρ)
  | .and d1 d2, ρ => .and (d1.rename ρ) (d2.rename ρ)

end

def Tm.weaken (t : Tm s) : Tm (s,x) := t.rename Rename.succ
def Value.weaken (v : Value s) : Value (s,x) := v.rename Rename.succ
def Defs.weaken (d : Defs s) : Defs (s,x) := d.rename Rename.succ

/-- Instantiate the innermost binder of a term by a variable. -/
def Tm.substVar (t : Tm (s,x)) (y : BVar s .var) : Tm s := t.rename (Rename.subst y)
def Value.substVar (v : Value (s,x)) (y : BVar s .var) : Value s := v.rename (Rename.subst y)
def Defs.substVar (d : Defs (s,x)) (y : BVar s .var) : Defs s := d.rename (Rename.subst y)

/-! ## Definition lookup -/

/-- The labels defined by a definition list. -/
def Defs.labels : Defs s → List Label
  | .typ A _ => [A]
  | .trm a _ => [a]
  | .and d1 d2 => d1.labels ++ d2.labels

/-- The type member at a label, if any.  The right conjunct shadows. -/
def Defs.lookupTyp : Defs s → Label → Option (Ty s)
  | .typ A T, ℓ => if ℓ = A then some T else none
  | .trm _ _, _ => none
  | .and d1 d2, ℓ => (d2.lookupTyp ℓ).or (d1.lookupTyp ℓ)

/-- The term member at a label, if any.  The right conjunct shadows. -/
def Defs.lookupTrm : Defs s → Label → Option (Tm s)
  | .typ _ _, _ => none
  | .trm a t, ℓ => if ℓ = a then some t else none
  | .and d1 d2, ℓ => (d2.lookupTrm ℓ).or (d1.lookupTrm ℓ)

/-! ## Declaration readers

The abstract view of a declaration reads its members off the type.  Each
reader descends an intersection with the right conjunct winning, which is the
convention of `Defs.lookupTyp` above. -/

/-- The bounds declared for a type member, if any. -/
def Ty.lookupTypDecl : Ty s → Label → Option (Ty s × Ty s)
  | .typ A S T, ℓ => if ℓ = A then some (S, T) else none
  | .and S T, ℓ => (T.lookupTypDecl ℓ).or (S.lookupTypDecl ℓ)
  | .top, _ | .bot, _ | .fld _ _, _ | .vfld _ _, _ | .sngl _, _
  | .sel _ _, _ | .mu _, _ | .all _ _, _ => none

/-- The type declared for a computation member, if any. -/
def Ty.lookupFldDecl : Ty s → Label → Option (Ty s)
  | .fld a T, ℓ => if ℓ = a then some T else none
  | .and S T, ℓ => (T.lookupFldDecl ℓ).or (S.lookupFldDecl ℓ)
  | .top, _ | .bot, _ | .typ _ _ _, _ | .vfld _ _, _ | .sngl _, _
  | .sel _ _, _ | .mu _, _ | .all _ _, _ => none

/-- The type declared for a stable member, if any. -/
def Ty.lookupVfldDecl : Ty s → Label → Option (Ty s)
  | .vfld a T, ℓ => if ℓ = a then some T else none
  | .and S T, ℓ => (T.lookupVfldDecl ℓ).or (S.lookupVfldDecl ℓ)
  | .top, _ | .bot, _ | .typ _ _ _, _ | .fld _ _, _ | .sngl _, _
  | .sel _ _, _ | .mu _, _ | .all _ _, _ => none

/-! ## The fragment: declaration shapes, well-formedness, distinctness -/

/-- Declaration-shaped types: the shapes a `μ` may bind. -/
inductive Ty.Decl : {s : Sig} → Ty s → Prop where
  | top : Ty.Decl (.top : Ty s)
  | typ : Ty.Decl (.typ A S T)
  | fld : Ty.Decl (.fld a T)
  | vfld : Ty.Decl (.vfld a T)
  | sngl : Ty.Decl (.sngl p)
  | mu : Ty.Decl T → Ty.Decl (.mu T)
  | and : Ty.Decl S → Ty.Decl T → Ty.Decl (.and S T)

/-- The decision procedure for `Ty.Decl` (`Ty.isDecl_iff`).  It is what
`Ty.tel` consults on the body of a `μ`, and it makes `Ty.Decl` decidable, so
that a derivation may discharge the premises of `Wf.mu`, `Rec-I` and `Rec-E`
by `decide`. -/
def Ty.isDecl : Ty s → Bool
  | .top => true
  | .typ _ _ _ => true
  | .fld _ _ => true
  | .vfld _ _ => true
  | .sngl _ => true
  | .mu T => T.isDecl
  | .and S T => S.isDecl && T.isDecl
  | .bot => false
  | .sel _ _ => false
  | .all _ _ => false

theorem Ty.isDecl_iff : ∀ {s : Sig} (T : Ty s), T.isDecl = true ↔ Ty.Decl T
  | _, .top => ⟨fun _ => .top, fun _ => rfl⟩
  | _, .typ _ _ _ => ⟨fun _ => .typ, fun _ => rfl⟩
  | _, .fld _ _ => ⟨fun _ => .fld, fun _ => rfl⟩
  | _, .vfld _ _ => ⟨fun _ => .vfld, fun _ => rfl⟩
  | _, .sngl _ => ⟨fun _ => .sngl, fun _ => rfl⟩
  | _, .bot => ⟨fun h => by simp [Ty.isDecl] at h, fun h => by cases h⟩
  | _, .sel _ _ => ⟨fun h => by simp [Ty.isDecl] at h, fun h => by cases h⟩
  | _, .all _ _ => ⟨fun h => by simp [Ty.isDecl] at h, fun h => by cases h⟩
  | _, .mu T =>
      ⟨fun h => .mu ((Ty.isDecl_iff T).mp h), fun h => by
        cases h with | mu h' => exact (Ty.isDecl_iff T).mpr h'⟩
  | _, .and S T =>
      ⟨fun h => by
        rw [Ty.isDecl, Bool.and_eq_true] at h
        exact .and ((Ty.isDecl_iff S).mp h.1) ((Ty.isDecl_iff T).mp h.2),
       fun h => by
        cases h with
        | and hS hT =>
            rw [Ty.isDecl, Bool.and_eq_true]
            exact ⟨(Ty.isDecl_iff S).mpr hS, (Ty.isDecl_iff T).mpr hT⟩⟩

instance Ty.Decl.instDecidable {s : Sig} (T : Ty s) : Decidable (Ty.Decl T) :=
  decidable_of_iff _ (Ty.isDecl_iff T)

/-- Well-formedness.  Structural, except that the body of a recursive type is
restricted to declaration shapes.  Intersections are unrestricted: a
non-declaration operand translates to a self-bound proposition (plan §13
item 9).  Bounds are arbitrary: `Wf {A : S..T}` does not ask for `S <: T`. -/
inductive Ty.Wf : {s : Sig} → Ty s → Prop where
  | top : Ty.Wf (.top : Ty s)
  | bot : Ty.Wf (.bot : Ty s)
  | sel : Ty.Wf (.sel p A)
  | typ : Ty.Wf S → Ty.Wf T → Ty.Wf (.typ A S T)
  | fld : Ty.Wf T → Ty.Wf (.fld a T)
  | vfld : Ty.Wf T → Ty.Wf (.vfld a T)
  | sngl : Ty.Wf (.sngl p)
  | mu : Ty.Wf T → Ty.Decl T → Ty.Wf (.mu T)
  | all : Ty.Wf S → Ty.Wf T → Ty.Wf (.all S T)
  | and : Ty.Wf S → Ty.Wf T → Ty.Wf (.and S T)

/-- The labels of a definition list are pairwise distinct. -/
inductive Defs.Distinct : {s : Sig} → Defs s → Prop where
  | typ : Defs.Distinct (.typ A T)
  | trm : Defs.Distinct (.trm a t)
  | and :
      Defs.Distinct d1 → Defs.Distinct d2 →
      (∀ ℓ, ℓ ∈ d1.labels → ℓ ∉ d2.labels) →
      Defs.Distinct (.and d1 d2)

end DotMNF

end Paths
