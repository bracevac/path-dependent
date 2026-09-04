import Coercions.FCdot.Debruijn

/-!
# DOT-MNF syntax

WadlerFest DOT in monadic normal form: `let` right-hand sides are arbitrary
terms, application and selection take variables.  The scoping discipline is
the one of `FCdot.Debruijn`, reused verbatim: signatures, bound variables,
renamings, and the label type are shared with the target so that the
translation of Plan III §8 is the identity on signatures.

`Path` is an inductive with a single constructor.  Every judgment that
mentions a receiver takes a `Path`, so that pDOT (§9) can add `sel` without
restructuring anything here.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Paths -/

/-- Paths.  In this plan a path is a variable. -/
inductive Path : Sig → Type where
  | var : BVar s .var → Path s
deriving DecidableEq

/-- The variable at the root of a path. -/
def Path.root : Path s → BVar s .var
  | .var x => x

def Path.rename : Path s1 → Rename s1 s2 → Path s2
  | .var x, ρ => .var (ρ.var x)

def Path.weaken (p : Path s) : Path (s,,k) := p.rename Rename.succ

/-- Instantiate the innermost binder of a path by a variable. -/
def Path.substVar (p : Path (s,,k)) (y : BVar s k) : Path s := p.rename (Rename.subst y)

@[simp] theorem Path.root_rename (p : Path s1) (ρ : Rename s1 s2) :
    (p.rename ρ).root = ρ.var p.root := by
  cases p <;> rfl

/-! ## Types -/

/-- Types of DOT-MNF. -/
inductive Ty : Sig → Type where
  | top : Ty s
  | bot : Ty s
  /-- Type declaration `{A : S..T}`.  Bad bounds are allowed. -/
  | typ : Label → Ty s → Ty s → Ty s
  /-- Field declaration `{a : T}`. -/
  | fld : Label → Ty s → Ty s
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
  | .sel p A, ρ => .sel (p.rename ρ) A
  | .mu T, ρ => .mu (T.rename ρ.lift)
  | .all S T, ρ => .all (S.rename ρ) (T.rename ρ.lift)
  | .and S T, ρ => .and (S.rename ρ) (T.rename ρ)

def Ty.weaken (T : Ty s) : Ty (s,,k) := T.rename Rename.succ

/-- Instantiate the innermost binder of a type by a variable. -/
def Ty.substVar (T : Ty (s,,k)) (y : BVar s k) : Ty s := T.rename (Rename.subst y)

/-! ## Terms, values, definitions -/

mutual

/-- Terms.  Application and projection take variables (monadic normal form). -/
inductive Tm : Sig → Type where
  | path : Path s → Tm s
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
  | .path p, ρ => .path (p.rename ρ)
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

/-! ## The fragment: declaration shapes, well-formedness, distinctness -/

/-- Declaration-shaped types: the only types that may be intersected. -/
inductive Ty.Decl : {s : Sig} → Ty s → Prop where
  | top : Ty.Decl (.top : Ty s)
  | typ : Ty.Decl (.typ A S T)
  | fld : Ty.Decl (.fld a T)
  | mu : Ty.Decl T → Ty.Decl (.mu T)
  | and : Ty.Decl S → Ty.Decl T → Ty.Decl (.and S T)

/-- Well-formedness.  Structural, except that intersections and recursive
types are restricted to declaration-shaped operands and bodies.  Bounds are
arbitrary: `Wf {A : S..T}` does not ask for `S <: T`. -/
inductive Ty.Wf : {s : Sig} → Ty s → Prop where
  | top : Ty.Wf (.top : Ty s)
  | bot : Ty.Wf (.bot : Ty s)
  | sel : Ty.Wf (.sel p A)
  | typ : Ty.Wf S → Ty.Wf T → Ty.Wf (.typ A S T)
  | fld : Ty.Wf T → Ty.Wf (.fld a T)
  | mu : Ty.Wf T → Ty.Decl T → Ty.Wf (.mu T)
  | all : Ty.Wf S → Ty.Wf T → Ty.Wf (.all S T)
  | and : Ty.Wf S → Ty.Wf T → Ty.Decl S → Ty.Decl T → Ty.Wf (.and S T)

/-- A type is a bare selection on the innermost binder (`x.B` under the self
binder `x`). -/
def Ty.isSelfSel : Ty (s,x) → Bool
  | .sel (.var .here) _ => true
  | _ => false

/-- Guarded definitions: no type member is defined as a bare selection on the
object's own self (`{A = x.B}`), so unfolding a definition always exposes a
different head. -/
inductive Defs.Guarded : {s : Sig} → Defs (s,x) → Prop where
  | typ : T.isSelfSel = false → Defs.Guarded (.typ A T)
  | trm : Defs.Guarded (.trm a t)
  | and : Defs.Guarded d1 → Defs.Guarded d2 → Defs.Guarded (.and d1 d2)

/-- Guarded declaration types: no member's *witness* is a bare selection on
the object's own self.  A type member's witness is its exact type, a field's
witness is its declared type, and the target defines the block name `x.ℓ` to
be that witness; a witness `x.B` would make `x.ℓ` an alias for another name
of the same block, which the target forbids (`FCdot.Witnesses.Guarded`, what
makes `FCdot.Ctx.resolve` terminate).  `Defs.Guarded` covers the type
members, whose witness is the definition itself; fields need this because
their witness comes from the declaration type, not from the definitions.
Plan §12 risk 2, resolved by excluding the unguarded case. -/
def Ty.Guarded : Ty (s,x) → Prop
  | .typ _ S _ => S.isSelfSel = false
  | .fld _ T => T.isSelfSel = false
  | .and S T => Ty.Guarded S ∧ Ty.Guarded T
  | _ => True

/-- The labels of a definition list are pairwise distinct. -/
inductive Defs.Distinct : {s : Sig} → Defs s → Prop where
  | typ : Defs.Distinct (.typ A T)
  | trm : Defs.Distinct (.trm a t)
  | and :
      Defs.Distinct d1 → Defs.Distinct d2 →
      (∀ ℓ, ℓ ∈ d1.labels → ℓ ∉ d2.labels) →
      Defs.Distinct (.and d1 d2)

end DotMNF
