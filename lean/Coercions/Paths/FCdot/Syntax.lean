import Coercions.Paths.FCdot.Debruijn

namespace Paths

/-!
# FCdot syntax

Types mention binder blocks `x.ℓ` and nothing else about terms.  Object
types are telescopes of propositions over a self block.  Evidence is a
proof-term language whose endpoints are assigned by typing.  Terms are in
monadic normal form over atoms; an atom is a variable under
erasure-invisible wrappers.
-/

namespace FCdot

/-! ## Paths

A path is a variable under a sequence of field selections.  A type names the
`ℓ`-member of the block of a path, and the base's block names are exactly the
paths of depth zero, so `x ∙ ℓ` reads `.var x ∙ ℓ`. -/

/-- Paths.  A variable, or a path followed by a field selection. -/
inductive Path : Sig → Type where
  | var : BVar s .var → Path s
  | sel : Path s → Label → Path s
deriving DecidableEq

/-- A variable is the path of depth zero.  This is what lets every base
occurrence of `x ∙ ℓ` parse unchanged. -/
instance : Coe (BVar s .var) (Path s) := ⟨Path.var⟩

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

/-- Path substitutions: one path for each term variable.  The shape of
`Rename`, with paths in place of variables.  It is what a type carries under
a binder, where a renaming cannot say that the substituted binder is a
path. -/
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

/-- Post-compose a path substitution with a renaming. -/
def compRename (σ : PathSubst s1 s2) (ρ : Rename s2 s3) : PathSubst s1 s3 where
  var := fun x => (σ.var x).rename ρ

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

/-- Pre-compose a renaming with a path substitution. -/
def Rename.pathComp (ρ : Rename s1 s2) (σ : PathSubst s2 s3) : PathSubst s1 s3 where
  var := fun x => σ.var (ρ.var x)

/-- Apply a path substitution to a path. -/
def Path.subst : Path s1 → PathSubst s1 s2 → Path s2
  | .var x, σ => σ.var x
  | .sel p a, σ => .sel (p.subst σ) a

/-- A path of depth one or more: a field step below a binder. -/
def Path.isSel : Path s → Bool
  | .var _ => false
  | .sel _ _ => true

@[simp] theorem Path.isSel_rename (p : Path s1) (ρ : Rename s1 s2) :
    (p.rename ρ).isSel = p.isSel := by
  cases p <;> rfl

theorem Path.isSel_subst {p : Path s1} (σ : PathSubst s1 s2) (h : p.isSel = true) :
    (p.subst σ).isSel = true := by
  cases p with
  | var x => cases h
  | sel p a => rfl

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

/-! ## Types, propositions, telescopes -/

mutual

inductive Ty : Sig → Type where
  | bot : Ty s
  /-- The `ℓ`-name of the block of a path.  A variable is the path of
      depth zero, so `x ∙ ℓ` reads `.var x ∙ ℓ`. -/
  | sel : Path s → Label → Ty s
  /-- Dependent arrow: the codomain may mention the parameter's block. -/
  | pi : Ty s → Ty (s,x) → Ty s
  /-- Object type: propositions over a self block. -/
  | obj : Telescope (s,x) → Ty s

inductive Proposition : Sig → Type where
  | le : Ty s → Ty s → Proposition s
  | eq : Ty s → Ty s → Proposition s
  | has : Label → Proposition s
  /-- Self-bound: the object itself is included in the type.  By convention
      the type is always a weakened closed type, so a bound never mentions
      the self block. -/
  | bnd : Ty s → Proposition s
  /-- `∋ᵛ ℓ`: the field `ℓ` is present and holds a stable body, so the name
      `self ∙ ℓ` denotes a block.  A field whose body is a computation gets
      `has` and no block. -/
  | hasVal : Label → Proposition s
  /-- `≈ q`: the self block is the block of the path `q`.  Two names that
      denote one object share one block, and this proposition is how the
      sharing is written in a type. -/
  | alias : Path s → Proposition s

/-- Telescope of propositions, oldest first.  Propositions do not bind. -/
inductive Telescope : Sig → Type where
  | nil : Telescope s
  | cons : Telescope s → Proposition s → Telescope s

end

deriving instance DecidableEq for Ty, Proposition, Telescope

/-- The top type is the object type with no propositions: every type is
included in it, and it says nothing about its inhabitants. -/
@[match_pattern] abbrev Ty.top : Ty s := .obj .nil

/-! ### Notation for types

`⊤` (the empty object type `μ .nil`), `⊥`, `p ∙ ℓ` (the `ℓ`-name of the
block of `p`, and `x ∙ ℓ` at a variable), `Π(S) T`, `μ Tel` (object type; the self binder is implicit),
propositions `S ⊑ T`, `S ≐ T`, `∋ ℓ`, `∋ᵛ ℓ`, `≈ q`, and telescopes
`Tel ▹ P`. -/

scoped notation "⊤" => Ty.top
scoped notation "⊥" => Ty.bot
scoped infix:80 " ∙ " => Ty.sel
scoped notation:max "Π(" S ") " T:max => Ty.pi S T
scoped prefix:max "μ " => Ty.obj
scoped infix:70 " ⊑ " => Proposition.le
scoped infix:70 " ≐ " => Proposition.eq
scoped prefix:max "∋ " => Proposition.has
scoped prefix:75 "⊑ " => Proposition.bnd
scoped prefix:max "∋ᵛ " => Proposition.hasVal
scoped prefix:max "≈ " => Proposition.alias
scoped infixl:65 " ▹ " => Telescope.cons

/-- The singleton object type of a path, `μ [≈ q↑]`.  It is the type of a
stable path that names the block of `q`, and of an atom rooted at that
block. -/
def Ty.snglOf (q : Path s) : Ty s := .obj (.nil ▹ ≈ q.weaken)

/-- Length of a telescope. -/
def Telescope.length : Telescope s → Nat
  | .nil => 0
  | .cons Tel _ => Tel.length + 1

/-- `Tel ∋ (i ↦ P)`: the `i`-th proposition of `Tel` (from the oldest) is `P`. -/
inductive Telescope.At : Telescope s → Nat → Proposition s → Prop where
  | here : Telescope.At (Tel ▹ P) Tel.length P
  | there : Telescope.At Tel i P → Telescope.At (Tel ▹ Q) i P

scoped notation:50 Tel:51 " ∋ " "(" i " ↦ " P ")" => Telescope.At Tel i P

/-- Concatenation of telescopes (second appended after the first). -/
def Telescope.append : Telescope s → Telescope s → Telescope s
  | Tel, .nil => Tel
  | Tel, .cons Tel' P => .cons (Tel.append Tel') P

instance : Append (Telescope s) := ⟨Telescope.append⟩

/-- Lookup by index, executable. -/
def Telescope.get? : Telescope s → Nat → Option (Proposition s)
  | .nil, _ => none
  | .cons Tel P, i => if i = Tel.length then some P else Tel.get? i

/-! ## Renaming of types -/

mutual

def Ty.rename : Ty s1 → Rename s1 s2 → Ty s2
  | .bot, _ => .bot
  | .sel p ℓ, ρ => .sel (p.rename ρ) ℓ
  | .pi S T, ρ => .pi (S.rename ρ) (T.rename ρ.lift)
  | .obj Tel, ρ => .obj (Tel.rename ρ.lift)

def Proposition.rename : Proposition s1 → Rename s1 s2 → Proposition s2
  | .le S T, ρ => .le (S.rename ρ) (T.rename ρ)
  | .eq S T, ρ => .eq (S.rename ρ) (T.rename ρ)
  | .has ℓ, _ => .has ℓ
  | .bnd T, ρ => .bnd (T.rename ρ)
  | .hasVal ℓ, _ => .hasVal ℓ
  | .alias q, ρ => .alias (q.rename ρ)

def Telescope.rename : Telescope s1 → Rename s1 s2 → Telescope s2
  | .nil, _ => .nil
  | .cons Tel P, ρ => .cons (Tel.rename ρ) (P.rename ρ)

end

def Ty.weaken (T : Ty s) : Ty (s,,k) := T.rename Rename.succ
def Telescope.weaken (Tel : Telescope s) : Telescope (s,,k) := Tel.rename Rename.succ
def Proposition.weaken (P : Proposition s) : Proposition (s,,k) := P.rename Rename.succ

/-- Instantiate the innermost binder of a type by a variable. -/
def Ty.substVar (T : Ty (s,,k)) (y : BVar s k) : Ty s := T.rename (Rename.subst y)
def Proposition.substVar (P : Proposition (s,,k)) (y : BVar s k) : Proposition s :=
  P.rename (Rename.subst y)
def Telescope.substVar (Tel : Telescope (s,,k)) (y : BVar s k) : Telescope s :=
  Tel.rename (Rename.subst y)

/-! ### Notation for weakening and instantiation

`T↑` weakens under a new binder; `T⟦y⟧` instantiates the innermost binder. -/

scoped postfix:max "↑" => Ty.weaken
scoped postfix:max "↑" => Telescope.weaken
scoped postfix:max "↑" => Proposition.weaken
scoped notation:max T:max "⟦" y "⟧" => Ty.substVar T y
scoped notation:max T:max "⟦" y "⟧" => Telescope.substVar T y
scoped notation:max T:max "⟦" y "⟧" => Proposition.substVar T y

/-! ## Path substitution of types

`Ty.substVar` is a renaming.  Instantiating the self binder by a *path* is a
genuine substitution, so it is carried by `PathSubst`, which lifts under a
binder.  `Ty.substPath_var` bridges the two. -/

mutual

def Ty.subst : Ty s1 → PathSubst s1 s2 → Ty s2
  | .bot, _ => .bot
  | .sel p ℓ, σ => .sel (p.subst σ) ℓ
  | .pi S T, σ => .pi (S.subst σ) (T.subst σ.lift)
  | .obj Tel, σ => .obj (Tel.subst σ.lift)

def Proposition.subst : Proposition s1 → PathSubst s1 s2 → Proposition s2
  | .le S T, σ => .le (S.subst σ) (T.subst σ)
  | .eq S T, σ => .eq (S.subst σ) (T.subst σ)
  | .has ℓ, _ => .has ℓ
  | .bnd T, σ => .bnd (T.subst σ)
  | .hasVal ℓ, _ => .hasVal ℓ
  | .alias q, σ => .alias (q.subst σ)

def Telescope.subst : Telescope s1 → PathSubst s1 s2 → Telescope s2
  | .nil, _ => .nil
  | .cons Tel P, σ => .cons (Tel.subst σ) (P.subst σ)

end

/-- Instantiate the innermost binder of a type by a path. -/
def Ty.substPath (T : Ty (s,x)) (q : Path s) : Ty s := T.subst (PathSubst.one q)

/-- Instantiate the innermost binder of a proposition by a path. -/
def Proposition.substPath (P : Proposition (s,x)) (q : Path s) : Proposition s :=
  P.subst (PathSubst.one q)

/-- Instantiate the innermost binder of a telescope by a path. -/
def Telescope.substPath (Tel : Telescope (s,x)) (q : Path s) : Telescope s :=
  Tel.subst (PathSubst.one q)

@[simp] theorem Ty.substPath_bot (q : Path s) : (Ty.bot (s := s,x)).substPath q = .bot := rfl
@[simp] theorem Ty.substPath_sel (p : Path (s,x)) (ℓ : Label) (q : Path s) :
    (Ty.sel p ℓ).substPath q = .sel (p.substPath q) ℓ := by
  simp only [Ty.substPath, Ty.subst, Path.subst_one]
@[simp] theorem Ty.substPath_pi (S : Ty (s,x)) (T : Ty (s,x,x)) (q : Path s) :
    (Ty.pi S T).substPath q = .pi (S.substPath q) (T.subst (PathSubst.one q).lift) := rfl
@[simp] theorem Ty.substPath_obj (Tel : Telescope (s,x,x)) (q : Path s) :
    (Ty.obj Tel).substPath q = .obj (Tel.subst (PathSubst.one q).lift) := rfl

@[simp] theorem Proposition.substPath_le (S T : Ty (s,x)) (q : Path s) :
    (Proposition.le S T).substPath q = .le (S.substPath q) (T.substPath q) := rfl
@[simp] theorem Proposition.substPath_eq (S T : Ty (s,x)) (q : Path s) :
    (Proposition.eq S T).substPath q = .eq (S.substPath q) (T.substPath q) := rfl
@[simp] theorem Proposition.substPath_has (ℓ : Label) (q : Path s) :
    (Proposition.has (s := s,x) ℓ).substPath q = .has ℓ := rfl
@[simp] theorem Proposition.substPath_bnd (T : Ty (s,x)) (q : Path s) :
    (Proposition.bnd T).substPath q = .bnd (T.substPath q) := rfl
@[simp] theorem Proposition.substPath_hasVal (ℓ : Label) (q : Path s) :
    (Proposition.hasVal (s := s,x) ℓ).substPath q = .hasVal ℓ := rfl
@[simp] theorem Proposition.substPath_alias (p : Path (s,x)) (q : Path s) :
    (Proposition.alias p).substPath q = .alias (p.substPath q) := by
  simp only [Proposition.substPath, Proposition.subst, Path.subst_one]

@[simp] theorem Telescope.substPath_nil (q : Path s) :
    (Telescope.nil (s := s,x)).substPath q = .nil := rfl
@[simp] theorem Telescope.substPath_cons (Tel : Telescope (s,x)) (P : Proposition (s,x))
    (q : Path s) : (Tel ▹ P).substPath q = Tel.substPath q ▹ P.substPath q := rfl

/-! A path substitution built from a renaming acts as that renaming. -/

mutual

theorem Ty.subst_ofRename {s1 s2 : Sig} : ∀ (T : Ty s1) (ρ : Rename s1 s2),
    T.subst (PathSubst.ofRename ρ) = T.rename ρ
  | .bot, _ => rfl
  | .sel p ℓ, ρ => by simp only [Ty.subst, Ty.rename, Path.subst_ofRename p ρ]
  | .pi S T, ρ => by
      simp only [Ty.subst, Ty.rename, PathSubst.lift_ofRename,
        Ty.subst_ofRename S ρ, Ty.subst_ofRename T ρ.lift]
  | .obj Tel, ρ => by
      simp only [Ty.subst, Ty.rename, PathSubst.lift_ofRename,
        Telescope.subst_ofRename Tel ρ.lift]

theorem Proposition.subst_ofRename {s1 s2 : Sig} : ∀ (P : Proposition s1) (ρ : Rename s1 s2),
    P.subst (PathSubst.ofRename ρ) = P.rename ρ
  | .le S T, ρ => by
      simp only [Proposition.subst, Proposition.rename, Ty.subst_ofRename S ρ,
        Ty.subst_ofRename T ρ]
  | .eq S T, ρ => by
      simp only [Proposition.subst, Proposition.rename, Ty.subst_ofRename S ρ,
        Ty.subst_ofRename T ρ]
  | .has ℓ, _ => rfl
  | .bnd T, ρ => by
      simp only [Proposition.subst, Proposition.rename, Ty.subst_ofRename T ρ]
  | .hasVal ℓ, _ => rfl
  | .alias q, ρ => by
      simp only [Proposition.subst, Proposition.rename, Path.subst_ofRename q ρ]

theorem Telescope.subst_ofRename {s1 s2 : Sig} : ∀ (Tel : Telescope s1) (ρ : Rename s1 s2),
    Tel.subst (PathSubst.ofRename ρ) = Tel.rename ρ
  | .nil, _ => rfl
  | .cons Tel P, ρ => by
      simp only [Telescope.subst, Telescope.rename, Telescope.subst_ofRename Tel ρ,
        Proposition.subst_ofRename P ρ]

end

/-- Substituting a variable path is the renaming `Ty.substVar`. -/
@[simp] theorem Ty.substPath_var (T : Ty (s,x)) (y : BVar s .var) :
    T.substPath (.var y) = T.substVar y := by
  rw [Ty.substPath, PathSubst.one_var, Ty.subst_ofRename, Ty.substVar]

/-- Substituting a variable path is the renaming `Proposition.substVar`. -/
@[simp] theorem Proposition.substPath_var (P : Proposition (s,x)) (y : BVar s .var) :
    P.substPath (.var y) = P.substVar y := by
  rw [Proposition.substPath, PathSubst.one_var, Proposition.subst_ofRename, Proposition.substVar]

/-- Substituting a variable path is the renaming `Telescope.substVar`. -/
@[simp] theorem Telescope.substPath_var (Tel : Telescope (s,x)) (y : BVar s .var) :
    Tel.substPath (.var y) = Tel.substVar y := by
  rw [Telescope.substPath, PathSubst.one_var, Telescope.subst_ofRename, Telescope.substVar]

/-! ## Block witnesses

The witnesses of a block: one type per label, absent labels reading as `⊤`.
They mention types only, so they are declared before evidence, whose `node`
constructor carries the witnesses of a node of the forest. -/

/-- Block witnesses, newest last. -/
inductive Witnesses : Sig → Type where
  | nil : Witnesses s
  | cons : Witnesses s → Label → Ty s → Witnesses s

deriving instance DecidableEq for Witnesses

def Witnesses.rename : Witnesses s1 → Rename s1 s2 → Witnesses s2
  | .nil, _ => .nil
  | .cons W ℓ T, ρ => .cons (W.rename ρ) ℓ (T.rename ρ)

/-! ## Evidence and atoms -/

/-- A hole of a template: the `j`-th proposition of the source telescope,
read as an inclusion.  An equality may be read in either direction. -/
inductive Hole : Type where
  | le : Nat → Hole
  | eq : Nat → Hole
  | eqSym : Nat → Hole
deriving DecidableEq

mutual

/-- Directed inclusion evidence.  No symmetry. -/
inductive LeCo : Sig → Type where
  | refl : Ty s → LeCo s
  | trans : LeCo s → LeCo s → LeCo s
  | top : Ty s → LeCo s
  | bot : Ty s → LeCo s
  | eqToLe : EqCo s → LeCo s
  /-- Contravariant domain, covariant codomain under the parameter binder. -/
  | pi : LeCo s → LeCo (s,x) → LeCo s
  /-- Object coercion between closed telescopes: the source telescope is
      annotated; the morphism proves each target proposition by a *template*
      (a closed coercion, a source proposition, a closed coercion). -/
  | obj : Telescope (s,x) → Morphism s → LeCo s
  /-- Pairing: two coercions into object types give one into the
      concatenation of their telescopes. -/
  | pair : Telescope (s,x) → Telescope (s,x) → LeCo s → LeCo s → LeCo s
  /-- The annotated object type is below its `i`-th bound. -/
  | bound : Telescope (s,x) → Nat → LeCo s
  /-- An `S` below `T` is an `S` below the one-bound object type `μ [⊑ T↑]`. -/
  | intoBnd : LeCo s → LeCo s
  /-- Elimination at an atom: the `i`-th proposition of the target telescope of `e`,
      instantiated at the root of `a`, when that proposition is an inclusion. -/
  | member : Atom s → LeCo s → Nat → LeCo s
  /-- Elimination at a stable path: the `i`-th proposition of the target
      telescope of `e`, instantiated at the path of `P`, when that proposition
      is an inclusion. -/
  | memberP : PathCo s → LeCo s → Nat → LeCo s

/-- Equality evidence. -/
inductive EqCo : Sig → Type where
  | refl : Ty s → EqCo s
  | symm : EqCo s → EqCo s
  | trans : EqCo s → EqCo s → EqCo s
  /-- Definition of a transparent binder's block name. -/
  | def : BVar s .var → Label → EqCo s
  /-- Definition of the block name of a path. -/
  | defP : Path s → Label → EqCo s
  | member : Atom s → LeCo s → Nat → EqCo s
  /-- Elimination at a stable path, at an equality proposition. -/
  | memberP : PathCo s → LeCo s → Nat → EqCo s

/-- Field-presence evidence. -/
inductive Has : Sig → Type where
  | member : Atom s → LeCo s → Nat → Has s
  /-- Elimination at a stable path, at a presence proposition. -/
  | memberP : PathCo s → LeCo s → Nat → Has s
  /-- Only valid inside the evidence block of an object literal that has the field. -/
  | field : Label → Has s

/-- One side of a template: an optional closed coercion, or one of the two
constant sides `bot` and `top`, which read nothing of the source. -/
inductive Side : Sig → Type where
  | none : Side s
  | some : LeCo s → Side s
  /-- The source endpoint is `⊥`; the annotation is the other endpoint,
      which the template's own source or target is. -/
  | bot : Ty (s,x) → Side s
  /-- The target endpoint is `⊤`; the annotation is the other endpoint. -/
  | top : Ty (s,x) → Side s

/-- A morphism into a telescope: one template per target proposition, oldest
first.  An inclusion is proven as `pre ∘ (source proposition) ∘ post` where
the source proposition is named by a `Hole`; an equality is a source
equality, possibly flipped; a field-presence proposition is inherited from
the source telescope by index. -/
inductive Morphism : Sig → Type where
  | nil : Morphism s
  | le : Morphism s → Side s → Hole → Side s → Morphism s
  | eq : Morphism s → Nat → Bool → Morphism s
  | has : Morphism s → Nat → Morphism s
  /-- A template for a target bound: a closed coercion out of the source
      object type. -/
  | bnd : Morphism s → LeCo s → Morphism s
  /-- Copy a stable presence `∋ᵛ ℓ` from the source by index. -/
  | hasVal : Morphism s → Nat → Morphism s
  /-- Read a presence `∋ ℓ` off a source stable presence `∋ᵛ ℓ`, by index. -/
  | hasOfVal : Morphism s → Nat → Morphism s
  /-- Copy an alias `≈ q` from the source by index. -/
  | aliasCopy : Morphism s → Nat → Morphism s

/-- Atoms: a variable under wrappers that erase to nothing. -/
inductive Atom : Sig → Type where
  | var : BVar s .var → Atom s
  | cast : Atom s → LeCo s → Atom s
  /-- `Rec-I`, annotated with the target telescope. -/
  | foldSelf : Telescope (s,x) → Atom s → Atom s
  | unfoldSelf : Atom s → Atom s
  /-- `And-I`: two typings of the same root, at the concatenated telescope. -/
  | both : Telescope (s,x) → Telescope (s,x) → Atom s → Atom s → Atom s
  /-- The atom at the singleton of `q`: the root of `a` names the block of
      `q`, so `a` also has the type `μ [≈ q↑]`.  `q` and `α` are annotations,
      as the telescope of `foldSelf` is: the other endpoint of an `AliasCo`
      is not syntactically computable. -/
  | sngl : Atom s → Path s → AliasCo s → Atom s

/-- A stable, typed path: a binder, a step through a stable presence
`∋ᵛ`, casts, aliasing, and the three object-type wrappers an atom
has.  `PathCo.path` reads off the path it names. -/
inductive PathCo : Sig → Type where
  | var : BVar s .var → PathCo s
  /-- One field step, at the index of the stable presence that licenses it. -/
  | sel : PathCo s → Label → Nat → PathCo s
  | cast : PathCo s → LeCo s → PathCo s
  /-- The path `p` names the block of `P`, so it has the type of `P`.  The
      path is an annotation, as the telescope of `foldSelf` is: the other
      endpoint of an `AliasCo` is not syntactically computable. -/
  | alias : AliasCo s → Path s → PathCo s → PathCo s
  /-- `Rec-I`, annotated with the target telescope. -/
  | foldSelf : Telescope (s,x) → PathCo s → PathCo s
  | unfoldSelf : PathCo s → PathCo s
  /-- `And-I`: two typings of one path, at the concatenated telescope. -/
  | both : Telescope (s,x) → Telescope (s,x) → PathCo s → PathCo s → PathCo s
  /-- The path at the singleton of `q`: `P` names the block of `q`, so it also
      has the type `μ [≈ q↑]`.  This is the introduction of a singleton, at a
      path and not at a type. -/
  | sngl : PathCo s → Path s → AliasCo s → PathCo s
  /-- The node of the forest at `p`, at the precise type of the literal whose
      block the table wrote there: its witnesses with the self still bound,
      its field labels and its stable field labels.  The typing rule reads the
      walk that follows no forwarding (decision 24). -/
  | node : Path s → Witnesses (s,x) → List Label → List Label → PathCo s

/-- Block identity evidence: `p ≈ q` says that the two paths name one block
of the forest.  A view carries the alias of a `≈` proposition, and the rest
are the laws of an equality.  No evidence reads a forwarding node of the
table: a forwarding serves resolution only (decision 24). -/
inductive AliasCo : Sig → Type where
  | refl : Path s → AliasCo s
  | symm : AliasCo s → AliasCo s
  | trans : AliasCo s → AliasCo s → AliasCo s
  /-- One field step on both sides. -/
  | sel : AliasCo s → Label → AliasCo s
  /-- The alias a view carries: the `i`-th proposition of the target telescope
      of `e`, when that proposition is an alias. -/
  | member : PathCo s → LeCo s → Nat → AliasCo s

end

deriving instance DecidableEq for LeCo, EqCo, Has, Side, Morphism, Atom, PathCo, AliasCo

/-- The variable under an atom's wrappers. -/
def Atom.root : Atom s → BVar s .var
  | .var x => x
  | .cast a _ => a.root
  | .foldSelf _ a => a.root
  | .unfoldSelf a => a.root
  | .both _ _ a _ => a.root
  | .sngl a _ _ => a.root

/-- The path a `PathCo` names. -/
def PathCo.path : PathCo s → Path s
  | .var x => .var x
  | .sel P a _ => .sel P.path a
  | .cast P _ => P.path
  | .alias _ p _ => p
  | .foldSelf _ P => P.path
  | .unfoldSelf P => P.path
  | .both _ _ P _ => P.path
  | .sngl P _ _ => P.path
  | .node p _ _ _ => p

/-- Every atom is a stable path of depth zero, under the same wrappers. -/
def Atom.toPathCo : Atom s → PathCo s
  | .var x => .var x
  | .cast a e => .cast a.toPathCo e
  | .foldSelf Tel a => .foldSelf Tel a.toPathCo
  | .unfoldSelf a => .unfoldSelf a.toPathCo
  | .both Tel₁ Tel₂ a b => .both Tel₁ Tel₂ a.toPathCo b.toPathCo
  | .sngl a q α => .sngl a.toPathCo q α

@[simp] theorem Atom.path_toPathCo : ∀ a : Atom s, a.toPathCo.path = .var a.root
  | .var _ => rfl
  | .cast a _ => Atom.path_toPathCo a
  | .foldSelf _ a => Atom.path_toPathCo a
  | .unfoldSelf a => Atom.path_toPathCo a
  | .both _ _ a _ => Atom.path_toPathCo a
  | .sngl a _ _ => Atom.path_toPathCo a

mutual

def LeCo.rename : LeCo s1 → Rename s1 s2 → LeCo s2
  | .refl T, ρ => .refl (T.rename ρ)
  | .trans e f, ρ => .trans (e.rename ρ) (f.rename ρ)
  | .top T, ρ => .top (T.rename ρ)
  | .bot T, ρ => .bot (T.rename ρ)
  | .eqToLe φ, ρ => .eqToLe (φ.rename ρ)
  | .pi e f, ρ => .pi (e.rename ρ) (f.rename ρ.lift)
  | .obj Tel m, ρ => .obj (Tel.rename ρ.lift) (m.rename ρ)
  | .pair Tel₁ Tel₂ e f, ρ => .pair (Tel₁.rename ρ.lift) (Tel₂.rename ρ.lift) (e.rename ρ) (f.rename ρ)
  | .bound Tel i, ρ => .bound (Tel.rename ρ.lift) i
  | .intoBnd e, ρ => .intoBnd (e.rename ρ)
  | .member a e i, ρ => .member (a.rename ρ) (e.rename ρ) i
  | .memberP P e i, ρ => .memberP (P.rename ρ) (e.rename ρ) i

def EqCo.rename : EqCo s1 → Rename s1 s2 → EqCo s2
  | .refl T, ρ => .refl (T.rename ρ)
  | .symm φ, ρ => .symm (φ.rename ρ)
  | .trans φ ψ, ρ => .trans (φ.rename ρ) (ψ.rename ρ)
  | .def x ℓ, ρ => .def (ρ.var x) ℓ
  | .defP p ℓ, ρ => .defP (p.rename ρ) ℓ
  | .member a e i, ρ => .member (a.rename ρ) (e.rename ρ) i
  | .memberP P e i, ρ => .memberP (P.rename ρ) (e.rename ρ) i

def Has.rename : Has s1 → Rename s1 s2 → Has s2
  | .member a e i, ρ => .member (a.rename ρ) (e.rename ρ) i
  | .memberP P e i, ρ => .memberP (P.rename ρ) (e.rename ρ) i
  | .field ℓ, _ => .field ℓ

def Side.rename : Side s1 → Rename s1 s2 → Side s2
  | .none, _ => .none
  | .some e, ρ => .some (e.rename ρ)
  | .bot X, ρ => .bot (X.rename ρ.lift)
  | .top X, ρ => .top (X.rename ρ.lift)

def Morphism.rename : Morphism s1 → Rename s1 s2 → Morphism s2
  | .nil, _ => .nil
  | .le m pre h post, ρ => .le (m.rename ρ) (pre.rename ρ) h (post.rename ρ)
  | .eq m j b, ρ => .eq (m.rename ρ) j b
  | .has m j, ρ => .has (m.rename ρ) j
  | .bnd m e, ρ => .bnd (m.rename ρ) (e.rename ρ)
  | .hasVal m j, ρ => .hasVal (m.rename ρ) j
  | .hasOfVal m j, ρ => .hasOfVal (m.rename ρ) j
  | .aliasCopy m j, ρ => .aliasCopy (m.rename ρ) j

def Atom.rename : Atom s1 → Rename s1 s2 → Atom s2
  | .var x, ρ => .var (ρ.var x)
  | .cast a e, ρ => .cast (a.rename ρ) (e.rename ρ)
  | .foldSelf Tel a, ρ => .foldSelf (Tel.rename ρ.lift) (a.rename ρ)
  | .unfoldSelf a, ρ => .unfoldSelf (a.rename ρ)
  | .both Tel₁ Tel₂ a b, ρ => .both (Tel₁.rename ρ.lift) (Tel₂.rename ρ.lift) (a.rename ρ) (b.rename ρ)
  | .sngl a q α, ρ => .sngl (a.rename ρ) (q.rename ρ) (α.rename ρ)

def PathCo.rename : PathCo s1 → Rename s1 s2 → PathCo s2
  | .var x, ρ => .var (ρ.var x)
  | .sel P a i, ρ => .sel (P.rename ρ) a i
  | .cast P e, ρ => .cast (P.rename ρ) (e.rename ρ)
  | .alias α p P, ρ => .alias (α.rename ρ) (p.rename ρ) (P.rename ρ)
  | .foldSelf Tel P, ρ => .foldSelf (Tel.rename ρ.lift) (P.rename ρ)
  | .unfoldSelf P, ρ => .unfoldSelf (P.rename ρ)
  | .both Tel₁ Tel₂ P Q, ρ =>
      .both (Tel₁.rename ρ.lift) (Tel₂.rename ρ.lift) (P.rename ρ) (Q.rename ρ)
  | .sngl P q α, ρ => .sngl (P.rename ρ) (q.rename ρ) (α.rename ρ)
  | .node p W ls vls, ρ => .node (p.rename ρ) (W.rename ρ.lift) ls vls

def AliasCo.rename : AliasCo s1 → Rename s1 s2 → AliasCo s2
  | .refl p, ρ => .refl (p.rename ρ)
  | .symm α, ρ => .symm (α.rename ρ)
  | .trans α β, ρ => .trans (α.rename ρ) (β.rename ρ)
  | .sel α a, ρ => .sel (α.rename ρ) a
  | .member P e i, ρ => .member (P.rename ρ) (e.rename ρ) i

end

/-- Renaming commutes with the path a `PathCo` names. -/
@[simp] theorem PathCo.path_rename {s1 s2 : Sig} :
    ∀ (P : PathCo s1) (ρ : Rename s1 s2), (P.rename ρ).path = P.path.rename ρ
  | .var _, _ => rfl
  | .sel P a _, ρ => by
      simp only [PathCo.rename, PathCo.path, Path.rename, PathCo.path_rename P ρ]
  | .cast P _, ρ => PathCo.path_rename P ρ
  | .alias _ _ _, _ => rfl
  | .foldSelf _ P, ρ => PathCo.path_rename P ρ
  | .unfoldSelf P, ρ => PathCo.path_rename P ρ
  | .both _ _ P _, ρ => PathCo.path_rename P ρ
  | .sngl P _ _, ρ => PathCo.path_rename P ρ
  | .node _ _ _ _, _ => rfl

/-! ## Terms and values -/

mutual

inductive Tm : Sig → Type where
  | atom : Atom s → Tm s
  | val : Value s → Tm s
  | app : Atom s → Atom s → Tm s
  /-- Field projection, annotated with the field-presence evidence. -/
  | proj : Atom s → Label → Has s → Tm s
  | «let» : Tm s → Tm (s,x) → Tm s
  | cast : Tm s → LeCo s → Tm s

inductive Value : Sig → Type where
  | lam : Ty s → Tm (s,x) → Value s
  /-- Object literal: block witnesses (absent labels are `⊤`) and fields.  Its
      precise type is the telescope generated from them (`Telescope.ofLiteral`). -/
  | obj : Witnesses (s,x) → Fields (s,x) → Value s
  /-- Adapted value: a wrapper, not a computation. -/
  | cast : Value s → LeCo s → Value s

inductive Fields : Sig → Type where
  | nil : Fields s
  | cons : Fields s → Label → Tm s → Fields s

end

deriving instance DecidableEq for Tm, Value, Fields

/-- Witness lookup; undefined labels are `⊤`. -/
def Witnesses.get : Witnesses s → Label → Ty s
  | .nil, _ => .top
  | .cons W ℓ' T, ℓ => if ℓ = ℓ' then T else W.get ℓ

/-- Labels of a witness list, oldest first (so that concatenation is list append). -/
def Witnesses.labels : Witnesses s → List Label
  | .nil => []
  | .cons W ℓ _ => W.labels ++ [ℓ]

/-- Only a listed label has a witness of its own: an unlisted one reads as `⊤`. -/
theorem Witnesses.get_of_not_mem_labels {s : Sig} :
    ∀ (W : Witnesses s) {ℓ : Label}, ℓ ∉ W.labels → W.get ℓ = ⊤
  | .nil, _, _ => rfl
  | .cons W ℓ' T, ℓ, h => by
      have h1 : ℓ ∉ W.labels := fun hm => h (by simp [Witnesses.labels, hm])
      have h2 : ℓ ≠ ℓ' := fun he => h (by simp [Witnesses.labels, he])
      rw [show Witnesses.get (Witnesses.cons W ℓ' T) ℓ = W.get ℓ by simp [Witnesses.get, h2]]
      exact Witnesses.get_of_not_mem_labels W h1

/-- Field lookup. -/
def Fields.get? : Fields s → Label → Option (Tm s)
  | .nil, _ => none
  | .cons F ℓ' t, ℓ => if ℓ = ℓ' then some t else F.get? ℓ

/-- Field presence, as a proposition on the syntax. -/
def Fields.Has (F : Fields s) (ℓ : Label) : Prop := (F.get? ℓ).isSome

/-- Definition entries of a literal's witnesses: one `self ∙ ℓ ≐ W₀.get ℓ` per
listed label (a shadowed label gets the outer definition, so every entry is
true of the literal).  Stated for an arbitrary self variable so that the
recursion is structural. -/
def Witnesses.eqEntriesOf (self : BVar s' .var) (W₀ : Witnesses s') : Witnesses s' → Telescope s'
  | .nil => .nil
  | .cons W ℓ _ => W₀.eqEntriesOf self W ▹ self ∙ ℓ ≐ W₀.get ℓ

def Witnesses.eqEntries (W : Witnesses (s,x)) : Telescope (s,x) := W.eqEntriesOf .here W

/-- Presence entries for a list of field labels, appended to a telescope. -/
def Telescope.hasEntries : Telescope s → List Label → Telescope s
  | Tel, [] => Tel
  | Tel, ℓ :: ls => (Tel.cons (.has ℓ)).hasEntries ls

/-- Stable-presence entries for a list of field labels, appended to a
telescope (as `Telescope.hasEntries`). -/
def Telescope.hasValEntries : Telescope s → List Label → Telescope s
  | Tel, [] => Tel
  | Tel, ℓ :: ls => (Tel.cons (.hasVal ℓ)).hasValEntries ls

/-- The precise telescope of an object literal: its definitions, then its
fields, then the fields whose body is stable.  The `∋ᵛ` entries come last,
so every index the base computes is unchanged, and at `vlabels = []` this is
the base's telescope. -/
def Telescope.ofLiteral (W : Witnesses (s,x)) (labels vlabels : List Label) : Telescope (s,x) :=
  (W.eqEntries.hasEntries labels).hasValEntries vlabels

mutual

def Tm.rename : Tm s1 → Rename s1 s2 → Tm s2
  | .atom a, ρ => .atom (a.rename ρ)
  | .val v, ρ => .val (v.rename ρ)
  | .app a b, ρ => .app (a.rename ρ) (b.rename ρ)
  | .proj a ℓ h, ρ => .proj (a.rename ρ) ℓ (h.rename ρ)
  | .let t u, ρ => .let (t.rename ρ) (u.rename ρ.lift)
  | .cast t e, ρ => .cast (t.rename ρ) (e.rename ρ)

def Value.rename : Value s1 → Rename s1 s2 → Value s2
  | .lam S t, ρ => .lam (S.rename ρ) (t.rename ρ.lift)
  | .obj W F, ρ => .obj (W.rename ρ.lift) (F.rename ρ.lift)
  | .cast v e, ρ => .cast (v.rename ρ) (e.rename ρ)

def Fields.rename : Fields s1 → Rename s1 s2 → Fields s2
  | .nil, _ => .nil
  | .cons F ℓ t, ρ => .cons (F.rename ρ) ℓ (t.rename ρ)

end

def Tm.weaken (t : Tm s) : Tm (s,,k) := t.rename Rename.succ
def Atom.weaken (a : Atom s) : Atom (s,,k) := a.rename Rename.succ
def Value.weaken (v : Value s) : Value (s,,k) := v.rename Rename.succ
def LeCo.weaken (e : LeCo s) : LeCo (s,,k) := e.rename Rename.succ

scoped postfix:max "↑" => Tm.weaken
scoped postfix:max "↑" => Atom.weaken
scoped postfix:max "↑" => Value.weaken
scoped postfix:max "↑" => LeCo.weaken

/-! ## The block forest

The block of a path is what resolution reads: either an object's own table,
holding its witnesses, its field labels, its stable field labels and its
children, or a forwarding to the path whose block this is.  A forwarding is
how a field holding an atom and an alias binder are recorded, and it is the
only way two names get one block.

Witnesses are written at absolute paths.  The block of a value sitting at `p`
carries the value's witnesses with the self replaced by `p`, and each child
carries its own witnesses at `.sel p a` and deeper.  The builder is therefore
`Value.blocksAt`, which takes the path the value sits at. -/

/-- Labels of a field list. -/
def Fields.labels : Fields s → List Label
  | .nil => []
  | .cons F ℓ _ => ℓ :: F.labels

/-- An object literal under value casts. -/
def Value.isObjLit : Value s → Bool
  | .obj _ _ => true
  | .cast v _ => v.isObjLit
  | .lam _ _ => false

mutual

/-- Evidence that eliminates nowhere: no `member` and no `memberP`, at any
depth of its morphisms and sides.  Its normal form reads no view.  A `pi`
coercion is kept raw by the normalizer, so it is table-only whatever its
parts are. -/
def LeCo.tableOnly : LeCo s → Bool
  | .refl _ => true
  | .trans e f => e.tableOnly && f.tableOnly
  | .top _ => true
  | .bot _ => true
  | .eqToLe φ => φ.tableOnly
  | .pi _ _ => true
  | .obj _ m => m.tableOnly
  | .pair _ _ e f => e.tableOnly && f.tableOnly
  | .bound _ _ => true
  | .intoBnd e => e.tableOnly
  | .member _ _ _ => false
  | .memberP _ _ _ => false

def EqCo.tableOnly : EqCo s → Bool
  | .refl _ => true
  | .symm φ => φ.tableOnly
  | .trans φ ψ => φ.tableOnly && ψ.tableOnly
  | .def _ _ => true
  | .defP _ _ => true
  | .member _ _ _ => false
  | .memberP _ _ _ => false

def Side.tableOnly : Side s → Bool
  | .none => true
  | .some e => e.tableOnly
  | .bot _ => true
  | .top _ => true

def Morphism.tableOnly : Morphism s → Bool
  | .nil => true
  | .le m pre _ post => m.tableOnly && pre.tableOnly && post.tableOnly
  | .eq m _ _ => m.tableOnly
  | .has m _ => m.tableOnly
  | .bnd m e => m.tableOnly && e.tableOnly
  | .hasVal m _ => m.tableOnly
  | .hasOfVal m _ => m.tableOnly
  | .aliasCopy m _ => m.tableOnly

end

/-- An object literal under table-only value casts. -/
def Value.isStableLit : Value s → Bool
  | .obj _ _ => true
  | .cast v e => v.isStableLit && e.tableOnly
  | .lam _ _ => false

theorem Value.isObjLit_of_isStableLit : ∀ {v : Value s}, v.isStableLit = true → v.isObjLit = true
  | .obj _ _, _ => rfl
  | .cast v _, h => by
      simp only [Value.isStableLit, Bool.and_eq_true] at h
      exact Value.isObjLit_of_isStableLit (v := v) h.1
  | .lam _ _, h => by simp [Value.isStableLit] at h

/-- A term body is stable when it is an object literal under casts
(decision 24).  A stable body is what a `∋ᵛ` proposition promises, and it is
what gets an object child in the block forest.  A field whose body is an atom
or a lambda is a plain field. -/
def Tm.isStable : Tm s → Bool
  | .val v => v.isStableLit
  | .cast t e => t.isStable && e.tableOnly
  | .atom _ => false
  | .app _ _ => false
  | .proj _ _ _ => false
  | .let _ _ => false

/-- Labels of the fields whose body is stable.  A literal may list one label
twice, and then the last field at the label decides, as `Fields.get?` reads it
(decision 25).  So a later field that is not stable removes the label. -/
def Fields.valLabels : Fields s → List Label
  | .nil => []
  | .cons F ℓ t => if t.isStable then ℓ :: F.valLabels else F.valLabels.filter (· ≠ ℓ)

mutual
/-- The block of one path: an object's own table, or a forwarding to the path
whose block this is. -/
inductive Block : Sig → Type where
  | obj : Witnesses s → List Label → List Label → Children s → Block s
  | fwd : Path s → Block s

/-- The children of a block.  `Children.at?` reads the last entry at a label. -/
inductive Children : Sig → Type where
  | nil : Children s
  | cons : Children s → Label → Block s → Children s
end

deriving instance DecidableEq for Block, Children

/-- Child lookup. -/
def Children.at? : Children s → Label → Option (Block s)
  | .nil, _ => none
  | .cons ch ℓ' b, ℓ => if ℓ = ℓ' then some b else ch.at? ℓ

/-- Remove every entry at a label. -/
def Children.dropLabel : Children s → Label → Children s
  | .nil, _ => .nil
  | .cons ch ℓ' b, ℓ => if ℓ' = ℓ then ch.dropLabel ℓ else .cons (ch.dropLabel ℓ) ℓ' b

/-- The child of a block at a label.  A forwarding node has no children of
its own: the walk follows it first. -/
def Block.childAt? : Block s → Label → Option (Block s)
  | .obj _ _ _ ch, ℓ => ch.at? ℓ
  | .fwd _, _ => none

/-- The definition a block gives a label, if it is an object node. -/
def Block.def? : Block s → Label → Option (Ty s)
  | .obj W _ _ _, ℓ => some (W.get ℓ)
  | .fwd _, _ => none

/-- The field labels a block lists, if it is an object node. -/
def Block.fields? : Block s → Option (List Label)
  | .obj _ Fs _ _ => some Fs
  | .fwd _ => none

/-- The stable field labels a block lists, if it is an object node. -/
def Block.valFields? : Block s → Option (List Label)
  | .obj _ _ Vs _ => some Vs
  | .fwd _ => none

mutual
/-- The number of forwarding nodes in a block. -/
def Block.fwdCount : Block s → Nat
  | .obj _ _ _ ch => ch.fwdCount
  | .fwd _ => 1

def Children.fwdCount : Children s → Nat
  | .nil => 0
  | .cons ch _ b => ch.fwdCount + b.fwdCount
end

/-! ### Renaming and path substitution of blocks -/

def Witnesses.subst : Witnesses s1 → PathSubst s1 s2 → Witnesses s2
  | .nil, _ => .nil
  | .cons W ℓ T, σ => .cons (W.subst σ) ℓ (T.subst σ)

/-- Instantiate the self binder of a witness list by a path. -/
def Witnesses.substPath (W : Witnesses (s,x)) (q : Path s) : Witnesses s :=
  W.subst (PathSubst.one q)

mutual
def Block.rename : Block s1 → Rename s1 s2 → Block s2
  | .obj W ls vls ch, ρ => .obj (W.rename ρ) ls vls (ch.rename ρ)
  | .fwd q, ρ => .fwd (q.rename ρ)

def Children.rename : Children s1 → Rename s1 s2 → Children s2
  | .nil, _ => .nil
  | .cons ch ℓ b, ρ => .cons (ch.rename ρ) ℓ (b.rename ρ)
end

def Block.weaken (B : Block s) : Block (s,,k) := B.rename Rename.succ

mutual
def Block.subst : Block s1 → PathSubst s1 s2 → Block s2
  | .obj W ls vls ch, σ => .obj (W.subst σ) ls vls (ch.subst σ)
  | .fwd q, σ => .fwd (q.subst σ)

def Children.subst : Children s1 → PathSubst s1 s2 → Children s2
  | .nil, _ => .nil
  | .cons ch ℓ b, σ => .cons (ch.subst σ) ℓ (b.subst σ)
end

/-- Instantiate the self binder of a block by a path. -/
def Block.substPath (B : Block (s,x)) (q : Path s) : Block s :=
  B.subst (PathSubst.one q)

/-- Instantiate the self binder of a child list by a path. -/
def Children.substPath (ch : Children (s,x)) (q : Path s) : Children s :=
  ch.subst (PathSubst.one q)

/-! ### The block builder

`Value.blockSelf` computes the block of a value with its own path still
bound, as the base's `Witnesses (s,x)` are, and `Value.blocksAt` writes it at
the path the value sits at. -/

mutual
/-- The block of a value, with the value's own path as the binder `.here`. -/
def Value.blockSelf : Value s → Block (s,x)
  | .cast v _ => v.blockSelf
  | .lam _ _ => .obj .nil [] [] .nil
  | .obj W F => .obj W F.labels F.valLabels (F.children (.var .here))

/-- The children a field list contributes to the block at `p`: one per field
whose body gives a child.  The last field at a label decides, as
`Fields.get?` reads it (decision 25): a later field that gives no child
removes the earlier entries at its label. -/
def Fields.children : Fields s → Path s → Children s
  | .nil, _ => .nil
  | .cons F ℓ t, p =>
      match t.childAt (.sel p ℓ) with
      | some b => .cons (F.children p) ℓ b
      | none => (F.children p).dropLabel ℓ

/-- The child a field body contributes at the child's own path: an object
literal gives its own block, an atom gives a forwarding to the atom's path,
for resolution only, and anything else, a lambda included, gives no child
(decision 24). -/
def Tm.childAt : Tm s → Path s → Option (Block s)
  | .val v, p => if v.isStableLit then some (v.blockSelf.substPath p) else none
  | .atom a, _ => some (.fwd (.var a.root))
  | .cast t e, p => if t.isStable && !e.tableOnly then none else t.childAt p
  | .app _ _, _ => none
  | .proj _ _ _, _ => none
  | .let _ _, _ => none
end

/-- The block a value defines when it sits at path `p`. -/
def Value.blocksAt (v : Value s) (p : Path s) : Block s := v.blockSelf.substPath p

/-! ### A stable field label is an object child

`Fields.valLabels` and `Fields.children` are two readings of one list, and
both read the last field at each label, as `Fields.get?` does (decision 25).
After decision 24 a field whose body is an atom still gives a child, a
forwarding for resolution only, and no stable label.  So a stable label is
exactly a label whose child at the walk is an object node, with no hypothesis
on the literal.  This is the coherence the `∋ᵛ` propositions of a literal's
telescope rest on. -/

theorem Children.at?_dropLabel {s : Sig} :
    ∀ (ch : Children s) (ℓ a : Label),
      (ch.dropLabel ℓ).at? a = if a = ℓ then none else ch.at? a
  | .nil, _, _ => by simp [Children.dropLabel, Children.at?]
  | .cons ch ℓ' b, ℓ, a => by
      by_cases h1 : ℓ' = ℓ
      · subst h1
        by_cases h2 : a = ℓ'
        · simp [Children.dropLabel, h2, Children.at?_dropLabel ch]
        · simp [Children.dropLabel, Children.at?, h2, Children.at?_dropLabel ch]
      · by_cases h2 : a = ℓ
        · subst h2
          have h3 : ¬ a = ℓ' := fun h => h1 h.symm
          simp [Children.dropLabel, Children.at?, h1, h3, Children.at?_dropLabel ch]
        · simp [Children.dropLabel, Children.at?, h1, h2, Children.at?_dropLabel ch]

@[simp] theorem Children.dropLabel_rename {s1 s2 : Sig} :
    ∀ (ch : Children s1) (ρ : Rename s1 s2) (ℓ : Label),
      (ch.rename ρ).dropLabel ℓ = (ch.dropLabel ℓ).rename ρ
  | .nil, _, _ => rfl
  | .cons ch ℓ' b, ρ, ℓ => by
      by_cases h : ℓ' = ℓ <;>
        simp [Children.rename, Children.dropLabel, h, Children.dropLabel_rename ch ρ ℓ]

@[simp] theorem Children.dropLabel_subst {s1 s2 : Sig} :
    ∀ (ch : Children s1) (σ : PathSubst s1 s2) (ℓ : Label),
      (ch.subst σ).dropLabel ℓ = (ch.dropLabel ℓ).subst σ
  | .nil, _, _ => rfl
  | .cons ch ℓ' b, σ, ℓ => by
      by_cases h : ℓ' = ℓ <;>
        simp [Children.subst, Children.dropLabel, h, Children.dropLabel_subst ch σ ℓ]

theorem Value.blockSelf_obj {s : Sig} :
    ∀ (v : Value s), ∃ W ls vls ch, v.blockSelf = Block.obj W ls vls ch
  | .obj _ F => ⟨_, F.labels, F.valLabels, _, rfl⟩
  | .cast v _ => Value.blockSelf_obj v
  | .lam _ _ => ⟨.nil, [], [], .nil, rfl⟩

/-- A field body is stable exactly when its child is an object node. -/
theorem Tm.isStable_iff_childAt_obj {s : Sig} :
    ∀ (t : Tm s) (p : Path s),
      t.isStable = true ↔ ∃ W ls vls ch, t.childAt p = some (Block.obj W ls vls ch)
  | .val v, p => by
      cases hv : v.isStableLit with
      | false => simp [Tm.isStable, Tm.childAt, hv]
      | true =>
          obtain ⟨W, ls, vls, ch, hb⟩ := Value.blockSelf_obj v
          simp only [Tm.isStable, Tm.childAt, hv, if_true, hb, Block.substPath, Block.subst,
            Option.some.injEq, true_iff]
          exact ⟨_, _, _, _, rfl⟩
  | .atom _, _ => by simp [Tm.isStable, Tm.childAt]
  | .cast t e, p => by
      have ih := Tm.isStable_iff_childAt_obj t p
      cases ht : t.isStable <;> cases he : e.tableOnly <;>
        simp_all [Tm.isStable, Tm.childAt]
  | .app _ _, _ => by simp [Tm.isStable, Tm.childAt]
  | .proj _ _ _, _ => by simp [Tm.isStable, Tm.childAt]
  | .let _ _, _ => by simp [Tm.isStable, Tm.childAt]

/-- A stable body has a child. -/
theorem Tm.childAt_isSome_of_isStable {s : Sig} {t : Tm s} (p : Path s)
    (h : t.isStable = true) : (t.childAt p).isSome := by
  obtain ⟨W, ls, vls, ch, hc⟩ := (Tm.isStable_iff_childAt_obj t p).1 h
  rw [hc]; rfl

@[simp] theorem Children.at?_subst {s1 s2 : Sig} :
    ∀ (ch : Children s1) (σ : PathSubst s1 s2) (ℓ : Label),
      (ch.subst σ).at? ℓ = (ch.at? ℓ).map (Block.subst · σ)
  | .nil, _, _ => rfl
  | .cons ch ℓ' b, σ, ℓ => by
      by_cases h : ℓ = ℓ' <;>
        simp [Children.subst, Children.at?, h, Children.at?_subst ch σ ℓ]

/-- The walk's child at `a` is the child of the field the machine projects. -/
theorem Fields.children_at? {s : Sig} :
    ∀ (F : Fields s) (p : Path s) (a : Label),
      (F.children p).at? a = (F.get? a).bind (fun t => t.childAt (.sel p a))
  | .nil, _, _ => rfl
  | .cons F ℓ t, p, a => by
      by_cases h : a = ℓ
      · subst h
        cases ht : t.childAt (.sel p a) with
        | none => simp [Fields.children, ht, Children.at?_dropLabel, Fields.get?]
        | some b => simp [Fields.children, ht, Children.at?, Fields.get?]
      · have ih := Fields.children_at? F p a
        cases ht : t.childAt (.sel p ℓ) with
        | none => simp [Fields.children, ht, Children.at?_dropLabel, Fields.get?, h, ih]
        | some b => simp [Fields.children, ht, Children.at?, Fields.get?, h, ih]

/-- A stable label is a label whose last field is stable. -/
theorem Fields.mem_valLabels_iff_get? {s : Sig} :
    ∀ (F : Fields s) (a : Label),
      a ∈ F.valLabels ↔ ∃ t, F.get? a = some t ∧ t.isStable = true
  | .nil, _ => by simp [Fields.valLabels, Fields.get?]
  | .cons F ℓ t, a => by
      have ih := Fields.mem_valLabels_iff_get? F a
      by_cases h : a = ℓ
      · subst h
        cases hs : t.isStable <;> simp [Fields.valLabels, Fields.get?, hs]
      · cases hs : t.isStable <;> simp [Fields.valLabels, Fields.get?, hs, h, ih]

/-- A stable label is exactly a label whose child at the walk is an object
node. -/
theorem Fields.mem_valLabels_iff_children {s : Sig} (F : Fields s) (p : Path s) (a : Label) :
    a ∈ F.valLabels ↔ ∃ W ls vls ch, (F.children p).at? a = some (.obj W ls vls ch) := by
  rw [Fields.mem_valLabels_iff_get?, Fields.children_at?]
  cases hg : F.get? a with
  | none => simp
  | some t =>
      simp only [Option.some.injEq, exists_eq_left', Option.bind_some]
      exact Tm.isStable_iff_childAt_obj t (.sel p a)

/-- The direction the walk reads: a label whose child is an object node is
stable. -/
theorem Fields.mem_valLabels_of_at? {s : Sig} {F : Fields s} {p : Path s} {a : Label}
    {W : Witnesses s} {ls vls : List Label} {ch : Children s}
    (h : (F.children p).at? a = some (.obj W ls vls ch)) : a ∈ F.valLabels :=
  (Fields.mem_valLabels_iff_children F p a).2 ⟨W, ls, vls, ch, h⟩

/-! ## Atom substitution

A substitution maps term variables to atoms.  Types and evidence only see the
root variable, so on them a substitution acts as the renaming of roots; on
terms the atom itself replaces the variable. -/

structure Subst (s1 s2 : Sig) where
  var : BVar s1 .var → Atom s2

namespace Subst

/-- The renaming of roots induced by a substitution. -/
def root (σ : Subst s1 s2) : Rename s1 s2 where
  var := fun {k} x => match k, x with
    | .var, x => (σ.var x).root

def lift (σ : Subst s1 s2) : Subst (s1,x) (s2,x) where
  var := fun
    | .here => .var .here
    | .there x => (σ.var x).weaken

/-- Substitute the innermost binder by an atom, keep the rest. -/
def single (a : Atom s) : Subst (s,x) s where
  var := fun
    | .here => a
    | .there x => .var x

def ofRename (ρ : Rename s1 s2) : Subst s1 s2 where
  var := fun x => .var (ρ.var x)

end Subst

/-- Use the innermost binder under a cast everywhere in a term. -/
def Subst.selfCast (E : LeCo (s,x)) : Subst (s,x) (s,x) where
  var := fun
    | .here => .cast (.var .here) E
    | .there y => .var (.there y)

mutual

def LeCo.subst : LeCo s1 → Subst s1 s2 → LeCo s2
  | .refl T, σ => .refl (T.rename σ.root)
  | .trans e f, σ => .trans (e.subst σ) (f.subst σ)
  | .top T, σ => .top (T.rename σ.root)
  | .bot T, σ => .bot (T.rename σ.root)
  | .eqToLe φ, σ => .eqToLe (φ.subst σ)
  | .pi e f, σ => .pi (e.subst σ) (f.subst σ.lift)
  | .obj Tel m, σ => .obj (Tel.rename σ.root.lift) (m.subst σ)
  | .pair Tel₁ Tel₂ e f, σ =>
      .pair (Tel₁.rename σ.root.lift) (Tel₂.rename σ.root.lift) (e.subst σ) (f.subst σ)
  | .bound Tel i, σ => .bound (Tel.rename σ.root.lift) i
  | .intoBnd e, σ => .intoBnd (e.subst σ)
  | .member a e i, σ => .member (a.subst σ) (e.subst σ) i
  | .memberP P e i, σ => .memberP (P.subst σ) (e.subst σ) i

def EqCo.subst : EqCo s1 → Subst s1 s2 → EqCo s2
  | .refl T, σ => .refl (T.rename σ.root)
  | .symm φ, σ => .symm (φ.subst σ)
  | .trans φ ψ, σ => .trans (φ.subst σ) (ψ.subst σ)
  | .def x ℓ, σ => .def (σ.root.var x) ℓ
  | .defP p ℓ, σ => .defP (p.rename σ.root) ℓ
  | .member a e i, σ => .member (a.subst σ) (e.subst σ) i
  | .memberP P e i, σ => .memberP (P.subst σ) (e.subst σ) i

def Has.subst : Has s1 → Subst s1 s2 → Has s2
  | .member a e i, σ => .member (a.subst σ) (e.subst σ) i
  | .memberP P e i, σ => .memberP (P.subst σ) (e.subst σ) i
  | .field ℓ, _ => .field ℓ

def Side.subst : Side s1 → Subst s1 s2 → Side s2
  | .none, _ => .none
  | .some e, σ => .some (e.subst σ)
  | .bot X, σ => .bot (X.rename σ.root.lift)
  | .top X, σ => .top (X.rename σ.root.lift)

def Morphism.subst : Morphism s1 → Subst s1 s2 → Morphism s2
  | .nil, _ => .nil
  | .le m pre h post, σ => .le (m.subst σ) (pre.subst σ) h (post.subst σ)
  | .eq m j b, σ => .eq (m.subst σ) j b
  | .has m j, σ => .has (m.subst σ) j
  | .bnd m e, σ => .bnd (m.subst σ) (e.subst σ)
  | .hasVal m j, σ => .hasVal (m.subst σ) j
  | .hasOfVal m j, σ => .hasOfVal (m.subst σ) j
  | .aliasCopy m j, σ => .aliasCopy (m.subst σ) j

def Atom.subst : Atom s1 → Subst s1 s2 → Atom s2
  | .var x, σ => σ.var x
  | .cast a e, σ => .cast (a.subst σ) (e.subst σ)
  | .foldSelf Tel a, σ => .foldSelf (Tel.rename σ.root.lift) (a.subst σ)
  | .unfoldSelf a, σ => .unfoldSelf (a.subst σ)
  | .both Tel₁ Tel₂ a b, σ =>
      .both (Tel₁.rename σ.root.lift) (Tel₂.rename σ.root.lift) (a.subst σ) (b.subst σ)
  | .sngl a q α, σ => .sngl (a.subst σ) (q.rename σ.root) (α.subst σ)

def PathCo.subst : PathCo s1 → Subst s1 s2 → PathCo s2
  | .var x, σ => (σ.var x).toPathCo
  | .sel P a i, σ => .sel (P.subst σ) a i
  | .cast P e, σ => .cast (P.subst σ) (e.subst σ)
  | .alias α p P, σ => .alias (α.subst σ) (p.rename σ.root) (P.subst σ)
  | .foldSelf Tel P, σ => .foldSelf (Tel.rename σ.root.lift) (P.subst σ)
  | .unfoldSelf P, σ => .unfoldSelf (P.subst σ)
  | .both Tel₁ Tel₂ P Q, σ =>
      .both (Tel₁.rename σ.root.lift) (Tel₂.rename σ.root.lift) (P.subst σ) (Q.subst σ)
  | .sngl P q α, σ => .sngl (P.subst σ) (q.rename σ.root) (α.subst σ)
  | .node p W ls vls, σ => .node (p.rename σ.root) (W.rename σ.root.lift) ls vls

def AliasCo.subst : AliasCo s1 → Subst s1 s2 → AliasCo s2
  | .refl p, σ => .refl (p.rename σ.root)
  | .symm α, σ => .symm (α.subst σ)
  | .trans α β, σ => .trans (α.subst σ) (β.subst σ)
  | .sel α a, σ => .sel (α.subst σ) a
  | .member P e i, σ => .member (P.subst σ) (e.subst σ) i

end

/-- A substitution acts on the path a `PathCo` names as the renaming of
roots, exactly as it acts on types. -/
@[simp] theorem PathCo.path_subst {s1 s2 : Sig} :
    ∀ (P : PathCo s1) (σ : Subst s1 s2), (P.subst σ).path = P.path.rename σ.root
  | .var x, σ => by
      simp only [PathCo.subst, PathCo.path, Path.rename, Atom.path_toPathCo]; rfl
  | .sel P a _, σ => by
      simp only [PathCo.subst, PathCo.path, Path.rename, PathCo.path_subst P σ]
  | .cast P _, σ => PathCo.path_subst P σ
  | .alias _ _ _, _ => rfl
  | .foldSelf _ P, σ => PathCo.path_subst P σ
  | .unfoldSelf P, σ => PathCo.path_subst P σ
  | .both _ _ P _, σ => PathCo.path_subst P σ
  | .sngl P _ _, σ => PathCo.path_subst P σ
  | .node _ _ _ _, _ => rfl

mutual

def Tm.subst : Tm s1 → Subst s1 s2 → Tm s2
  | .atom a, σ => .atom (a.subst σ)
  | .val v, σ => .val (v.subst σ)
  | .app a b, σ => .app (a.subst σ) (b.subst σ)
  | .proj a ℓ h, σ => .proj (a.subst σ) ℓ (h.subst σ)
  | .let t u, σ => .let (t.subst σ) (u.subst σ.lift)
  | .cast t e, σ => .cast (t.subst σ) (e.subst σ)

def Value.subst : Value s1 → Subst s1 s2 → Value s2
  | .lam S t, σ => .lam (S.rename σ.root) (t.subst σ.lift)
  | .obj W F, σ => .obj (W.rename σ.root.lift) (F.subst σ.lift)
  | .cast v e, σ => .cast (v.subst σ) (e.subst σ)

def Fields.subst : Fields s1 → Subst s1 s2 → Fields s2
  | .nil, _ => .nil
  | .cons F ℓ t, σ => .cons (F.subst σ) ℓ (t.subst σ)

end

/-- Instantiate the innermost binder of a term by an atom. -/
def Tm.substAtom (t : Tm (s,x)) (a : Atom s) : Tm s := t.subst (Subst.single a)

/-! ## Path substitution of evidence

A path substitution on evidence sends each variable to a `PathCo`.  Types see
the paths the `PathCo`s name, through `PSub.paths`.  An atom becomes the
`PathCo` of its root under the same wrappers, so elimination at an atom
becomes elimination at a path: `member` goes to `memberP`, and `def` to
`defP`.  It maps evidence to evidence and never touches a term or a value
(Fact 1).  This is what closes the coercion of a field of a nested literal
over the store (decision 24, P1.5). -/

/-- A path substitution on evidence: one `PathCo` per term variable. -/
structure PSub (s1 s2 : Sig) where
  var : BVar s1 .var → PathCo s2

namespace PSub

/-- The path substitution on types that a `PSub` induces. -/
def paths (σ : PSub s1 s2) : PathSubst s1 s2 := ⟨fun x => (σ.var x).path⟩

/-- Lift under one binder: the new binder maps to itself. -/
def lift (σ : PSub s1 s2) : PSub (s1,x) (s2,x) where
  var := fun
    | .here => .var .here
    | .there x => (σ.var x).rename Rename.succ

/-- The identity. -/
def id : PSub s s := ⟨fun x => .var x⟩

/-- Extend by the self of a literal: the new binder goes to `P`. -/
def cons (τ : PSub s1 s2) (P : PathCo s2) : PSub (s1,x) s2 where
  var := fun
    | .here => P
    | .there y => τ.var y

end PSub

mutual

def LeCo.psubst : LeCo s1 → PSub s1 s2 → LeCo s2
  | .refl T, σ => .refl (T.subst σ.paths)
  | .trans e f, σ => .trans (e.psubst σ) (f.psubst σ)
  | .top T, σ => .top (T.subst σ.paths)
  | .bot T, σ => .bot (T.subst σ.paths)
  | .eqToLe φ, σ => .eqToLe (φ.psubst σ)
  | .pi e f, σ => .pi (e.psubst σ) (f.psubst σ.lift)
  | .obj Tel m, σ => .obj (Tel.subst σ.paths.lift) (m.psubst σ)
  | .pair Tel₁ Tel₂ e f, σ =>
      .pair (Tel₁.subst σ.paths.lift) (Tel₂.subst σ.paths.lift) (e.psubst σ) (f.psubst σ)
  | .bound Tel i, σ => .bound (Tel.subst σ.paths.lift) i
  | .intoBnd e, σ => .intoBnd (e.psubst σ)
  | .member a e i, σ => .memberP (a.psubst σ) (e.psubst σ) i
  | .memberP P e i, σ => .memberP (P.psubst σ) (e.psubst σ) i

def EqCo.psubst : EqCo s1 → PSub s1 s2 → EqCo s2
  | .refl T, σ => .refl (T.subst σ.paths)
  | .symm φ, σ => .symm (φ.psubst σ)
  | .trans φ ψ, σ => .trans (φ.psubst σ) (ψ.psubst σ)
  | .def x ℓ, σ => .defP (σ.var x).path ℓ
  | .defP p ℓ, σ => .defP (p.subst σ.paths) ℓ
  | .member a e i, σ => .memberP (a.psubst σ) (e.psubst σ) i
  | .memberP P e i, σ => .memberP (P.psubst σ) (e.psubst σ) i

def Side.psubst : Side s1 → PSub s1 s2 → Side s2
  | .none, _ => .none
  | .some e, σ => .some (e.psubst σ)
  | .bot X, σ => .bot (X.subst σ.paths.lift)
  | .top X, σ => .top (X.subst σ.paths.lift)

def Morphism.psubst : Morphism s1 → PSub s1 s2 → Morphism s2
  | .nil, _ => .nil
  | .le m pre h post, σ => .le (m.psubst σ) (pre.psubst σ) h (post.psubst σ)
  | .eq m j b, σ => .eq (m.psubst σ) j b
  | .has m j, σ => .has (m.psubst σ) j
  | .bnd m e, σ => .bnd (m.psubst σ) (e.psubst σ)
  | .hasVal m j, σ => .hasVal (m.psubst σ) j
  | .hasOfVal m j, σ => .hasOfVal (m.psubst σ) j
  | .aliasCopy m j, σ => .aliasCopy (m.psubst σ) j

/-- An atom becomes the path of its root, under the same wrappers. -/
def Atom.psubst : Atom s1 → PSub s1 s2 → PathCo s2
  | .var x, σ => σ.var x
  | .cast a e, σ => .cast (a.psubst σ) (e.psubst σ)
  | .foldSelf Tel a, σ => .foldSelf (Tel.subst σ.paths.lift) (a.psubst σ)
  | .unfoldSelf a, σ => .unfoldSelf (a.psubst σ)
  | .both Tel₁ Tel₂ a b, σ =>
      .both (Tel₁.subst σ.paths.lift) (Tel₂.subst σ.paths.lift) (a.psubst σ) (b.psubst σ)
  | .sngl a q α, σ => .sngl (a.psubst σ) (q.subst σ.paths) (α.psubst σ)

def PathCo.psubst : PathCo s1 → PSub s1 s2 → PathCo s2
  | .var x, σ => σ.var x
  | .sel P a i, σ => .sel (P.psubst σ) a i
  | .cast P e, σ => .cast (P.psubst σ) (e.psubst σ)
  | .alias α p P, σ => .alias (α.psubst σ) (p.subst σ.paths) (P.psubst σ)
  | .foldSelf Tel P, σ => .foldSelf (Tel.subst σ.paths.lift) (P.psubst σ)
  | .unfoldSelf P, σ => .unfoldSelf (P.psubst σ)
  | .both Tel₁ Tel₂ P Q, σ =>
      .both (Tel₁.subst σ.paths.lift) (Tel₂.subst σ.paths.lift) (P.psubst σ) (Q.psubst σ)
  | .sngl P q α, σ => .sngl (P.psubst σ) (q.subst σ.paths) (α.psubst σ)
  | .node p W ls vls, σ => .node (p.subst σ.paths) (W.subst σ.paths.lift) ls vls

def AliasCo.psubst : AliasCo s1 → PSub s1 s2 → AliasCo s2
  | .refl p, σ => .refl (p.subst σ.paths)
  | .symm α, σ => .symm (α.psubst σ)
  | .trans α β, σ => .trans (α.psubst σ) (β.psubst σ)
  | .sel α a, σ => .sel (α.psubst σ) a
  | .member P e i, σ => .member (P.psubst σ) (e.psubst σ) i

end

/-- The path an atom names after the substitution is its root's image. -/
@[simp] theorem Atom.path_psubst {s1 s2 : Sig} :
    ∀ (a : Atom s1) (σ : PSub s1 s2), (a.psubst σ).path = (σ.var a.root).path
  | .var _, _ => rfl
  | .cast a _, σ => Atom.path_psubst a σ
  | .foldSelf _ a, σ => Atom.path_psubst a σ
  | .unfoldSelf a, σ => Atom.path_psubst a σ
  | .both _ _ a _, σ => Atom.path_psubst a σ
  | .sngl a _ _, σ => Atom.path_psubst a σ

/-- The path a `PathCo` names after the substitution is its path's image. -/
@[simp] theorem PathCo.path_psubst {s1 s2 : Sig} :
    ∀ (P : PathCo s1) (σ : PSub s1 s2), (P.psubst σ).path = P.path.subst σ.paths
  | .var _, _ => rfl
  | .sel P a _, σ => by
      simp only [PathCo.psubst, PathCo.path, Path.subst, PathCo.path_psubst P σ]
  | .cast P _, σ => PathCo.path_psubst P σ
  | .alias _ _ _, _ => rfl
  | .foldSelf _ P, σ => PathCo.path_psubst P σ
  | .unfoldSelf P, σ => PathCo.path_psubst P σ
  | .both _ _ P _, σ => PathCo.path_psubst P σ
  | .sngl P _ _, σ => PathCo.path_psubst P σ
  | .node _ _ _ _, _ => rfl

end FCdot

end Paths
