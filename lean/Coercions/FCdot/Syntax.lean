import Coercions.FCdot.Debruijn

/-!
# FCdot syntax

Types mention binder blocks `x.ℓ` and nothing else about terms.  Object
types are telescopes of propositions over a self block.  Evidence is a
proof-term language whose endpoints are assigned by typing.  Terms are in
monadic normal form over atoms; an atom is a variable under
erasure-invisible wrappers.
-/

namespace FCdot

/-! ## Types, propositions, telescopes -/

mutual

inductive Ty : Sig → Type where
  | top : Ty s
  | bot : Ty s
  /-- The `ℓ`-name of the block of term binder `x`. -/
  | sel : BVar s .var → Label → Ty s
  /-- Dependent arrow: the codomain may mention the parameter's block. -/
  | pi : Ty s → Ty (s,x) → Ty s
  /-- Object type: propositions over a self block. -/
  | obj : Telescope (s,x) → Ty s

inductive Proposition : Sig → Type where
  | le : Ty s → Ty s → Proposition s
  | eq : Ty s → Ty s → Proposition s
  | has : Label → Proposition s

/-- Telescope of propositions, oldest first.  Propositions do not bind. -/
inductive Telescope : Sig → Type where
  | nil : Telescope s
  | cons : Telescope s → Proposition s → Telescope s

end

deriving instance DecidableEq for Ty, Proposition, Telescope

/-- Length of a telescope. -/
def Telescope.length : Telescope s → Nat
  | .nil => 0
  | .cons Tel _ => Tel.length + 1

/-- `Telescope.At Tel i P`: the `i`-th proposition of `Tel` (from the oldest) is `P`. -/
inductive Telescope.At : Telescope s → Nat → Proposition s → Prop where
  | here : Telescope.At (.cons Tel P) Tel.length P
  | there : Telescope.At Tel i P → Telescope.At (.cons Tel Q) i P

/-- Concatenation of telescopes (second appended after the first). -/
def Telescope.append : Telescope s → Telescope s → Telescope s
  | Tel, .nil => Tel
  | Tel, .cons Tel' P => .cons (Tel.append Tel') P

/-- Lookup by index, executable. -/
def Telescope.get? : Telescope s → Nat → Option (Proposition s)
  | .nil, _ => none
  | .cons Tel P, i => if i = Tel.length then some P else Tel.get? i

/-! ## Renaming of types -/

mutual

def Ty.rename : Ty s1 → Rename s1 s2 → Ty s2
  | .top, _ => .top
  | .bot, _ => .bot
  | .sel x ℓ, ρ => .sel (ρ.var x) ℓ
  | .pi S T, ρ => .pi (S.rename ρ) (T.rename ρ.lift)
  | .obj Tel, ρ => .obj (Tel.rename ρ.lift)

def Proposition.rename : Proposition s1 → Rename s1 s2 → Proposition s2
  | .le S T, ρ => .le (S.rename ρ) (T.rename ρ)
  | .eq S T, ρ => .eq (S.rename ρ) (T.rename ρ)
  | .has ℓ, _ => .has ℓ

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

/-! ## Evidence and atoms -/

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
  /-- Pointwise object coercion from the annotated source telescope: a morphism
      between telescopes under the self block. -/
  | obj : Telescope (s,x) → Morphism (s,x) → LeCo s
  /-- Elimination at an atom: the `i`-th proposition of the target telescope of `e`,
      instantiated at the root of `a`, when that proposition is an inclusion. -/
  | member : Atom s → LeCo s → Nat → LeCo s

/-- Equality evidence. -/
inductive EqCo : Sig → Type where
  | refl : Ty s → EqCo s
  | symm : EqCo s → EqCo s
  | trans : EqCo s → EqCo s → EqCo s
  /-- Definition of a transparent binder's block name. -/
  | def : BVar s .var → Label → EqCo s
  | member : Atom s → LeCo s → Nat → EqCo s

/-- Field-presence evidence. -/
inductive Has : Sig → Type where
  | member : Atom s → LeCo s → Nat → Has s
  /-- Only valid inside the evidence block of an object literal that has the field. -/
  | field : Label → Has s

/-- A morphism into a telescope: one piece of evidence per target proposition, oldest first. -/
inductive Morphism : Sig → Type where
  | nil : Morphism s
  | le : Morphism s → LeCo s → Morphism s
  | eq : Morphism s → EqCo s → Morphism s
  | has : Morphism s → Has s → Morphism s

/-- Atoms: a variable under wrappers that erase to nothing. -/
inductive Atom : Sig → Type where
  | var : BVar s .var → Atom s
  | cast : Atom s → LeCo s → Atom s
  /-- `Rec-I`, annotated with the target telescope. -/
  | foldSelf : Telescope (s,x) → Atom s → Atom s
  | unfoldSelf : Atom s → Atom s

end

/-- The variable under an atom's wrappers. -/
def Atom.root : Atom s → BVar s .var
  | .var x => x
  | .cast a _ => a.root
  | .foldSelf _ a => a.root
  | .unfoldSelf a => a.root

mutual

def LeCo.rename : LeCo s1 → Rename s1 s2 → LeCo s2
  | .refl T, ρ => .refl (T.rename ρ)
  | .trans e f, ρ => .trans (e.rename ρ) (f.rename ρ)
  | .top T, ρ => .top (T.rename ρ)
  | .bot T, ρ => .bot (T.rename ρ)
  | .eqToLe φ, ρ => .eqToLe (φ.rename ρ)
  | .pi e f, ρ => .pi (e.rename ρ) (f.rename ρ.lift)
  | .obj Tel m, ρ => .obj (Tel.rename ρ.lift) (m.rename ρ.lift)
  | .member a e i, ρ => .member (a.rename ρ) (e.rename ρ) i

def EqCo.rename : EqCo s1 → Rename s1 s2 → EqCo s2
  | .refl T, ρ => .refl (T.rename ρ)
  | .symm φ, ρ => .symm (φ.rename ρ)
  | .trans φ ψ, ρ => .trans (φ.rename ρ) (ψ.rename ρ)
  | .def x ℓ, ρ => .def (ρ.var x) ℓ
  | .member a e i, ρ => .member (a.rename ρ) (e.rename ρ) i

def Has.rename : Has s1 → Rename s1 s2 → Has s2
  | .member a e i, ρ => .member (a.rename ρ) (e.rename ρ) i
  | .field ℓ, _ => .field ℓ

def Morphism.rename : Morphism s1 → Rename s1 s2 → Morphism s2
  | .nil, _ => .nil
  | .le m e, ρ => .le (m.rename ρ) (e.rename ρ)
  | .eq m φ, ρ => .eq (m.rename ρ) (φ.rename ρ)
  | .has m h, ρ => .has (m.rename ρ) (h.rename ρ)

def Atom.rename : Atom s1 → Rename s1 s2 → Atom s2
  | .var x, ρ => .var (ρ.var x)
  | .cast a e, ρ => .cast (a.rename ρ) (e.rename ρ)
  | .foldSelf Tel a, ρ => .foldSelf (Tel.rename ρ.lift) (a.rename ρ)
  | .unfoldSelf a, ρ => .unfoldSelf (a.rename ρ)

end

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
  /-- Object literal: declared telescope, block witnesses (absent labels are `⊤`),
      evidence for the telescope at the transparent self binder, and fields. -/
  | obj : Telescope (s,x) → Witnesses (s,x) → Morphism (s,x) → Fields (s,x) → Value s
  /-- Adapted value: a wrapper, not a computation. -/
  | cast : Value s → LeCo s → Value s

inductive Witnesses : Sig → Type where
  | nil : Witnesses s
  | cons : Witnesses s → Label → Ty s → Witnesses s

inductive Fields : Sig → Type where
  | nil : Fields s
  | cons : Fields s → Label → Tm s → Fields s

end

/-- Witness lookup; undefined labels are `⊤`. -/
def Witnesses.get : Witnesses s → Label → Ty s
  | .nil, _ => .top
  | .cons W ℓ' T, ℓ => if ℓ = ℓ' then T else W.get ℓ

/-- Field lookup. -/
def Fields.get? : Fields s → Label → Option (Tm s)
  | .nil, _ => none
  | .cons F ℓ' t, ℓ => if ℓ = ℓ' then some t else F.get? ℓ

/-- Field presence, as a proposition on the syntax. -/
def Fields.Has (F : Fields s) (ℓ : Label) : Prop := (F.get? ℓ).isSome

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
  | .obj Tel W E F, ρ => .obj (Tel.rename ρ.lift) (W.rename ρ.lift) (E.rename ρ.lift) (F.rename ρ.lift)
  | .cast v e, ρ => .cast (v.rename ρ) (e.rename ρ)

def Witnesses.rename : Witnesses s1 → Rename s1 s2 → Witnesses s2
  | .nil, _ => .nil
  | .cons W ℓ T, ρ => .cons (W.rename ρ) ℓ (T.rename ρ)

def Fields.rename : Fields s1 → Rename s1 s2 → Fields s2
  | .nil, _ => .nil
  | .cons F ℓ t, ρ => .cons (F.rename ρ) ℓ (t.rename ρ)

end

def Tm.weaken (t : Tm s) : Tm (s,,k) := t.rename Rename.succ
def Atom.weaken (a : Atom s) : Atom (s,,k) := a.rename Rename.succ
def Value.weaken (v : Value s) : Value (s,,k) := v.rename Rename.succ
def LeCo.weaken (e : LeCo s) : LeCo (s,,k) := e.rename Rename.succ

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
  | .obj Tel m, σ => .obj (Tel.rename σ.root.lift) (m.subst σ.lift)
  | .member a e i, σ => .member (a.subst σ) (e.subst σ) i

def EqCo.subst : EqCo s1 → Subst s1 s2 → EqCo s2
  | .refl T, σ => .refl (T.rename σ.root)
  | .symm φ, σ => .symm (φ.subst σ)
  | .trans φ ψ, σ => .trans (φ.subst σ) (ψ.subst σ)
  | .def x ℓ, σ => .def (σ.root.var x) ℓ
  | .member a e i, σ => .member (a.subst σ) (e.subst σ) i

def Has.subst : Has s1 → Subst s1 s2 → Has s2
  | .member a e i, σ => .member (a.subst σ) (e.subst σ) i
  | .field ℓ, _ => .field ℓ

def Morphism.subst : Morphism s1 → Subst s1 s2 → Morphism s2
  | .nil, _ => .nil
  | .le m e, σ => .le (m.subst σ) (e.subst σ)
  | .eq m φ, σ => .eq (m.subst σ) (φ.subst σ)
  | .has m h, σ => .has (m.subst σ) (h.subst σ)

def Atom.subst : Atom s1 → Subst s1 s2 → Atom s2
  | .var x, σ => σ.var x
  | .cast a e, σ => .cast (a.subst σ) (e.subst σ)
  | .foldSelf Tel a, σ => .foldSelf (Tel.rename σ.root.lift) (a.subst σ)
  | .unfoldSelf a, σ => .unfoldSelf (a.subst σ)

end

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
  | .obj Tel W E F, σ =>
      .obj (Tel.rename σ.root.lift) (W.rename σ.root.lift) (E.subst σ.lift) (F.subst σ.lift)
  | .cast v e, σ => .cast (v.subst σ) (e.subst σ)

def Fields.subst : Fields s1 → Subst s1 s2 → Fields s2
  | .nil, _ => .nil
  | .cons F ℓ t, σ => .cons (F.subst σ) ℓ (t.subst σ)

end

/-- Instantiate the innermost binder of a term by an atom. -/
def Tm.substAtom (t : Tm (s,x)) (a : Atom s) : Tm s := t.subst (Subst.single a)

end FCdot
