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

/-- The top type is the object type with no propositions: every type is
included in it, and it says nothing about its inhabitants. -/
@[match_pattern] abbrev Ty.top : Ty s := .obj .nil

/-! ### Notation for types

`⊤` (the empty object type `μ .nil`), `⊥`, `x ∙ ℓ` (the `ℓ`-name of `x`'s
block), `Π(S) T`, `μ Tel` (object type; the self binder is implicit),
propositions `S ⊑ T`, `S ≐ T`, `∋ ℓ`, and telescopes `Tel ▹ P`. -/

scoped notation "⊤" => Ty.top
scoped notation "⊥" => Ty.bot
scoped infix:80 " ∙ " => Ty.sel
scoped notation:max "Π(" S ") " T:max => Ty.pi S T
scoped prefix:max "μ " => Ty.obj
scoped infix:70 " ⊑ " => Proposition.le
scoped infix:70 " ≐ " => Proposition.eq
scoped prefix:max "∋ " => Proposition.has
scoped infixl:65 " ▹ " => Telescope.cons

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

/-! ### Notation for weakening and instantiation

`T↑` weakens under a new binder; `T⟦y⟧` instantiates the innermost binder. -/

scoped postfix:max "↑" => Ty.weaken
scoped postfix:max "↑" => Telescope.weaken
scoped postfix:max "↑" => Proposition.weaken
scoped notation:max T:max "⟦" y "⟧" => Ty.substVar T y
scoped notation:max T:max "⟦" y "⟧" => Telescope.substVar T y
scoped notation:max T:max "⟦" y "⟧" => Proposition.substVar T y

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

/-- One side of a template: an optional closed coercion. -/
inductive Side : Sig → Type where
  | none : Side s
  | some : LeCo s → Side s

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

/-- Atoms: a variable under wrappers that erase to nothing. -/
inductive Atom : Sig → Type where
  | var : BVar s .var → Atom s
  | cast : Atom s → LeCo s → Atom s
  /-- `Rec-I`, annotated with the target telescope. -/
  | foldSelf : Telescope (s,x) → Atom s → Atom s
  | unfoldSelf : Atom s → Atom s
  /-- `And-I`: two typings of the same root, at the concatenated telescope. -/
  | both : Telescope (s,x) → Telescope (s,x) → Atom s → Atom s → Atom s

end

/-- The variable under an atom's wrappers. -/
def Atom.root : Atom s → BVar s .var
  | .var x => x
  | .cast a _ => a.root
  | .foldSelf _ a => a.root
  | .unfoldSelf a => a.root
  | .both _ _ a _ => a.root

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

def Side.rename : Side s1 → Rename s1 s2 → Side s2
  | .none, _ => .none
  | .some e, ρ => .some (e.rename ρ)

def Morphism.rename : Morphism s1 → Rename s1 s2 → Morphism s2
  | .nil, _ => .nil
  | .le m pre h post, ρ => .le (m.rename ρ) (pre.rename ρ) h (post.rename ρ)
  | .eq m j b, ρ => .eq (m.rename ρ) j b
  | .has m j, ρ => .has (m.rename ρ) j

def Atom.rename : Atom s1 → Rename s1 s2 → Atom s2
  | .var x, ρ => .var (ρ.var x)
  | .cast a e, ρ => .cast (a.rename ρ) (e.rename ρ)
  | .foldSelf Tel a, ρ => .foldSelf (Tel.rename ρ.lift) (a.rename ρ)
  | .unfoldSelf a, ρ => .unfoldSelf (a.rename ρ)
  | .both Tel₁ Tel₂ a b, ρ => .both (Tel₁.rename ρ.lift) (Tel₂.rename ρ.lift) (a.rename ρ) (b.rename ρ)

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
  /-- Object literal: block witnesses (absent labels are `⊤`) and fields.  Its
      precise type is the telescope generated from them (`Telescope.ofLiteral`). -/
  | obj : Witnesses (s,x) → Fields (s,x) → Value s
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

/-- The precise telescope of an object literal: its definitions, then its fields. -/
def Telescope.ofLiteral (W : Witnesses (s,x)) (labels : List Label) : Telescope (s,x) :=
  W.eqEntries.hasEntries labels

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

scoped postfix:max "↑" => Tm.weaken
scoped postfix:max "↑" => Atom.weaken
scoped postfix:max "↑" => Value.weaken
scoped postfix:max "↑" => LeCo.weaken

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

def Side.subst : Side s1 → Subst s1 s2 → Side s2
  | .none, _ => .none
  | .some e, σ => .some (e.subst σ)

def Morphism.subst : Morphism s1 → Subst s1 s2 → Morphism s2
  | .nil, _ => .nil
  | .le m pre h post, σ => .le (m.subst σ) (pre.subst σ) h (post.subst σ)
  | .eq m j b, σ => .eq (m.subst σ) j b
  | .has m j, σ => .has (m.subst σ) j

def Atom.subst : Atom s1 → Subst s1 s2 → Atom s2
  | .var x, σ => σ.var x
  | .cast a e, σ => .cast (a.subst σ) (e.subst σ)
  | .foldSelf Tel a, σ => .foldSelf (Tel.rename σ.root.lift) (a.subst σ)
  | .unfoldSelf a, σ => .unfoldSelf (a.subst σ)
  | .both Tel₁ Tel₂ a b, σ =>
      .both (Tel₁.rename σ.root.lift) (Tel₂.rename σ.root.lift) (a.subst σ) (b.subst σ)

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
  | .obj W F, σ => .obj (W.rename σ.root.lift) (F.subst σ.lift)
  | .cast v e, σ => .cast (v.subst σ) (e.subst σ)

def Fields.subst : Fields s1 → Subst s1 s2 → Fields s2
  | .nil, _ => .nil
  | .cons F ℓ t, σ => .cons (F.subst σ) ℓ (t.subst σ)

end

/-- Instantiate the innermost binder of a term by an atom. -/
def Tm.substAtom (t : Tm (s,x)) (a : Atom s) : Tm s := t.subst (Subst.single a)

end FCdot
