import Coercions.CapturesCC.FCdot.Debruijn

namespace CapturesCC

/-!
# FCdot syntax

Types mention binder blocks `x.ℓ` and nothing else about terms.  A type is a
*shape* with a *capture set* beside it, `S ^ C`; shapes are what the vanilla
line called types, plus the inert box former `□ T`.  Object shapes are
telescopes of propositions over a self block.  Evidence is a proof-term
language whose endpoints are assigned by typing: `ShapeCo` between shapes,
`CapCo` between capture sets, and `LeCo` the pair of the two.  Terms are in
monadic normal form over atoms; an atom is a variable under
erasure-invisible wrappers.  A box is a *value* (`Value.box`) and an
unboxing a *term* (`Tm.unbox`), not atom wrappers, so that the capability an
atom denotes is always the capability of its root.
-/

namespace FCdot

/-! ## Capture sets

A capture atom is a term binder `{x}`, a capture binder `{κ}`, or the
capture name `ℓ` of the block of a term binder, `{x∙ℓ}`.  A capture set is a
list of atoms, read as the finite set of its members. -/

inductive CapAtom : Sig → Type where
  /-- `{x}`, the capability of a term binder. -/
  | var : BVar s .var → CapAtom s
  /-- `{κ}`, a capture binder. -/
  | cvar : BVar s .cap → CapAtom s
  /-- `{x∙ℓ}`, the capture set named `ℓ` in the block of `x`. -/
  | name : BVar s .var → Label → CapAtom s
deriving DecidableEq, Repr

/-- A capture set: a list of atoms, read as a finite set. -/
abbrev CaptureSet (s : Sig) : Type := List (CapAtom s)

/-- Union of capture sets is concatenation of the underlying lists. -/
instance CaptureSet.instUnion : Union (CaptureSet s) := ⟨List.append⟩

@[simp] theorem CaptureSet.union_def (C D : CaptureSet s) : C ∪ D = C ++ D := rfl

/-- Membership test. -/
def CaptureSet.elem : CaptureSet s → CapAtom s → Bool
  | [], _ => false
  | b :: C, a => if a = b then true else CaptureSet.elem C a

theorem CaptureSet.elem_iff {s : Sig} {a : CapAtom s} :
    ∀ C : CaptureSet s, C.elem a = true ↔ a ∈ C
  | [] => by simp [CaptureSet.elem]
  | b :: C => by
      by_cases h : a = b
      · simp [CaptureSet.elem, h]
      · simp [CaptureSet.elem, h, List.mem_cons, CaptureSet.elem_iff C]

/-- Every atom of the first set is an atom of the second, decided. -/
def CaptureSet.subset : CaptureSet s → CaptureSet s → Bool
  | [], _ => true
  | a :: C, D => D.elem a && CaptureSet.subset C D

/-- Every atom of the first set is an atom of the second, as a proposition. -/
def CaptureSet.Subset (C D : CaptureSet s) : Prop := ∀ a, a ∈ C → a ∈ D

theorem CaptureSet.subset_iff {s : Sig} :
    ∀ C D : CaptureSet s, C.subset D = true ↔ C.Subset D
  | [], D => by
      simp only [CaptureSet.subset, CaptureSet.Subset]
      refine ⟨fun _ a ha => ?_, fun _ => trivial⟩
      cases ha
  | a :: C, D => by
      simp only [CaptureSet.subset, Bool.and_eq_true, CaptureSet.elem_iff,
        CaptureSet.subset_iff C D, CaptureSet.Subset]
      constructor
      · intro ⟨ha, hC⟩ b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hC b hb
      · intro h
        exact ⟨h a (List.mem_cons.mpr (Or.inl rfl)),
          fun b hb => h b (List.mem_cons.mpr (Or.inr hb))⟩

instance CaptureSet.instDecidableSubset (C D : CaptureSet s) : Decidable (C.Subset D) :=
  if h : C.subset D = true then
    .isTrue ((CaptureSet.subset_iff C D).mp h)
  else
    .isFalse (fun hs => h ((CaptureSet.subset_iff C D).mpr hs))

/-- Renaming of a capture atom: all three forms carry variables only. -/
def CapAtom.rename : CapAtom s1 → Rename s1 s2 → CapAtom s2
  | .var x, ρ => .var (ρ.var x)
  | .cvar κ, ρ => .cvar (ρ.var κ)
  | .name x ℓ, ρ => .name (ρ.var x) ℓ

/-- Renaming of a capture set is pointwise. -/
def CaptureSet.rename (C : CaptureSet s1) (ρ : Rename s1 s2) : CaptureSet s2 :=
  C.map (fun a => a.rename ρ)

/-! ## Shapes, types, propositions, telescopes -/

mutual

/-- Shapes: what the vanilla line called types, plus the box former. -/
inductive Shape : Sig → Type where
  | bot : Shape s
  /-- The `ℓ`-name of the block of term binder `x`. -/
  | sel : BVar s .var → Label → Shape s
  /-- Dependent arrow: the codomain may mention the parameter's block.  The
      domain is a `Dom s` and the codomain a `Cod s`. -/
  | pi : Ty s → Ty (s,x) → Shape s
  /-- Object shape: propositions over a self block. -/
  | obj : Telescope (s,x) → Shape s
  /-- The box former: inert, neither a proposition nor a telescope entry. -/
  | box : Ty s → Shape s

/-- A type is a shape with a capture set, written `S ^ C`. -/
inductive Ty : Sig → Type where
  | capt : CaptureSet s → Shape s → Ty s

inductive Proposition : Sig → Type where
  | le : Shape s → Shape s → Proposition s
  | eq : Shape s → Shape s → Proposition s
  | has : Label → Proposition s
  /-- Self-bound: the object itself is included in the shape.  By convention
      the shape is always a weakened closed shape, so a bound never mentions
      the self block. -/
  | bnd : Shape s → Proposition s
  /-- Subcapturing between capture sets.  Like every proposition it lives
      under the self, and its right side may mention the self block. -/
  | leC : CaptureSet s → CaptureSet s → Proposition s
  /-- Equality of capture sets, under the self as well. -/
  | eqC : CaptureSet s → CaptureSet s → Proposition s

/-- Telescope of propositions, oldest first.  Propositions do not bind. -/
inductive Telescope : Sig → Type where
  | nil : Telescope s
  | cons : Telescope s → Proposition s → Telescope s

end

deriving instance DecidableEq for Shape, Ty, Proposition, Telescope

/-- The domain of an arrow, behind one name. -/
abbrev Dom (s : Sig) : Type := Ty s
/-- The codomain of an arrow, behind one name: it may mention the parameter. -/
abbrev Cod (s : Sig) : Type := Ty (s,x)

/-- The top shape is the object shape with no propositions: every shape is
included in it, and it says nothing about its inhabitants. -/
@[match_pattern] abbrev Shape.top : Shape s := .obj .nil

/-- A shape with the empty capture set. -/
abbrev Ty.pure (S : Shape s) : Ty s := .capt [] S

/-! ### Notation for shapes and types

`⊤` (the empty object shape `μ .nil`), `⊥`, `x ∙ ℓ` (the `ℓ`-name of `x`'s
block), `Π(S) T`, `μ Tel` (object shape; the self binder is implicit),
`□ T` (the box shape), `S ^ C` (the type with shape `S` and capture set `C`),
propositions `S ⊑ T`, `S ≐ T`, `∋ ℓ`, and telescopes `Tel ▹ P`. -/

scoped notation "⊤" => Shape.top
scoped notation "⊥" => Shape.bot
scoped infix:80 " ∙ " => Shape.sel
scoped notation:max "Π(" S ") " T:max => Shape.pi S T
scoped prefix:max "μ " => Shape.obj
scoped prefix:max "□ " => Shape.box
scoped notation:75 S:76 " ^ " C:76 => Ty.capt C S
scoped infix:70 " ⊑ " => Proposition.le
scoped infix:70 " ≐ " => Proposition.eq
scoped prefix:max "∋ " => Proposition.has
scoped prefix:75 "⊑ " => Proposition.bnd
scoped infix:70 " ⊑ᶜ " => Proposition.leC
scoped infix:70 " ≐ᶜ " => Proposition.eqC
scoped infixl:65 " ▹ " => Telescope.cons

/-- The shape of a type: a type is a shape with a capture set beside it, and
this is the shape.  The vanilla line's `Ty` is exactly this shape; a
statement that read a vanilla type reads this projection. -/
def Ty.shape : Ty s → Shape s
  | .capt _ S => S

@[simp] theorem Ty.shape_capt (C : CaptureSet s) (S : Shape s) : (S ^ C).shape = S := rfl

/-- A type is its shape with its capture set. -/
theorem Ty.shape_eq_iff {T : Ty s} {S : Shape s} : T.shape = S ↔ ∃ C, T = S ^ C := by
  cases T with
  | capt C S' =>
      constructor
      · rintro rfl; exact ⟨C, rfl⟩
      · rintro ⟨C', h⟩; cases h; rfl

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

/-! ## Renaming of shapes and types -/

mutual

def Shape.rename : Shape s1 → Rename s1 s2 → Shape s2
  | .bot, _ => .bot
  | .sel x ℓ, ρ => .sel (ρ.var x) ℓ
  | .pi S T, ρ => .pi (S.rename ρ) (T.rename ρ.lift)
  | .obj Tel, ρ => .obj (Tel.rename ρ.lift)
  | .box T, ρ => .box (T.rename ρ)

def Ty.rename : Ty s1 → Rename s1 s2 → Ty s2
  | .capt C S, ρ => .capt (C.rename ρ) (S.rename ρ)

def Proposition.rename : Proposition s1 → Rename s1 s2 → Proposition s2
  | .le S T, ρ => .le (S.rename ρ) (T.rename ρ)
  | .eq S T, ρ => .eq (S.rename ρ) (T.rename ρ)
  | .has ℓ, _ => .has ℓ
  | .bnd T, ρ => .bnd (T.rename ρ)
  | .leC C D, ρ => .leC (C.rename ρ) (D.rename ρ)
  | .eqC C D, ρ => .eqC (C.rename ρ) (D.rename ρ)

def Telescope.rename : Telescope s1 → Rename s1 s2 → Telescope s2
  | .nil, _ => .nil
  | .cons Tel P, ρ => .cons (Tel.rename ρ) (P.rename ρ)

end

def CapAtom.weaken (a : CapAtom s) : CapAtom (s,,k) := a.rename Rename.succ
def CaptureSet.weaken (C : CaptureSet s) : CaptureSet (s,,k) := C.rename Rename.succ
def Shape.weaken (S : Shape s) : Shape (s,,k) := S.rename Rename.succ
def Ty.weaken (T : Ty s) : Ty (s,,k) := T.rename Rename.succ
def Telescope.weaken (Tel : Telescope s) : Telescope (s,,k) := Tel.rename Rename.succ
def Proposition.weaken (P : Proposition s) : Proposition (s,,k) := P.rename Rename.succ

/-- Instantiate the innermost binder of a shape or type by a variable. -/
def CaptureSet.substVar (C : CaptureSet (s,,k)) (y : BVar s k) : CaptureSet s :=
  C.rename (Rename.subst y)
def Shape.substVar (S : Shape (s,,k)) (y : BVar s k) : Shape s := S.rename (Rename.subst y)
def Ty.substVar (T : Ty (s,,k)) (y : BVar s k) : Ty s := T.rename (Rename.subst y)
def Proposition.substVar (P : Proposition (s,,k)) (y : BVar s k) : Proposition s :=
  P.rename (Rename.subst y)
def Telescope.substVar (Tel : Telescope (s,,k)) (y : BVar s k) : Telescope s :=
  Tel.rename (Rename.subst y)

/-- The capture set of a type: a type is a shape with a capture set beside
it, and this is the capture set. -/
def Ty.captureSet : Ty s → CaptureSet s
  | .capt C _ => C

@[simp] theorem Ty.captureSet_capt (C : CaptureSet s) (S : Shape s) :
    (Ty.capt C S).captureSet = C := rfl

@[simp] theorem Ty.captureSet_weaken (T : Ty s) :
    (T.weaken (k := k)).captureSet = T.captureSet.weaken := by
  cases T; rfl

/-! ### Notation for weakening and instantiation

`T↑` weakens under a new binder of any kind; `T⟦y⟧` instantiates the
innermost binder. -/

scoped postfix:max "↑" => CaptureSet.weaken
scoped postfix:max "↑" => Shape.weaken
scoped postfix:max "↑" => Ty.weaken
scoped postfix:max "↑" => Telescope.weaken
scoped postfix:max "↑" => Proposition.weaken
scoped notation:max T:max "⟦" y "⟧" => CaptureSet.substVar T y
scoped notation:max T:max "⟦" y "⟧" => Shape.substVar T y
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

/-- A hole of a capture template: the `j`-th proposition of the source
telescope, read as an inclusion of capture sets.  A capture equality may be
read in either direction. -/
inductive HoleC : Type where
  | leC : Nat → HoleC
  | eqC : Nat → HoleC
  | eqSymC : Nat → HoleC
deriving DecidableEq

mutual

/-- Directed inclusion evidence between shapes.  No symmetry. -/
inductive ShapeCo : Sig → Type where
  | refl : Shape s → ShapeCo s
  | trans : ShapeCo s → ShapeCo s → ShapeCo s
  | top : Shape s → ShapeCo s
  | bot : Shape s → ShapeCo s
  | eqToLe : EqCo s → ShapeCo s
  /-- Contravariant domain, covariant codomain under the parameter binder.
      Both are coercions between types. -/
  | pi : LeCo s → LeCo (s,x) → ShapeCo s
  /-- Object coercion between closed telescopes: the source telescope is
      annotated; the morphism proves each target proposition by a *template*
      (a closed coercion, a source proposition, a closed coercion). -/
  | obj : Telescope (s,x) → Morphism s → ShapeCo s
  /-- Pairing: two coercions into object shapes give one into the
      concatenation of their telescopes. -/
  | pair : Telescope (s,x) → Telescope (s,x) → ShapeCo s → ShapeCo s → ShapeCo s
  /-- The annotated object shape is below its `i`-th bound. -/
  | bound : Telescope (s,x) → Nat → ShapeCo s
  /-- An `S` below `T` is an `S` below the one-bound object shape `μ [⊑ T↑]`. -/
  | intoBnd : ShapeCo s → ShapeCo s
  /-- Elimination at an atom: the `i`-th proposition of the target telescope of `e`,
      instantiated at the root of `a`, when that proposition is an inclusion. -/
  | member : Atom s → ShapeCo s → Nat → ShapeCo s
  /-- The box former is covariant in the boxed type. -/
  | boxed : LeCo s → ShapeCo s

/-- Inclusion evidence between capture sets. -/
inductive CapCo : Sig → Type where
  | refl : CaptureSet s → CapCo s
  | trans : CapCo s → CapCo s → CapCo s
  /-- A syntactic inclusion `C₁ ⊆ C₂`, decided at typing. -/
  | elem : CaptureSet s → CaptureSet s → CapCo s
  | union : CapCo s → CapCo s → CapCo s
  /-- An atom's own capture set is below the capture set of its type. -/
  | capvar : Atom s → CapCo s
  /-- Elimination at an atom: the `i`-th proposition of the target telescope
      of `e`, instantiated at the root of `a`, when that proposition is a
      subcapturing proposition. -/
  | member : Atom s → ShapeCo s → Nat → CapCo s
  /-- An equality of capture sets read as an inclusion. -/
  | eqToLe : CapEq s → CapCo s

/-- Equality evidence between capture sets. -/
inductive CapEq : Sig → Type where
  | refl : CaptureSet s → CapEq s
  | symm : CapEq s → CapEq s
  | trans : CapEq s → CapEq s → CapEq s
  /-- Definition of a transparent binder's capture name.  (`defᶜ` of the
      plan: `ᶜ` is not a legal Lean identifier character.) -/
  | defC : BVar s .var → Label → CapEq s
  | member : Atom s → ShapeCo s → Nat → CapEq s

/-- One step of a capture-template side: closed capture evidence, weakened
under the self, or a syntactic inclusion of sets that may mention the self
(plan-5a (c-2′)). -/
inductive CapStep : Sig → Type where
  | closed : CapCo s → CapStep s
  | incl : CaptureSet (s,x) → CaptureSet (s,x) → CapStep s

/-- A capture-template side: a chain of steps, oldest first.  It is the list
of its steps; chains compose by concatenation. -/
inductive SideC : Sig → Type where
  | nil : SideC s
  | cons : CapStep s → SideC s → SideC s

/-- Inclusion evidence between types: a shape coercion and a capture
coercion. -/
inductive LeCo : Sig → Type where
  | capt : ShapeCo s → CapCo s → LeCo s

/-- Equality evidence between shapes. -/
inductive EqCo : Sig → Type where
  | refl : Shape s → EqCo s
  | symm : EqCo s → EqCo s
  | trans : EqCo s → EqCo s → EqCo s
  /-- Definition of a transparent binder's block name. -/
  | def : BVar s .var → Label → EqCo s
  | member : Atom s → ShapeCo s → Nat → EqCo s

/-- Field-presence evidence. -/
inductive Has : Sig → Type where
  | member : Atom s → ShapeCo s → Nat → Has s
  /-- Only valid inside the evidence block of an object literal that has the field. -/
  | field : Label → Has s

/-- One side of a template: an optional closed shape coercion. -/
inductive Side : Sig → Type where
  | none : Side s
  | some : ShapeCo s → Side s

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
      object shape. -/
  | bnd : Morphism s → ShapeCo s → Morphism s
  /-- A template for a target subcapturing proposition: a side chain, a hole
      naming a source capture proposition, and a side chain. -/
  | leC : Morphism s → SideC s → HoleC → SideC s → Morphism s
  /-- A target capture equality is a source capture equality, possibly
      flipped. -/
  | eqC : Morphism s → Nat → Bool → Morphism s

/-- Atoms: a variable under wrappers that erase to nothing. -/
inductive Atom : Sig → Type where
  | var : BVar s .var → Atom s
  | cast : Atom s → LeCo s → Atom s
  /-- `Rec-I`, annotated with the target telescope. -/
  | foldSelf : Telescope (s,x) → Atom s → Atom s
  | unfoldSelf : Atom s → Atom s
  /-- `And-I`: two typings of the same root, at the concatenated telescope. -/
  | both : Telescope (s,x) → Telescope (s,x) → Atom s → Atom s → Atom s
  /-- Recapturing: the atom keeps its shape and takes a wider capture set. -/
  | recap : Atom s → CapCo s → Atom s

end

deriving instance DecidableEq for ShapeCo, CapCo, CapEq, CapStep, SideC, LeCo, EqCo, Has,
  Side, Morphism, Atom

/-- The variable under an atom's wrappers. -/
def Atom.root : Atom s → BVar s .var
  | .var x => x
  | .cast a _ => a.root
  | .foldSelf _ a => a.root
  | .unfoldSelf a => a.root
  | .both _ _ a _ => a.root
  | .recap a _ => a.root

/-- Concatenation of capture-template sides. -/
def SideC.append : SideC s → SideC s → SideC s
  | .nil, q => q
  | .cons st q, q' => .cons st (q.append q')

instance : Append (SideC s) := ⟨SideC.append⟩

mutual

def ShapeCo.rename : ShapeCo s1 → Rename s1 s2 → ShapeCo s2
  | .refl T, ρ => .refl (T.rename ρ)
  | .trans e f, ρ => .trans (e.rename ρ) (f.rename ρ)
  | .top T, ρ => .top (T.rename ρ)
  | .bot T, ρ => .bot (T.rename ρ)
  | .eqToLe φ, ρ => .eqToLe (φ.rename ρ)
  | .pi e f, ρ => .pi (e.rename ρ) (f.rename ρ.lift)
  | .obj Tel m, ρ => .obj (Tel.rename ρ.lift) (m.rename ρ)
  | .pair Tel₁ Tel₂ e f, ρ =>
      .pair (Tel₁.rename ρ.lift) (Tel₂.rename ρ.lift) (e.rename ρ) (f.rename ρ)
  | .bound Tel i, ρ => .bound (Tel.rename ρ.lift) i
  | .intoBnd e, ρ => .intoBnd (e.rename ρ)
  | .member a e i, ρ => .member (a.rename ρ) (e.rename ρ) i
  | .boxed d, ρ => .boxed (d.rename ρ)

def CapCo.rename : CapCo s1 → Rename s1 s2 → CapCo s2
  | .refl C, ρ => .refl (C.rename ρ)
  | .trans f g, ρ => .trans (f.rename ρ) (g.rename ρ)
  | .elem C D, ρ => .elem (C.rename ρ) (D.rename ρ)
  | .union f g, ρ => .union (f.rename ρ) (g.rename ρ)
  | .capvar a, ρ => .capvar (a.rename ρ)
  | .member a e i, ρ => .member (a.rename ρ) (e.rename ρ) i
  | .eqToLe φ, ρ => .eqToLe (φ.rename ρ)

def CapEq.rename : CapEq s1 → Rename s1 s2 → CapEq s2
  | .refl C, ρ => .refl (C.rename ρ)
  | .symm φ, ρ => .symm (φ.rename ρ)
  | .trans φ ψ, ρ => .trans (φ.rename ρ) (ψ.rename ρ)
  | .defC x ℓ, ρ => .defC (ρ.var x) ℓ
  | .member a e i, ρ => .member (a.rename ρ) (e.rename ρ) i

def CapStep.rename : CapStep s1 → Rename s1 s2 → CapStep s2
  | .closed f, ρ => .closed (f.rename ρ)
  | .incl C D, ρ => .incl (C.rename ρ.lift) (D.rename ρ.lift)

def SideC.rename : SideC s1 → Rename s1 s2 → SideC s2
  | .nil, _ => .nil
  | .cons st q, ρ => .cons (st.rename ρ) (q.rename ρ)

def LeCo.rename : LeCo s1 → Rename s1 s2 → LeCo s2
  | .capt e f, ρ => .capt (e.rename ρ) (f.rename ρ)

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
  | .bnd m e, ρ => .bnd (m.rename ρ) (e.rename ρ)
  | .leC m q h q', ρ => .leC (m.rename ρ) (q.rename ρ) h (q'.rename ρ)
  | .eqC m j b, ρ => .eqC (m.rename ρ) j b

def Atom.rename : Atom s1 → Rename s1 s2 → Atom s2
  | .var x, ρ => .var (ρ.var x)
  | .cast a e, ρ => .cast (a.rename ρ) (e.rename ρ)
  | .foldSelf Tel a, ρ => .foldSelf (Tel.rename ρ.lift) (a.rename ρ)
  | .unfoldSelf a, ρ => .unfoldSelf (a.rename ρ)
  | .both Tel₁ Tel₂ a b, ρ =>
      .both (Tel₁.rename ρ.lift) (Tel₂.rename ρ.lift) (a.rename ρ) (b.rename ρ)
  | .recap a f, ρ => .recap (a.rename ρ) (f.rename ρ)

end

/-! ## Terms and values -/

/-- Capture witnesses of an object literal: one capture set per label.  An
absent label reads as the empty set.  (`Wᶜ` of the plan.) -/
inductive CapWitnesses : Sig → Type where
  | nil : CapWitnesses s
  | cons : CapWitnesses s → Label → CaptureSet s → CapWitnesses s
deriving DecidableEq

/-- Capture-witness lookup; undefined labels are the empty set. -/
def CapWitnesses.get : CapWitnesses s → Label → CaptureSet s
  | .nil, _ => []
  | .cons W ℓ' C, ℓ => if ℓ = ℓ' then C else W.get ℓ

/-- Labels of a capture-witness list, oldest first. -/
def CapWitnesses.labels : CapWitnesses s → List Label
  | .nil => []
  | .cons W ℓ _ => W.labels ++ [ℓ]

/-- Only a listed label has a capture witness of its own; an unlisted one
reads as the empty set. -/
theorem CapWitnesses.get_of_not_mem_labels {s : Sig} :
    ∀ (W : CapWitnesses s) {ℓ : Label}, ℓ ∉ W.labels → W.get ℓ = []
  | .nil, _, _ => rfl
  | .cons W ℓ' C, ℓ, h => by
      have h1 : ℓ ∉ W.labels := fun hm => h (by simp [CapWitnesses.labels, hm])
      have h2 : ℓ ≠ ℓ' := fun he => h (by simp [CapWitnesses.labels, he])
      rw [show CapWitnesses.get (CapWitnesses.cons W ℓ' C) ℓ = W.get ℓ by
        simp [CapWitnesses.get, h2]]
      exact CapWitnesses.get_of_not_mem_labels W h1

def CapWitnesses.rename : CapWitnesses s1 → Rename s1 s2 → CapWitnesses s2
  | .nil, _ => .nil
  | .cons W ℓ C, ρ => .cons (W.rename ρ) ℓ (C.rename ρ)

mutual

inductive Tm : Sig → Type where
  | atom : Atom s → Tm s
  | val : Value s → Tm s
  | app : Atom s → Atom s → Tm s
  /-- Field projection, annotated with the field-presence evidence. -/
  | proj : Atom s → Label → Has s → Tm s
  /-- `let x = t in u ⦃U'; f⦄`.  The let declares the use set `U'` of its
      body and carries the avoidance evidence `f` putting the body's use set
      below `U'` weakened.  `U'` is data, so that `uses` is structural. -/
  | «let» : Tm s → Tm (s,x) → CaptureSet s → CapCo (s,x) → Tm s
  | cast : Tm s → LeCo s → Tm s
  /-- Unboxing: a term, not an atom.  It reads the atom's box and charges
      the boxed capture set against the declared set `U` by the evidence
      `f`. -/
  | unbox : Atom s → CaptureSet s → CapCo s → Tm s

inductive Value : Sig → Type where
  /-- `λ^A(x : T). t ⦃g⦄`: the assigned capture set `A`, the parameter type,
      the body, and the closing evidence `g` putting the body's use set below
      `A` weakened united with the parameter. -/
  | lam : CaptureSet s → Ty s → Tm (s,x) → CapCo (s,x) → Value s
  /-- Object literal `ν^A(W; Wᶜ; F)`: the assigned capture set, block
      witnesses (absent labels are `⊤`), capture witnesses (absent labels are
      `[]`), and fields.  Its precise shape is the telescope generated from
      them (`Telescope.ofLiteral`). -/
  | obj : CaptureSet s → Witnesses (s,x) → CapWitnesses (s,x) → Fields (s,x) → Value s
  /-- A boxed atom: a value with no witnesses and no fields.  The box shape
      hides the captured set, so a box is pure. -/
  | box : Atom s → Value s
  /-- Adapted value: a wrapper, not a computation. -/
  | cast : Value s → LeCo s → Value s

/-- Block witnesses.  A type witness defines a block name, which is a shape. -/
inductive Witnesses : Sig → Type where
  | nil : Witnesses s
  | cons : Witnesses s → Label → Shape s → Witnesses s

inductive Fields : Sig → Type where
  | nil : Fields s
  /-- `ℓ = t ⦃g⦄`: the field's term with the closing evidence putting its use
      set below the literal's assigned set united with the self. -/
  | cons : Fields s → Label → Tm s → CapCo s → Fields s

end

/-- Witness lookup; undefined labels are `⊤`. -/
def Witnesses.get : Witnesses s → Label → Shape s
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
  | .cons F ℓ' t _, ℓ => if ℓ = ℓ' then some t else F.get? ℓ

/-- Field presence, as a proposition on the syntax. -/
def Fields.Has (F : Fields s) (ℓ : Label) : Prop := (F.get? ℓ).isSome

/-! ## Annotations, use sets, and the inspected root

A value carries the capture set its introduction rule assigns to it: a
lambda and a literal carry it as a field, a box is pure, and a cast keeps
the annotation of the value under it.  A term carries a *use set*, computed
by a total structural function from the sets the syntax declares.  A state
inspects at most one root, the variable whose stored value the next step
reads. -/

/-- The capture set a value's introduction rule assigns to it. -/
def Value.annot : Value s → CaptureSet s
  | .lam A _ _ _ => A
  | .obj A _ _ _ => A
  | .box _ => []
  | .cast v _ => v.annot

@[simp] theorem Value.annot_lam (A : CaptureSet s) (T : Ty s) (t : Tm (s,x))
    (g : CapCo (s,x)) : (Value.lam A T t g).annot = A := rfl

@[simp] theorem Value.annot_obj (A : CaptureSet s) (W : Witnesses (s,x))
    (Wc : CapWitnesses (s,x)) (F : Fields (s,x)) : (Value.obj A W Wc F).annot = A := rfl

@[simp] theorem Value.annot_box (a : Atom s) : (Value.box a).annot = [] := rfl

@[simp] theorem Value.annot_cast (v : Value s) (e : LeCo s) :
    (Value.cast v e).annot = v.annot := rfl

/-- The use set of a term: the capabilities the term may still read.  It is
total and structural, because every set a binder declares is data. -/
def Tm.uses : Tm s → CaptureSet s
  | .atom a => [.var a.root]
  | .val _ => []
  | .app a b => [.var a.root, .var b.root]
  | .proj a _ _ => [.var a.root]
  | .let t _ U _ => t.uses ∪ U
  | .cast t _ => t.uses
  | .unbox a U _ => [.var a.root] ∪ U

@[simp] theorem Tm.uses_atom (a : Atom s) : (Tm.atom a).uses = [.var a.root] := rfl
@[simp] theorem Tm.uses_val (v : Value s) : (Tm.val v).uses = [] := rfl
@[simp] theorem Tm.uses_app (a b : Atom s) :
    (Tm.app a b).uses = [.var a.root, .var b.root] := rfl
@[simp] theorem Tm.uses_proj (a : Atom s) (ℓ : Label) (h : Has s) :
    (Tm.proj a ℓ h).uses = [.var a.root] := rfl
@[simp] theorem Tm.uses_let (t : Tm s) (u : Tm (s,x)) (U : CaptureSet s) (f : CapCo (s,x)) :
    (Tm.let t u U f).uses = t.uses ∪ U := rfl
@[simp] theorem Tm.uses_cast (t : Tm s) (e : LeCo s) : (Tm.cast t e).uses = t.uses := rfl
@[simp] theorem Tm.uses_unbox (a : Atom s) (U : CaptureSet s) (f : CapCo s) :
    (Tm.unbox a U f).uses = [.var a.root] ∪ U := rfl

/-- The root a term reads when it steps: the function of an application, the
receiver of a projection, the box of an unboxing.  Every other term reads no
stored value. -/
def Tm.inspects : Tm s → Option (BVar s .var)
  | .app a _ => some a.root
  | .proj a _ _ => some a.root
  | .unbox a _ _ => some a.root
  | _ => none

@[simp] theorem Tm.inspects_app (a b : Atom s) : (Tm.app a b).inspects = some a.root := rfl
@[simp] theorem Tm.inspects_proj (a : Atom s) (ℓ : Label) (h : Has s) :
    (Tm.proj a ℓ h).inspects = some a.root := rfl
@[simp] theorem Tm.inspects_unbox (a : Atom s) (U : CaptureSet s) (f : CapCo s) :
    (Tm.unbox a U f).inspects = some a.root := rfl
@[simp] theorem Tm.inspects_atom (a : Atom s) : (Tm.atom a).inspects = none := rfl
@[simp] theorem Tm.inspects_val (v : Value s) : (Tm.val v).inspects = none := rfl
@[simp] theorem Tm.inspects_let (t : Tm s) (u : Tm (s,x)) (U : CaptureSet s)
    (f : CapCo (s,x)) : (Tm.let t u U f).inspects = none := rfl
@[simp] theorem Tm.inspects_cast (t : Tm s) (e : LeCo s) : (Tm.cast t e).inspects = none := rfl

/-- An inspected root is used.  This is the bridge between the prediction
theorem, which is about use sets, and the steps, which read roots. -/
theorem Tm.inspects_mem_uses {s : Sig} {t : Tm s} {x : BVar s .var}
    (h : t.inspects = some x) : CapAtom.var x ∈ t.uses := by
  cases t with
  | app a b => cases h; simp
  | proj a ℓ hh => cases h; simp
  | unbox a U f => cases h; simp
  | atom a => simp at h
  | val v => simp at h
  | «let» t u U f => simp at h
  | cast t e => simp at h

/-- Definition entries of a literal's witnesses: one `self ∙ ℓ ≐ W₀.get ℓ` per
listed label (a shadowed label gets the outer definition, so every entry is
true of the literal).  Stated for an arbitrary self variable so that the
recursion is structural. -/
def Witnesses.eqEntriesOf (self : BVar s' .var) (W₀ : Witnesses s') : Witnesses s' → Telescope s'
  | .nil => .nil
  | .cons W ℓ _ => W₀.eqEntriesOf self W ▹ self ∙ ℓ ≐ W₀.get ℓ

def Witnesses.eqEntries (W : Witnesses (s,x)) : Telescope (s,x) := W.eqEntriesOf .here W

/-- Capture-definition entries of a literal's capture witnesses: one
`[name self ℓ] ≐ᶜ Wᶜ.get ℓ` per listed label, appended to a telescope.  A
shadowed label gets the outer witness, so every entry is true of the
literal.  Stated for an arbitrary self variable and an arbitrary base so that
the recursion is structural and the entries land after the type block. -/
def CapWitnesses.eqEntriesOf (self : BVar s' .var) (W₀ : CapWitnesses s')
    (base : Telescope s') : CapWitnesses s' → Telescope s'
  | .nil => base
  | .cons W ℓ _ => W₀.eqEntriesOf self base W ▹ [CapAtom.name self ℓ] ≐ᶜ W₀.get ℓ

def CapWitnesses.eqEntries (W : CapWitnesses (s,x)) (base : Telescope (s,x)) :
    Telescope (s,x) := W.eqEntriesOf .here base W

/-- Presence entries for a list of field labels, appended to a telescope. -/
def Telescope.hasEntries : Telescope s → List Label → Telescope s
  | Tel, [] => Tel
  | Tel, ℓ :: ls => (Tel.cons (.has ℓ)).hasEntries ls

/-- The precise telescope of an object literal: its type definitions, then
its capture definitions, then its fields. -/
def Telescope.ofLiteral (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x))
    (labels : List Label) : Telescope (s,x) :=
  (Wc.eqEntries W.eqEntries).hasEntries labels

mutual

def Tm.rename : Tm s1 → Rename s1 s2 → Tm s2
  | .atom a, ρ => .atom (a.rename ρ)
  | .val v, ρ => .val (v.rename ρ)
  | .app a b, ρ => .app (a.rename ρ) (b.rename ρ)
  | .proj a ℓ h, ρ => .proj (a.rename ρ) ℓ (h.rename ρ)
  | .let t u U f, ρ => .let (t.rename ρ) (u.rename ρ.lift) (U.rename ρ) (f.rename ρ.lift)
  | .cast t e, ρ => .cast (t.rename ρ) (e.rename ρ)
  | .unbox a U f, ρ => .unbox (a.rename ρ) (U.rename ρ) (f.rename ρ)

def Value.rename : Value s1 → Rename s1 s2 → Value s2
  | .lam A S t g, ρ => .lam (A.rename ρ) (S.rename ρ) (t.rename ρ.lift) (g.rename ρ.lift)
  | .obj A W Wc F, ρ =>
      .obj (A.rename ρ) (W.rename ρ.lift) (Wc.rename ρ.lift) (F.rename ρ.lift)
  | .box a, ρ => .box (a.rename ρ)
  | .cast v e, ρ => .cast (v.rename ρ) (e.rename ρ)

def Witnesses.rename : Witnesses s1 → Rename s1 s2 → Witnesses s2
  | .nil, _ => .nil
  | .cons W ℓ T, ρ => .cons (W.rename ρ) ℓ (T.rename ρ)

def Fields.rename : Fields s1 → Rename s1 s2 → Fields s2
  | .nil, _ => .nil
  | .cons F ℓ t g, ρ => .cons (F.rename ρ) ℓ (t.rename ρ) (g.rename ρ)

end

def Tm.weaken (t : Tm s) : Tm (s,,k) := t.rename Rename.succ
def Atom.weaken (a : Atom s) : Atom (s,,k) := a.rename Rename.succ
def Value.weaken (v : Value s) : Value (s,,k) := v.rename Rename.succ
def ShapeCo.weaken (e : ShapeCo s) : ShapeCo (s,,k) := e.rename Rename.succ
def CapCo.weaken (f : CapCo s) : CapCo (s,,k) := f.rename Rename.succ
def LeCo.weaken (e : LeCo s) : LeCo (s,,k) := e.rename Rename.succ

scoped postfix:max "↑" => Tm.weaken
scoped postfix:max "↑" => Atom.weaken
scoped postfix:max "↑" => Value.weaken
scoped postfix:max "↑" => ShapeCo.weaken
scoped postfix:max "↑" => CapCo.weaken
scoped postfix:max "↑" => LeCo.weaken

/-! ## Atom substitution

A substitution maps term variables to atoms and capture variables to capture
variables.  Types and evidence only see the root variable, so on them a
substitution acts as the renaming of roots (`Subst.root`); on terms the atom
itself replaces the variable. -/

structure Subst (s1 s2 : Sig) where
  var : BVar s1 .var → Atom s2
  cvar : BVar s1 .cap → BVar s2 .cap

namespace Subst

/-- The renaming of roots induced by a substitution. -/
def root (σ : Subst s1 s2) : Rename s1 s2 where
  var := fun {k} x => match k, x with
    | .var, x => (σ.var x).root
    | .cap, x => σ.cvar x

def lift (σ : Subst s1 s2) : Subst (s1,x) (s2,x) where
  var := fun
    | .here => .var .here
    | .there x => (σ.var x).weaken
  cvar := fun
    | .there x => .there (σ.cvar x)

/-- Pass under a capture binder.  (`liftᶜ` of the plan: `ᶜ` is not a legal
Lean identifier character, so the capture-sort twin of a name carries the
suffix `C`.) -/
def liftC (σ : Subst s1 s2) : Subst (s1,c) (s2,c) where
  var := fun
    | .there x => (σ.var x).weaken
  cvar := fun
    | .here => .here
    | .there x => .there (σ.cvar x)

/-- Substitute the innermost binder by an atom, keep the rest. -/
def single (a : Atom s) : Subst (s,x) s where
  var := fun
    | .here => a
    | .there x => .var x
  cvar := fun
    | .there x => x

def ofRename (ρ : Rename s1 s2) : Subst s1 s2 where
  var := fun x => .var (ρ.var x)
  cvar := fun x => ρ.var x

end Subst

/-- Use the innermost binder under a cast everywhere in a term. -/
def Subst.selfCast (E : LeCo (s,x)) : Subst (s,x) (s,x) where
  var := fun
    | .here => .cast (.var .here) E
    | .there y => .var (.there y)
  cvar := fun
    | .there y => .there y

/-! ### Substitution on evidence, atoms and terms -/

mutual

def ShapeCo.subst : ShapeCo s1 → Subst s1 s2 → ShapeCo s2
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
  | .boxed d, σ => .boxed (d.subst σ)

def CapCo.subst : CapCo s1 → Subst s1 s2 → CapCo s2
  | .refl C, σ => .refl (C.rename σ.root)
  | .trans f g, σ => .trans (f.subst σ) (g.subst σ)
  | .elem C D, σ => .elem (C.rename σ.root) (D.rename σ.root)
  | .union f g, σ => .union (f.subst σ) (g.subst σ)
  | .capvar a, σ => .capvar (a.subst σ)
  | .member a e i, σ => .member (a.subst σ) (e.subst σ) i
  | .eqToLe φ, σ => .eqToLe (φ.subst σ)

def CapEq.subst : CapEq s1 → Subst s1 s2 → CapEq s2
  | .refl C, σ => .refl (C.rename σ.root)
  | .symm φ, σ => .symm (φ.subst σ)
  | .trans φ ψ, σ => .trans (φ.subst σ) (ψ.subst σ)
  | .defC x ℓ, σ => .defC (σ.root.var x) ℓ
  | .member a e i, σ => .member (a.subst σ) (e.subst σ) i

def CapStep.subst : CapStep s1 → Subst s1 s2 → CapStep s2
  | .closed f, σ => .closed (f.subst σ)
  | .incl C D, σ => .incl (C.rename σ.root.lift) (D.rename σ.root.lift)

def SideC.subst : SideC s1 → Subst s1 s2 → SideC s2
  | .nil, _ => .nil
  | .cons st q, σ => .cons (st.subst σ) (q.subst σ)

def LeCo.subst : LeCo s1 → Subst s1 s2 → LeCo s2
  | .capt e f, σ => .capt (e.subst σ) (f.subst σ)

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
  | .bnd m e, σ => .bnd (m.subst σ) (e.subst σ)
  | .leC m q h q', σ => .leC (m.subst σ) (q.subst σ) h (q'.subst σ)
  | .eqC m j b, σ => .eqC (m.subst σ) j b

def Atom.subst : Atom s1 → Subst s1 s2 → Atom s2
  | .var x, σ => σ.var x
  | .cast a e, σ => .cast (a.subst σ) (e.subst σ)
  | .foldSelf Tel a, σ => .foldSelf (Tel.rename σ.root.lift) (a.subst σ)
  | .unfoldSelf a, σ => .unfoldSelf (a.subst σ)
  | .both Tel₁ Tel₂ a b, σ =>
      .both (Tel₁.rename σ.root.lift) (Tel₂.rename σ.root.lift) (a.subst σ) (b.subst σ)
  | .recap a f, σ => .recap (a.subst σ) (f.subst σ)

end

mutual

def Tm.subst : Tm s1 → Subst s1 s2 → Tm s2
  | .atom a, σ => .atom (a.subst σ)
  | .val v, σ => .val (v.subst σ)
  | .app a b, σ => .app (a.subst σ) (b.subst σ)
  | .proj a ℓ h, σ => .proj (a.subst σ) ℓ (h.subst σ)
  | .let t u U f, σ =>
      .let (t.subst σ) (u.subst σ.lift) (U.rename σ.root) (f.subst σ.lift)
  | .cast t e, σ => .cast (t.subst σ) (e.subst σ)
  | .unbox a U f, σ => .unbox (a.subst σ) (U.rename σ.root) (f.subst σ)

def Value.subst : Value s1 → Subst s1 s2 → Value s2
  | .lam A S t g, σ =>
      .lam (A.rename σ.root) (S.rename σ.root) (t.subst σ.lift) (g.subst σ.lift)
  | .obj A W Wc F, σ =>
      .obj (A.rename σ.root) (W.rename σ.root.lift) (Wc.rename σ.root.lift) (F.subst σ.lift)
  | .box a, σ => .box (a.subst σ)
  | .cast v e, σ => .cast (v.subst σ) (e.subst σ)

def Fields.subst : Fields s1 → Subst s1 s2 → Fields s2
  | .nil, _ => .nil
  | .cons F ℓ t g, σ => .cons (F.subst σ) ℓ (t.subst σ) (g.subst σ)

end

/-- Instantiate the innermost binder of a term by an atom. -/
def Tm.substAtom (t : Tm (s,x)) (a : Atom s) : Tm s := t.subst (Subst.single a)

end FCdot

end CapturesCC
