import Coercions.Captures.DotToFCdot.Types

namespace Captures

/-!
# Translation of evidence and of variable typings (Plan III §8.1, M3)

A subtyping derivation becomes closed inclusion evidence; a typing
derivation of a variable becomes an atom rooted at that variable.  The two
are mutual: `Sel-<:` and `<:-Sel` have typing premises, and a variable
typing can go through subsumption.

The object rules translate to template morphisms (plan §13 items 8 and 9):

* `And₁`, `And₂` project by identity templates on the first or second half
  when the operand is an object shape, and by the self-bound cast
  `LeCo.bound` when it is not;
* `And` pairs and `And-I` intersects two typings of the same root (`both`),
  each operand first put into its telescope by `into`/`intoAtom`: the
  identity on an object shape, `LeCo.intoBnd` on anything else;
* `Fld` and `Typ` map each proposition through the translated bound;
* `Sel-<:`, `<:-Sel` are `member` at the atom, on the exact proposition;
* `Rec-I`, `Rec-E` unfold at the root and refold at the other telescope;
* a variable bound by an object literal is cast from the literal's precise
  type to its declared type (`litCo`), reading every proposition off the
  literal's definition equalities and field presences.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Morphisms built from telescopes -/

/-- Concatenation of morphisms. -/
def _root_.Captures.FCdot.Morphism.append : FCdot.Morphism s → FCdot.Morphism s → FCdot.Morphism s
  | m, .nil => m
  | m, .le m' pre h post => .le (m.append m') pre h post
  | m, .eq m' j b => .eq (m.append m') j b
  | m, .has m' j => .has (m.append m') j
  | m, .bnd m' e => .bnd (m.append m') e

/-- A telescope with no self-bound propositions at all.  `Ty.telSelf`
produces one only on a shape that `Wf.mu` excludes. -/
def _root_.Captures.FCdot.Telescope.NoBnd : FCdot.Telescope s' → Prop
  | .nil => True
  | .cons _ (.bnd _) => False
  | .cons Tel _ => FCdot.Telescope.NoBnd Tel

/-- A telescope all of whose self-bounds are weakened closed types, which is
the closedness convention of `FCdot` (plan §13 item 9).  `Ty.tel` produces
only these (`Ty.tel_closedBnds`), and only these can be copied by identity
templates. -/
inductive _root_.Captures.FCdot.Telescope.ClosedBnds : {s : FCdot.Sig} → FCdot.Telescope (s,x) → Prop where
  | nil : FCdot.Telescope.ClosedBnds (.nil : FCdot.Telescope (s,x))
  | le {Tel : FCdot.Telescope (s,x)} {X Y : FCdot.Ty (s,x)} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.le X Y))
  | eq {Tel : FCdot.Telescope (s,x)} {X Y : FCdot.Ty (s,x)} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.eq X Y))
  | has {Tel : FCdot.Telescope (s,x)} {ℓ : Label} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.has ℓ))
  | bnd {Tel : FCdot.Telescope (s,x)} {T : FCdot.Ty s} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.bnd T.weaken))

/-- The identity templates of a telescope whose propositions sit at positions
`off, off + 1, …` of the source `src`.  A self-bound is copied by the cast
of the source object type through the source's own bound at that position,
which is why the source telescope is an argument. -/
def identityMorphism (src : FCdot.Telescope (s,x)) (off : Nat) :
    FCdot.Telescope (s,x) → FCdot.Morphism s
  | .nil => .nil
  | .cons Tel (.le _ _) =>
      .le (identityMorphism src off Tel) .none (.le (off + Tel.length)) .none
  | .cons Tel (.eq _ _) => .eq (identityMorphism src off Tel) (off + Tel.length) false
  | .cons Tel (.has _) => .has (identityMorphism src off Tel) (off + Tel.length)
  | .cons Tel (.bnd _) =>
      .bnd (identityMorphism src off Tel) (.bound src (off + Tel.length))

/-! ## Putting an operand into its telescope -/

/-- Evidence `⟦S⟧ ≤ μ (tel T)` out of evidence `⟦S⟧ ≤ ⟦T⟧`.  For an object
shape the two targets are the same type; otherwise `tel T` is the single
self-bound `[⊑ ⟦T⟧↑]` and `LeCo.intoBnd` moves into it. -/
def into (T : Ty s) (d : FCdot.LeCo s) : FCdot.LeCo s :=
  if T.isObj then d else .intoBnd d

/-- The same at the level of atoms: an atom of `⟦T⟧` as an atom of
`μ (tel T)`.  Casting preserves the root, which is what `And-I` needs. -/
def intoAtom (T : Ty s) (a : FCdot.Atom s) : FCdot.Atom s :=
  if T.isObj then a else .cast a (.intoBnd (.refl T.translate))

@[simp] theorem intoAtom_root (T : Ty s) (a : FCdot.Atom s) :
    (intoAtom T a).root = a.root := by
  rw [intoAtom]
  split <;> simp [FCdot.Atom.root]

/-- The morphism from a literal's precise telescope to its declaration type,
with the next unused definition-equality and field-presence positions.
Type members read both bounds off the definition equality; fields inherit
their presence and read their bound off the definition equality.

The two counters run in opposite orders on an intersection: the definition
equalities of `Telescope.ofLiteral` follow `Ty.witnesses`, whose left
conjunct sits innermost (lowest positions), while its presence entries
follow `Ty.fieldLabels`, whose *right* conjunct comes first (see there).
So `S` gets the equality positions `e …` and the presence positions after
`T`'s, and `T` gets the presence positions `h …`. -/
def litMorphism : Ty (s,x) → Nat → Nat → FCdot.Morphism s × Nat × Nat
  | .typ _ _ _, e, h =>
      (.le (.le .nil .none (.eqSym e) .none) .none (.eq e) .none, e + 1, h)
  | .fld _ _, e, h => (.le (.has .nil h) .none (.eq e) .none, e + 1, h + 1)
  | .and S T, e, h =>
      let (m₁, e₁, h₁) := litMorphism S e (h + T.fieldLabels.length)
      let (m₂, e₂, _) := litMorphism T e₁ h
      (m₁.append m₂, e₂, h₁)
  | _, e, h => (.nil, e, h)

/-- The coercion from a literal's precise type to `⟦μ(x. T)⟧`. -/
def litCo (T : Ty (s,x)) : FCdot.LeCo s :=
  .obj (FCdot.Telescope.ofLiteral T.witnesses T.fieldLabels)
    (litMorphism T 0 T.witnesses.length).1

/-- The atom of a variable: the variable itself, cast from the literal's
precise type when the binder is a literal's self. -/
def Ctx.varAtom : Ctx s → BVar s .var → FCdot.Atom s
  | .cons _ _, .here => .var .here
  | .cons Γ _, .there y => (Γ.varAtom y).weaken
  | .consSelf _ _ T, .here => .cast (.var .here) (litCo T).weaken
  | .consSelf Γ _ _, .there y => (Γ.varAtom y).weaken

/-! ## The translation -/

mutual

/-- `⟦d⟧ : ⟦S⟧ ≤ ⟦T⟧`. -/
def Sub.translate : {Γ : Ctx s} → {S T : Ty s} → Sub Γ S T → FCdot.LeCo s
  | _, T, _, .top => .top T.translate
  | _, _, T, .bot => .bot T.translate
  | _, T, _, .refl => .refl T.translate
  | _, _, _, .trans d₁ d₂ => .trans d₁.translate d₂.translate
  | _, .and S T, _, .and1 =>
      if S.isObj then
        .obj (Ty.tel (.and S T)) (identityMorphism (Ty.tel (.and S T)) 0 S.tel)
      else .bound (Ty.tel (.and S T)) 0
  | _, .and S T, _, .and2 =>
      if T.isObj then
        .obj (Ty.tel (.and S T)) (identityMorphism (Ty.tel (.and S T)) S.tel.length T.tel)
      else .bound (Ty.tel (.and S T)) S.tel.length
  | _, _, .and T U, .and d₁ d₂ =>
      .pair T.tel U.tel (into T d₁.translate) (into U d₂.translate)
  | _, .fld a T, _, .fld d =>
      .obj (Ty.tel (.fld a T)) (.le (.has .nil 0) .none (.le 1) (.some d.translate))
  | _, .typ A S₁ T₁, _, .typ d₁ d₂ =>
      .obj (Ty.tel (.typ A S₁ T₁))
        (.le (.le .nil (.some d₁.translate) (.le 0) .none) .none (.le 1) (.some d₂.translate))
  | _, _, _, @Sub.selUpper _ _ _ A S T h =>
      .member h.translateAtom (.refl (Ty.translate (.typ A S T))) 1
  | _, _, _, @Sub.selLower _ _ _ A S T h =>
      .member h.translateAtom (.refl (Ty.translate (.typ A S T))) 0
  | _, _, _, .all d₁ d₂ => .pi d₁.translate d₂.translate

/-- The atom of a variable typing, rooted at the variable. -/
def HasTy.translateAtom : {Γ : Ctx s} → {x : BVar s .var} → {T : Ty s} →
    HasTy Γ (.path (.var x)) T → FCdot.Atom s
  | Γ, x, _, .var => Γ.varAtom x
  | _, x, _, @HasTy.recI _ _ _ T h _ =>
      .foldSelf T.telSelf (.unfoldSelf h.translateAtom)
  | _, x, _, @HasTy.recE _ _ _ T h _ =>
      .foldSelf (Ty.tel (T.substVar x)) (.unfoldSelf h.translateAtom)
  | _, _, _, @HasTy.andI _ _ _ T U h₁ h₂ =>
      .both T.tel U.tel (intoAtom T h₁.translateAtom) (intoAtom U h₂.translateAtom)
  | _, _, _, .sub h d => .cast h.translateAtom d.translate

end

end DotMNF

end Captures
