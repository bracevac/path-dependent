import Coercions.DotToFCdot.Types

/-!
# Translation of evidence and of variable typings (Plan III §8.1, M3)

A subtyping derivation becomes closed inclusion evidence; a typing
derivation of a variable becomes an atom rooted at that variable.  The two
are mutual: `Sel-<:` and `<:-Sel` have typing premises, and a variable
typing can go through subsumption.

The object rules translate to template morphisms (plan §13 item 8):

* `And₁`, `And₂` project by identity templates on the first or second half;
* `And` pairs; `And-I` intersects two typings of the same root (`both`);
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
def _root_.FCdot.Morphism.append : FCdot.Morphism s → FCdot.Morphism s → FCdot.Morphism s
  | m, .nil => m
  | m, .le m' pre h post => .le (m.append m') pre h post
  | m, .eq m' j b => .eq (m.append m') j b
  | m, .has m' j => .has (m.append m') j

/-- The identity templates of a telescope whose propositions sit at positions
`off, off + 1, …` of the source. -/
def identityMorphism (off : Nat) : FCdot.Telescope (s,x) → FCdot.Morphism s
  | .nil => .nil
  | .cons Tel (.le _ _) => .le (identityMorphism off Tel) .none (.le (off + Tel.length)) .none
  | .cons Tel (.eq _ _) => .eq (identityMorphism off Tel) (off + Tel.length) false
  | .cons Tel (.has _) => .has (identityMorphism off Tel) (off + Tel.length)

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
  | _, .and S T, _, .and1 _ _ => .obj (Ty.tel (.and S T)) (identityMorphism 0 S.tel)
  | _, .and S T, _, .and2 _ _ => .obj (Ty.tel (.and S T)) (identityMorphism S.tel.length T.tel)
  | _, _, .and T U, .and d₁ d₂ _ _ => .pair T.tel U.tel d₁.translate d₂.translate
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
  | _, _, _, @HasTy.andI _ _ _ T U h₁ h₂ _ _ =>
      .both T.tel U.tel h₁.translateAtom h₂.translateAtom
  | _, _, _, .sub h d => .cast h.translateAtom d.translate

end

end DotMNF
