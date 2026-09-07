import Coercions.Captures.DotToFCdot.Types

namespace Captures

/-!
# Translation of evidence and of variable typings (Plan III §8.1, M3)

A subtyping derivation becomes closed inclusion evidence; a subcapturing
derivation becomes closed capture evidence; a typing derivation of a variable
becomes an atom rooted at that variable.  The three are mutual: `Sel-<:`,
`<:-Sel`, `sc-sel-lower` and `sc-sel-upper` have typing premises, and a
variable typing can go through subsumption.

The object rules translate to template morphisms (plan §13 items 8 and 9):

* `And₁`, `And₂` project by identity templates on the first or second half
  when the operand is an object shape, and by the self-bound cast
  `ShapeCo.bound` when it is not;
* `And` pairs and `And-I` intersects two typings of the same root (`both`),
  each operand first put into its telescope by `into`/`intoAtom`: the
  identity on an object shape, `ShapeCo.intoBnd` on anything else;
* `Fld` routes the presence, the type entry and the capture entry, the last
  through a capture side chain built from the closed capture half of the
  field's type inclusion;
* `Cap` is an object morphism of two capture templates, each carrying one
  closed capture coercion under the self;
* `Typ` maps each proposition through the translated bound;
* `Boxed` is the target's `boxed`;
* `Sel-<:`, `<:-Sel`, `sc-sel-lower` and `sc-sel-upper` are `member` at the
  atom, on the exact proposition;
* `Rec-I`, `Rec-E` unfold at the root and refold at the other telescope;
* a variable bound by an object literal is cast from the literal's precise
  type to its declared type (`litCo`), reading every proposition off the
  literal's definition equalities, capture definitions and field presences.

Inclusion evidence between shapes is `ShapeCo`, between capture sets is
`CapCo`, and a type inclusion is a pair of the two, so `Sub.translate` of
`capt d f` is `capt ⟦d⟧ ⟦f⟧`.
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
  | m, .leC m' q h q' => .leC (m.append m') q h q'
  | m, .eqC m' j b => .eqC (m.append m') j b

/-- A telescope with no self-bound propositions at all.  `Shape.telSelf`
produces one only on a shape that `Wf.mu` excludes. -/
def _root_.Captures.FCdot.Telescope.NoBnd : FCdot.Telescope s' → Prop
  | .nil => True
  | .cons _ (.bnd _) => False
  | .cons Tel _ => FCdot.Telescope.NoBnd Tel

/-- A telescope all of whose self-bounds are weakened closed types, which is
the closedness convention of `FCdot` (plan §13 item 9).  `Shape.tel` produces
only these (`Shape.tel_closedBnds`), and only these can be copied by identity
templates. -/
inductive _root_.Captures.FCdot.Telescope.ClosedBnds : {s : FCdot.Sig} → FCdot.Telescope (s,x) → Prop where
  | nil : FCdot.Telescope.ClosedBnds (.nil : FCdot.Telescope (s,x))
  | le {Tel : FCdot.Telescope (s,x)} {X Y : FCdot.Shape (s,x)} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.le X Y))
  | eq {Tel : FCdot.Telescope (s,x)} {X Y : FCdot.Shape (s,x)} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.eq X Y))
  | has {Tel : FCdot.Telescope (s,x)} {ℓ : Label} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.has ℓ))
  | bnd {Tel : FCdot.Telescope (s,x)} {T : FCdot.Shape s} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.bnd T.weaken))
  | leC {Tel : FCdot.Telescope (s,x)} {C D : FCdot.CaptureSet (s,x)} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.leC C D))
  | eqC {Tel : FCdot.Telescope (s,x)} {C D : FCdot.CaptureSet (s,x)} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.eqC C D))

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
  | .cons Tel (.leC _ _) =>
      .leC (identityMorphism src off Tel) .nil (.leC (off + Tel.length)) .nil
  | .cons Tel (.eqC _ _) => .eqC (identityMorphism src off Tel) (off + Tel.length) false

/-! ## Putting an operand into its telescope -/

/-- Evidence `⟦S⟧ ≤ μ (tel T)` out of evidence `⟦S⟧ ≤ ⟦T⟧`.  For an object
shape the two targets are the same shape; otherwise `tel T` is the single
self-bound `[⊑ ⟦T⟧↑]` and `ShapeCo.intoBnd` moves into it. -/
def into (T : Shape s) (e : FCdot.ShapeCo s) : FCdot.ShapeCo s :=
  if T.isObj then e else .intoBnd e

/-- The same at the level of atoms: an atom of `⟦T⟧ ^ ⟦C⟧` as an atom of
`(μ (tel T)) ^ ⟦C⟧`.  Casting preserves the root, which is what `And-I`
needs, and the capture set is carried through unchanged. -/
def intoAtom (T : Shape s) (C : CaptureSet s) (a : FCdot.Atom s) : FCdot.Atom s :=
  if T.isObj then a
  else .cast a ((FCdot.ShapeCo.intoBnd (.refl T.translate)).atC C.translate)

@[simp] theorem intoAtom_root (T : Shape s) (C : CaptureSet s) (a : FCdot.Atom s) :
    (intoAtom T C a).root = a.root := by
  rw [intoAtom]
  split <;> simp [FCdot.Atom.root]

/-- The morphism from a literal's precise telescope to its declaration shape,
with the next unused definition-equality, capture-equality and
field-presence positions.  Type members read both bounds off the definition
equality; a capture member reads both of its inclusions off the capture
definition, the lower one through a flipped hole; fields inherit their
presence, read their bound off the definition equality and their declared
capture set off the capture definition.

The definition and capture counters run in the structural order, the left
conjunct of an intersection at the lower positions, because the definition
equalities of `Telescope.ofLiteral` follow `Shape.witnesses` and its capture
equalities follow `Shape.capWitnesses`.  The presence counter runs the other
way, because the presence entries follow `Shape.fieldLabels`, whose *right*
conjunct comes first (see there). -/
def litMorphism : Shape (s,x) → Nat → Nat → Nat → FCdot.Morphism s × Nat × Nat × Nat
  | .typ _ _ _, e, c, h =>
      (.le (.le .nil .none (.eqSym e) .none) .none (.eq e) .none, e + 1, c, h)
  | .cap _ _ _, e, c, h =>
      (.leC (.leC .nil .nil (.eqSymC c) .nil) .nil (.eqC c) .nil, e, c + 1, h)
  | .fld _ _, e, c, h =>
      (.leC (.le (.has .nil h) .none (.eq e) .none) .nil (.eqC c) .nil, e + 1, c + 1, h + 1)
  | .and S T, e, c, h =>
      let (m₁, e₁, c₁, h₁) := litMorphism S e c (h + T.fieldLabels.length)
      let (m₂, e₂, c₂, _) := litMorphism T e₁ c₁ h
      (m₁.append m₂, e₂, c₂, h₁)
  | _, e, c, h => (.nil, e, c, h)

/-- The coercion from a literal's precise shape to `⟦μ(x. S)⟧`.

The precise telescope is `type equalities, capture equalities, presences`,
so the definition equalities start at `0`, the capture equalities start at
`|W|`, and the presences start after both earlier blocks, at `|W| + |Wᶜ|`
(`FCdot.CapWitnesses.eqEntries_length`). -/
def litCo (S : Shape (s,x)) : FCdot.ShapeCo s :=
  .obj (FCdot.Telescope.ofLiteral S.witnesses S.capWitnesses S.fieldLabels)
    (litMorphism S 0 S.witnesses.length
      (S.witnesses.length + S.capWitnesses.length)).1

/-- The atom of a variable: the variable itself, cast from the literal's
precise type when the binder is a literal's self.  The cast keeps the
literal's assigned capture set on both sides. -/
def Ctx.varAtom : Ctx s → BVar s .var → FCdot.Atom s
  | .cons _ _, .here => .var .here
  | .cons Γ _, .there y => (Γ.varAtom y).weaken
  | .consSelf _ _ S U, .here =>
      .cast (.var .here) (FCdot.LeCo.weaken ((litCo S).atC U.translate))
  | .consSelf Γ _ _ _, .there y => (Γ.varAtom y).weaken
  | .consC Γ, .there y => (Γ.varAtom y).weaken

/-! ## The translation -/

mutual

/-- `⟦f⟧` on subcapturing derivations. -/
def Subcap.translate : {Γ : Ctx s} → {C C' : CaptureSet s} → Subcap Γ C C' → FCdot.CapCo s
  | _, C, _, .refl => .refl C.translate
  | _, _, _, .trans f g => .trans f.translate g.translate
  | _, C₁, C₂, .elem _ => .elem C₁.translate C₂.translate
  | _, _, _, .union f g => .union f.translate g.translate
  | Γ, _, _, @Subcap.var _ _ x => .capvar (Γ.varAtom x)
  | _, _, _, @Subcap.selLower _ _ _ _ A c₁ c₂ _ h =>
      .member h.translateAtom (.refl (Shape.cap A c₁ c₂).translate) 0
  | _, _, _, @Subcap.selUpper _ _ _ _ A c₁ c₂ _ h =>
      .member h.translateAtom (.refl (Shape.cap A c₁ c₂).translate) 1
  termination_by _ _ _ d => sizeOf d
  decreasing_by
    all_goals try simp_wf
    all_goals try simp only [← CaptureSet.union_def, Subcap.union.sizeOf_spec]
    all_goals omega

/-- `⟦d⟧` on shape-subtyping derivations: the vanilla evidence translation,
whose target sort is `ShapeCo`, with the two new rules. -/
def SubShape.translate : {Γ : Ctx s} → {S T : Shape s} → SubShape Γ S T → FCdot.ShapeCo s
  | _, S, _, .top => .top S.translate
  | _, _, S, .bot => .bot S.translate
  | _, S, _, .refl => .refl S.translate
  | _, _, _, .trans d₁ d₂ => .trans d₁.translate d₂.translate
  | _, .and S T, _, .and1 =>
      if S.isObj then
        .obj (Shape.tel (.and S T)) (identityMorphism (Shape.tel (.and S T)) 0 S.tel)
      else .bound (Shape.tel (.and S T)) 0
  | _, .and S T, _, .and2 =>
      if T.isObj then
        .obj (Shape.tel (.and S T)) (identityMorphism (Shape.tel (.and S T)) S.tel.length T.tel)
      else .bound (Shape.tel (.and S T)) S.tel.length
  | _, _, .and T U, .and d₁ d₂ =>
      .pair T.tel U.tel (into T d₁.translate) (into U d₂.translate)
  | _, _, _, @SubShape.fld _ _ a (.capt C S) _ (.capt dS dC) =>
      .obj (Shape.tel (.fld a (.capt C S)))
        (.leC (.le (.has .nil 0) .none (.le 1) (.some dS.translate)) .nil (.leC 2)
          (.cons (.closed dC.translate) .nil))
  | _, .typ A S₁ T₁, _, .typ d₁ d₂ =>
      .obj (Shape.tel (.typ A S₁ T₁))
        (.le (.le .nil (.some d₁.translate) (.le 0) .none) .none (.le 1)
          (.some d₂.translate))
  | _, _, _, @SubShape.cap _ _ A c₁ c₂ _ _ f₁ f₂ =>
      .obj (Shape.tel (.cap A c₁ c₂))
        (.leC (.leC .nil (.cons (.closed f₁.translate) .nil) (.leC 0) .nil) .nil (.leC 1)
          (.cons (.closed f₂.translate) .nil))
  | _, _, _, .box d => .boxed d.translate
  | _, _, _, @SubShape.selUpper _ _ _ _ A S T _ h =>
      .member h.translateAtom (.refl (Shape.typ A S T).translate) 1
  | _, _, _, @SubShape.selLower _ _ _ _ A S T _ h =>
      .member h.translateAtom (.refl (Shape.typ A S T).translate) 0
  | _, _, _, .all d₁ d₂ => .pi d₁.translate d₂.translate
  termination_by _ _ _ d => sizeOf d

/-- `⟦d⟧ : ⟦S ^ C⟧ ≤ ⟦S' ^ C'⟧`: the pair of the two halves. -/
def Sub.translate : {Γ : Ctx s} → {T T' : Ty s} → Sub Γ T T' → FCdot.LeCo s
  | _, _, _, .capt d f => .capt d.translate f.translate
  termination_by _ _ _ d => sizeOf d

/-- The atom of a variable typing, rooted at the variable.  `Var` recaptures
the binder's atom at the singleton `{x}`, which is the capture set the source
rule concludes at. -/
def HasTy.translateAtom : {U : CaptureSet s} → {Γ : Ctx s} → {x : BVar s .var} → {T : Ty s} →
    HasTy U Γ (.path (.var x)) T → FCdot.Atom s
  | _, Γ, x, _, .var => .recap (Γ.varAtom x) (.refl [FCdot.CapAtom.var x])
  | _, _, _, _, @HasTy.recI _ _ _ _ S _ h _ =>
      .foldSelf S.telSelf (.unfoldSelf h.translateAtom)
  | _, _, x, _, @HasTy.recE _ _ _ _ S _ h _ =>
      .foldSelf (Shape.tel (S.substVar x)) (.unfoldSelf h.translateAtom)
  | _, _, _, _, @HasTy.andI _ _ _ _ S₁ S₂ C h₁ h₂ =>
      .both S₁.tel S₂.tel (intoAtom S₁ C h₁.translateAtom) (intoAtom S₂ C h₂.translateAtom)
  | _, _, _, _, .sub h d _ => .cast h.translateAtom d.translate
  termination_by _ _ _ _ h => sizeOf h

end

end DotMNF

end Captures
