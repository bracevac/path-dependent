import Coercions.Paths.DotToFCdot.Types

namespace Paths

/-!
# Translation of evidence and of variable typings (Plan III §8.1, M3, and stage P2.3 of plan-5g)

A subtyping derivation becomes closed inclusion evidence.  A path typing
becomes path evidence whose path is the translated path.  A typing derivation
of a variable becomes an atom rooted at that variable.  Subtyping and path
typing are mutual: `Sel-<:` and `<:-Sel` have path typing premises, and a path
typing can go through subsumption.

The object rules translate to template morphisms (plan §13 items 8 and 9).

* `And₁`, `And₂` project by identity templates on the first or second half
  when the operand is an object shape. They project by the self-bound cast
  `LeCo.bound` when it is not.
* `And` pairs and `And-I` intersects two typings of the same root (`both`).
  Each operand is first put into its telescope by `into`, `intoAtom` or
  `intoPath`: the identity on an object shape, `LeCo.intoBnd` on anything else.
* `Fld`, the stable `Fld` and `Typ` map each proposition through the
  translated bound. `Sub.vfldToFld` forgets the stable presence.
* `Sel-<:`, `<:-Sel` are `memberP` at the path image, on the exact
  proposition (decision 33).
* `Rec-I`, `Rec-E` unfold at the root and refold at the other telescope.
* `Sub.mu` is the template morphism of its `SubDecl`, whose sides are the
  self-free steps.
* The singleton rules of path typing are the alias rules of `PathCo`, with
  the alias read off a singleton by `aliasOf`.
* A variable bound by an object literal is cast from the literal's precise
  type to its declared type (`litCo`), reading every proposition off the
  literal's definition equalities, field presences and stable presences.

Every function of this module is structural (decision 31), so that the kernel
unfolds a translation.
-/

namespace DotMNF

open FCdot (Kind Sig BVar Rename Label)

/-! ## Morphisms built from telescopes -/

/-- Concatenation of morphisms. -/
def _root_.Paths.FCdot.Morphism.append : FCdot.Morphism s → FCdot.Morphism s → FCdot.Morphism s
  | m, .nil => m
  | m, .le m' pre h post => .le (m.append m') pre h post
  | m, .eq m' j b => .eq (m.append m') j b
  | m, .has m' j => .has (m.append m') j
  | m, .bnd m' e => .bnd (m.append m') e
  | m, .hasVal m' j => .hasVal (m.append m') j
  | m, .hasOfVal m' j => .hasOfVal (m.append m') j
  | m, .aliasCopy m' j => .aliasCopy (m.append m') j

/-- A telescope with no self-bound propositions at all.  `Ty.telSelf`
produces one only on a shape that `Wf.mu` excludes. -/
def _root_.Paths.FCdot.Telescope.NoBnd : FCdot.Telescope s' → Prop
  | .nil => True
  | .cons _ (.bnd _) => False
  | .cons Tel _ => FCdot.Telescope.NoBnd Tel

/-- A telescope all of whose self-bounds are weakened closed types, which is
the closedness convention of `FCdot` (plan §13 item 9).  `Ty.tel` produces
only these (`Ty.tel_closedBnds`), and only these can be copied by identity
templates.  A stable presence and an alias are copied by index, so they may
occur anywhere. -/
inductive _root_.Paths.FCdot.Telescope.ClosedBnds : {s : FCdot.Sig} → FCdot.Telescope (s,x) → Prop where
  | nil : FCdot.Telescope.ClosedBnds (.nil : FCdot.Telescope (s,x))
  | le {Tel : FCdot.Telescope (s,x)} {X Y : FCdot.Ty (s,x)} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.le X Y))
  | eq {Tel : FCdot.Telescope (s,x)} {X Y : FCdot.Ty (s,x)} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.eq X Y))
  | has {Tel : FCdot.Telescope (s,x)} {ℓ : Label} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.has ℓ))
  | bnd {Tel : FCdot.Telescope (s,x)} {T : FCdot.Ty s} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.bnd T.weaken))
  | hasVal {Tel : FCdot.Telescope (s,x)} {ℓ : Label} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.hasVal ℓ))
  | alias {Tel : FCdot.Telescope (s,x)} {q : FCdot.Path (s,x)} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.alias q))

/-- The identity templates of a telescope whose propositions sit at positions
`off, off + 1, …` of the source `src`.  A self-bound is copied by the cast
of the source object type through the source's own bound at that position,
which is why the source telescope is an argument.  A stable presence and an
alias are copied by index.

The telescope is taken at any signature (decision 31).  The templates read
only its shape, and at the signature `(s,x)` this is the vanilla function.
Taken at `(s,x)` only, Lean compiles the recursion as well-founded, and the
kernel does not unfold it. -/
def identityMorphism (src : FCdot.Telescope (s,x)) (off : Nat) :
    {s' : Sig} → FCdot.Telescope s' → FCdot.Morphism s
  | _, .nil => .nil
  | _, .cons Tel (.le _ _) =>
      .le (identityMorphism src off Tel) .none (.le (off + Tel.length)) .none
  | _, .cons Tel (.eq _ _) => .eq (identityMorphism src off Tel) (off + Tel.length) false
  | _, .cons Tel (.has _) => .has (identityMorphism src off Tel) (off + Tel.length)
  | _, .cons Tel (.bnd _) =>
      .bnd (identityMorphism src off Tel) (.bound src (off + Tel.length))
  | _, .cons Tel (.hasVal _) => .hasVal (identityMorphism src off Tel) (off + Tel.length)
  | _, .cons Tel (.alias _) => .aliasCopy (identityMorphism src off Tel) (off + Tel.length)

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

/-- `intoAtom`'s twin on path evidence.  Casting preserves the path, which is
what `And-I` at a path needs. -/
def intoPath (T : Ty s) (P : FCdot.PathCo s) : FCdot.PathCo s :=
  if T.isObj then P else .cast P (.intoBnd (.refl T.translate))

@[simp] theorem intoPath_path (T : Ty s) (P : FCdot.PathCo s) :
    (intoPath T P).path = P.path := by
  rw [intoPath]
  split <;> simp [FCdot.PathCo.path]

/-- The alias a singleton path typing licenses: the evidence of
`FCdot.alias_of_sngl`, which reads the alias at index 0 of `Ty.snglOf q`. -/
def aliasOf (P : FCdot.PathCo s) (q : FCdot.Path s) : FCdot.AliasCo s :=
  .member P (.refl (FCdot.Ty.snglOf q)) 0

/-- The morphism from a literal's precise telescope to its declaration type,
with the next unused positions of the three counters: definition equalities
`e`, presences `h`, stable presences `v`.  Type members read both bounds off
the definition equality.  Fields inherit their presence and read their bound
off the definition equality.  A stable field copies its stable presence as
well.

The counters run in opposite orders on an intersection.  The definition
equalities of `Telescope.ofLiteral` follow `Ty.witnesses`, whose left
conjunct sits innermost (lowest positions).  Its presence entries follow
`Ty.fieldLabels` and its stable presences `Ty.valLabels`, whose *right*
conjunct comes first (see there).  So `S` gets the equality positions `e …`
and the presence positions after `T`'s, and `T` gets the next equality
position and the presence positions `h …` and `v …`.  The morphism lives over
any outer scope `s'` and reads only the shape of `T`.  There is no alias
counter: `Telescope.ofLiteral` has no alias entry. -/
def litMorphism : Ty s → Nat → Nat → Nat → FCdot.Morphism s' × Nat × Nat × Nat
  | .typ _ _ _, e, h, v =>
      (.le (.le .nil .none (.eqSym e) .none) .none (.eq e) .none, e + 1, h, v)
  | .fld _ _, e, h, v => (.le (.has .nil h) .none (.eq e) .none, e + 1, h + 1, v)
  | .vfld _ _, e, h, v =>
      (.le (.hasVal (.has .nil h) v) .none (.eq e) .none, e + 1, h + 1, v + 1)
  | .and S T, e, h, v =>
      let r₁ := litMorphism S e (h + T.fieldLabels.length) (v + T.valLabels.length)
      let r₂ := litMorphism T r₁.2.1 h v
      (FCdot.Morphism.append r₁.1 r₂.1, r₂.2.1, r₁.2.2.1, r₁.2.2.2)
  | .top, e, h, v => (.nil, e, h, v)
  | .bot, e, h, v => (.nil, e, h, v)
  | .sngl _, e, h, v => (.nil, e, h, v)
  | .sel _ _, e, h, v => (.nil, e, h, v)
  | .mu _, e, h, v => (.nil, e, h, v)
  | .all _ _, e, h, v => (.nil, e, h, v)

/-- The coercion from a literal's precise type to `⟦μ(x. T)⟧`. -/
def litCo (T : Ty (s,x)) : FCdot.LeCo s :=
  .obj (FCdot.Telescope.ofLiteral T.witnesses T.fieldLabels T.valLabels)
    (litMorphism T 0 T.witnesses.length (T.witnesses.length + T.fieldLabels.length)).1

/-- The atom of a variable: the variable itself, cast from the literal's
precise type when the binder is a literal's self. -/
def Ctx.varAtom : Ctx s → BVar s .var → FCdot.Atom s
  | .cons _ _, .here => .var .here
  | .cons Γ _, .there y => (Γ.varAtom y).weaken
  | .consSelf _ _ T, .here => .cast (.var .here) (litCo T).weaken
  | .consSelf Γ _ _, .there y => (Γ.varAtom y).weaken

/-! ## The positions `SubDecl` reads

In `telSelfAt self D` a type member's lower bound sits at the answer `i` and
its upper bound at `i + 1`.  A plain field's `∋` sits at `i` and its bound at
`i + 1`.  A stable field's `∋`, `∋ᵛ` and bound sit at `i`, `i + 1` and
`i + 2`.  The right conjunct wins, as in `Ty.lookupTypDecl`. -/

/-- The position of the lower bound of `A` in `telSelfAt self D`. -/
def Ty.typIdx (self : BVar s .var) : Ty s → Label → Nat → Option Nat
  | .typ A _ _, ℓ, off => if ℓ = A then some off else none
  | .and S T, ℓ, off =>
      (Ty.typIdx self T ℓ (off + (S.telSelfAt self).length)).or (Ty.typIdx self S ℓ off)
  | _, _, _ => none

/-- The position of `∋ a` of a plain field in `telSelfAt self D`. -/
def Ty.fldIdx (self : BVar s .var) : Ty s → Label → Nat → Option Nat
  | .fld a _, ℓ, off => if ℓ = a then some off else none
  | .and S T, ℓ, off =>
      (Ty.fldIdx self T ℓ (off + (S.telSelfAt self).length)).or (Ty.fldIdx self S ℓ off)
  | _, _, _ => none

/-- The position of `∋ a` of a stable field in `telSelfAt self D`. -/
def Ty.vfldIdx (self : BVar s .var) : Ty s → Label → Nat → Option Nat
  | .vfld a _, ℓ, off => if ℓ = a then some off else none
  | .and S T, ℓ, off =>
      (Ty.vfldIdx self T ℓ (off + (S.telSelfAt self).length)).or (Ty.vfldIdx self S ℓ off)
  | _, _, _ => none

/-! ## The translation

Subtyping and path typing are one mutual block, since `Sel-<:` and `<:-Sel`
read a path typing and a path typing may go through subsumption.  The atom
image of a variable typing is on term typing and comes after the block
(decision 31). -/

mutual

/-- A self-free step as a template side. -/
def SelfFree.translate : {Γ : Ctx s} → {X Y : Ty (s,x)} → SelfFree Γ X Y → FCdot.Side s
  | _, _, _, .refl => .none
  | _, _, X, .bot => .bot X.translate
  | _, X, _, .top => .top X.translate
  | _, _, _, .closed d => .some d.translate

/-- The abstract view of a declaration body as a template morphism over
`telSelf D`.  Each template reads its member at the position `Ty.typIdx`,
`Ty.fldIdx` or `Ty.vfldIdx` gives. -/
def SubDecl.translate : {Γ : Ctx s} → {D D' : Ty (s,x)} → SubDecl Γ D D' → FCdot.Morphism s
  | _, _, _, .top => .nil
  | _, D, _, SubDecl.typ (A := A) _ sf₁ sf₂ =>
      let i := (D.typIdx .here A 0).getD 0
      .le (.le .nil sf₁.translate (.le i) .none) .none (.le (i + 1)) sf₂.translate
  | _, D, _, SubDecl.fld (a := a) _ sf =>
      let i := (D.fldIdx .here a 0).getD 0
      .le (.has .nil i) .none (.le (i + 1)) sf.translate
  | _, D, _, SubDecl.vfld (a := a) _ sf =>
      let i := (D.vfldIdx .here a 0).getD 0
      .le (.hasVal (.has .nil i) (i + 1)) .none (.le (i + 2)) sf.translate
  | _, D, _, SubDecl.vfldToFld (a := a) _ sf =>
      let i := (D.vfldIdx .here a 0).getD 0
      .le (.has .nil i) .none (.le (i + 2)) sf.translate
  | _, _, _, .and d₁ d₂ => FCdot.Morphism.append d₁.translate d₂.translate

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
  | _, .vfld a T, _, .vfld d =>
      .obj (Ty.tel (.vfld a T)) (.le (.hasVal (.has .nil 0) 1) .none (.le 2) (.some d.translate))
  | _, .vfld a T, _, .vfldToFld =>
      .obj (Ty.tel (.vfld a T)) (.le (.has .nil 0) .none (.le 2) .none)
  | _, .typ A S₁ T₁, _, .typ d₁ d₂ =>
      .obj (Ty.tel (.typ A S₁ T₁))
        (.le (.le .nil (.some d₁.translate) (.le 0) .none) .none (.le 1) (.some d₂.translate))
  | _, _, _, Sub.selUpper (A := A) (S := S) (T := T) h =>
      .memberP h.translatePath (.refl (Ty.translate (.typ A S T))) 1
  | _, _, _, Sub.selLower (A := A) (S := S) (T := T) h =>
      .memberP h.translatePath (.refl (Ty.translate (.typ A S T))) 0
  | _, _, _, .all d₁ d₂ => .pi d₁.translate d₂.translate
  | _, .mu D, _, .mu d _ _ => .obj (Ty.telSelf D) d.translate

/-- The path image of a path typing.  Its path is the translated path
(`PathTy.translatePath_path`). -/
def PathTy.translatePath : {Γ : Ctx s} → {p : Path s} → {T : Ty s} →
    PathTy Γ p T → FCdot.PathCo s
  | Γ, .var x, _, .var => (Γ.varAtom x).toPathCo
  | _, _, _, PathTy.sel (a := a) (T := T) h =>
      .cast (.sel h.translatePath a 1)
        (.memberP h.translatePath (.refl (Ty.translate (.vfld a T))) 2)
  | _, _, _, PathTy.recI (T := T) h _ => .foldSelf T.telSelf (.unfoldSelf h.translatePath)
  | _, p, _, PathTy.recE (T := T) h _ =>
      .foldSelf (Ty.tel (T.substPath p)) (.unfoldSelf h.translatePath)
  | _, _, _, PathTy.andI (T := T) (U := U) h₁ h₂ =>
      .both T.tel U.tel (intoPath T h₁.translatePath) (intoPath U h₂.translatePath)
  | _, _, _, .sub h d => .cast h.translatePath d.translate
  | _, p, _, .snglRefl h => .sngl h.translatePath p.translate (.refl p.translate)
  | _, p, _, PathTy.snglTrans (q := q) h₁ h₂ =>
      .alias (aliasOf h₁.translatePath q.translate) p.translate h₂.translatePath
  | _, q, _, PathTy.snglSym (p := p) h₁ h₂ =>
      .sngl h₂.translatePath p.translate (.symm (aliasOf h₁.translatePath q.translate))
  | _, q, _, PathTy.snglInv h₁ =>
      .cast (.alias (.symm (aliasOf h₁.translatePath q.translate)) q.translate h₁.translatePath)
        (.top (FCdot.Ty.snglOf q.translate))
  | _, _, _, PathTy.snglSel (q := q) (a := a) h₁ h₂ =>
      .sngl (.sel h₂.translatePath a 1) (FCdot.Path.sel q.translate a)
        (.sel (aliasOf h₁.translatePath q.translate) a)

end

/-- The atom of a variable typing, rooted at the variable.  The base's
clauses, and the bridge at a singleton: the variable's own atom, with the
alias read off the path image by `alias_of_sngl`.  The root is an argument so
that every term index is a variable and the recursion is structural.  The
last clause is unreachable from `HasTy.translateAtom`, since no other rule
concludes at a variable. -/
def HasTy.translateAtomAt (x0 : BVar s .var) : {Γ : Ctx s} → {t : Tm s} → {T : Ty s} →
    HasTy Γ t T → FCdot.Atom s
  | Γ, .path x, _, .var => Γ.varAtom x
  | _, _, _, HasTy.recI (T := T) h _ => .foldSelf T.telSelf (.unfoldSelf (h.translateAtomAt x0))
  | _, .path x, _, HasTy.recE (T := T) h _ =>
      .foldSelf (Ty.tel (T.substVar x)) (.unfoldSelf (h.translateAtomAt x0))
  | _, _, _, HasTy.andI (T := T) (U := U) h₁ h₂ =>
      .both T.tel U.tel (intoAtom T (h₁.translateAtomAt x0)) (intoAtom U (h₂.translateAtomAt x0))
  | Γ, .path x, _, HasTy.sngl (q := q) d =>
      .sngl (Γ.varAtom x) q.translate (aliasOf d.translatePath q.translate)
  | _, _, _, .sub h d => .cast (h.translateAtomAt x0) d.translate
  | _, _, _, _ => .var x0

/-- The atom of a variable typing, rooted at the variable.  The vanilla name
and signature, with the subject `.path x` (P0.9, row 1). -/
def HasTy.translateAtom {Γ : Ctx s} {x : BVar s .var} {T : Ty s}
    (h : HasTy Γ (.path x) T) : FCdot.Atom s :=
  h.translateAtomAt x

end DotMNF

end Paths
