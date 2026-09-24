import Coercions.Classifiers.DotToFCdot.Types
import Coercions.Classifiers.FCdot.LevelInversion

namespace Classifiers

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
def _root_.Classifiers.FCdot.Morphism.append : FCdot.Morphism s → FCdot.Morphism s → FCdot.Morphism s
  | m, .nil => m
  | m, .le m' pre h post => .le (m.append m') pre h post
  | m, .eq m' j b => .eq (m.append m') j b
  | m, .has m' j => .has (m.append m') j
  | m, .bnd m' e => .bnd (m.append m') e
  | m, .leC m' q h q' => .leC (m.append m') q h q'
  | m, .eqC m' j b => .eqC (m.append m') j b
  | m, .kindC m' q j φ => .kindC (m.append m') q j φ
  | m, .kindCle m' q h q' g φ => .kindCle (m.append m') q h q' g φ

/-- A telescope with no self-bound propositions at all.  `Shape.telSelf`
produces one only on a shape that `Wf.mu` excludes. -/
def _root_.Classifiers.FCdot.Telescope.NoBnd : FCdot.Telescope s' → Prop
  | .nil => True
  | .cons _ (.bnd _) => False
  | .cons Tel _ => FCdot.Telescope.NoBnd Tel

/-- A telescope all of whose self-bounds are weakened closed types, which is
the closedness convention of `FCdot` (plan §13 item 9).  `Shape.tel` produces
only these (`Shape.tel_closedBnds`), and only these can be copied by identity
templates. -/
inductive _root_.Classifiers.FCdot.Telescope.ClosedBnds : {s : FCdot.Sig} → FCdot.Telescope (s,x) → Prop where
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
  | kindC {Tel : FCdot.Telescope (s,x)} {C : FCdot.CaptureSet (s,x)} {φ : Classifiers.Cls.Kind} :
      FCdot.Telescope.ClosedBnds Tel → FCdot.Telescope.ClosedBnds (.cons Tel (.kindC C φ))

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
  | .cons Tel (.kindC _ φ) =>
      .kindC (identityMorphism src off Tel) .nil (off + Tel.length) φ

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
  | .consRoot Γ, .there y => (Γ.varAtom y).weaken
  | .consInst Γ _, .there y => (Γ.varAtom y).weaken
  | .consCls Γ _, .there y => (Γ.varAtom y).weaken

/-- **T-B3.4, step 2.**  A variable's atom reads no telescope.  Every
`.there` clause weakens, which is a renaming, and the one head clause with
content is the literal's self: `ShapeCo.atC e C` is `.capt e (.refl C)`, so
the capture half of the cast is `refl` and `Atom.MemberFree.cast` matches.
This is why `Atom.MemberFree` looks at the capture half of a cast only.  The
shape half of a literal's coercion does read the telescope, and it never
becomes capture evidence. -/
theorem Ctx.varAtom_memberFree : ∀ {s : FCdot.Sig} (Γ : Ctx s) (x : BVar s .var),
    (Γ.varAtom x).MemberFree
  | _, .cons _ _, .here => .var _
  | _, .cons Γ _, .there y => (Ctx.varAtom_memberFree Γ y).weaken
  | _, .consSelf _ _ _ _, .here => .cast (.var _) (.refl _)
  | _, .consSelf Γ _ _ _, .there y => (Ctx.varAtom_memberFree Γ y).weaken
  | _, .consC Γ, .there y => (Ctx.varAtom_memberFree Γ y).weaken
  | _, .consRoot Γ, .there y => (Ctx.varAtom_memberFree Γ y).weaken
  | _, .consInst Γ _, .there y => (Ctx.varAtom_memberFree Γ y).weaken
  | _, .consCls Γ _, .there y => (Ctx.varAtom_memberFree Γ y).weaken

/-! ## Member-free source evidence

**T-B3.4, step 3.**  `Subcap.MemberFree` was stated here before K2.  It now
sits in `DotMNF/Typing.lean`, beside `CapKind.MemberFree`, because the two
are mutual: `Subcap.proj` premises a kinding and `CapKind.kle` premises a
subcapturing.  Its constructors are unchanged and it gained one clause per
new subcapturing rule. -/

/-! ## The translation -/

/-- The target evidence of the source's level rule at an atom.  On the four
copied atoms with a target atom it is `CapCo.level` at that atom, which is
what the copied clause wrote; on `any` and `fresh` the translated set is
empty and the evidence is the syntactic inclusion, which is what the copied
clause wrote there too.  A projection reads through `CapAtom.translate?`,
and the target's own level test reads through a projection. -/
def levelCo (e : CapAtom s) (κ : BVar s .cap) : FCdot.CapCo s :=
  match e.translate? with
  | some b => .level b (.cvar κ)
  | none => .elem [] [.cvar κ]

/-! ### Kinding evidence at one atom

Four source kinding rules conclude about a single atom, and three of them
carry that atom.  The target drops `any` and `fresh`, so at such an atom the
translated set is empty and the evidence is `nil`, which is the target's own
rule for the empty set.  On every atom the target keeps, each helper is the
rule the plan writes. -/

def kprojCo (a : CapAtom s) : FCdot.KindCo s :=
  match a.translate? with
  | some b => .kproj b
  | none => .nil

def kclsCo (a : CapAtom s) : FCdot.KindCo s :=
  match a.translate? with
  | some b => .kcls b
  | none => .nil

def kcvarCo (a : CapAtom s) (g : FCdot.KindCo s) : FCdot.KindCo s :=
  match a.translate? with
  | some b => .kcvar b g
  | none => .nil

/-- The head of a kinded set.  An atom the target drops contributes nothing,
and the reading of the set is the reading of its tail. -/
def kconsCo (a : CapAtom s) (g h : FCdot.KindCo s) : FCdot.KindCo s :=
  match a.translate? with
  | some _ => .cons g h
  | none => h

mutual

/-- `⟦f⟧` on subcapturing derivations. -/
def Subcap.translate : {Γ : Ctx s} → {C C' : CaptureSet s} → Subcap Γ C C' → FCdot.CapCo s
  | _, C, _, .refl => .refl C.translate
  | _, _, _, .trans f g => .trans f.translate g.translate
  | _, C₁, C₂, .elem _ => .elem C₁.translate C₂.translate
  | _, _, _, .union f g => .union f.translate g.translate
  | Γ, _, _, @Subcap.var _ _ x => .capvar (Γ.varAtom x)
  | _, C, _, @Subcap.inst _ _ κ _ _ =>
      .eqToLe (.symm (.instC (.cvar κ) C.translate))
  /- **B3.6.**  The level rule translates to the target's level rule at the
     translated atom.  The two notation cases are unreachable in a typed
     derivation, and they are given evidence rather than an absurdity, so
     the clause stays a leaf, and it adds no obligation to the
     `decreasing_by` block below. -/
  | _, _, _, @Subcap.level _ Γ e κ _ _ => levelCo e κ
  | _, _, _, @Subcap.unproj _ _ C φ => .unprojC C.translate φ
  | _, _, _, @Subcap.proj _ _ C φ g => .projC g.translate C.translate φ
  | _, _, _, @Subcap.projMono _ _ _ _ ψ f => .projMono f.translate ψ
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
  /- **K2.8.**  A set-bounded capture member is retyped at a kind bound.
     The source telescope is the member's two `leC` entries, the hole is its
     upper bound at index `1`, both chains are empty, and the closed kinding
     is the rule's own premise. -/
  | _, _, _, @SubShape.capkI _ _ A c₁ c₂ φ g =>
      .obj (Shape.tel (.cap A c₁ c₂))
        (.kindCle .nil .nil (.leC 1) .nil g.translate φ)
  /- Widening of a kind bound: the identity template at the one kinding
     proposition of the source telescope, read at the wider kind. -/
  | _, _, _, @SubShape.capk _ _ A φ₁ φ₂ _ =>
      .obj (Shape.tel (.capk A φ₁)) (.kindC .nil .nil 0 φ₂)
  termination_by _ _ _ d => sizeOf d

/-- `⟦d⟧ : ⟦S ^ C⟧ ≤ ⟦S' ^ C'⟧`: the pair of the two halves. -/
def Sub.translate : {Γ : Ctx s} → {T T' : Ty s} → Sub Γ T T' → FCdot.LeCo s
  | _, _, _, .capt d f => .capt d.translate f.translate
  termination_by _ _ _ d => sizeOf d

/-- `⟦d⟧` on answer inclusions: a plain inclusion is a plain coercion, a
pack is the target's pack, and the congruence is the target's `cong`.  It is
the clause list of B2.10 verbatim. -/
def ESub.translate : {Γ : Ctx s} → {E E' : ETy s} → ESub Γ E E' → FCdot.ELeCo s
  | _, _, _, .ty d => .plain d.translate
  | _, _, _, @ESub.pack _ _ C _ _ _ f d => .pack C.translate f.translate d.translate
  | _, _, _, .exist f d => .cong f.translate d.translate
  termination_by _ _ _ d => sizeOf d

/-- `⟦g⟧` on capture-kinding derivations.  It mirrors `FCdot.KindCo` rule by
rule, with `ksel` sent to `kmember` exactly as `Subcap.selUpper` is sent to
`member`: through `HasTy.translateAtom` and the member's own telescope, at
index `0`, since a kind-bounded member compiles to a one-entry telescope. -/
def CapKind.translate : {Γ : Ctx s} → {C : CaptureSet s} → {φ : Cls.Kind} →
    CapKind Γ C φ → FCdot.KindCo s
  | _, _, _, .nil => .nil
  | _, _, _, @CapKind.cons _ _ a _ _ g h => kconsCo a g.translate h.translate
  | _, _, _, @CapKind.kproj _ _ a _ _ => kprojCo a
  | _, _, _, @CapKind.kcls _ _ a _ _ _ _ => kclsCo a
  | Γ, _, _, @CapKind.kvar _ _ _ x _ _ g => .kvar (Γ.varAtom x) g.translate
  | _, _, _, @CapKind.kcvar _ _ a _ _ _ _ _ g => kcvarCo a g.translate
  | _, _, _, @CapKind.ksel _ _ _ _ A φ _ h =>
      .kmember h.translateAtom (.refl (Shape.capk A φ).translate) 0
  | _, _, _, @CapKind.kprojS _ _ C ψ _ g => .kprojS g.translate C.translate ψ
  | _, _, _, @CapKind.ksub _ _ _ φ₁ _ g _ => .ksub g.translate φ₁
  | _, _, _, .kle f g => .kle f.translate g.translate
  termination_by _ _ _ d => sizeOf d

/-- The atom of a variable typing, rooted at the variable.  `Var` recaptures
the binder's atom at the singleton `{x}`, which is the capture set the source
rule concludes at. -/
def HasTy.translateAtom : {U : CaptureSet s} → {Γ : Ctx s} → {x : BVar s .var} → {T : Ty s} →
    HasTy U Γ (.path (.var x)) (.ty T) → FCdot.Atom s
  | _, Γ, x, _, .var => .recap (Γ.varAtom x) (.refl [FCdot.CapAtom.var x])
  | _, _, _, _, @HasTy.recI _ _ _ _ S _ h _ =>
      .foldSelf S.telSelf (.unfoldSelf h.translateAtom)
  | _, _, x, _, @HasTy.recE _ _ _ _ S _ h _ =>
      .foldSelf (Shape.tel (S.substVar x)) (.unfoldSelf h.translateAtom)
  | _, _, _, _, @HasTy.andI _ _ _ _ S₁ S₂ C h₁ h₂ =>
      .both S₁.tel S₂.tel (intoAtom S₁ C h₁.translateAtom) (intoAtom S₂ C h₂.translateAtom)
  | _, _, _, _, .sub h (.ty d) _ => .cast h.translateAtom d.translate
  termination_by _ _ _ _ h => sizeOf h

end

/-! ## Member-freeness is preserved by the translation

**T-B3.4, step 4.**  An induction following `Subcap.translate`'s own case
split.  The six member-free rules translate to the six member-free target
rules, and `var` needs `Ctx.varAtom_memberFree`.  The `level` clause is a
leaf in both, so the case is a five-way `cases` on the atom. -/

mutual

theorem Subcap.translate_memberFree : ∀ {s : FCdot.Sig} {Γ : Ctx s} {C C' : CaptureSet s}
    {d : Subcap Γ C C'}, d.MemberFree → d.translate.MemberFree
  | _, _, _, _, _, .refl => by rw [Subcap.translate]; exact .refl _
  | _, _, _, _, _, .trans hf hg => by
      rw [Subcap.translate]
      exact .trans (Subcap.translate_memberFree hf) (Subcap.translate_memberFree hg)
  | _, _, _, _, _, .elem _ => by rw [Subcap.translate]; exact .elem _ _
  | _, _, _, _, _, .union hf hg => by
      rw [Subcap.translate]
      exact .union (Subcap.translate_memberFree hf) (Subcap.translate_memberFree hg)
  | _, Γ, _, _, _, .var => by rw [Subcap.translate]; exact .capvar (Ctx.varAtom_memberFree Γ _)
  | _, _, _, _, @Subcap.level _ _ e _ _ _, .level _ _ => by
      rw [Subcap.translate]
      unfold levelCo
      cases e.translate?
      · exact .elem _ _
      · exact .level _ _
  | _, _, _, _, _, .unproj => by rw [Subcap.translate]; exact .unprojC _ _
  | _, _, _, _, _, .proj hg => by
      rw [Subcap.translate]
      exact .projC _ _ (CapKind.translate_memberFree hg)
  | _, _, _, _, _, .projMono hd => by
      rw [Subcap.translate]
      exact .projMono _ (Subcap.translate_memberFree hd)

/-- The same for source kinding: the nine member-free rules translate to the
target's member-free rules, and `ksel` is excluded on both sides. -/
theorem CapKind.translate_memberFree : ∀ {s : FCdot.Sig} {Γ : Ctx s} {C : CaptureSet s}
    {φ : Cls.Kind} {g : CapKind Γ C φ}, g.MemberFree → g.translate.MemberFree
  | _, _, _, _, _, .nil => by rw [CapKind.translate]; exact .nil
  | _, _, _, _, @CapKind.cons _ _ a _ _ _ _, .cons hg hh => by
      rw [CapKind.translate]
      unfold kconsCo
      cases a.translate?
      · exact CapKind.translate_memberFree hh
      · exact .cons (CapKind.translate_memberFree hg) (CapKind.translate_memberFree hh)
  | _, _, _, _, @CapKind.kproj _ _ a _ _, .kproj _ => by
      rw [CapKind.translate]
      unfold kprojCo
      cases a.translate?
      · exact .nil
      · exact .kproj _
  | _, _, _, _, @CapKind.kcls _ _ a _ _ _ _, .kcls _ _ => by
      rw [CapKind.translate]
      unfold kclsCo
      cases a.translate?
      · exact .nil
      · exact .kcls _
  | _, Γ, _, _, _, .kvar _ hg => by
      rw [CapKind.translate]
      exact .kvar (Ctx.varAtom_memberFree Γ _) (CapKind.translate_memberFree hg)
  | _, _, _, _, @CapKind.kcvar _ _ a _ _ _ _ _ _, .kcvar _ _ hg => by
      rw [CapKind.translate]
      unfold kcvarCo
      cases a.translate?
      · exact .nil
      · exact .kcvar _ (CapKind.translate_memberFree hg)
  | _, _, _, _, _, .kprojS hg => by
      rw [CapKind.translate]
      exact .kprojS _ _ (CapKind.translate_memberFree hg)
  | _, _, _, _, _, .ksub _ hg => by
      rw [CapKind.translate]
      exact .ksub _ (CapKind.translate_memberFree hg)
  | _, _, _, _, _, .kle hf hg => by
      rw [CapKind.translate]
      exact .kle (Subcap.translate_memberFree hf) (CapKind.translate_memberFree hg)

end

end DotMNF

end Classifiers
