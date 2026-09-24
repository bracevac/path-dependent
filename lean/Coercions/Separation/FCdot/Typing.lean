import Coercions.Separation.FCdot.Names

namespace Separation

/-!
# FCdot typing

Evidence typing assigns endpoints to proof terms.  Term typing has no
subsumption; every inclusion is an explicit `cast`.  Elimination at an atom
(`member`) is the only way member facts flow from a binder's type to its
block.

A type is a shape with a capture set, so inclusion of types splits into two
families: the *shape* family `Γ ⊢ˢ e : S ≤ S'`, which is the vanilla family
read at the shape sort, and the *capture* family `Γ ⊢ᶜ f : C ⊑ C'`.  A type
inclusion `Γ ⊢ capt e f : S ^ C ≤ S' ^ C'` is the pair of the two.  Capture
equality `Γ ⊢ᶜ φ : C ≡ C'` sits beside them, and both capture families
mention atoms (`capvar`, `member`), so they live in the mutual block.  An
atom's own capability is the capability of its root: a box is a *value* and
an unboxing a *term*, not atom wrappers, so every rule that opens a self
binder at an atom opens it at `a.root`, as in the vanilla line.
-/

namespace FCdot

/-! ## Reading a capture proposition at a hole

A capture template names a proposition of its source telescope and reads it
as an inclusion: a subcapturing proposition as it is, a capture equality in
either direction. -/

/-- `src.HoleAtC h C₁ C₂`: in `src`, the capture hole `h` proves `C₁ ⊑ C₂`. -/
inductive Telescope.HoleAtC (src : Telescope (s,x)) :
    HoleC → CaptureSet (s,x) → CaptureSet (s,x) → Prop where
  | leC : src ∋ (j ↦ C₁ ⊑ᶜ C₂) → Telescope.HoleAtC src (.leC j) C₁ C₂
  | eqC : src ∋ (j ↦ C₁ ≐ᶜ C₂) → Telescope.HoleAtC src (.eqC j) C₁ C₂
  | eqSymC : src ∋ (j ↦ C₂ ≐ᶜ C₁) → Telescope.HoleAtC src (.eqSymC j) C₁ C₂

/-! ### Notation for the evidence judgments

Declared before the judgments so that the rules can use them; the
pretty-printers are attached after. -/

set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ᶜ " f:51 " : " C:71 " ⊑ " D:71 => CapCo.HasType Γ f C D
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ᶜ " φ:51 " : " C:71 " ≡ " D:71 => CapEq.HasType Γ φ C D
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ˢ " e:51 " : " S:51 " ≤ " T:51 => ShapeCo.HasType Γ e S T
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ " e:51 " : " S:51 " ≤ " T:51 => LeCo.HasType Γ e S T
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ " φ:51 " : " S:51 " ≡ " T:51 => EqCo.HasType Γ φ S T
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ " h:51 " : " x:max " ∋ " ℓ:max => Has.HasType Γ h x ℓ
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ " m:51 " : " src:51 " ⇒ " Tel:51 => Morphism.HasType Γ src m Tel
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ₐ " a:51 " : " T:51 => Atom.HasType Γ a T
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ᵉ " g:51 " : " E:51 " ≤ " E':51 => ELeCo.HasType Γ g E E'
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ₚ " p:51 " : " E:51 => PAtom.HasType Γ p E

mutual

/-- `Γ ⊢ᶜ f : C ⊑ D`: inclusion evidence between capture sets.  It mentions
atoms (`capvar`, `member`), so it belongs to the mutual block. -/
inductive CapCo.HasType : Ctx s → CapCo s → CaptureSet s → CaptureSet s → Prop where
  | refl : Γ ⊢ᶜ .refl C : C ⊑ C
  | trans : Γ ⊢ᶜ f : C₁ ⊑ C₂ → Γ ⊢ᶜ g : C₂ ⊑ C₃ → Γ ⊢ᶜ .trans f g : C₁ ⊑ C₃
  /-- A syntactic inclusion, decided. -/
  | elem : CaptureSet.Subset C₁ C₂ → Γ ⊢ᶜ .elem C₁ C₂ : C₁ ⊑ C₂
  | union : Γ ⊢ᶜ f : C₁ ⊑ D → Γ ⊢ᶜ g : C₂ ⊑ D → Γ ⊢ᶜ .union f g : (C₁ ∪ C₂) ⊑ D
  /-- An atom's own capture set is below the capture set of its type.  No side
      condition: a chain with a box in it has the empty capture set. -/
  | capvar :
      Γ ⊢ₐ a : S ^ C →
      Γ ⊢ᶜ .capvar a : [CapAtom.var a.root] ⊑ C
  /-- Elimination at an atom, in the capture sort: the `i`-th proposition of
      the object shape `e` lands in, instantiated at the atom. -/
  | member :
      Γ ⊢ₐ a : S ^ D →
      Γ ⊢ˢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ C₁ ⊑ᶜ C₂) →
      Γ ⊢ᶜ .member a e i : C₁⟦a.root⟧ ⊑ C₂⟦a.root⟧
  | eqToLe : Γ ⊢ᶜ φ : C₁ ≡ C₂ → Γ ⊢ᶜ .eqToLe φ : C₁ ⊑ C₂
  /-- `Γ ⊢ᶜ level e r : {e} ⊑ᶜ {r}` when `r` is a scope root and the level of
      `e` is `r` or encloses it, and `e` is access-only: consumption never
      goes below a root (plan-5h S0.3, decisions 6 and 37).  The premise
      reads the mode reading of names, in which a parameter is a plain leaf.
      Both sides are singletons.  A set shaped conclusion is a `union` of
      instances. -/
  | level :
      Γ.IsRoot r →
      Γ.LvlLe e r →
      Γ.AccessOnly [e] →
      Γ ⊢ᶜ .level e r : [e] ⊑ [r]
  /-- `{a at m} ⊑ {a at m'}` when `m ≤ m'`: `{ro a} ⊑ {a} ⊑ {consume a}`. -/
  | modeLe : m ≤ m' → Γ ⊢ᶜ .modeLe a m m' : [a.atMode m] ⊑ [a.atMode m']
  /-- The read-only view of an inclusion. -/
  | roMap : Γ ⊢ᶜ f : C ⊑ D → Γ ⊢ᶜ .roMap f : C.ro ⊑ D.ro
  /-- `W ⊑ {h}` for an heir `h` of `W`, when what the heir owns is
      access-only (decision 37).  There is deliberately no rule for the other
      direction. -/
  | ownLe : Γ.OwnOf a W → Γ.AccessOnly W → Γ ⊢ᶜ .ownLe a W : W ⊑ [a]

/-- `Γ ⊢ᶜ φ : C ≡ D`: equality evidence between capture sets. -/
inductive CapEq.HasType : Ctx s → CapEq s → CaptureSet s → CaptureSet s → Prop where
  | refl : Γ ⊢ᶜ .refl C : C ≡ C
  | symm : Γ ⊢ᶜ φ : C₁ ≡ C₂ → Γ ⊢ᶜ .symm φ : C₂ ≡ C₁
  | trans : Γ ⊢ᶜ φ : C₁ ≡ C₂ → Γ ⊢ᶜ ψ : C₂ ≡ C₃ → Γ ⊢ᶜ .trans φ ψ : C₁ ≡ C₃
  /-- Definition of a transparent binder's capture name. -/
  | defC : Γ.lookupDefC x ℓ = some C → Γ ⊢ᶜ .defC x ℓ : [CapAtom.name x ℓ] ≡ C
  /-- An instance binder stands for the set it was opened at.  Both
      directions come from it through `symm` and `eqToLe`. -/
  | instC : Γ.InstOf a C → Γ ⊢ᶜ .instC a C : [a] ≡ C
  | member :
      Γ ⊢ₐ a : S ^ D →
      Γ ⊢ˢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ C₁ ≐ᶜ C₂) →
      Γ ⊢ᶜ .member a e i : C₁⟦a.root⟧ ≡ C₂⟦a.root⟧

/-- One step of a capture-template side: closed capture evidence weakened
under the self, or a syntactic inclusion of sets that may mention the self. -/
inductive CapStep.HasType : Ctx s → CapStep s → CaptureSet (s,x) → CaptureSet (s,x) → Prop where
  | closed : Γ ⊢ᶜ f : A ⊑ B → CapStep.HasType Γ (.closed f) A↑ B↑
  | incl : CaptureSet.Subset C D → CapStep.HasType Γ (.incl C D) C D

/-- A capture-template side is a chain of steps, typed step by step; the empty
chain is the identity. -/
inductive SideC.HasType : Ctx s → SideC s → CaptureSet (s,x) → CaptureSet (s,x) → Prop where
  | nil : SideC.HasType Γ .nil X X
  | cons :
      CapStep.HasType Γ st X Y →
      SideC.HasType Γ q Y Z →
      SideC.HasType Γ (.cons st q) X Z

/-- `Γ ⊢ˢ e : S ≤ T`: inclusion evidence between shapes. -/
inductive ShapeCo.HasType : Ctx s → ShapeCo s → Shape s → Shape s → Prop where
  | refl : Γ ⊢ˢ .refl S : S ≤ S
  | trans : Γ ⊢ˢ e : S ≤ M → Γ ⊢ˢ f : M ≤ T → Γ ⊢ˢ .trans e f : S ≤ T
  | top : Γ ⊢ˢ .top S : S ≤ ⊤
  | bot : Γ ⊢ˢ .bot S : ⊥ ≤ S
  | eqToLe : Γ ⊢ φ : S ≡ T → Γ ⊢ˢ .eqToLe φ : S ≤ T
  /-- Contravariant domain, covariant codomain; both are type inclusions.
      Both arrows' capture binders are opened at one scope, and that scope
      has a root of its own, which is the scope discipline of the stage.  The
      codomain evidence charges nothing: a fresh pack under an arrow packs
      no name (plan-5h decision 38). -/
  | pi {T1 T2 : Dom s} {U1 U2 : Cod s} :
      Γ.scope ⊢ e : T2.underRoot ≤ T1.underRoot →
      Γ.body T2 ⊢ᵉ f : U1.underRoot ≤ U2.underRoot →
      f.charge = [] →
      Γ ⊢ˢ .pi e f : Π(T1) U1 ≤ Π(T2) U2
  /-- Object coercion between closed telescopes: the morphism proves each target
      proposition by a template over a source proposition. -/
  | obj :
      Γ ⊢ m : Tel ⇒ Tel' →
      Γ ⊢ˢ .obj Tel m : μ Tel ≤ μ Tel'
  /-- Pairing: two coercions into object shapes give one into the concatenation. -/
  | pair :
      Γ ⊢ˢ e : S ≤ μ Tel₁ →
      Γ ⊢ˢ f : S ≤ μ Tel₂ →
      Γ ⊢ˢ .pair Tel₁ Tel₂ e f : S ≤ μ (Tel₁ ++ Tel₂)
  /-- The annotated object shape is below its `i`-th bound. -/
  | bound :
      Tel ∋ (i ↦ ⊑ S↑) →
      Γ ⊢ˢ .bound Tel i : μ Tel ≤ S
  /-- An `S` below `T` is an `S` below the one-bound object shape. -/
  | intoBnd :
      Γ ⊢ˢ e : S ≤ T →
      Γ ⊢ˢ .intoBnd e : S ≤ μ (.nil ▹ ⊑ T↑)
  | member :
      Γ ⊢ₐ a : S ^ C →
      Γ ⊢ˢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ S' ⊑ T') →
      Γ ⊢ˢ .member a e i : S'⟦a.root⟧ ≤ T'⟦a.root⟧
  /-- The box former is covariant in the boxed type. -/
  | boxed :
      Γ ⊢ d : T ≤ T' →
      Γ ⊢ˢ .boxed d : □ T ≤ □ T'
  /-- A cell is read as its read-only view.  A cell itself is invariant: it
      has no rule but `refl`, `trans`, `top`, `bot` and `eqToLe`. -/
  | toReader : Γ ⊢ˢ .toReader T : Shape.cell T ≤ Shape.reader T
  /-- A read-only view is covariant in the content type. -/
  | readerCov :
      Γ ⊢ d : T ≤ T' →
      Γ ⊢ˢ .readerCov d : Shape.reader T ≤ Shape.reader T'

/-- `Γ ⊢ d : T ≤ T'`: inclusion evidence between types, a shape inclusion
paired with a capture inclusion. -/
inductive LeCo.HasType : Ctx s → LeCo s → Ty s → Ty s → Prop where
  | capt :
      Γ ⊢ˢ e : S ≤ S' →
      Γ ⊢ᶜ f : C ⊑ C' →
      Γ ⊢ .capt e f : S ^ C ≤ S' ^ C'

/-- `Γ ⊢ φ : S ≡ T`: equality evidence between shapes. -/
inductive EqCo.HasType : Ctx s → EqCo s → Shape s → Shape s → Prop where
  | refl : Γ ⊢ .refl S : S ≡ S
  | symm : Γ ⊢ φ : S ≡ T → Γ ⊢ .symm φ : T ≡ S
  | trans : Γ ⊢ φ : S ≡ M → Γ ⊢ ψ : M ≡ T → Γ ⊢ .trans φ ψ : S ≡ T
  | def : Γ.lookupDef x ℓ = some W → Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W
  | member :
      Γ ⊢ₐ a : S ^ C →
      Γ ⊢ˢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ S' ≐ T') →
      Γ ⊢ .member a e i : S'⟦a.root⟧ ≡ T'⟦a.root⟧

/-- `Γ ⊢ h : x ∋ ℓ`: `h` proves that the block of `x` has field `ℓ`. -/
inductive Has.HasType : Ctx s → Has s → BVar s .var → Label → Prop where
  | member :
      Γ ⊢ₐ a : S ^ C →
      Γ ⊢ˢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ ∋ ℓ) →
      Γ ⊢ .member a e i : a.root ∋ ℓ
  | field :
      Γ.lookupFields x = some Fs → ℓ ∈ Fs →
      Γ ⊢ .field ℓ : x ∋ ℓ

/-- A template side: `none` leaves the endpoint as it is; `some e` is a closed
coercion `A ≤ B` between weakened closed shapes. -/
inductive Side.HasType : Ctx s → Side s → Shape (s,x) → Shape (s,x) → Prop where
  | none : Side.HasType Γ .none X X
  | some : Γ ⊢ˢ e : A ≤ B → Side.HasType Γ (.some e) A↑ B↑

/-- `Γ ⊢ m : src ⇒ Tel`: `m` proves every proposition of the closed telescope
`Tel` from the propositions of the closed source telescope `src`, one
template per target proposition. -/
inductive Morphism.HasType : Ctx s → Telescope (s,x) → Morphism s → Telescope (s,x) → Prop where
  | nil : Γ ⊢ .nil : src ⇒ .nil
  | le : Γ ⊢ m : src ⇒ Tel → src ∋ (j ↦ X ⊑ Y) →
      Side.HasType Γ pre S X → Side.HasType Γ post Y T →
      Γ ⊢ .le m pre (.le j) post : src ⇒ Tel ▹ S ⊑ T
  | leEq : Γ ⊢ m : src ⇒ Tel → src ∋ (j ↦ X ≐ Y) →
      Side.HasType Γ pre S X → Side.HasType Γ post Y T →
      Γ ⊢ .le m pre (.eq j) post : src ⇒ Tel ▹ S ⊑ T
  | leEqSym : Γ ⊢ m : src ⇒ Tel → src ∋ (j ↦ Y ≐ X) →
      Side.HasType Γ pre S X → Side.HasType Γ post Y T →
      Γ ⊢ .le m pre (.eqSym j) post : src ⇒ Tel ▹ S ⊑ T
  | eq : Γ ⊢ m : src ⇒ Tel → src ∋ (j ↦ X ≐ Y) →
      Γ ⊢ .eq m j false : src ⇒ Tel ▹ X ≐ Y
  | eqSym : Γ ⊢ m : src ⇒ Tel → src ∋ (j ↦ X ≐ Y) →
      Γ ⊢ .eq m j true : src ⇒ Tel ▹ Y ≐ X
  | has : Γ ⊢ m : src ⇒ Tel → src ∋ (j ↦ ∋ ℓ) →
      Γ ⊢ .has m j : src ⇒ Tel ▹ ∋ ℓ
  /-- A target bound is proven by a closed coercion out of the source object
      shape. -/
  | bnd : Γ ⊢ m : src ⇒ Tel → Γ ⊢ˢ e : μ src ≤ S →
      Γ ⊢ .bnd m e : src ⇒ Tel ▹ ⊑ S↑
  /-- A target subcapturing proposition: a side chain into the hole's left
      endpoint, a hole naming a source capture proposition, a side chain out
      of its right endpoint. -/
  | leC : Γ ⊢ m : src ⇒ Tel → src.HoleAtC h C₁ C₂ →
      SideC.HasType Γ q D₁ C₁ → SideC.HasType Γ q' C₂ D₂ →
      Γ ⊢ .leC m q h q' : src ⇒ Tel ▹ D₁ ⊑ᶜ D₂
  /-- A target capture equality is a source capture equality. -/
  | eqC : Γ ⊢ m : src ⇒ Tel → src ∋ (j ↦ C₁ ≐ᶜ C₂) →
      Γ ⊢ .eqC m j false : src ⇒ Tel ▹ C₁ ≐ᶜ C₂
  /-- … possibly flipped. -/
  | eqSymC : Γ ⊢ m : src ⇒ Tel → src ∋ (j ↦ C₁ ≐ᶜ C₂) →
      Γ ⊢ .eqC m j true : src ⇒ Tel ▹ C₂ ≐ᶜ C₁

/-- `Γ ⊢ₐ a : T`: atoms. -/
inductive Atom.HasType : Ctx s → Atom s → Ty s → Prop where
  | var : Γ ⊢ₐ .var x : Γ.lookupTy x
  | cast : Γ ⊢ₐ a : T → Γ ⊢ e : T ≤ T' → Γ ⊢ₐ .cast a e : T'
  /-- `Rec-E`: the self block of the object shape is the atom's own block. -/
  | unfoldSelf :
      Γ ⊢ₐ a : (μ Tel) ^ C →
      Γ ⊢ₐ .unfoldSelf a : (μ (Tel⟦a.root⟧)↑) ^ C
  /-- `Rec-I`. -/
  | foldSelf :
      Γ ⊢ₐ a : (μ (Tel⟦a.root⟧)↑) ^ C →
      Γ ⊢ₐ .foldSelf Tel a : (μ Tel) ^ C
  /-- `And-I`: two typings of the same root, at the same capture set. -/
  | both :
      Γ ⊢ₐ a : (μ Tel₁) ^ C →
      Γ ⊢ₐ b : (μ Tel₂) ^ C →
      b.root = a.root →
      Γ ⊢ₐ .both Tel₁ Tel₂ a b : (μ (Tel₁ ++ Tel₂)) ^ C
  /-- Recapturing: the atom keeps its shape and takes any capture set its own
      capture set is below. -/
  | recap :
      Γ ⊢ₐ a : S ^ C →
      Γ ⊢ᶜ f : [CapAtom.var a.root] ⊑ C' →
      Γ ⊢ₐ .recap a f : S ^ C'

/-- `Γ ⊢ᵉ g : E ≤ E'`: inclusion evidence between answers.  It premises the
type family, and `ShapeCo.HasType.pi` premises it, so it belongs to the
block. -/
inductive ELeCo.HasType : Ctx s → ELeCo s → ETy s → ETy s → Prop where
  | plain : Γ ⊢ e : T ≤ T' → Γ ⊢ᵉ .plain e : .ty T ≤ .ty T'
  /-- Packing: the witness is below the declared bound, and the residual
      inclusion is read under an instance binding for the witness, in a scope
      with a root of its own. -/
  | pack {T : Dom s} :
      Γ ⊢ᶜ h : C ⊑ C₀ →
      Γ.scopeInst C ⊢ e : (Ty.weaken (k := .cap) (Ty.weaken (k := .cap) T')) ≤ T.underRoot →
      Γ.AccessOnly C →
      Γ ⊢ᵉ .pack C h e : .ty T' ≤ ∃ᶜ[C₀] T
  /-- Congruence: the bound is covariant and both bodies are read under a
      scope of their own. -/
  | cong {T T' : Dom s} :
      Γ ⊢ᶜ h : C₀ ⊑ C₀' →
      Γ.scope ⊢ e : T.underRoot ≤ T'.underRoot →
      Γ ⊢ᵉ .cong h e : ∃ᶜ[C₀] T ≤ ∃ᶜ[C₀'] T'
  | trans : Γ ⊢ᵉ g : E₁ ≤ E₂ → Γ ⊢ᵉ h : E₂ ≤ E₃ → Γ ⊢ᵉ .trans g h : E₁ ≤ E₃
  /-- A fresh pack: the witness is a list of distinct consumable names, and
      the residual inclusion is read in a scope that opens a root and then an
      heir of the witness.  The pack charges its witness at the `consume`
      mode (`ELeCo.charge`). -/
  | packF {Γ : Ctx s} {W : CaptureSet s} {e : LeCo (Sig.scope s)} {T' : Ty s} {T : Dom s} :
      CaptureSet.IsNames W → List.Nodup W →
      (∀ κ : BVar s .cap, CapAtom.cvar κ ∈ W → Ctx.Consumable Γ κ) →
      Γ.scopeOwn W ⊢ e : (Ty.weaken (k := .cap) (Ty.weaken (k := .cap) T')) ≤ T.underRoot →
      Γ ⊢ᵉ .packF W e : .ty T' ≤ ∃ᶠ T
  /-- Congruence of `∃ᶠ`: both bodies are read under a scope whose binder is
      a location. -/
  | congF {Γ : Ctx s} {e : LeCo (Sig.scope s)} {T T' : Dom s} :
      ((Γ.consC .root).consC (.loc true [])) ⊢ e : T.underRoot ≤ T'.underRoot →
      Γ ⊢ᵉ .congF e : ∃ᶠ T ≤ ∃ᶠ T'

end

open Lean PrettyPrinter in
@[app_unexpander CapCo.HasType] def CapCo.HasType.unexpand : Unexpander
  | `($_ $Γ $f $C $D) => `($Γ ⊢ᶜ $f : $C ⊑ $D)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander CapEq.HasType] def CapEq.HasType.unexpand : Unexpander
  | `($_ $Γ $φ $C $D) => `($Γ ⊢ᶜ $φ : $C ≡ $D)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander ShapeCo.HasType] def ShapeCo.HasType.unexpand : Unexpander
  | `($_ $Γ $e $S $T) => `($Γ ⊢ˢ $e : $S ≤ $T)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander LeCo.HasType] def LeCo.HasType.unexpand : Unexpander
  | `($_ $Γ $e $S $T) => `($Γ ⊢ $e : $S ≤ $T)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander EqCo.HasType] def EqCo.HasType.unexpand : Unexpander
  | `($_ $Γ $φ $S $T) => `($Γ ⊢ $φ : $S ≡ $T)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Has.HasType] def Has.HasType.unexpand : Unexpander
  | `($_ $Γ $h $x $ℓ) => `($Γ ⊢ $h : $x ∋ $ℓ)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Morphism.HasType] def Morphism.HasType.unexpand : Unexpander
  | `($_ $Γ $src $m $Tel) => `($Γ ⊢ $m : $src ⇒ $Tel)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Atom.HasType] def Atom.HasType.unexpand : Unexpander
  | `($_ $Γ $a $T) => `($Γ ⊢ₐ $a : $T)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander ELeCo.HasType] def ELeCo.HasType.unexpand : Unexpander
  | `($_ $Γ $g $E $E') => `($Γ ⊢ᵉ $g : $E ≤ $E')
  | _ => throw ()

/-- `Γ ⊢ₚ p : E`: packed atoms.  It premises only judgments of the block
above, so it is stated after it. -/
inductive PAtom.HasType : Ctx s → PAtom s → ETy s → Prop where
  | plain : Γ ⊢ₐ a : T → Γ ⊢ₚ .plain a : .ty T
  | pack {T : Dom s} :
      Γ ⊢ₐ a : S →
      Γ ⊢ᶜ h : C ⊑ C₀ →
      Γ.scopeInst C ⊢ e : (Ty.weaken (k := .cap) (Ty.weaken (k := .cap) S)) ≤ T.underRoot →
      Γ.AccessOnly C →
      Γ ⊢ₚ .pack C h e a : ∃ᶜ[C₀] T
  /-- The twin of `pack` for `∃ᶠ`, with the premises of `ELeCo.HasType.packF`. -/
  | packF {Γ : Ctx s} {a : Atom s} {S : Ty s} {W : CaptureSet s} {e : LeCo (Sig.scope s)}
      {T : Dom s} :
      Γ ⊢ₐ a : S →
      CaptureSet.IsNames W → List.Nodup W →
      (∀ κ : BVar s .cap, CapAtom.cvar κ ∈ W → Ctx.Consumable Γ κ) →
      Γ.scopeOwn W ⊢ e : (Ty.weaken (k := .cap) (Ty.weaken (k := .cap) S)) ≤ T.underRoot →
      Γ ⊢ₚ .packF W e a : ∃ᶠ T

open Lean PrettyPrinter in
@[app_unexpander PAtom.HasType] def PAtom.HasType.unexpand : Unexpander
  | `($_ $Γ $p $E) => `($Γ ⊢ₚ $p : $E)
  | _ => throw ()

/-! ## Member-free capture evidence

Capture evidence that reads no telescope: no `member`, no `eqToLe`, and every
atom it reaches through `capvar` carries member-free capture evidence in its
wrappers.  Bad capture bounds enter capture evidence only through `member`
and `eqToLe`, so this is exactly the restriction under which capture evidence
never lowers a level, which is `level_inversion`. -/

mutual

/-- Capture evidence that reads no telescope. -/
inductive CapCo.MemberFree {s : Sig} : CapCo s → Prop where
  | refl (C : CaptureSet s) : (CapCo.refl C).MemberFree
  | trans {f g : CapCo s} : f.MemberFree → g.MemberFree → (CapCo.trans f g).MemberFree
  | elem (C D : CaptureSet s) : (CapCo.elem C D).MemberFree
  | union {f g : CapCo s} : f.MemberFree → g.MemberFree → (CapCo.union f g).MemberFree
  | capvar {a : Atom s} : a.MemberFree → (CapCo.capvar a).MemberFree
  | level (e r : CapAtom s) : (CapCo.level e r).MemberFree
  | modeLe (a : CapAtom s) (m m' : EMode) : (CapCo.modeLe a m m').MemberFree
  | roMap {f : CapCo s} : f.MemberFree → (CapCo.roMap f).MemberFree
  | ownLe (a : CapAtom s) (W : CaptureSet s) : (CapCo.ownLe a W).MemberFree

/-- An atom whose capture wrappers are member free. -/
inductive Atom.MemberFree {s : Sig} : Atom s → Prop where
  | var (x : BVar s .var) : (Atom.var x).MemberFree
  | cast {a : Atom s} {e : ShapeCo s} {f : CapCo s} :
      a.MemberFree → f.MemberFree → (Atom.cast a (.capt e f)).MemberFree
  | recap {a : Atom s} {f : CapCo s} :
      a.MemberFree → f.MemberFree → (Atom.recap a f).MemberFree
  | foldSelf {a : Atom s} (Tel : Telescope (s,x)) :
      a.MemberFree → (Atom.foldSelf Tel a).MemberFree
  | unfoldSelf {a : Atom s} : a.MemberFree → (Atom.unfoldSelf a).MemberFree
  | both {a b : Atom s} (Tel₁ Tel₂ : Telescope (s,x)) :
      a.MemberFree → b.MemberFree → (Atom.both Tel₁ Tel₂ a b).MemberFree

end

/-! ### Notation for the term judgments -/

set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ " t:51 " :ᵉ " E:51 => Tm.HasType Γ t E
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ᵥ " v:51 " : " T:51 => Value.HasType Γ v T
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ᵥᵉ " v:51 " : " E:51 => Value.HasTypeE Γ v E
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ᶠ[" A "] " F:51 => Fields.HasType Γ A F

mutual

/-- `Γ ⊢ t :ᵉ E`: terms.  The index is an answer, and `Tm.HasTy` below is
the plain reading, which carries the notation `Γ ⊢ t : T`. -/
inductive Tm.HasType : Ctx s → Tm s → ETy s → Prop where
  | atom : Γ ⊢ₚ p : E → Γ ⊢ .atom p :ᵉ E
  /-- A program value holds no cell: a cell is created by `newLet` alone. -/
  | val : Γ ⊢ᵥᵉ v : E → Value.CellFree v → Γ ⊢ .val v :ᵉ E
  /-- The argument is checked at the *instantiated* domain: the arrow's
      capture binder goes to the argument's root.  A caller reaches it with
      `recap` and reflexivity.  The result is the codomain with the parameter
      at the argument and the capture binder at its root.  The callee's set
      is accessible and what it consumes is consumable, the argument is
      access-only and accessible where it crosses into the callee (plan-5h
      decision 39), and the argument names nothing the callee consumes. -/
  | app {T : Dom s} {U : Cod s} :
      Γ ⊢ₐ a : (Π(T) U) ^ C →
      Γ ⊢ₐ b : T.subst (Subst.singleC (.var b.root)) →
      Γ.Accessible C → Γ.ConsumeOk C →
      Γ.AccessOnly [.var b.root] →
      Γ.Accessible [.var b.root] →
      Γ.ArgSep [.var b.root] C →
      Γ ⊢ .app a b :ᵉ U.subst (Subst.arg b)
  /-- A field's result is the block name `ℓ` of the atom's root, captured at
      the capture name of the same label.  The capture witness `Wᶜ(ℓ)` of a
      literal is the declared capture set of the field's result, read by
      `defC` and resolved by `capsAtom`.  The receiver's set is accessible and
      what it consumes is consumable. -/
  | proj :
      Γ ⊢ₐ a : T →
      Γ ⊢ h : a.root ∋ ℓ →
      Γ.Accessible T.captureSet → Γ.ConsumeOk T.captureSet →
      Γ ⊢ .proj a ℓ h :ᵉ .ty ((a.root ∙ ℓ) ^ [CapAtom.name a.root ℓ])
  /-- The body of a let declares the use set `U'`, and the avoidance evidence
      `f` puts the body's use set below it.  `U'` does not mention the bound
      variable, so the use set of the let is structural.  The body may have an
      answer; a let whose body is plain is the rule as it stands.  The body is
      read with the head's consumed names killed, and those are consumable
      binders (`Ctx.KillOk`, plan-5h decision 38). -/
  | «let» :
      Γ ⊢ t :ᵉ .ty T →
      Γ.KillOk t.uses →
      (Γ.killFor t.uses).cons (.opaque T) ⊢ u :ᵉ E↑ →
      (Γ.killFor t.uses).cons (.opaque T) ⊢ᶜ f : u.uses ⊑ U'↑ →
      Γ ⊢ .let t u U' f :ᵉ E
  | cast : Γ ⊢ t :ᵉ .ty T → Γ ⊢ e : T ≤ T' → Γ ⊢ .cast t e :ᵉ .ty T'
  /-- The answer cast: the same former at the answer sort.  The evidence is
      read after the term, with the term's consumed names killed, and those
      are consumable binders. -/
  | castE : Γ ⊢ t :ᵉ E → Γ.KillOk t.uses → Γ.killFor t.uses ⊢ᵉ g : E ≤ E' →
      Γ ⊢ .castE t g :ᵉ E'
  /-- The head's bound is charged to the declared use set, the answer avoids
      both opened binders, and the body may name the opened binder in its
      charge.  The opened capture binder is rigid: it has no scope of its
      own, so two `letex`es open two incomparable binders.  The bound names
      nothing the declared set consumes, and the body is read with the
      head's consumed names killed.  Both kill sets, the head's uses and the
      declared set, consume only consumable binders.  The bound is accessible
      in the body's kill context, since the unpack instantiates the opened
      binder at it (plan-5h decision 39). -/
  | letex {T : Ty (s,c)} {C₀ U' : CaptureSet s} {E : ETy s} :
      Γ ⊢ t :ᵉ ∃ᶜ[C₀] T →
      Γ.KillOk t.uses →
      Γ ⊢ᶜ h : C₀ ⊑ U' → Γ.KillOk U' →
      Γ.ArgSep C₀ U' →
      (Γ.killFor t.uses).Accessible C₀ →
      (((Γ.killFor t.uses).consC .star).cons (.opaque T)) ⊢ u :ᵉ
        (ETy.weaken (k := .var) (ETy.weaken (k := .cap) E)) →
      (((Γ.killFor t.uses).consC .star).cons (.opaque T)) ⊢ᶜ f :
        u.uses ⊑ ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
          ∪ [CapAtom.cvar (.there .here)]) →
      Γ ⊢ .letex t u U' h f :ᵉ E
  /-- Unboxing, charged with the boxed capture set against the use set `U`
      the term declares.  The box's own set is accessible. -/
  | unbox :
      Γ ⊢ₐ a : (□ (S ^ C)) ^ D →
      Γ ⊢ᶜ f : C ⊑ U →
      Γ.Accessible D →
      Γ ⊢ .unbox a U f :ᵉ .ty (S ^ C)
  /-- Allocation of a cell at a fresh location: the content is pure, and the
      body is read under the location and the cell binder.  The body may
      consume its own location, and the declared set `U'` avoids it, so a
      fresh location is charged to nothing outside. -/
  | newLet {T : Ty s} {E : ETy s} {U' : CaptureSet s} :
      Γ ⊢ₐ a : T → T.captureSet = [] →
      Γ.cellCtx T ⊢ u :ᵉ (ETy.weaken (k := .var) (ETy.weaken (k := .cap) E)) →
      Γ.cellCtx T ⊢ᶜ f :
        u.uses ⊑ ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
          ∪ [CapAtom.mode .consume (CapAtom.cvar (.there .here))]) →
      Γ ⊢ .newLet a u U' f :ᵉ E
  /-- A read through a cell or a reader, whose set is accessible. -/
  | read {S : Shape s} {C : CaptureSet s} {T : Ty s} :
      Γ ⊢ₐ a : S ^ C → S.IsRefOf T → Γ.Accessible C →
      Γ ⊢ .read a :ᵉ .ty T
  /-- A write of a value of the content type into a cell whose set is
      accessible. -/
  | write {T : Ty s} {C : CaptureSet s} :
      Γ ⊢ₐ a : (Shape.cell T) ^ C → Γ ⊢ₐ b : T → Γ.Accessible C →
      Γ ⊢ .write a b :ᵉ .ty Ty.unit
  /-- The unpacking of `∃ᶠ`: the body is read with the head's consumed names
      killed, which are consumable binders, and with an opened name that
      claims them.  The body may consume
      its opened name, and the declared set `U'` avoids it. -/
  | letexF {T : Ty (s,c)} {E : ETy s} {U' : CaptureSet s} :
      Γ ⊢ t :ᵉ ∃ᶠ T →
      Γ.KillOk t.uses →
      Γ.freshCtx t.uses T ⊢ u :ᵉ (ETy.weaken (k := .var) (ETy.weaken (k := .cap) E)) →
      Γ.freshCtx t.uses T ⊢ᶜ f :
        u.uses ⊑ ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
          ∪ [CapAtom.mode .consume (CapAtom.cvar (.there .here))]) →
      Γ ⊢ .letexF t u U' f :ᵉ E

/-- `Γ ⊢ᵥ v : T`: values.  A value is pure: its type's capture set is empty in
this stage. -/
inductive Value.HasType : Ctx s → Value s → Ty s → Prop where
  /-- A lambda carries the capture set `A` its rule assigns to it, and the
      closing evidence `g` puts the body's use set below `A` weakened united
      with the parameter. -/
  | lam {T : Dom s} {U : Cod s} :
      Γ.body T ⊢ t :ᵉ U.underRoot →
      Γ.body T ⊢ᶜ g : t.uses ⊑ (A↑↑↑ ∪ [CapAtom.var .here]) →
      Γ ⊢ᵥ .lam A T t g : (Π(T) U) ^ A
  /-- An object literal has its precise type, generated from its witnesses and
      fields, at the capture set `A` it carries.  Fields are typed with the
      self binder at that type, against the same `A`. -/
  | obj {A : CaptureSet s} {F : Fields ((s,c),x)} {Γ : Ctx s} {W : Witnesses (s,x)}
      {Wc : CapWitnesses (s,x)} :
      Γ.objBody ((μ (Telescope.ofLiteral W Wc F.labels)) ^ A) W Wc F.labels ⊢ᶠ[A↑] F →
      (∀ ℓ : Label, ℓ ∈ CapWitnesses.labels Wc →
        Ctx.AccessOnly (Ctx.cons Γ (Binding.transparent
          ((μ (Telescope.ofLiteral W Wc (Fields.labels F))) ^ A) W Wc (Fields.labels F)))
          [CapAtom.name .here ℓ]) →
      Γ ⊢ᵥ .obj A W Wc F : (μ (Telescope.ofLiteral W Wc F.labels)) ^ A
  /-- Boxing is pure: the box shape hides the captured set.  A box is a
      literal with no witnesses and no fields. -/
  | box :
      Γ ⊢ₐ a : T →
      Γ ⊢ᵥ .box a : (□ T) ^ []
  | cast : Γ ⊢ᵥ v : T → Γ ⊢ e : T ≤ T' → Γ ⊢ᵥ .cast v e : T'
  /-- A cell sits at a location that claims nothing, and holds pure
      content: a capability is stored boxed (plan-5h decision 13). -/
  | cell {Γ : Ctx s} {c : CapAtom s} {b : Bool} {a : Atom s} {T : Ty s} :
      Ctx.LocOf Γ c b →
      Γ ⊢ₐ a : T →
      Ty.captureSet T = [] →
      Γ ⊢ᵥ .cell c a : (Shape.cell T) ^ [c]
  /-- A read-only view of the cell at a transparent binder.  In a store every
      term binder is transparent, and a transparent binder keeps its declared
      type across a substitution, so the view keeps its type there. -/
  | reader {Γ : Ctx s} {r : BVar s .var} {T : Ty s} {C : CaptureSet s} :
      Ctx.IsTransparent Γ r →
      Ctx.lookupTy Γ r = (Shape.cell T) ^ C →
      Γ ⊢ᵥ .reader r : (Shape.reader T) ^ [CapAtom.mode .ro (CapAtom.var r)]

/-- `Γ ⊢ᵥᵉ v : E`: values at the answer sort.  `Value.HasType` has no `pack`
rule, so a packed value has an existential answer and no other, and a packed
value is never stored. -/
inductive Value.HasTypeE : Ctx s → Value s → ETy s → Prop where
  | plain : Γ ⊢ᵥ v : T → Γ ⊢ᵥᵉ v : .ty T
  | pack {T : Dom s} :
      Γ ⊢ᵥ v : S →
      Γ ⊢ᶜ h : C ⊑ C₀ →
      Γ.scopeInst C ⊢ e : (Ty.weaken (k := .cap) (Ty.weaken (k := .cap) S)) ≤ T.underRoot →
      Γ.AccessOnly C →
      Γ ⊢ᵥᵉ .pack C h e v : ∃ᶜ[C₀] T
  /-- The twin of `pack` for `∃ᶠ`, with the premises of `ELeCo.HasType.packF`. -/
  | packF {Γ : Ctx s} {v : Value s} {S : Ty s} {W : CaptureSet s} {e : LeCo (Sig.scope s)}
      {T : Dom s} :
      Γ ⊢ᵥ v : S →
      CaptureSet.IsNames W → List.Nodup W →
      (∀ κ : BVar s .cap, CapAtom.cvar κ ∈ W → Ctx.Consumable Γ κ) →
      Γ.scopeOwn W ⊢ e : (Ty.weaken (k := .cap) (Ty.weaken (k := .cap) S)) ≤ T.underRoot →
      Γ ⊢ᵥᵉ .packF W e v : ∃ᶠ T

/-- `Γ ⊢ᶠ[A] F`: each field `ℓ = t` has type `(self ∙ ℓ) ^ {self ∙ ℓ}`, and
its closing evidence puts its use set below the literal's assigned set `A`
weakened united with the self.  The index `A` is the literal's assigned
set. -/
inductive Fields.HasType : Ctx (s,x) → CaptureSet s → Fields (s,x) → Prop where
  | nil : Γ ⊢ᶠ[A] .nil
  | cons :
      Γ ⊢ᶠ[A] F →
      Γ ⊢ t :ᵉ .ty ((.here ∙ ℓ) ^ [CapAtom.name .here ℓ]) →
      Γ ⊢ᶜ g : t.uses ⊑ (A↑ ∪ [CapAtom.var .here]) →
      Γ ⊢ᶠ[A] .cons F ℓ t g

end

/-! ### The base rules of the reshaped formers

A head that consumes nothing kills nothing (`Ctx.killFor_of_noConsume`), and a
declared set that consumes nothing is separated from every bound
(`Ctx.argSep_of_noConsume`).  So on a base program, where no set consumes, the
reshaped `let`, `castE` and `letex` are the rules of the copied base
(plan-5h S0.11). -/

theorem Tm.HasType.let_of_noConsume {Γ : Ctx s} {t : Tm s} {T : Ty s} {u : Tm (s,x)}
    {E : ETy s} {f : CapCo (s,x)} {U' : CaptureSet s}
    (ht : Γ ⊢ t :ᵉ .ty T) (hn : Γ.NoConsume t.uses)
    (hu : Γ.cons (.opaque T) ⊢ u :ᵉ E↑) (hf : Γ.cons (.opaque T) ⊢ᶜ f : u.uses ⊑ U'↑) :
    Γ ⊢ .let t u U' f :ᵉ E := by
  have hk := Ctx.killFor_of_noConsume hn
  refine .let ht (Ctx.KillOk.of_noConsume hn) ?_ ?_ <;> rw [hk]
  · exact hu
  · exact hf

theorem Tm.HasType.castE_of_noConsume {Γ : Ctx s} {t : Tm s} {E E' : ETy s} {g : ELeCo s}
    (ht : Γ ⊢ t :ᵉ E) (hn : Γ.NoConsume t.uses) (hg : Γ ⊢ᵉ g : E ≤ E') :
    Γ ⊢ .castE t g :ᵉ E' := by
  have hk := Ctx.killFor_of_noConsume hn
  refine .castE ht (Ctx.KillOk.of_noConsume hn) ?_
  rw [hk]
  exact hg

theorem Tm.HasType.letex_of_noConsume {Γ : Ctx s} {t : Tm s} {h : CapCo s}
    {u : Tm ((s,c),x)} {f : CapCo ((s,c),x)} {T : Ty (s,c)} {C₀ U' : CaptureSet s}
    {E : ETy s}
    (ht : Γ ⊢ t :ᵉ ∃ᶜ[C₀] T) (hn : Γ.NoConsume t.uses) (hU : Γ.NoConsume U')
    (hc : Γ ⊢ᶜ h : C₀ ⊑ U') (hacc : Γ.Accessible C₀)
    (hu : ((Γ.consC .star).cons (.opaque T)) ⊢ u :ᵉ
      (ETy.weaken (k := .var) (ETy.weaken (k := .cap) E)))
    (hf : ((Γ.consC .star).cons (.opaque T)) ⊢ᶜ f :
      u.uses ⊑ ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
        ∪ [CapAtom.cvar (.there .here)])) :
    Γ ⊢ .letex t u U' h f :ᵉ E := by
  have hk := Ctx.killFor_of_noConsume hn
  refine .letex ht (Ctx.KillOk.of_noConsume hn) hc (Ctx.KillOk.of_noConsume hU)
    (Ctx.argSep_of_noConsume hU) ?_ ?_ ?_ <;> rw [hk]
  · exact hacc
  · exact hu
  · exact hf

/-- The plain reading of term typing.  It carries the notation `Γ ⊢ t : T`,
so every statement written that way is the proposition it was before the
answer sort came in. -/
abbrev Tm.HasTy (Γ : Ctx s) (t : Tm s) (T : Ty s) : Prop := Tm.HasType Γ t (.ty T)

scoped notation:40 Γ:51 " ⊢ " t:51 " : " T:51 => Tm.HasTy Γ t T

open Lean PrettyPrinter in
@[app_unexpander Tm.HasType] def Tm.HasType.unexpand : Unexpander
  | `($_ $Γ $t $E) => `($Γ ⊢ $t :ᵉ $E)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Tm.HasTy] def Tm.HasTy.unexpand : Unexpander
  | `($_ $Γ $t $T) => `($Γ ⊢ $t : $T)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Value.HasType] def Value.HasType.unexpand : Unexpander
  | `($_ $Γ $v $T) => `($Γ ⊢ᵥ $v : $T)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Value.HasTypeE] def Value.HasTypeE.unexpand : Unexpander
  | `($_ $Γ $v $E) => `($Γ ⊢ᵥᵉ $v : $E)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Fields.HasType] def Fields.HasType.unexpand : Unexpander
  | `($_ $Γ $A $F) => `($Γ ⊢ᶠ[$A] $F)
  | _ => throw ()

end FCdot

end Separation
