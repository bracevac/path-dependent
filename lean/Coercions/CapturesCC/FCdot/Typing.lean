import Coercions.CapturesCC.FCdot.Context

namespace CapturesCC

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
      `e` is `r` or encloses it.  Both sides are singletons.  A set shaped
      conclusion is a `union` of instances. -/
  | level :
      Γ.IsRoot r →
      Γ.LvlLe e r →
      Γ ⊢ᶜ .level e r : [e] ⊑ [r]

/-- `Γ ⊢ᶜ φ : C ≡ D`: equality evidence between capture sets. -/
inductive CapEq.HasType : Ctx s → CapEq s → CaptureSet s → CaptureSet s → Prop where
  | refl : Γ ⊢ᶜ .refl C : C ≡ C
  | symm : Γ ⊢ᶜ φ : C₁ ≡ C₂ → Γ ⊢ᶜ .symm φ : C₂ ≡ C₁
  | trans : Γ ⊢ᶜ φ : C₁ ≡ C₂ → Γ ⊢ᶜ ψ : C₂ ≡ C₃ → Γ ⊢ᶜ .trans φ ψ : C₁ ≡ C₃
  /-- Definition of a transparent binder's capture name. -/
  | defC : Γ.lookupDefC x ℓ = some C → Γ ⊢ᶜ .defC x ℓ : [CapAtom.name x ℓ] ≡ C
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
  /-- Contravariant domain, covariant codomain; both are type inclusions. -/
  | pi :
      Γ ⊢ e : T2 ≤ T1 →
      Γ.cons (.opaque T2) ⊢ f : U1 ≤ U2 →
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

/-! ### Notation for the term judgments -/

set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ " t:51 " : " T:51 => Tm.HasType Γ t T
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ᵥ " v:51 " : " T:51 => Value.HasType Γ v T
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ᶠ[" A "] " F:51 => Fields.HasType Γ A F

mutual

/-- `Γ ⊢ t : T`: terms. -/
inductive Tm.HasType : Ctx s → Tm s → Ty s → Prop where
  | atom : Γ ⊢ₐ a : T → Γ ⊢ .atom a : T
  | val : Γ ⊢ᵥ v : T → Γ ⊢ .val v : T
  | app :
      Γ ⊢ₐ a : (Π(T) U) ^ C →
      Γ ⊢ₐ b : T →
      Γ ⊢ .app a b : U⟦b.root⟧
  /-- A field's result is the block name `ℓ` of the atom's root, captured at
      the capture name of the same label.  The capture witness `Wᶜ(ℓ)` of a
      literal is the declared capture set of the field's result, read by
      `defC` and resolved by `capsAtom`. -/
  | proj :
      Γ ⊢ₐ a : T →
      Γ ⊢ h : a.root ∋ ℓ →
      Γ ⊢ .proj a ℓ h : (a.root ∙ ℓ) ^ [CapAtom.name a.root ℓ]
  /-- The body of a let declares the use set `U'`, and the avoidance evidence
      `f` puts the body's use set below it.  `U'` does not mention the bound
      variable, so the use set of the let is structural. -/
  | «let» :
      Γ ⊢ t : T →
      Γ.cons (.opaque T) ⊢ u : U↑ →
      Γ.cons (.opaque T) ⊢ᶜ f : u.uses ⊑ U'↑ →
      Γ ⊢ .let t u U' f : U
  | cast : Γ ⊢ t : T → Γ ⊢ e : T ≤ T' → Γ ⊢ .cast t e : T'
  /-- Unboxing, charged with the boxed capture set against the use set `U`
      the term declares. -/
  | unbox :
      Γ ⊢ₐ a : (□ (S ^ C)) ^ D →
      Γ ⊢ᶜ f : C ⊑ U →
      Γ ⊢ .unbox a U f : S ^ C

/-- `Γ ⊢ᵥ v : T`: values.  A value is pure: its type's capture set is empty in
this stage. -/
inductive Value.HasType : Ctx s → Value s → Ty s → Prop where
  /-- A lambda carries the capture set `A` its rule assigns to it, and the
      closing evidence `g` puts the body's use set below `A` weakened united
      with the parameter. -/
  | lam :
      Γ.cons (.opaque T) ⊢ t : U →
      Γ.cons (.opaque T) ⊢ᶜ g : t.uses ⊑ (A↑ ∪ [CapAtom.var .here]) →
      Γ ⊢ᵥ .lam A T t g : (Π(T) U) ^ A
  /-- An object literal has its precise type, generated from its witnesses and
      fields, at the capture set `A` it carries.  Fields are typed with the
      self binder at that type, against the same `A`. -/
  | obj :
      Γ.cons (.transparent ((μ (Telescope.ofLiteral W Wc F.labels)) ^ A) W Wc F.labels) ⊢ᶠ[A] F →
      Γ ⊢ᵥ .obj A W Wc F : (μ (Telescope.ofLiteral W Wc F.labels)) ^ A
  /-- Boxing is pure: the box shape hides the captured set.  A box is a
      literal with no witnesses and no fields. -/
  | box :
      Γ ⊢ₐ a : T →
      Γ ⊢ᵥ .box a : (□ T) ^ []
  | cast : Γ ⊢ᵥ v : T → Γ ⊢ e : T ≤ T' → Γ ⊢ᵥ .cast v e : T'

/-- `Γ ⊢ᶠ[A] F`: each field `ℓ = t` has type `(self ∙ ℓ) ^ {self ∙ ℓ}`, and
its closing evidence puts its use set below the literal's assigned set `A`
weakened united with the self.  The index `A` is the literal's assigned
set. -/
inductive Fields.HasType : Ctx (s,x) → CaptureSet s → Fields (s,x) → Prop where
  | nil : Γ ⊢ᶠ[A] .nil
  | cons :
      Γ ⊢ᶠ[A] F →
      Γ ⊢ t : (.here ∙ ℓ) ^ [CapAtom.name .here ℓ] →
      Γ ⊢ᶜ g : t.uses ⊑ (A↑ ∪ [CapAtom.var .here]) →
      Γ ⊢ᶠ[A] .cons F ℓ t g

end

open Lean PrettyPrinter in
@[app_unexpander Tm.HasType] def Tm.HasType.unexpand : Unexpander
  | `($_ $Γ $t $T) => `($Γ ⊢ $t : $T)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Value.HasType] def Value.HasType.unexpand : Unexpander
  | `($_ $Γ $v $T) => `($Γ ⊢ᵥ $v : $T)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Fields.HasType] def Fields.HasType.unexpand : Unexpander
  | `($_ $Γ $A $F) => `($Γ ⊢ᶠ[$A] $F)
  | _ => throw ()

end FCdot

end CapturesCC
