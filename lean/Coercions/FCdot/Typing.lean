import Coercions.FCdot.Context

/-!
# FCdot typing

Evidence typing assigns endpoints to proof terms.  Term typing has no
subsumption; every inclusion is an explicit `cast`.  Elimination at an atom
(`member`) is the only way member facts flow from a binder's type to its
block.
-/

namespace FCdot

/-! ### Notation for the evidence judgments

Declared before the judgments so that the rules can use them; the
pretty-printers are attached after. -/

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

/-- `Γ ⊢ e : S ≤ T`: inclusion evidence. -/
inductive LeCo.HasType : Ctx s → LeCo s → Ty s → Ty s → Prop where
  | refl : Γ ⊢ .refl T : T ≤ T
  | trans : Γ ⊢ e : S ≤ M → Γ ⊢ f : M ≤ T → Γ ⊢ .trans e f : S ≤ T
  | top : Γ ⊢ .top T : T ≤ ⊤
  | bot : Γ ⊢ .bot T : ⊥ ≤ T
  | eqToLe : Γ ⊢ φ : S ≡ T → Γ ⊢ .eqToLe φ : S ≤ T
  | pi :
      Γ ⊢ e : S2 ≤ S1 →
      Γ.cons (.opaque S2) ⊢ f : T1 ≤ T2 →
      Γ ⊢ .pi e f : Π(S1) T1 ≤ Π(S2) T2
  /-- Object coercion between closed telescopes: the morphism proves each target
      proposition by a template over a source proposition. -/
  | obj :
      Γ ⊢ m : Tel ⇒ Tel' →
      Γ ⊢ .obj Tel m : μ Tel ≤ μ Tel'
  /-- Pairing: two coercions into object types give one into the concatenation. -/
  | pair :
      Γ ⊢ e : S ≤ μ Tel₁ →
      Γ ⊢ f : S ≤ μ Tel₂ →
      Γ ⊢ .pair Tel₁ Tel₂ e f : S ≤ μ (Tel₁ ++ Tel₂)
  | member :
      Γ ⊢ₐ a : S →
      Γ ⊢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ S' ⊑ T') →
      Γ ⊢ .member a e i : S'⟦a.root⟧ ≤ T'⟦a.root⟧

/-- `Γ ⊢ φ : S ≡ T`: equality evidence. -/
inductive EqCo.HasType : Ctx s → EqCo s → Ty s → Ty s → Prop where
  | refl : Γ ⊢ .refl T : T ≡ T
  | symm : Γ ⊢ φ : S ≡ T → Γ ⊢ .symm φ : T ≡ S
  | trans : Γ ⊢ φ : S ≡ M → Γ ⊢ ψ : M ≡ T → Γ ⊢ .trans φ ψ : S ≡ T
  | def : Γ.lookupDef x ℓ = some W → Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W
  | member :
      Γ ⊢ₐ a : S →
      Γ ⊢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ S' ≐ T') →
      Γ ⊢ .member a e i : S'⟦a.root⟧ ≡ T'⟦a.root⟧

/-- `Γ ⊢ h : x ∋ ℓ`: `h` proves that the block of `x` has field `ℓ`. -/
inductive Has.HasType : Ctx s → Has s → BVar s .var → Label → Prop where
  | member :
      Γ ⊢ₐ a : S →
      Γ ⊢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ ∋ ℓ) →
      Γ ⊢ .member a e i : a.root ∋ ℓ
  | field :
      Γ.lookupFields x = some Fs → ℓ ∈ Fs →
      Γ ⊢ .field ℓ : x ∋ ℓ

/-- A template side: `none` leaves the endpoint as it is; `some e` is a closed
coercion `A ≤ B` between weakened closed types. -/
inductive Side.HasType : Ctx s → Side s → Ty (s,x) → Ty (s,x) → Prop where
  | none : Side.HasType Γ .none X X
  | some : Γ ⊢ e : A ≤ B → Side.HasType Γ (.some e) A↑ B↑

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

/-- `Γ ⊢ₐ a : T`: atoms. -/
inductive Atom.HasType : Ctx s → Atom s → Ty s → Prop where
  | var : Γ ⊢ₐ .var x : Γ.lookupTy x
  | cast : Γ ⊢ₐ a : S → Γ ⊢ e : S ≤ T → Γ ⊢ₐ .cast a e : T
  /-- `Rec-E`: the self block of the object type is the atom's own block. -/
  | unfoldSelf :
      Γ ⊢ₐ a : μ Tel →
      Γ ⊢ₐ .unfoldSelf a : μ (Tel⟦a.root⟧)↑
  /-- `Rec-I`. -/
  | foldSelf :
      Γ ⊢ₐ a : μ (Tel⟦a.root⟧)↑ →
      Γ ⊢ₐ .foldSelf Tel a : μ Tel
  /-- `And-I`: two typings of the same root. -/
  | both :
      Γ ⊢ₐ a : μ Tel₁ →
      Γ ⊢ₐ b : μ Tel₂ →
      b.root = a.root →
      Γ ⊢ₐ .both Tel₁ Tel₂ a b : μ (Tel₁ ++ Tel₂)

end

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
scoped notation:40 Γ:51 " ⊢ᶠ " F:51 => Fields.HasType Γ F

mutual

/-- `Γ ⊢ t : T`: terms. -/
inductive Tm.HasType : Ctx s → Tm s → Ty s → Prop where
  | atom : Γ ⊢ₐ a : T → Γ ⊢ .atom a : T
  | val : Γ ⊢ᵥ v : T → Γ ⊢ .val v : T
  | app :
      Γ ⊢ₐ a : Π(S) T →
      Γ ⊢ₐ b : S →
      Γ ⊢ .app a b : T⟦b.root⟧
  | proj :
      Γ ⊢ₐ a : S →
      Γ ⊢ h : a.root ∋ ℓ →
      Γ ⊢ .proj a ℓ h : a.root ∙ ℓ
  | «let» :
      Γ ⊢ t : T →
      Γ.cons (.opaque T) ⊢ u : U↑ →
      Γ ⊢ .let t u : U
  | cast : Γ ⊢ t : S → Γ ⊢ e : S ≤ T → Γ ⊢ .cast t e : T

/-- `Γ ⊢ᵥ v : T`: values. -/
inductive Value.HasType : Ctx s → Value s → Ty s → Prop where
  | lam :
      Γ.cons (.opaque S) ⊢ t : T →
      Γ ⊢ᵥ .lam S t : Π(S) T
  /-- An object literal has its precise type, generated from its witnesses and
      fields.  Fields are typed with the self binder at that type. -/
  | obj :
      W.Guarded →
      Γ.cons (.transparent (μ (Telescope.ofLiteral W F.labels)) W F.labels) ⊢ᶠ F →
      Γ ⊢ᵥ .obj W F : μ (Telescope.ofLiteral W F.labels)
  | cast : Γ ⊢ᵥ v : S → Γ ⊢ e : S ≤ T → Γ ⊢ᵥ .cast v e : T

/-- `Γ ⊢ᶠ F`: each field `ℓ = t` has type `self ∙ ℓ`. -/
inductive Fields.HasType : Ctx (s,x) → Fields (s,x) → Prop where
  | nil : Γ ⊢ᶠ .nil
  | cons : Γ ⊢ᶠ F → Γ ⊢ t : .here ∙ ℓ → Γ ⊢ᶠ .cons F ℓ t

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
  | `($_ $Γ $F) => `($Γ ⊢ᶠ $F)
  | _ => throw ()

end FCdot
