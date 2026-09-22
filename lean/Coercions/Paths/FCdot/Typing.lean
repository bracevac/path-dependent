import Coercions.Paths.FCdot.Context

namespace Paths

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
scoped notation:40 Γ:51 " ⊢ " h:51 " : " p:max " ∋ " ℓ:max => Has.HasType Γ h p ℓ
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ " m:51 " : " src:51 " ⇒ " Tel:51 => Morphism.HasType Γ src m Tel
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ₐ " a:51 " : " T:51 => Atom.HasType Γ a T
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ᵖ " P:51 " : " T:51 => PathCo.HasType Γ P T
-- The alias judgment between two paths.  The token is `≋`, not `≈`: the
-- proposition `≈ q` is a prefix at the highest level, so `p ≈ q` also parses
-- as `p` applied to that proposition.
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ " α:51 " : " p:51 " ≋ " q:51 => AliasCo.HasType Γ α p q

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
  /-- The annotated object type is below its `i`-th bound. -/
  | bound :
      Tel ∋ (i ↦ ⊑ T↑) →
      Γ ⊢ .bound Tel i : μ Tel ≤ T
  /-- An `S` below `T` is an `S` below the one-bound object type. -/
  | intoBnd :
      Γ ⊢ e : S ≤ T →
      Γ ⊢ .intoBnd e : S ≤ μ (.nil ▹ ⊑ T↑)
  | member :
      Γ ⊢ₐ a : S →
      Γ ⊢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ S' ⊑ T') →
      Γ ⊢ .member a e i : S'⟦a.root⟧ ≤ T'⟦a.root⟧
  /-- Elimination at a stable path.  `member` is this rule at a path of depth
      zero, by `Ty.substPath_var`. -/
  | memberP :
      Γ ⊢ᵖ P : S →
      Γ ⊢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ S' ⊑ T') →
      Γ ⊢ .memberP P e i : S'.substPath P.path ≤ T'.substPath P.path

/-- `Γ ⊢ φ : S ≡ T`: equality evidence. -/
inductive EqCo.HasType : Ctx s → EqCo s → Ty s → Ty s → Prop where
  | refl : Γ ⊢ .refl T : T ≡ T
  | symm : Γ ⊢ φ : S ≡ T → Γ ⊢ .symm φ : T ≡ S
  | trans : Γ ⊢ φ : S ≡ M → Γ ⊢ ψ : M ≡ T → Γ ⊢ .trans φ ψ : S ≡ T
  | def : Γ.lookupDef x ℓ = some W → Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W
  /-- Definition of the block name of a path.  `def` is this rule at a path of
      depth zero, by `Ctx.lookupDefP_var`. -/
  | defP : Γ.lookupDefP p ℓ = some W → Γ ⊢ .defP p ℓ : p ∙ ℓ ≡ W
  | member :
      Γ ⊢ₐ a : S →
      Γ ⊢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ S' ≐ T') →
      Γ ⊢ .member a e i : S'⟦a.root⟧ ≡ T'⟦a.root⟧
  | memberP :
      Γ ⊢ᵖ P : S →
      Γ ⊢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ S' ≐ T') →
      Γ ⊢ .memberP P e i : S'.substPath P.path ≡ T'.substPath P.path

/-- `Γ ⊢ h : p ∋ ℓ`: `h` proves that the block of `p` has field `ℓ`.  A binder
is the path of depth zero, so the base's rules read as they read today. -/
inductive Has.HasType : Ctx s → Has s → Path s → Label → Prop where
  | member :
      Γ ⊢ₐ a : S →
      Γ ⊢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ ∋ ℓ) →
      Γ ⊢ .member a e i : (Path.var a.root) ∋ ℓ
  | memberP :
      Γ ⊢ᵖ P : S →
      Γ ⊢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ ∋ ℓ) →
      Γ ⊢ .memberP P e i : P.path ∋ ℓ
  | field :
      Γ.lookupFields x = some Fs → ℓ ∈ Fs →
      Γ ⊢ .field ℓ : (Path.var x) ∋ ℓ

/-- A template side: `none` leaves the endpoint as it is; `some e` is a closed
coercion `A ≤ B` between weakened closed types.  `bot` and `top` are the two
constant sides.  Neither reads the source, so a template that uses one stays
closed. -/
inductive Side.HasType : Ctx s → Side s → Ty (s,x) → Ty (s,x) → Prop where
  | none : Side.HasType Γ .none X X
  | some : Γ ⊢ e : A ≤ B → Side.HasType Γ (.some e) A↑ B↑
  | bot : Side.HasType Γ (.bot X) ⊥ X
  | top : Side.HasType Γ (.top X) X ⊤

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
      type. -/
  | bnd : Γ ⊢ m : src ⇒ Tel → Γ ⊢ e : μ src ≤ T →
      Γ ⊢ .bnd m e : src ⇒ Tel ▹ ⊑ T↑
  /-- A stable presence is copied from the source by index. -/
  | hasVal : Γ ⊢ m : src ⇒ Tel → src ∋ (j ↦ ∋ᵛ ℓ) →
      Γ ⊢ .hasVal m j : src ⇒ Tel ▹ ∋ᵛ ℓ
  /-- A presence is read off a source stable presence by index. -/
  | hasOfVal : Γ ⊢ m : src ⇒ Tel → src ∋ (j ↦ ∋ᵛ ℓ) →
      Γ ⊢ .hasOfVal m j : src ⇒ Tel ▹ ∋ ℓ
  /-- An alias is copied from the source by index. -/
  | aliasCopy : Γ ⊢ m : src ⇒ Tel → src ∋ (j ↦ ≈ q) →
      Γ ⊢ .aliasCopy m j : src ⇒ Tel ▹ ≈ q

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
  /-- Introduction of a singleton, at the root of an atom.  The premise is
      about the root and never about the type, which is what keeps every other
      inhabitant of the atom's type out of the singleton. -/
  | sngl :
      Γ ⊢ₐ a : S →
      Γ ⊢ α : (Path.var a.root) ≋ q →
      Γ ⊢ₐ .sngl a q α : Ty.snglOf q

/-- `Γ ⊢ᵖ P : T`: the block at `P.path` exists and its type is `T`.  The
atom rules, one field step through a stable presence, and aliasing. -/
inductive PathCo.HasType : Ctx s → PathCo s → Ty s → Prop where
  | var : Γ ⊢ᵖ .var x : Γ.lookupTy x
  /-- One field step, licensed by a stable presence of the path's own type.
      This is decision 1: a field that holds a computation gives `∋ a` and no
      step, so a name below it is opaque. -/
  | sel :
      Γ ⊢ᵖ P : μ Tel →
      Tel ∋ (i ↦ ∋ᵛ a) →
      Γ ⊢ᵖ .sel P a i : P.path ∙ a
  | cast : Γ ⊢ᵖ P : S → Γ ⊢ e : S ≤ T → Γ ⊢ᵖ .cast P e : T
  /-- Two names of one block have one type. -/
  | alias :
      Γ ⊢ α : p ≋ P.path →
      Γ ⊢ᵖ P : T →
      Γ ⊢ᵖ .alias α p P : T
  /-- `Rec-E`: the self block of the object type is the path's own block. -/
  | unfoldSelf :
      Γ ⊢ᵖ P : μ Tel →
      Γ ⊢ᵖ .unfoldSelf P : μ ((Tel.substPath P.path)↑)
  /-- `Rec-I`. -/
  | foldSelf :
      Γ ⊢ᵖ P : μ ((Tel.substPath P.path)↑) →
      Γ ⊢ᵖ .foldSelf Tel P : μ Tel
  /-- `And-I`: two typings of one path. -/
  | both :
      Γ ⊢ᵖ P : μ Tel₁ →
      Γ ⊢ᵖ Q : μ Tel₂ →
      Q.path = P.path →
      Γ ⊢ᵖ .both Tel₁ Tel₂ P Q : μ (Tel₁ ++ Tel₂)
  /-- Introduction of a singleton, at a path.  This is pDOT's `ty_sngl`: the
      path is typed at the singleton of `q`, and nothing else is. -/
  | sngl :
      Γ ⊢ᵖ P : S →
      Γ ⊢ α : P.path ≋ q →
      Γ ⊢ᵖ .sngl P q α : Ty.snglOf q
  /-- A node of the forest, at the precise type of the literal whose block the
      table wrote at `p`.  The premise reads `Ctx.nodeBlock`, the walk that
      follows no forwarding, so a path whose walk passes a forwarding is no
      node (decision 24).  The path is a field step: a binder is typed by
      `var` at its declared type, and the block of a closure's binder is
      `obj nil [] [] nil`, whose literal type is not the closure's. -/
  | node :
      p.isSel = true →
      Γ.nodeBlock p = some (.obj (W.substPath p) ls vls ch) →
      Γ ⊢ᵖ .node p W ls vls : μ (Telescope.ofLiteral W ls vls)

/-- `Γ ⊢ α : p ≋ q`: the two paths name one block of the forest.  A view's
alias is read by `member`, and the rest are the laws of an equality.  No rule
reads the table or the store, which is why T2 is an induction.  A forwarding
node of the table serves resolution only (decision 24). -/
inductive AliasCo.HasType : Ctx s → AliasCo s → Path s → Path s → Prop where
  | refl : Γ ⊢ .refl p : p ≋ p
  | symm : Γ ⊢ α : p ≋ q → Γ ⊢ .symm α : q ≋ p
  | trans : Γ ⊢ α : p ≋ q → Γ ⊢ β : q ≋ r → Γ ⊢ .trans α β : p ≋ r
  | sel : Γ ⊢ α : p ≋ q → Γ ⊢ .sel α a : (Path.sel p a) ≋ (Path.sel q a)
  /-- The alias a view carries.  Its soundness is the `alias` clause of
      `EntryTyped`, which is where the semantic condition lives. -/
  | member :
      Γ ⊢ᵖ P : S →
      Γ ⊢ e : S ≤ μ Tel →
      Tel ∋ (i ↦ ≈ q) →
      Γ ⊢ .member P e i : P.path ≋ (q.substPath P.path)

end

/-- Every typed atom is a typed stable path of depth zero, under the same
wrappers.  This is row 1 of table P1.9 on the evidence side: a binder is the
path of depth zero, and `Telescope.substPath_var` bridges the two
instantiations. -/
theorem PathCo.HasType.ofAtom {s : Sig} {Γ : Ctx s} :
    ∀ {a : Atom s} {T : Ty s}, Γ ⊢ₐ a : T → Γ ⊢ᵖ a.toPathCo : T
  | _, _, .var => .var
  | _, _, .cast ha he => .cast (PathCo.HasType.ofAtom ha) he
  | _, _, @Atom.HasType.unfoldSelf _ _ a Tel ha => by
      have := PathCo.HasType.unfoldSelf (PathCo.HasType.ofAtom ha)
      simpa [Atom.toPathCo, Atom.path_toPathCo] using this
  | _, _, @Atom.HasType.foldSelf _ _ a Tel ha => by
      have ha' := PathCo.HasType.ofAtom ha
      simp only [Atom.path_toPathCo, Telescope.substPath_var] at ha' ⊢
      exact PathCo.HasType.foldSelf (by simpa [Atom.path_toPathCo] using ha')
  | _, _, @Atom.HasType.both _ _ a Tel₁ b Tel₂ ha hb hr => by
      exact PathCo.HasType.both (PathCo.HasType.ofAtom ha) (PathCo.HasType.ofAtom hb)
        (by simp [Atom.path_toPathCo, hr])
  | _, _, @Atom.HasType.sngl _ _ a S α q ha hα => by
      refine PathCo.HasType.sngl (PathCo.HasType.ofAtom ha) ?_
      rw [Atom.path_toPathCo]
      exact hα

/-- The alias a singleton licenses, read off the type by `AliasCo.member` at
index 0 with `LeCo.refl`.  With `LeCo.intoSngl` gone this is the only way an
alias proposition reaches a telescope out of a `sngl` step. -/
theorem alias_of_sngl {s : Sig} {Γ : Ctx s} {P : PathCo s} {q : Path s}
    (hP : Γ ⊢ᵖ P : Ty.snglOf q) :
    Γ ⊢ .member P (.refl (Ty.snglOf q)) 0 : P.path ≋ q := by
  have h := AliasCo.HasType.member hP (LeCo.HasType.refl (T := Ty.snglOf q))
    (Telescope.At.here (Tel := .nil) (P := .alias q.weaken))
  simpa [Telescope.length, Path.weaken_substPath] using h

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
@[app_unexpander PathCo.HasType] def PathCo.HasType.unexpand : Unexpander
  | `($_ $Γ $P $T) => `($Γ ⊢ᵖ $P : $T)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander AliasCo.HasType] def AliasCo.HasType.unexpand : Unexpander
  | `($_ $Γ $α $p $q) => `($Γ ⊢ $α : $p ≋ $q)
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
      Γ ⊢ h : (Path.var a.root) ∋ ℓ →
      Γ ⊢ .proj a ℓ h : a.root ∙ ℓ
  | «let» :
      Γ ⊢ t : T →
      Γ.cons (.opaque T) ⊢ u : U↑ →
      Γ ⊢ .let t u : U
  /-- The let over a path.  The term is typed at the singleton of `q`, and the
      binder is transparent at the forwarding node to `q`, so both readings of
      the alias are in scope in the body, the type and the table. -/
  | letPath :
      Γ ⊢ t : Ty.snglOf q →
      Γ.cons (Binding.fwdAt q) ⊢ u : U↑ →
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
      Γ.cons (.transparent (μ (Telescope.ofLiteral W F.labels F.valLabels))
          (.obj W F.labels F.valLabels (F.children (.var .here)))) ⊢ᶠ F →
      Γ ⊢ᵥ .obj W F : μ (Telescope.ofLiteral W F.labels F.valLabels)
  | cast : Γ ⊢ᵥ v : S → Γ ⊢ e : S ≤ T → Γ ⊢ᵥ .cast v e : T

/-- `Γ ⊢ᶠ F`: each field `ℓ = t` has type `self ∙ ℓ`. -/
inductive Fields.HasType : Ctx (s,x) → Fields (s,x) → Prop where
  | nil : Γ ⊢ᶠ .nil
  | cons : Γ ⊢ᶠ F → Γ ⊢ t : (Path.var .here) ∙ ℓ → Γ ⊢ᶠ .cons F ℓ t

end

/-! ## The let over a field declared at a singleton

`letPath` covers `let y = x.a in u` when `x ∙ a` is defined, or declared, as a
singleton.  Two forms, one at a prefix whose block the table holds and one at
an opaque prefix root, where the singleton is read off the declared
telescope. -/

/-- The let over a field whose definition the table gives as a singleton. -/
theorem letPath_of_field {s : Sig} {Γ : Ctx s} {x : BVar s .var} {a : Label} {h : Has s}
    {q : Path s} {u : Tm (s,x)} {U : Ty s}
    (hx : Γ ⊢ₐ .var x : Γ.lookupTy x) (hh : Γ ⊢ h : (Path.var x) ∋ a)
    (hdef : Γ.lookupDefP (.var x) a = some (Ty.snglOf q))
    (hu : Γ.cons (Binding.fwdAt q) ⊢ u : U↑) :
    Γ ⊢ .let (.cast (.proj (.var x) a h) (.eqToLe (.defP (.var x) a))) u : U :=
  .letPath (.cast (.proj hx hh) (.eqToLe (.defP hdef))) hu

/-- The twin at an opaque prefix root: the singleton comes off the declared
telescope by `EqCo.member` in place of `EqCo.defP`. -/
theorem letPath_of_member {s : Sig} {Γ : Ctx s} {w : BVar s .var} {a : Label} {hf : Has s}
    {S : Ty s} {e : LeCo s} {Tel : Telescope (s,x)} {i : Nat} {q : Path s}
    {u : Tm (s,x)} {U : Ty s}
    (hw : Γ ⊢ₐ .var w : S) (he : Γ ⊢ e : S ≤ μ Tel)
    (hAt : Tel ∋ (i ↦ ((Path.var .here) ∙ a) ≐ (Ty.snglOf q)↑))
    (hh : Γ ⊢ hf : (Path.var w) ∋ a)
    (hu : Γ.cons (Binding.fwdAt q) ⊢ u : U↑) :
    Γ ⊢ .let (.cast (.proj (.var w) a hf) (.eqToLe (.member (.var w) e i))) u : U := by
  refine Tm.HasType.letPath (Tm.HasType.cast (Tm.HasType.proj hw hh) ?_) hu
  have hm := LeCo.HasType.eqToLe (EqCo.HasType.member hw he hAt)
  rw [Ty.weaken_substVar] at hm
  simpa [Atom.root, Ty.substVar, Ty.rename, Path.rename] using hm

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

end Paths
