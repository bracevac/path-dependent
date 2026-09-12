import Coercions.Classifiers.FCdot.Context

namespace Classifiers

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

/-! ### Reading a kinding proposition at a hole

A kinding hole names one proposition of its source telescope and reads it as
it stands.  There is no flipped reading, because a kinding proposition is not
an equality, so the hole is a plain index and not a `HoleC`. -/

/-- `src.HoleAtK j C φ`: the `j`-th proposition of `src` is `C ⊑ᵏ φ`. -/
inductive Telescope.HoleAtK (src : Telescope (s,x)) :
    Nat → CaptureSet (s,x) → Cls.Kind → Prop where
  | kindC : src ∋ (j ↦ C ⊑ᵏ φ) → Telescope.HoleAtK src j C φ

/-! ### Notation for the evidence judgments

Declared before the judgments so that the rules can use them; the
pretty-printers are attached after. -/

set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ᶜ " f:51 " : " C:71 " ⊑ " D:71 => CapCo.HasType Γ f C D
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ᶜ " φ:51 " : " C:71 " ≡ " D:71 => CapEq.HasType Γ φ C D
set_option hygiene false in
scoped notation:40 Γ:51 " ⊢ᵏ " g:51 " : " C:71 " ⊑ᵏ " φ:71 => KindCo.HasType Γ g C φ
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
      `e` is `r` or encloses it.  Both sides are singletons.  A set shaped
      conclusion is a `union` of instances. -/
  | level :
      Γ.IsRoot r →
      Γ.LvlLe e r →
      Γ ⊢ᶜ .level e r : [e] ⊑ [r]
  /-- A projection only drops atoms, so the projected set is below the set it
      projects.  Capless(K) reads this off its kind aware `CaptureSet.Subset`;
      a capture set is a plain list here, so it is a rule. -/
  | unprojC : Γ ⊢ᶜ .unprojC C φ : C.proj φ ⊑ C
  /-- `sc-proj` (`Subcapt.lean:69`): a set kinded at `φ` is below its own
      projection at `φ`.  Stated on a set, and the singleton form of
      Capless(K) is the instance at `C = [a]`.  The set and the kind are on
      the evidence term, where the checker reads them. -/
  | projC : Γ ⊢ᵏ g : C ⊑ᵏ φ → Γ ⊢ᶜ .projC g C φ : C ⊑ C.proj φ
  /-- The congruence, which gives the projection form of every other rule.
      `sc-var` at a projection is this rule composed with `capvar`, since
      `[a].proj ψ` is `[a ↾ ψ]`. -/
  | projMono : Γ ⊢ᶜ f : C ⊑ D → Γ ⊢ᶜ .projMono f ψ : C.proj ψ ⊑ D.proj ψ

/-- `Γ ⊢ᵏ g : C ⊑ᵏ φ`: kinding evidence.  Every capability `C` reaches
carries a classifier that `φ` admits.  It mentions atoms (`kvar`, `kmember`)
and shape coercions (`kmember`), and `CapCo.HasType.projC` premises it, so it
belongs to the mutual block.

Two rules of Capless(K) are merged into one here, and both merges are exact.
`kproj` is `k-cbound` and `k-absurd` (`Subcapt.lean:50,54`) read through
`CapAtom.kindOf`, which is `⊤` at a bare atom, so the family covers a bare
atom exactly as Capless(K) covers a capture, where every capture carries a
kind by construction.  `kcls` is `k-label` and `k-label-absurd`
(`Subcapt.lean:51-52`): `k-label` asks `(ψ ∩ φ) ∋ c`, which by
`Kind.contains_inter` is `ψ ∋ c ∧ φ ∋ c`, and `k-label-absurd` asks
`¬ ψ ∋ c`, so their disjunction is the implication `ψ ∋ c → φ ∋ c`.
`kcls` applies at a binder that *declares* a classifier, which is the `cls`
flavour and nothing else, exactly as Capless(K)'s two label rules apply at a
label.  A `star` binder declares none: `Ctx.Ren.instC`, the instantiation
lemma T-B2.1, reads a `star` binder as an instance of an arbitrary set, so a
rule that read the root classifier off a `star` binder would not survive that
map.  That is not a matter of taste.  K6x of `FCdot/Examples.lean` exhibits a
context where such a rule derives a kinding whose canonical form is true, and
`Ctx.Ren.instC` carries that context to one where the same canonical form is
false, so the kinding family would lose `KindCo.HasType.renameR`.  The price
is that the family is not complete at a `star` binder, and K6x decides both
halves of the gap.  A `star` binder is Capless(K)'s capture variable at the
kind bound `⊤`, and `kproj` is its rule. -/
inductive KindCo.HasType : Ctx s → KindCo s → CaptureSet s → Cls.Kind → Prop where
  /-- k-empty (`Subcapt.lean:55`). -/
  | nil : Γ ⊢ᵏ .nil : [] ⊑ᵏ φ
  /-- k-union (`Subcapt.lean:53`). -/
  | cons : Γ ⊢ᵏ g : [a] ⊑ᵏ φ → Γ ⊢ᵏ h : C ⊑ᵏ φ → Γ ⊢ᵏ .cons g h : (a :: C) ⊑ᵏ φ
  /-- k-cbound and k-absurd in one (`Subcapt.lean:50,54`): an atom whose own
      kind is below the target is kinded, whatever it resolves to.  At a bare
      atom the premise asks that `φ` admit every classifier, which is what a
      root stands for. -/
  | kproj : a.kindOf.Subkind φ → Γ ⊢ᵏ .kproj a : [a] ⊑ᵏ φ
  /-- k-label and k-label-absurd in one (`Subcapt.lean:51-52`): a capability
      with a declared classifier is kinded when that classifier is admitted
      by the target as soon as the projection admits it.  The premise is read
      flavour-wise on the base of the atom, as `CapEq.HasType.instC` reads an
      instance binder, so that the rule travels along a substitution. -/
  | kcls :
      Γ.ClsOf a.base c →
      (a.kindOf.Contains c → φ.Contains c) →
      Γ ⊢ᵏ .kcls a : [a] ⊑ᵏ φ
  /-- k-var (`Subcapt.lean:48`). -/
  | kvar :
      Γ ⊢ₐ b : S ^ C →
      a.base = CapAtom.var b.root →
      Γ ⊢ᵏ g : C.proj a.kindOf ⊑ᵏ φ →
      Γ ⊢ᵏ .kvar b g : [a] ⊑ᵏ φ
  /-- k-cvar (`Subcapt.lean:49`), at both set bounds the tree distinguishes,
      which is what `Ctx.SetOf` reads.  The evidence carries the atom and the
      rule reads its binder off `CapAtom.base`, for the reason `CapEq.instC`
      gives. -/
  | kcvar :
      Γ.SetOf a.base C →
      Γ ⊢ᵏ g : C.proj a.kindOf ⊑ᵏ φ →
      Γ ⊢ᵏ .kcvar a g : [a] ⊑ᵏ φ
  /-- The telescope member, the rule Capless(K) has no counterpart for: the
      `i`-th proposition of the object shape `e` lands in, instantiated at the
      atom.  Read beside `CapCo.HasType.member`. -/
  | kmember :
      Γ ⊢ₐ b : S ^ D →
      Γ ⊢ˢ e : S ≤ μ Tel →
      Telescope.HoleAtK Tel i C φ →
      Γ ⊢ᵏ .kmember b e i : C⟦b.root⟧ ⊑ᵏ φ
  /-- Projection only shrinks a set, so a kinded set stays kinded under
      one.  The source set is on the evidence term, where the checker reads
      it: `CaptureSet.proj` is not invertible. -/
  | kprojS : Γ ⊢ᵏ g : C ⊑ᵏ φ → Γ ⊢ᵏ .kprojS g C ψ : C.proj ψ ⊑ᵏ φ
  /-- k-sub (`Subcapt.lean:99-109`), a primitive constructor and not a derived
      lemma, so that the checker is one structural match.  The kind on the
      evidence term is the *source* kind `φ₁`: the target is what a checking
      mode is given, and the source is what it has to be told. -/
  | ksub : Γ ⊢ᵏ g : C ⊑ᵏ φ₁ → φ₁.Subkind φ₂ → Γ ⊢ᵏ .ksub g φ₁ : C ⊑ᵏ φ₂

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
      has a root of its own, which is the scope discipline of the stage. -/
  | pi {T1 T2 : Dom s} {U1 U2 : Cod s} :
      Γ.scope ⊢ e : T2.underRoot ≤ T1.underRoot →
      Γ.body T2 ⊢ᵉ f : U1.underRoot ≤ U2.underRoot →
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
  /-- A target kinding proposition: a side chain lowering the target set to
      the source set of the `j`-th source kinding proposition, and an
      admission step from the source kind to the target kind.  The step is
      `Cls.Kind.AdmitsStep` and not `Cls.Kind.Subkind`, so that the identity
      template on a kinding proposition is derivable: subkinding is not known
      to be reflexive, which is decision 6. -/
  | kindC : Γ ⊢ m : src ⇒ Tel → src ∋ (j ↦ C ⊑ᵏ φ₁) →
      SideC.HasType Γ q D C → φ₁.AdmitsStep φ₂ →
      Γ ⊢ .kindC m q j φ₂ : src ⇒ Tel ▹ D ⊑ᵏ φ₂

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
      Γ ⊢ᵉ .pack C h e : .ty T' ≤ ∃ᶜ[C₀] T
  /-- Congruence: the bound is covariant and both bodies are read under a
      scope of their own. -/
  | cong {T T' : Dom s} :
      Γ ⊢ᶜ h : C₀ ⊑ C₀' →
      Γ.scope ⊢ e : T.underRoot ≤ T'.underRoot →
      Γ ⊢ᵉ .cong h e : ∃ᶜ[C₀] T ≤ ∃ᶜ[C₀'] T'
  | trans : Γ ⊢ᵉ g : E₁ ≤ E₂ → Γ ⊢ᵉ h : E₂ ≤ E₃ → Γ ⊢ᵉ .trans g h : E₁ ≤ E₃

end

open Lean PrettyPrinter in
@[app_unexpander CapCo.HasType] def CapCo.HasType.unexpand : Unexpander
  | `($_ $Γ $f $C $D) => `($Γ ⊢ᶜ $f : $C ⊑ $D)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander KindCo.HasType] def KindCo.HasType.unexpand : Unexpander
  | `($_ $Γ $g $C $φ) => `($Γ ⊢ᵏ $g : $C ⊑ᵏ $φ)
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
      Γ ⊢ₚ .pack C h e a : ∃ᶜ[C₀] T

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
  | unprojC (C : CaptureSet s) (φ : Cls.Kind) : (CapCo.unprojC C φ).MemberFree
  | projC {g : KindCo s} (C : CaptureSet s) (φ : Cls.Kind) :
      g.MemberFree → (CapCo.projC g C φ).MemberFree
  | projMono {f : CapCo s} (ψ : Cls.Kind) : f.MemberFree → (CapCo.projMono f ψ).MemberFree

/-- Kinding evidence that reads no telescope: no `kmember`, and every atom it
reaches through `kvar` carries member-free capture evidence in its wrappers.
It excludes `kmember` exactly as `CapCo.MemberFree` excludes `member`. -/
inductive KindCo.MemberFree {s : Sig} : KindCo s → Prop where
  | nil : (KindCo.nil : KindCo s).MemberFree
  | cons {g h : KindCo s} : g.MemberFree → h.MemberFree → (KindCo.cons g h).MemberFree
  | kproj (a : CapAtom s) : (KindCo.kproj a).MemberFree
  | kcls (a : CapAtom s) : (KindCo.kcls a).MemberFree
  | kvar {b : Atom s} {g : KindCo s} :
      b.MemberFree → g.MemberFree → (KindCo.kvar b g).MemberFree
  | kcvar {g : KindCo s} (a : CapAtom s) : g.MemberFree → (KindCo.kcvar a g).MemberFree
  | kprojS {g : KindCo s} (C : CaptureSet s) (ψ : Cls.Kind) :
      g.MemberFree → (KindCo.kprojS g C ψ).MemberFree
  | ksub {g : KindCo s} (φ : Cls.Kind) : g.MemberFree → (KindCo.ksub g φ).MemberFree

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
  | val : Γ ⊢ᵥᵉ v : E → Γ ⊢ .val v :ᵉ E
  /-- The argument is checked at the *instantiated* domain: the arrow's
      capture binder goes to the argument's root.  A caller reaches it with
      `recap` and reflexivity.  The result is the codomain with the parameter
      at the argument and the capture binder at its root. -/
  | app {T : Dom s} {U : Cod s} :
      Γ ⊢ₐ a : (Π(T) U) ^ C →
      Γ ⊢ₐ b : T.subst (Subst.singleC (.var b.root)) →
      Γ ⊢ .app a b :ᵉ U.subst (Subst.arg b)
  /-- A field's result is the block name `ℓ` of the atom's root, captured at
      the capture name of the same label.  The capture witness `Wᶜ(ℓ)` of a
      literal is the declared capture set of the field's result, read by
      `defC` and resolved by `capsAtom`. -/
  | proj :
      Γ ⊢ₐ a : T →
      Γ ⊢ h : a.root ∋ ℓ →
      Γ ⊢ .proj a ℓ h :ᵉ .ty ((a.root ∙ ℓ) ^ [CapAtom.name a.root ℓ])
  /-- The body of a let declares the use set `U'`, and the avoidance evidence
      `f` puts the body's use set below it.  `U'` does not mention the bound
      variable, so the use set of the let is structural.  The body may have an
      answer; a let whose body is plain is the rule as it stands. -/
  | «let» :
      Γ ⊢ t :ᵉ .ty T →
      Γ.cons (.opaque T) ⊢ u :ᵉ E↑ →
      Γ.cons (.opaque T) ⊢ᶜ f : u.uses ⊑ U'↑ →
      Γ ⊢ .let t u U' f :ᵉ E
  | cast : Γ ⊢ t :ᵉ .ty T → Γ ⊢ e : T ≤ T' → Γ ⊢ .cast t e :ᵉ .ty T'
  /-- The answer cast: the same former at the answer sort. -/
  | castE : Γ ⊢ t :ᵉ E → Γ ⊢ᵉ g : E ≤ E' → Γ ⊢ .castE t g :ᵉ E'
  /-- The head's bound is charged to the declared use set, the answer avoids
      both opened binders, and the body may name the opened binder in its
      charge.  The opened capture binder is rigid: it has no scope of its
      own, so two `letex`es open two incomparable binders. -/
  | letex {T : Ty (s,c)} {C₀ U' : CaptureSet s} {E : ETy s} :
      Γ ⊢ t :ᵉ ∃ᶜ[C₀] T →
      Γ ⊢ᶜ h : C₀ ⊑ U' →
      ((Γ.consC .star).cons (.opaque T)) ⊢ u :ᵉ
        (ETy.weaken (k := .var) (ETy.weaken (k := .cap) E)) →
      ((Γ.consC .star).cons (.opaque T)) ⊢ᶜ f :
        u.uses ⊑ ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U'))
          ∪ [CapAtom.cvar (.there .here)]) →
      Γ ⊢ .letex t u U' h f :ᵉ E
  /-- Unboxing, charged with the boxed capture set against the use set `U`
      the term declares. -/
  | unbox :
      Γ ⊢ₐ a : (□ (S ^ C)) ^ D →
      Γ ⊢ᶜ f : C ⊑ U →
      Γ ⊢ .unbox a U f :ᵉ .ty (S ^ C)

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
  | obj :
      Γ.objBody ((μ (Telescope.ofLiteral W Wc F.labels)) ^ A) W Wc F.labels ⊢ᶠ[A↑] F →
      Γ ⊢ᵥ .obj A W Wc F : (μ (Telescope.ofLiteral W Wc F.labels)) ^ A
  /-- Boxing is pure: the box shape hides the captured set.  A box is a
      literal with no witnesses and no fields. -/
  | box :
      Γ ⊢ₐ a : T →
      Γ ⊢ᵥ .box a : (□ T) ^ []
  | cast : Γ ⊢ᵥ v : T → Γ ⊢ e : T ≤ T' → Γ ⊢ᵥ .cast v e : T'

/-- `Γ ⊢ᵥᵉ v : E`: values at the answer sort.  `Value.HasType` has no `pack`
rule, so a packed value has an existential answer and no other, and a packed
value is never stored. -/
inductive Value.HasTypeE : Ctx s → Value s → ETy s → Prop where
  | plain : Γ ⊢ᵥ v : T → Γ ⊢ᵥᵉ v : .ty T
  | pack {T : Dom s} :
      Γ ⊢ᵥ v : S →
      Γ ⊢ᶜ h : C ⊑ C₀ →
      Γ.scopeInst C ⊢ e : (Ty.weaken (k := .cap) (Ty.weaken (k := .cap) S)) ≤ T.underRoot →
      Γ ⊢ᵥᵉ .pack C h e v : ∃ᶜ[C₀] T

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

end Classifiers
