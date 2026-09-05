# FCdot

FCdot is the explicit-evidence coercion target of Plan III
(`plan-3-dot-mnf-to-fcdot.md`): a DOT-like calculus in which every use of
subtyping, type equality, and field presence is a proof term, and in which
those proof terms erase to nothing.  This directory is milestone M1: the
calculus, its checker, its machine, and the metatheory that makes the
erasure safe.

## Reading order

| module | contents |
|---|---|
| `Debruijn` | signatures `s`, bound variables `BVar s k`, renamings |
| `Syntax` | types, propositions, telescopes; evidence (`LeCo`, `EqCo`, `Has`, `Morphism`); atoms; terms and values; renaming |
| `Context` | bindings, contexts, lookup of types, definitions and fields |
| `Typing` | the judgments `Γ ⊢ e : S ≤ T`, `Γ ⊢ φ : S ≡ T`, `Γ ⊢ h : x ∋ ℓ`, `Γ ⊢ m : src ⇒ Tel`, `Γ ⊢ₐ a : T`, `Γ ⊢ t : T`, `Γ ⊢ᵥ v : T`, `Γ ⊢ᶠ F` |
| `Store` | stores, store typing `⊢ σ : Γ` |
| `Normalizer` | head normal forms of closed evidence, views of atoms, the fuel-indexed normalizer `σ ⊢ e ⇓[n] F` |
| `Machine` | continuations `Γ ⊢ₖ K : T ⇒ U`, states, the step relation `st ⟶ st'` |
| `Erasure` | erasure `⌊·⌋` into the shared runtime |
| `RenameLemmas`, `TypingRename`, `Transparency`, `TypingSubst` | renaming and substitution, and their action on typing |
| `Preservation` | inversion lemmas, `preservation` (modulo the `FormsTyped` obligation) |
| `ErasureMetatheory` | forward simulation `erase_step`, backward simulation `erase_reflect` (modulo canonical forms), final states |
| `Checker`, `CheckerCompleteness` | the decision procedure and `checkTm_iff` and friends |
| `Resolution` | `Γ.resolve`: following transparent definitions, and why a fixed fuel suffices |
| `FormTyping` | typedness of forms `Γ ⊨ F : S ≤ T`, `Γ ⊨[r] F : S ≤ T`, entries, and views `Γ ⊨[r, σ] V : Tel` |
| `FormAlgebra` | composition and application of typed forms; fuel monotonicity and determinism |
| `CanonicalForms` | the canonical-forms theorem; the chain of casts; `preservation'`, `erase_reflect'` |
| `Progress` | `progress`, `not_stuck` |
| `Consistency` | shapes of closed inclusions; no closed `⊤ ≤ ⊥`; block names are defined; stores stay typed along runs (`reachable_consistent`) |
| `Examples` | the examples E1 to E7, decided in the kernel |

## Notation

All notation is `scoped` in namespace `FCdot`.

| | |
|---|---|
| `⊤`, `⊥`, `x ∙ ℓ`, `Π(S) T`, `μ Tel` | types; `μ` binds the implicit self variable of the telescope |
| `S ⊑ T`, `S ≐ T`, `∋ ℓ` | propositions (data, hence not `≤`, `=`) |
| `Tel ▹ P`, `Tel ∋ (i ↦ P)` | telescope extension; the `i`-th proposition, counted from the oldest (also for entries `Es` and views `V`) |
| `T↑`, `T⟦y⟧` | weakening under a new binder; instantiation of the innermost binder |
| `Γ ⊢ e : S ≤ T`, `Γ ⊢ φ : S ≡ T`, `Γ ⊢ h : x ∋ ℓ` | inclusion, equality, and presence evidence |
| `Γ ⊢ m : src ⇒ Tel` | a template morphism proving the closed telescope `Tel` from the propositions of `src` |
| `Γ ⊢ₐ a : T`, `Γ ⊢ t : T`, `Γ ⊢ᵥ v : T`, `Γ ⊢ᶠ F` | atoms, terms, values, fields |
| `⊢ σ : Γ`, `Γ ⊢ₖ K : T ⇒ U` | stores and continuations |
| `st ⟶ st'`, `st ⟶* st'`, `⌊st⌋` | steps and erasure |
| `σ ⊢ e ⇓[n] F`, `σ ⊢ m ⇓ₘ[n] Es`, `σ ⊢ a ⇓ᵥ[n] V`, `σ ⊢ x ; h ⇓ₕ[n] (y, ℓ)`, `σ ⊢ a ⇓ᶜ[n] (a', F)` | normalization with fuel `n` |
| `Γ ⊨ F : S ≤ T`, `Γ ⊨[r] F : S ≤ T` | typed coercion form; typed chain of casts at root `r` |
| `Γ ⊨ Es : Tel₁ ⇒ Tel₂`, `Γ ⊨[r, σ] V : Tel` | typed template entries between closed telescopes; typed view |

## Design

* **Inert stores.**  An object literal `obj W F` carries witnesses `W` (a
  definition per block label) and fields `F`.  Its precise type is the
  telescope generated from them, `μ (Telescope.ofLiteral W F.labels)`: one
  `self ∙ ℓ ≐ W.get ℓ` per witness, one `∋ ℓ` per field.  Facts beyond
  definitions are established by coercions in the term.  Block names are
  *defined* by these witnesses (`Ctx.lookupDef`); a witness may itself be a
  name of the same block, so aliases within a block are allowed, including
  same-block cycles.  Resolution (`Ctx.resolve`) follows such aliases;
  alias-tolerant resolution shows a fixed fuel always suffices, because a
  chain of definitions either settles at a shape or an undefined name, or
  else must repeat within `Γ.defPairs.length` steps (pigeonhole on the
  context's finitely many defined names), and a cyclic alias resolves to
  `⊤` (the empty object type).
* **Object coercions are template morphisms.**  `obj Tel m : μ Tel ≤ μ Tel'`
  compares two closed telescopes; each target proposition is proven by a
  *template* `pre ∘ (source proposition j) ∘ post` with closed sides typed
  in `Γ`, or is a source equality (possibly flipped), or inherits a
  presence by index.  A template never eliminates through the self's
  members, which is what keeps normalization structural: the normal form
  of a coercion does not depend on the atom it is applied to, composition
  substitutes templates into templates, and application looks the source
  proposition up in the atom's view.  `pair` intersects two coercions into
  object types; the atom `both` intersects two typings of one root
  (`And-I`).  `⊤` is the empty object type `μ .nil`.
* **Two modes of typedness.**  Coercion forms and views are typed with plain
  shapes (`Γ.resolve`).  Only the chain of casts of an atom is typed at the
  atom's root, where the self block is opened at that root, so `foldSelf`
  and `unfoldSelf` are invisible to it (`Ctx.resolveAt`, `ChainTyped`).
  Plain typedness lifts to any root (`FormTyped.atRoot`) with no
  well-definedness hypothesis.

## Main theorems

```
checkTm_iff        : checkTm Γ t T = true ↔ Γ ⊢ t : T
le_canon           : ⊢ σ : Γ → Γ ⊢ e : S ≤ T → ∃ n F, σ ⊢ e ⇓[n] F ∧ Γ ⊨ F : S ≤ T
atom_canon         : ⊢ σ : Γ → Γ ⊢ₐ a : S → ∃ n V, σ ⊢ a ⇓ᵥ[n] V ∧
                       (∀ Tel, Γ.resolve S = μ Tel → Γ ⊨[a.root, σ] V : Tel) ∧ Γ.resolve S ≠ ⊥
has_canon          : ⊢ σ : Γ → Γ ⊢ h : x ∋ ℓ → ∃ n, σ ⊢ x ; h ⇓ₕ[n] (x, ℓ) ∧ σ.HasField x ℓ
closedAtomForm_typed : ⊢ σ : Γ → Γ ⊢ₐ a : S →
                       ∃ n a' F, σ ⊢ a ⇓ᶜ[n] (a', F) ∧ Γ ⊨[a.root] F : Γ.lookupTy a.root ≤ S
preservation'      : st.Typed U → st ⟶ st' → ∃ ρ, st'.Typed (U.rename ρ)
progress           : st.Typed U → st.Final ∨ ∃ s' (st' : State s'), st ⟶ st'
erase_step         : st ⟶ st' → (cast-frame step ∧ ⌊st⌋ = ⌊st'⌋) ∨ Runtime.Step ⌊st⌋ ⌊st'⌋
erase_reflect'     : ⊢ st.σ : Γ → (∃ T, Γ ⊢ st.t : T) → Runtime.Step ⌊st⌋ r →
                       ∃ st', st ⟶* st' ∧ ⌊st'⌋ = r
closed_le_shapes   : ⊢ σ : Γ → Γ ⊢ e : S ≤ T → (S resolves to ⊥) ∨ (T resolves to ⊤) ∨
                       (equal resolutions) ∨ (both Π) ∨ (both μ)
reachable_consistent : st.Typed U → st ⟶* st' → ∃ Γ, ⊢ st'.σ : Γ ∧ (¬ ∃ e, Γ ⊢ e : ⊤ ≤ ⊥) ∧
                       ∀ x ℓ, ∃ W, Γ.lookupDef x ℓ = some W ∧ Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W
```

Axioms (`#print axioms`): `propext` and `Quot.sound` for all of the above.  The
tree contains no `sorry`, `axiom`, `partial`, or `native_decide`.

## What is not here

No open-evidence normalization: the machine only ever normalizes closed
evidence over the store, and that is all the metatheory needs.  The
translation from `DotMNF` lives in `lean/Coercions/DotToFCdot/`.
