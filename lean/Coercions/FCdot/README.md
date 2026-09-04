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
| `Context` | bindings, contexts, lookup of types, definitions and fields; guardedness |
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
| `Examples` | the five mandatory examples E1 to E5, decided in the kernel |

## Notation

All notation is `scoped` in namespace `FCdot`.

| | |
|---|---|
| `⊤`, `⊥`, `x ∙ ℓ`, `Π(S) T`, `μ Tel` | types; `μ` binds the implicit self variable of the telescope |
| `S ⊑ T`, `S ≐ T`, `∋ ℓ` | propositions (data, hence not `≤`, `=`) |
| `Tel ▹ P`, `Tel ∋ (i ↦ P)` | telescope extension; the `i`-th proposition, counted from the oldest (also for entries `Es` and views `V`) |
| `T↑`, `T⟦y⟧` | weakening under a new binder; instantiation of the innermost binder |
| `Γ ⊢ e : S ≤ T`, `Γ ⊢ φ : S ≡ T`, `Γ ⊢ h : x ∋ ℓ` | inclusion, equality, and presence evidence |
| `Γ ⊢ m : src ⇒ Tel` | a morphism proving the opened telescope `Tel`, inheriting presence from `src` |
| `Γ ⊢ₐ a : T`, `Γ ⊢ t : T`, `Γ ⊢ᵥ v : T`, `Γ ⊢ᶠ F` | atoms, terms, values, fields |
| `⊢ σ : Γ`, `Γ ⊢ₖ K : T ⇒ U` | stores and continuations |
| `st ⟶ st'`, `st ⟶* st'`, `⌊st⌋` | steps and erasure |
| `σ ⊢ e ⇓[n] F`, `σ ⊢ m ⇓ₘ[n] Es`, `σ ⊢ a ⇓ᵥ[n] V`, `σ ⊢ x ; h ⇓ₕ[n] (y, ℓ)`, `σ ⊢ a ⇓ᶜ[n] (a', F)` | normalization with fuel `n` |
| `Γ ⊨ F : S ≤ T`, `Γ ⊨[r] F : S ≤ T` | typed coercion form; typed chain of casts at root `r` |
| `Γ ⊨ Es : Tel₁ ⇒ Tel₂`, `Γ ⊨[r, σ] V : Tel` | typed entries; typed view |

## Design

* **Inert stores.**  An object literal `obj W F` carries witnesses `W` (a
  definition per block label) and fields `F`.  Its precise type is the
  telescope generated from them, `μ (Telescope.ofLiteral W F.labels)`: one
  `self ∙ ℓ ≐ W.get ℓ` per witness, one `∋ ℓ` per field.  Facts beyond
  definitions are established by coercions in the term.
* **Opened object coercions.**  `obj Tel m : μ Tel↑ ≤ μ Tel'↑` compares two
  telescopes with no self binder; a closed, self-mentioning object type is
  reached only from an atom, by `foldSelf`.  This is DOT, which has no
  subtyping rule between `μ` types.  Consequently the normal form of a
  coercion does not depend on the atom it is applied to, and the normalizer
  is structural.
* **One plain typedness; chains typed at opened shapes.**  Coercion forms,
  entries, and views are typed with plain shapes (`Γ.resolve`), by one
  inductive `Γ ⊨ F : S ≤ T`.  The chain of casts of an atom rooted at `r` is
  not a second judgment: it is plain typedness at the resolved endpoints
  with their self block opened at `r` (`Γ ⊨[r] F : S ≤ T` is
  `Γ ⊨ F : Γ.resolveAt r S ≤ Γ.resolveAt r T`), so `foldSelf` and
  `unfoldSelf` are invisible to it.  Plain typedness at `S, T` gives
  typedness at the opened shapes at any root (`FormTyped.atRoot`), and the
  chain composes by the plain composition lemma (`ChainTyped.combine`).
* **Telescope-shaped forms.**  Entries of an object form and views of atoms
  are telescope-shaped inductives (`Es ▹ E`, `V ▹ P`, oldest first) indexed
  by `Es ∋ (i ↦ E)`, `V ∋ (i ↦ P)`, exactly like `Telescope.At`; their
  typedness judgments mirror the telescope they are typed against.

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
```

Axioms (`#print axioms`): `propext` and `Quot.sound` for all of the above;
`progress` and `erase_reflect'` additionally use `Classical.choice`.  The
tree contains no `sorry`, `axiom`, `partial`, or `native_decide`.

## What is not here

No open-evidence normalization: the machine only ever normalizes closed
evidence over the store, and that is all the metatheory needs.  No
consistency corollaries stated separately (they are milestone M5).  The
translation from `DotMNF` is milestones M3 to M4.
