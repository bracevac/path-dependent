# FCdot, at stage K2 of classifiers

FCdot is the explicit-evidence coercion target of Plan III
(`plan-3-dot-mnf-to-fcdot.md`): a DOT-like calculus in which every use of
subtyping, type equality, and field presence is a proof term, and in which
those proof terms erase to nothing.  This directory is milestone M1: the
calculus, its checker, its machine, and the metatheory that makes the
erasure safe.

## Reading order

| module | contents |
|---|---|
| `Cls` (`Coercions.Classifiers.Cls`) | the classifier tree, kinds as subtrees with exclusions, and their order, membership, emptiness, intersection, subtraction and subkinding.  Below the whole development, importing nothing of it |
| `Debruijn` | signatures `s`, bound variables `BVar s k`, renamings |
| `Syntax` | types, propositions, telescopes, the answer sort `ETy` with its declared bound; evidence (`LeCo`, `ELeCo`, `EqCo`, `Has`, `Morphism`); atoms and packed atoms `PAtom`; terms and values; renaming, and substitution `Subst` with an atom-valued capture component and the instantiations `singleC`, `arg`, `enter`, `enterC`, `enterObj`, `instRoot` |
| `Context` | bindings, contexts, lookup of types, definitions and fields, levels as positions on the spine, the instance reader `Ctx.InstOf`, and the four scope contexts `Ctx.scope`, `Ctx.scopeInst`, `Ctx.body`, `Ctx.objBody` |
| `Typing` | the judgments `Γ ⊢ e : S ≤ T`, `Γ ⊢ᵉ g : E ≤ E'`, `Γ ⊢ φ : S ≡ T`, `Γ ⊢ h : x ∋ ℓ`, `Γ ⊢ m : src ⇒ Tel`, `Γ ⊢ₐ a : T`, `Γ ⊢ₚ p : E`, `Γ ⊢ t :ᵉ E`, `Γ ⊢ᵥ v : T`, `Γ ⊢ᵥᵉ v : E`, `Γ ⊢ᶠ[A] F` |
| `Store` | stores, store typing `⊢ σ : Γ` |
| `Normalizer` | head normal forms of closed evidence, views of atoms, the fuel-indexed normalizer `σ ⊢ e ⇓[n] F` |
| `Machine` | continuations `Γ ⊢ₖ K : E ⇒ U`, states, the step relation `st ⟶ st'`, and the answer coercion applied to a value or a packed atom (`Value.applyE`, `PAtom.applyE`) |
| `Erasure` | erasure `⌊·⌋` into the shared runtime |
| `RenameLemmas`, `TypingRename`, `Transparency`, `TypingSubst` | renaming and substitution, and their action on typing |
| `Preservation` | inversion lemmas, `preservation` (modulo the `FormsTyped` obligation) |
| `ErasureMetatheory` | forward simulation `erase_step`, backward simulation `erase_reflect` (modulo canonical forms), final states |
| `Checker`, `CheckerCompleteness` | the decision procedure and `checkTm_iff` and friends |
| `Resolution` | `Γ.resolve`: following transparent definitions, and why a fixed fuel suffices; capture resolution `Ctx.caps`, its expansion `Ctx.capBinders`, `Ctx.expandAtom`, `Ctx.expand`, and `Ctx.roots = expand ∘ caps` |
| `LevelInversion` | `level_inversion`: member-free capture evidence never lowers a level, store free |
| `Levels` | levels as positions on the spine: the order lemmas of `Ctx.root?`, `Ctx.lvl`, `Ctx.isRootB` and `Ctx.lvlLeB`, L0 (every binder is at or outside the innermost root), and the weakening commutations |
| `FormTyping` | typedness of forms `Γ ⊨ F : S ≤ T`, `Γ ⊨[r] F : S ≤ T`, entries, and views `Γ ⊨[r, σ] V : Tel` |
| `FormAlgebra` | composition and application of typed forms; fuel monotonicity and determinism |
| `CanonicalForms` | the canonical-forms theorem, including item 6 (`cap_canon`) and item 7 (an atom's root is below the capture set of its type); the chain of casts; `closed_box_inversion`; `preservation'`, `erase_reflect'` |
| `Progress` | `progress`, `not_stuck` |
| `Consistency` | shapes of closed inclusions; no closed `⊤ ≤ ⊥`; block names are defined; stores stay typed along runs (`reachable_consistent`) |
| `Prediction` | the use-set half of preservation (`step_uses`), `capture_prediction` along a run, `inspects_covered`, `effect_safety`, `classified_prediction` and `classified_effect_safety`, `returned_capture_bound` |
| `Examples` | the examples E1 to E8 and the capture examples C3, C4, C1, C6, decided in the kernel; the target side of the A3a source examples S3, C2, C7; and the target side of the A3b ones, `S1_client` (an operation declared at `{fs}` recaptured at `{cp.C}` by the lower bound of a capture member), `S1_translated`, `S1_erase`, `S2_translated`, `S2_erase`, and C5, the packing of an existential result: `C5_capWitnesses`, `C5_witnesses` and `C5_litMorphism` read off the translation, `C5_literal` and `C5_packing` decided by `checkValue` and `checkLe`, and `C5_client`, the caller that reaches `{fs}` only through the member's upper bound; and the B1 examples `scope_order`, `C2_typed` (the literal, with the class root outside the self), `X4_no_level` and `X4_no_escape` (the `withFile` escape rejected, store free), `X5_fires` (the counterfactual binder order), `C5a_level` and `S2_level` (a concrete assigned set below a scope root), and the B2 examples Y1 to Y5 (`freshCell` with two calls whose opened binders are incomparable, `makeLogger` packed at the parameter, C5b, the `withFile` escape rejected by isolation and by the level check, and the `fresh` halves of C5a and S2), with the three source `fresh` examples translated and typed |

## Notation

All notation is `scoped` in namespace `FCdot`.

| | |
|---|---|
| `⊤`, `⊥`, `x ∙ ℓ`, `Π(S) T`, `μ Tel` | types; `μ` binds the implicit self variable of the telescope |
| `S ⊑ T`, `S ≐ T`, `∋ ℓ`, `⊑ T` | propositions (data, hence not `≤`, `=`); `⊑ T` is the *self-bound* "the object itself is included in `T`" |
| `Tel ▹ P`, `Tel ∋ (i ↦ P)` | telescope extension; the `i`-th proposition, counted from the oldest (also for entries `Es` and views `V`) |
| `T↑`, `T⟦y⟧` | weakening under a new binder; instantiation of the innermost binder |
| `Γ ⊢ e : S ≤ T`, `Γ ⊢ φ : S ≡ T`, `Γ ⊢ h : x ∋ ℓ` | inclusion, equality, and presence evidence |
| `Γ ⊢ m : src ⇒ Tel` | a template morphism proving the closed telescope `Tel` from the propositions of `src` |
| `Γ ⊢ₐ a : T`, `Γ ⊢ t : T`, `Γ ⊢ᵥ v : T`, `Γ ⊢ᶠ[A] F` | atoms, terms, values, fields |
| `⊢ σ : Γ`, `Γ ⊢ₖ K : T ⇒ U` | stores and continuations |
| `st ⟶ st'`, `st ⟶* st'`, `⌊st⌋` | steps and erasure |
| `σ ⊢ e ⇓[n] F`, `σ ⊢ m ⇓ₘ[n] Es`, `σ ⊢ a ⇓ᵥ[n] V`, `σ ⊢ x ; h ⇓ₕ[n] (y, ℓ)`, `σ ⊢ a ⇓ᶜ[n] (a', F)` | normalization with fuel `n` |
| `Γ ⊨ F : S ≤ T`, `Γ ⊨[r] F : S ≤ T` | typed coercion form; typed chain of casts at root `r` |
| `Γ ⊨ Es : Tel₁ ⇒ Tel₂`, `Γ ⊨[r, σ] V : Tel` | typed template entries between closed telescopes; typed view |

## Design

* **Inert stores.**  An object literal `obj W Wᶜ F` carries witnesses `W` (a
  definition per block label), capture witnesses `Wᶜ` (a capture set per
  block label, `[]` where absent) and fields `F`.  Its precise type is the
  telescope generated from them, `μ (Telescope.ofLiteral W Wᶜ F.labels)`: one
  `self ∙ ℓ ≐ W.get ℓ` per witness, then one `[name self ℓ] ≐ᶜ Wᶜ.get ℓ` per
  capture witness, then one `∋ ℓ` per field.  Facts beyond
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
* **Self-bound propositions.**  A telescope may also carry `⊑ T`: the object
  itself is included in `T`.  This is what lets an intersection whose
  operand is not a declaration (a type selection, a function type, `⊥`)
  still be an object type.  `LeCo.bound Tel i` casts through the `i`-th
  bound, `LeCo.intoBnd` puts an inclusion into a one-bound object type, and
  `Morphism.bnd` proves a target bound by a coercion out of the source
  object type.  On normal forms: `Form.bnd i F` is "through bound `i`, then
  `F`", `Form.into Es` is a coercion whose entries do not consult the view
  of the source, and `Entry.thru H E` is an entry *routed* through `H` --
  the entry `E` reads the object type `H` reaches from the source rather
  than the source itself.  Routes never nest and are always sub-forms of the
  form that carries them, so applying a form to a view stays structural in
  the form.  Pairing produces an `into` form (`Form.freeEntries` routes each
  component's entries through the identity, or through the bound it goes
  under).
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
                       (equal resolutions) ∨ (both Π) ∨ (both μ) ∨
                       (S resolves to an object type with a bound below T) ∨
                       (T resolves to an object type, bounds-only unless S is one too)
reachable_consistent : st.Typed U → st ⟶* st' → ∃ Γ, ⊢ st'.σ : Γ ∧ (¬ ∃ e, Γ ⊢ e : ⊤ ≤ ⊥) ∧
                       ∀ x ℓ, ∃ W, Γ.lookupDef x ℓ = some W ∧ Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W
```

Axioms (`#print axioms`): `propext` and `Quot.sound` for all of the above.  The
tree contains no `sorry`, `axiom`, `partial`, or `native_decide`.

## What is not here

No open-evidence normalization: the machine only ever normalizes closed
evidence over the store, and that is all the metatheory needs.  The
translation from `DotMNF` lives in `lean/Coercions/DotToFCdot/`.

## Stage A0

What A0 changed in each module.  The tables above describe what the modules contain.

| module | what A0 changed |
|---|---|
| `Debruijn` | `Kind` gains `cap`; `Sig.extend_cap`, notation `,c`; everything else was already kind-generic |
| `Syntax` | `CapAtom`, `CaptureSet` with its union, `Subset` and its decision; `Shape` (the vanilla `Ty`, plus `box`), `Ty ::= S ^ C`, `Ty.pure`, `Ty.shape`, `Dom`/`Cod`; `ShapeCo`/`CapCo`/`LeCo`; `Subst.cvar`, `Subst.liftC` |
| `Context` | `CapBound` (all four bounds), `Ctx.consC`, `Ctx.lookupCap`; `lookupDef` returns a `Shape`; no binder records a level |
| `Store`, `Runtime.lean` | `Store.consC` on both sides, `Store.Typed.consC` with no premise; `Store.Typed.cons`'s premises named |
| `Typing` | the shape family `Γ ⊢ˢ e : S ≤ S'`, the capture family `Γ ⊢ᶜ f : C ⊑ C'` with `refl`, `trans`, `elem`, `union`, and the pairing `Γ ⊢ capt e f : S ^ C ≤ S' ^ C'`; `boxed`; `both` at one capture set; values and projections are pure |
| `RenameLemmas`, `TypingRename`, `Transparency`, `TypingSubst` | each vanilla lemma split into its `Shape`/`Ty` pair; weakening stated at an arbitrary kind; `weakenC` twins and `Subst.Typed.liftC` |
| `Checker`, `CheckerCompleteness` | `synthShape`/`checkShape` and `synthCap`/`checkCap` (deciding `Subset`) beside `synthLe`/`checkLe`; `checkTm_iff` and friends unchanged |
| `Normalizer` | `hnfShape` (the vanilla `hnf`) and `hnf` on `LeCo`; `Form.boxed` carrying the evidence between the boxed types, as `Form.pi` carries its domain and codomain evidence, with its `combine` clauses |
| `Resolution` | resolution on shapes; `Ctx.caps`/`Ctx.capsAtom`/`Ctx.capsBound`, `Ctx.roots`, `Ctx.Root`, `CapLe` and `RootsEq` with the five properties and store monotonicity |
| `FormTyping`, `FormAlgebra` | forms typed between shapes; `FormTyped.boxed` carrying the coercion between the boxed types, as `FormTyped.pi` carries its domain and codomain evidence, and its algebra |
| `CanonicalForms` | `shape_canon` (the vanilla `le_canon`) and `le_canon` above it; `closedAtomForm_typed` between the two shapes |
| `Machine`, `Erasure`, `Preservation`, `ErasureMetatheory` | unchanged but for the capture store slot |
| `Progress`, `Consistency` | unchanged statements; `closed_le_shapes` gains one disjunct, "the target resolves to a box" |
| `Examples` | E1 to E8 with `^ []` everywhere, still decided in the kernel |

## Stage A1

A1 puts the capture sort into telescopes: capture propositions live under the self, a
literal records a capture witness per label, capture evidence can read a variable, a
telescope entry, or a definition, and the canonical-forms theorem gains its capture
item.  A1 also carries out the **box revision** of `plan-5c-captures-stages.md` §A1
("Design correction, second version"): the atom wrappers `Atom.box` and `Atom.unbox`
of A0 are removed, boxing becomes a *value* and unboxing a *term*, and so every atom's
capability is the capability of its root, which is what makes the capture rules and
the view of an atom instantiate at the same thing.

| module | what A1 changed |
|---|---|
| `Syntax` | `Proposition.leC`/`eqC`, `CapEq`, `CapStep`/`SideC`, `HoleC`, `Morphism.leC`/`eqC`, `Atom.recap`, `CapCo.capvar`/`member`/`eqToLe`, `CapWitnesses` with `get`/`labels`/`eqEntries`; `Value.obj W Wᶜ F` and `Telescope.ofLiteral W Wᶜ labels`, whose capture block sits between the type block and the presences; the box revision: `Atom.box`/`Atom.unbox` out, `Value.box` and `Tm.unbox` in |
| `Context` | `Binding.transparent` records the literal's `CapWitnesses`; `Ctx.lookupDefC` reads a capture witness at the binder |
| `Store` | `Store.Typed.cons` records the value's capture witnesses; a stored box is a literal with no witnesses and no fields |
| `Typing` | `capvar`, `member` in the capture sort, `defC`, `eqToLe`, and the capture-equality family `Γ ⊢ᶜ φ : C ≡ C'`; `Atom.recap`; capture templates `Morphism.leC`/`eqC` over `SideC` chains, with `Telescope.HoleAtC`, `CapStep.HasType` and `SideC.HasType`; `Value.HasType.box` and `Tm.HasType.unbox` (the A0 atom rules, read one sort up); `Value.HasType.obj` at `ofLiteral W Wᶜ F.labels` |
| `RenameLemmas`, `TypingRename`, `Transparency`, `TypingSubst` | renaming and substitution for the new families; substitution into a capture set is the root renaming, as in A0 |
| `Checker`, `CheckerCompleteness` | `synthCapEq`/`checkCapEq` beside `synthCap`/`checkCap`; synthesis for `capvar`, `member` in both capture families, `defC`, `eqToLe`, `recap`, `leC` with side chains and `eqC`; `checkTm_iff` and friends unchanged |
| `Normalizer` | `Entry.leC`/`eqC` (a capture template is its own normal form) and the data-free `PropForm.leC`/`eqC`; `Entries.through` and `Entry.prefix` on capture entries; `Value.precView` through the capture witnesses; `closedAtomForm` and `view` at `recap`, and no clauses for the two removed atom wrappers |
| `Resolution` | the `name` clause of `Ctx.capsAtom` follows the capture witness, with fuel equal to the number of capture witnesses of the block plus one and the empty set as the least solution at a cycle; `Ctx.Root_name`, the resolution lemma in the capture sort, and monotonicity of `roots` in the fuel |
| `FormTyping`, `FormAlgebra` | `SideTypedC` for chains, `EntriesTyped.leC`/`eqC`/`eqSymC`, `EntryTyped` likewise, `ViewTyped.leC`/`eqC`; the capture cases of `Form.combine_typed`, `EntriesTyped.through`, `Form.pair_typed` and `entriesAt_typed` are transitivity of `CapLe` and of root equality |
| `CanonicalForms` | `cap_canon` and its equality twin `capeq_canon` move into the mutual induction with `shape_canon`, `le_canon` and `atom_canon`; `atom_canon` gains item 7; `capEqForms_typed` types the capture block of a literal's precise view; the `SideC` bridge `capstep_canon`/`sideC_canon`; `closed_box_inversion` in place of `chain_box_inv` |
| `Machine`, `Erasure`, `Preservation`, `ErasureMetatheory` | the `unbox` steps read the head form of the atom's casts, as the application steps do, and `FormsTyped` gains the two clauses that type them (`boxed`, `boxRefl`); `recap` is stripped by `adjust` where casts are; a box is allocated like any literal, erases to the runtime's inert box, and an unbox erases to the runtime's `unbox`, so `erase_step` and `erase_reflect'` keep their statements |
| `Progress`, `Consistency` | `progress` gains the `unbox` case, discharged by `closed_box_inversion`; `EntryTyped.bnd_of_bndsOnly` gains the impossible cases for the new slots; the consistency corollary in the capture sort at a platform binder (`Store.Typed.no_cap_escape`, `no_cap_star_le_nil`) |
| `Examples` | E1 to E8 read as A1 literals with an empty capture-witness list, still decided in the kernel, plus C3 (bad capture bounds under a lambda, with the consistency corollary) and C4 (`sc-var` and capture `member` at the same wrapped atom) |

## Stage A2

A2 makes the capture sets that A1 carries do their job.  A value carries the capture
set its introduction rule assigns to it, so a stored value's binder has a real capture
set and `roots` at a variable is no longer empty.  A term has a use set, computed by a
total structural function `uses`, with explicit evidence wherever a use set is
discharged against a declared set.  And the prediction theorem is proven: along any run
from a typed state the roots of the use set only shrink, and every step that inspects a
root inspects one whose roots lie in the use set.  No new sort, no new evidence family,
no new form, entry or slot: use sets are not in types.

| module | what A2 changed |
|---|---|
| `Syntax` | the new data fields of `Tm.let t u U' f`, `Tm.unbox a U f`, `Value.lam A T t g`, `Value.obj A W Wc F` and `Fields.cons F l t g`; `Value.annot`; the total structural `Tm.uses` and `Tm.inspects` with their simp equations and `Tm.inspects_mem_uses`; `Ty.captureSet` moved here from `Resolution`, so that `Store` can see it |
| `RenameLemmas` | `CaptureSet.rename_union`; `Tm.uses_rename`, `Tm.uses_subst`, `Tm.uses_substAtom` (a substitution acts on a use set by the root renaming of A0), `Tm.inspects_rename`, `Tm.inspects_subst`; every `rename_id`, `rename_comp` and `subst_ofRename` proof names the new fields |
| `Context` | `Fields.labels` names the field's closing evidence and ignores it |
| `Typing` | the new premises: `let` carries `f : uses u ⊑ U'↑`, `lam` and `fields` carry `g : uses t ⊑ (A↑ ∪ [var .here])`, `unbox` charges against its declared `U` in place of `[]`; `lam` and `obj` conclude at the value's own annotation `A`; `Fields.HasType` is indexed by that annotation; `proj` concludes `(a.root ∙ l) ^ [name a.root l]` |
| `TypingRename`, `Transparency`, `TypingSubst` | the indexed `Fields.HasType.rename`, `refine` and `subst`; `CaptureSet.closing_rename`; `CapCo.HasType.substAtom` and `CapCo.HasType.letBody_substAtom`, the substitution lemma preservation needs at the `rename` step |
| `Store` | `Value.annot_rename` and `annot_weaken`; `Value.HasType.captureSet_annot` (a literal is typed at its own annotation) and `Store.Typed.lookup_annot` (the capture set of a binder's type is the stored value's annotation); `Store.Typed.cons` unchanged |
| `Checker`, `CheckerCompleteness` | `checkTm` computes `uses` and checks the new capture premises with `synthCap`; `checkFields` takes the literal's assigned set; the three kernels carry explicit `termination_by` measures; `checkTm_iff` and its friends unchanged |
| `Normalizer` | `Value.precView` names the literal's annotation and ignores it; nothing else, since use sets are not in types |
| `Resolution` | unchanged; `capsAtom` at a term binder already reads the capture set of the binder's type, which is now the stored value's annotation |
| `Machine` | `Frame.let u U' f` with its two new fields and the matching premise of `Cont.Typed.let`; `usesK`, `State.uses`, `State.inspects`; `Store.Ext` with `comp`, `roots`, `root_iff`, `capLe` and `injective`; `Store.Typed.ctx_unique`; two new imports, `Resolution` and `CheckerCompleteness` |
| `Erasure`, `ErasureMetatheory` | every clause drops the new annotations and the new evidence; `Tm.inspects_erase` and `State.inspects_erase`; `erase_step`, `erase_reflect`, `final_erase` and `final_reflect` unchanged |
| `FormTyping`, `FormAlgebra` | `Store.HasField` names the literal's annotation; nothing else |
| `Preservation` | the factored step-result lemmas `Fields.HasType.getFull`, `Tm.HasType.projFieldFull`, `Store.Typed.lam_closing`, `Tm.HasType.let_inv`, `Tm.HasType.cast_inv`, `Tm.HasType.letBody_substAtom`, `Store.Typed.unboxRefl_result`, `Store.Typed.unboxCast_result`, `CapCo.HasType.adjust` and `CapCo.HasType.adjust_none`; `Value.HasType.lam_inv` exposes the closing evidence as a third conjunct; `preservation` unchanged |
| `CanonicalForms`, `Progress`, `Consistency` | patterns and existentials name the new fields (`closed_has_field`, `closed_pi_inversion`); every statement unchanged; item 7 of `atom_canon` is unchanged and now has content |
| `Prediction` | the new module: `step_uses`, `capture_prediction`, `inspects_covered`, `effect_safety` and `returned_capture_bound`, with the helpers `Store.Typed.root_annot`, `Store.Typed.app_uses`, `Store.Typed.proj_uses`, `CapLe.mem` and `Value.core_annot` |
| `Examples` | every example term carries the new fields; E2, E5 and E6 gained the capture-definition entry of their field, E5 and E6 are typed at the capture set their field body really uses, and E8's result carries the capture name of its label; the new examples C1 (use sets computed by `decide`) and C6 (the rejected variant, a run, and the prediction instantiated) |

### Notation added by A0, A1 and A2

All the vanilla notation still works, at the sort the vanilla line used it.  New in A0:

| | |
|---|---|
| `S ^ C` | the type with shape `S` and capture set `C`; `Ty.pure S = S ^ []` |
| `□ T` | the box shape |
| `s,c` | a signature extended by a capture binder (beside `s,x`); contexts and stores extend by `Ctx.consC` / `Store.consC` |
| `Γ ⊢ˢ e : S ≤ T` | inclusion evidence between shapes (the vanilla `Γ ⊢ e : S ≤ T`) |
| `Γ ⊢ᶜ f : C ⊑ D` | inclusion evidence between capture sets |
| `Γ ⊢ e : T ≤ T'` | inclusion evidence between types, a shape inclusion paired with a capture inclusion |
| `σ ⊢ e ⇓ˢ[n] F` | head form of a shape coercion (`σ ⊢ e ⇓[n] F` stays on type coercions) |

New in A1:

| | |
|---|---|
| `C₁ ⊑ᶜ C₂`, `C₁ ≐ᶜ C₂` | capture propositions, under the self like every proposition; their right sides may mention `[var .here]` and `[name .here ℓ]` |
| `Γ ⊢ᶜ φ : C ≡ D` | capture *equality* evidence (`CapEq`), beside the inclusion judgment `Γ ⊢ᶜ f : C ⊑ D` |
| `σ ⊢ a ⇓ᶜ[n] (a', F)` | the chain of casts of an atom, with `Atom.recap` one more transparent wrapper in it |

New in A2:

| | |
|---|---|
| `Γ ⊢ᶠ[A] F` | field typing, indexed by the literal's assigned capture set (the vanilla `Γ ⊢ᶠ F`) |

A2 adds no other notation.  `uses`, `usesK`, `State.uses`, `annot`, `inspects` and
`Store.Ext` are plain identifiers.

`ᶜ` is not a legal Lean identifier character, so an identifier the plan spells with a
`ᶜ` suffix carries the ASCII suffix `C` here (`Ctx.consC`, `Store.consC`,
`Subst.liftC`, `Store.Typed.consC`, `Proposition.leC`/`eqC`, `CapEq.defC`,
`Ctx.lookupDefC`, `SideC`, `HoleC`, `CapWitnesses`); notation tokens such as `⊑ᶜ`,
`≐ᶜ` and `⊢ᶜ` are unaffected.

### Main theorems, restated

Every statement below is the vanilla statement, restated: what the vanilla line wrote
at `Ty` is written at `Shape` wherever the position carries no capture set, and at
`Ty` wherever it does.  Nothing gained a hypothesis; `atom_canon` gained a conjunct
(item 7), which is a strengthening.

```
FCdot.checkTm_iff        : checkTm Γ t T = true ↔ Γ ⊢ t : T
FCdot.shape_canon        : ⊢ σ : Γ → Γ ⊢ˢ e : S ≤ T → ∃ n F, σ ⊢ e ⇓ˢ[n] F ∧ Γ ⊨ F : S ≤ T
FCdot.le_canon           : ⊢ σ : Γ → Γ ⊢ d : S ≤ T →
                             ∃ n F, σ ⊢ d ⇓[n] F ∧ Γ ⊨ F : S.shape ≤ T.shape
FCdot.atom_canon         : ⊢ σ : Γ → Γ ⊢ₐ a : S → (∃ n V, σ ⊢ a ⇓ᵥ[n] V ∧
                             (∀ Tel, Γ.resolve S.shape = μ Tel → Γ ⊨[a.root, σ] V : Tel) ∧
                             Γ.resolve S.shape ≠ ⊥) ∧
                             CapLe Γ [.var a.root] S.captureSet
FCdot.cap_canon          : ⊢ σ : Γ → Γ ⊢ᶜ f : C ⊑ D → CapLe Γ C D
FCdot.capeq_canon        : ⊢ σ : Γ → Γ ⊢ᶜ φ : C ≡ D → RootsEq Γ C D
FCdot.closed_box_inversion : ⊢ σ : Γ → Γ ⊢ₐ a : (□ T) ^ D →
                             ∃ b a' n F, σ.lookup a.root = .box b ∧ σ ⊢ a ⇓ᶜ[n] (a', F) ∧
                             (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d, F = .boxed d)
FCdot.closedAtomForm_typed : ⊢ σ : Γ → Γ ⊢ₐ a : S → ∃ n a' F, σ ⊢ a ⇓ᶜ[n] (a', F) ∧
                             Γ ⊨[a.root] F : (Γ.lookupTy a.root).shape ≤ S.shape
FCdot.preservation'      : st.Typed U → st ⟶ st' → ∃ ρ, st'.Typed (U.rename ρ)
FCdot.progress           : st.Typed U → st.Final ∨ ∃ s' (st' : State s'), st ⟶ st'
FCdot.not_stuck          : st.Typed U → ¬ st.Stuck
FCdot.erase_step         : st ⟶ st' → (cast-frame step ∧ ⌊st⌋ = ⌊st'⌋) ∨ Runtime.Step ⌊st⌋ ⌊st'⌋
FCdot.erase_reflect'     : ⊢ st.σ : Γ → (∃ T, Γ ⊢ st.t : T) → Runtime.Step ⌊st⌋ r →
                             ∃ st', st ⟶* st' ∧ ⌊st'⌋ = r
FCdot.closed_le_shapes   : the vanilla eight-way disjunction on Γ.resolve _.shape,
                             with one new disjunct: the target resolves to a box
FCdot.Store.Typed.no_top_le_bot : ¬ ∃ e C C', Γ ⊢ e : ⊤ ^ C ≤ ⊥ ^ C'
FCdot.Store.Typed.no_cap_star_le_nil : Γ.lookupCap κ = .star → ¬ ∃ f, Γ ⊢ᶜ f : [cvar κ] ⊑ []
FCdot.reachable_consistent : st.Typed U → st ⟶* st' → ∃ Γ, ⊢ st'.σ : Γ ∧
                             (¬ ∃ e C C', Γ ⊢ e : ⊤ ^ C ≤ ⊥ ^ C') ∧
                             ∀ x ℓ, ∃ W, Γ.lookupDef x ℓ = some W ∧ Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W
```

Item 7 of the theorem is the second conjunct of `atom_canon`: over a typed store, the
root of a typed atom is below the capture set of the atom's type.  Its cases are one
line each because the box revision leaves no atom whose capture set disagrees with its
root: `var` is the definition of `Ctx.capsAtom`, `cast a (capt e f)` composes the
hypothesis with `cap_canon f`, `recap a f` *is* `cap_canon` of its own evidence, and
`foldSelf`, `unfoldSelf` and `both` pass the set through.

A2 changed none of these statements.  It gave item 7 its content: at a variable bound
to a stored value the capture set of the binder's type is that value's annotation
(`Store.Typed.lookup_annot`, `Store.Typed.root_annot`).

### The five theorems of A2

`Prediction.lean` states the use-set half of preservation beside `preservation'`, never
folded into it.

```
FCdot.step_uses              : ⊢ st.σ : Γ → st.Typed U → st ⟶ st' →
                                 ∃ ρ, Store.Ext st.σ st'.σ ρ ∧
                                 ∀ Γ', ⊢ st'.σ : Γ' → CapLe Γ' st'.uses (st.uses.rename ρ)
FCdot.capture_prediction     : st.Typed U → st ⟶* st' →
                                 ∃ ρ, Store.Ext st.σ st'.σ ρ ∧
                                 ∀ Γ', ⊢ st'.σ : Γ' → CapLe Γ' st'.uses (st.uses.rename ρ)
FCdot.inspects_covered       : st.inspects = some x → CapLe Γ [var x] st.uses
FCdot.effect_safety          : st.Typed U → ⊢ st.σ : Γ → st ⟶* st' →
                                 ¬ Γ.Root (cvar κ) st.uses → st'.inspects = some x →
                                 ⊢ st'.σ : Γ' →
                                 ∃ ρ, Store.Ext st.σ st'.σ ρ ∧ ¬ Γ'.Root (cvar (ρ.var κ)) [var x]
FCdot.returned_capture_bound : ⊢ σ : Γ →
                                 (⟨σ, nil, val v⟩.Typed (S ^ C) → CapLe Γ v.annot C) ∧
                                 (⟨σ, nil, atom a⟩.Typed (S ^ C) → CapLe Γ [var a.root] C)
```

`Store.Ext σ σ' ρ` is the canonical embedding of a store into an extension of it
(`refl`, `cons`, `consC`).  It composes, and over two typings of the two stores it
carries `roots` along the renaming, which is `Ctx.caps_weaken` iterated.

### The capture examples C1 and C6

```
Examples.C1_typed         : C1Ctx ⊢ᵥ c1val : c1Ty
Examples.C1_uses_console  : C1prog1.uses = {c1, unit, console, log}
Examples.C1_uses_pure     : C1prog2.uses = {c1, unit}
Examples.C6_rejected      : checkValue C1Ctx c1bad c1badTy = false
Examples.C6_run           : C6st0 ⟶* C6st7
Examples.C6_covered       : the instance of inspects_covered composed with
                            capture_prediction at the state that reads console
Examples.C6_safe          : the instance of effect_safety for the program whose use
                            set has no root κ₂
```

`c1` is the closure of plan V-A §2.6 in the platform context of two rigid capture
binders.  The bad variant, whose inner annotation is empty, is rejected by the checker
in the kernel; the good one is run, and the prediction is instantiated at the state
that inspects `console`.

Axioms (`#print axioms`): `propext` and `Quot.sound` for all of the above, and for
`Examples.C3_typed`, `Examples.C3_badBounds`, `Examples.C4_capvar`,
`Examples.C4_member`.  The tree contains no `sorry`, `axiom`, `partial`, `unsafe`, or
`native_decide`, and no Mathlib.

## Stage A3a

The source became capturing in A3a, and two things reached the target.

The erasure of a box changed.  A1 sent a box to a one-field runtime object at a reserved label
`boxLabel` and an unboxing to that field's projection.  Once the source has boxes too, a source
object literal with a field at that label and a source box have the same erasure, and the simulation
that ties the two calculi together by erasure alone cannot tell them apart.  The runtime therefore
has an inert box of its own.  `Value.erase` sends a box to `Runtime.Tm.box` at the boxed atom's root
and `Tm.erase` sends an unboxing to `Runtime.Tm.unbox` at the same root, `boxLabel` and its two
lemmas `boxField_get?` and `boxField_substVar` are gone, and `unbox_erase_step` is gone with them.
`erase_step`, `erase_reflect`, `erase_reflect'`, `final_erase` and `final_reflect` keep their
statements word for word.  `Value.erase_eq_obj` recovered the stage A2 statement it had briefly lost,
"a literal whose erasure is a runtime object is an object", and the box half of it is the new
`Value.erase_eq_box`.  `Runtime.Step.unbox_inv` joins `app_inv` and `proj_inv`.

The examples gained the target side of the three source examples of the stage.

```
Examples.S3_client     : S3Ctx ⊢ S3client : S3clientTy
Examples.C7_client     : C7Ctx ⊢ C7client : C7clientTy
Examples.C7_rejected   : checkTm C7Ctx C7clientBad C7clientTy = false
Examples.C2_client     : C2Ctx ⊢ C2client : Ty.pure ⊤
Examples.S3_translated : ⟦platCtx⟧ ⊢ ⟦S3_typed⟧ : ⟦S3Ty⟧
Examples.C2_translated : ⟦platCtx⟧ ⊢ ⟦C2_typed⟧ : ⟦C2Ty⟧
Examples.C7_translated : ⟦platCtx⟧ ⊢ ⟦C7_typed⟧ : ⟦C7Ty⟧
Examples.S3_erase      : ⌊⟦S3_typed⟧⌋ = ⌊S3tm⌋
Examples.C2_erase      : ⌊⟦C2_typed⟧⌋ = ⌊C2tm⌋
Examples.C7_erase      : ⌊⟦C7_typed⟧⌋ = ⌊C7tm⌋
```

The three `_client` theorems are the client half of each example, written directly in the target in
the context the translation of the source types produces, and decided by the structural checker in
the kernel.  S3 reads a field declared at a type member and unboxes what the member's upper bound
says is a box.  C7 reads one element of a container of boxed capabilities and unboxes it at `{κ₁}`,
and `C7_rejected` is the same client with the empty use set and the syntactic capture evidence, which
the checker refuses.  C2 reads a closure off an abstract capture member and calls it, and the call is
charged to `{κ₁,κ₂}` by `capvar` composed with the member's upper bound.  The three `_translated`
theorems are `HasTy.translate_typed` at the source derivations, and the three `_erase` theorems are
`HasTy.translate_erase` at the same.  Neither is decided by the checker: the type translation and the
term translation are compiled by well-founded recursion, so neither reduces in the kernel, and
`decide +kernel` cannot be run on a goal that mentions them.

Axioms (`#print axioms`): `propext` and `Quot.sound` for all of the above.

## Stage B0

B0 is the first stage of captures the compiler's way (`plan-5d-captures-cc-stages.md` §B0).
It touches the target only and adds no term former.  It adds the universal root as a capture
atom, the level order on capture atoms, the one evidence rule that reads that order, the
expansion of a root into what it stands for, and the theorems that make the order sound over
a typed store.

A level is a position on the spine, not a field on a binding.  `Ctx.lvl` reads the innermost
root binder of the prefix that precedes a binder, and a root is its own level.  `none` means
the outermost level, the universal root `⊤ᶜ`.  `Ctx.lvlLeB e r` says that the level of `e`
is `r` or encloses it, so an inner root absorbs an outer capability and never the reverse.
Everything is `Bool` valued, and `Ctx.IsRoot`, `Ctx.LvlLe` and `Ctx.Confined` are `abbrev`s,
so `by decide` closes a level side condition on a concrete context in the kernel.

`Ctx.roots` keeps its name, its signature and its fuel argument, and its body becomes
`Γ.expand (Γ.caps n C)`.  Expansion opens a root into the universal root and every opaque
binder at its level or outside it, and leaves everything else alone.  On a root-free context
whose resolution mentions no `⊤ᶜ`, expansion is the identity and `roots` is `caps` again
(`Ctx.roots_eq_caps_of_rootFree`), which is why every statement of the DOT way about roots
means on a store context and on the platform prefix what it meant before.

| module | what B0 changed |
|---|---|
| `Syntax` | the capture atom `CapAtom.top` with the notation `⊤ᶜ`, and the capture coercion `CapCo.level e r`; one clause each in `CapAtom.rename`, `CapCo.rename` and `CapCo.subst`; `DecidableEq` derives as before |
| `RenameLemmas` | one case each in `CapCo.rename_id`, `CapCo.rename_comp`, `CapCo.subst_ofRename`; the `CapAtom` lemmas are covered by their existing scripts |
| `Context` | the level block after `lookupCap`: `BVar.depth`, `CapBound.opaque`, `CapBound.isRoot`, `depthGe`, `Ctx.root?`, `Ctx.rootAtom`, `Ctx.lvl`, `Ctx.lvlAtom`, `Ctx.rootDepth?`, `Ctx.isRootB`, `Ctx.lvlLeB`, the abbreviations `Ctx.IsRoot` and `Ctx.LvlLe`, and `Ctx.Confined` with its decision instance; no binding records a level |
| `Levels` | the new module: the unfolding equations of `Ctx.root?` and `Ctx.lvl`, the order lemmas `Ctx.top_lvlLe`, `Ctx.lvl_root`, `Ctx.root?_isRoot`, `Ctx.lvl_isRoot`, `Ctx.root?_min`, `Ctx.root?_none`, `Ctx.LvlLe.refl_of_root`, `Ctx.LvlLe.trans`, L0 in its four forms (`Ctx.lvl_le_rootAtom` and its `.var`, `.name` and set-level twins), the level of an atom `Ctx.lvlOf` with `Ctx.lvlOf_isRoot` and `Ctx.lvlLe_lvlOf`, and the ten weakening commutations `Ctx.lvl_weaken(C)`, `Ctx.lvlAtom_weaken(C)`, `Ctx.lvlLeB_weaken(C)`, `Ctx.isRootB_weaken(C)`, `Ctx.Confined.weaken(C)` |
| `Resolution` | one leaf clause `⊤ᶜ` in `Ctx.capsAtom`; `Ctx.capBinders`, `Ctx.expandAtom`, `Ctx.expand` with `expand_nil`, `expand_cons`, `expand_append`, `expand_subset`, `mem_expand`, `mem_expandAtom_self`, `expand_eq_self`, `expand_weaken`, `expand_weakenC`, `expandAtom_mono`; `Ctx.caps_opaque`; `Ctx.caps_confined` and `Ctx.capsAtom_confined`; `Ctx.roots` redefined as `Γ.expand (Γ.caps n C)`, with `Ctx.roots_eq_caps` becoming `Ctx.roots_eq_expand_caps` and the new `Ctx.roots_eq_caps_of_rootFree`; `CapLe.weakenC` gains `b.opaque = false` |
| `Typing` | the rule `CapCo.HasType.level` |
| `TypingRename`, `Transparency`, `TypingSubst` | `Ctx.Ren` and `Subst.Typed` gain the three capture fields `capRoot`, `capLvl`, `capInner`; `Ctx.Refines` gains `rootEq`, `lvlEq`, `capEq`; `Ctx.Ren.succC`, `Subst.Typed.liftC` and the nine `weakenC` theorems gain `b.isRoot = false`; the new instance `Ctx.Ren.liftC`; one case each in `CapCo.HasType.rename`, `.subst` and `.refine` |
| `Checker`, `CheckerCompleteness` | one clause `⊤ᶜ` in `CapAtom.rename?`; the `level` case of `synthCapCore`, which tests `Ctx.isRootB` and `Ctx.lvlLeB` and so reduces in the kernel; one case in `CapCo.HasType.complete` |
| `Store` | `Store.Typed.consC` gains `b.isRoot = false`: a store binds capabilities, never scopes |
| `Machine` | `Store.Ext.consC` gains `b.opaque = false`; `Store.Ext.roots` goes through `Ctx.expand_weakenC`; the other `Store.Ext` theorems keep their statements |
| `Preservation`, `ErasureMetatheory`, `FormAlgebra` | the six lemmas that say a term binding is invisible to the capture spine (`Ctx.lvl_cons_eq` and friends); the capture fields of `Subst.Typed.selfCast`, `Ctx.Ren.selfObj` and `Subst.Typed.selfCastOpaque`; the `consC` patterns take one more binder |
| `CanonicalForms` | `cap_canon` gains the `level` case, with `Ctx.caps_of_isRoot` and `Ctx.roots_of_isRoot`; `Ctx.Root_var` gains two expansion steps |
| `Consistency` | `Ctx.caps_of_opaque`; the seven theorems of B0.8: `Store.Typed.rootFree`, `Store.Typed.confined`, `lvl_canon`, `rigid_canon`, `rigid_target`, `lvl_safety`, `no_inner_escape`; `Ctx.Root_cvar_rigid` gains one expansion step |
| `Prediction` | nothing |
| `Examples` | every existing example unchanged but for two proof steps in `C6_store` and `C6_no_kappa2`; the new examples X1, X2 and X3 |

### Notation added by B0

| | |
|---|---|
| `⊤ᶜ` | the universal root, `CapAtom.top`: the local root of the whole program, the compiler's `caps.any` as a constant |

B0 adds no other notation.  `CapCo.level`, `Ctx.lvl`, `Ctx.isRootB`, `Ctx.lvlLeB`,
`Ctx.expand` and `Ctx.roots` are plain identifiers.  `ᶜ` is still not a legal Lean identifier
character, so an identifier the plan spells with a `ᶜ` suffix carries the ASCII suffix `C`.
The token `⊤ᶜ` is notation and is unaffected.

### The rule

```
FCdot.CapCo.HasType.level : Γ.IsRoot r → Γ.LvlLe e r → Γ ⊢ᶜ .level e r : [e] ⊑ [r]
```

Both sides are singletons, and a set-shaped conclusion is a `union` of instances.  The right
side is a `CapAtom` and not a capture variable, because the universal root is an atom and a
rule with a variable on the right cannot name it.

### Statements restated

Nothing was weakened.  These are the statements of the DOT way, restated where B0 changed
the representation, together with the reason each means what it meant.

```
FCdot.Ctx.roots               : Γ.roots n C = Γ.expand (Γ.caps n C)
                                  name, signature and fuel unchanged; caps ⊆ roots, and
                                  roots = caps on every root-free context
FCdot.Ctx.roots_eq_expand_caps : Γ.roots n C = Γ.expand (Γ.caps n C)
                                  the simp lemma Ctx.roots_eq_caps was, one function further
FCdot.Ctx.roots_eq_caps_of_rootFree : Γ.root? = none → ⊤ᶜ ∉ Γ.caps n C →
                                  Γ.roots n C = Γ.caps n C
FCdot.CapLe.of_subset, .union, .weaken : statements kept, proofs gain an expansion step
FCdot.CapLe.weakenC           : gains b.opaque = false; an appended non-opaque binder is
                                  invisible to expansion
FCdot.Ctx.Root_cvar_rigid, .Root_var, .Root_name : statements kept
FCdot.Store.Typed.no_cap_escape, .no_cap_star_le_nil : statements and proofs kept
FCdot.Store.Typed.consC       : gains b.isRoot = false
FCdot.Store.Ext.consC         : gains b.opaque = false
FCdot.Ctx.Ren, FCdot.Subst.Typed : three capture fields each, additive
FCdot.Ctx.Refines             : three capture fields, additive
the nine weakenC theorems     : gain b.isRoot = false
FCdot.cap_canon               : statement kept, one case added
FCdot.atom_canon              : nothing; only what CapLe means underneath changed
the five Prediction theorems  : nothing
```

### New theorems

```
FCdot.Ctx.caps_confined  : Γ.Confined C r → Γ.Confined (Γ.caps n C) r
FCdot.Ctx.lvl_le_rootAtom : Γ.LvlLe (.cvar y) Γ.rootAtom          -- L0, and its .var/.name twins
FCdot.Ctx.mem_expandAtom_self : a ∈ Γ.expandAtom a
FCdot.Ctx.expandAtom_mono : Γ.IsRoot r → (a = ⊤ᶜ ∨ (Γ.lookupCap κ).opaque) → Γ.LvlLe a r →
                              (Γ.expandAtom a).Subset (Γ.expandAtom r)
FCdot.Ctx.caps_opaque    : a ∈ Γ.caps n C → a = ⊤ᶜ ∨ ∃ κ, a = .cvar κ ∧ (Γ.lookupCap κ).opaque
FCdot.Store.Typed.rootFree : ⊢ σ : Γ → Γ.root? = none
FCdot.Store.Typed.confined : ⊢ σ : Γ → ⊤ᶜ ∉ C → Γ.Confined C ⊤ᶜ
FCdot.lvl_canon          : ⊢ σ : Γ → Γ ⊢ᶜ f : C₁ ⊑ C₂ → (∀ m, Γ.Confined (Γ.caps m C₂) r) →
                              Γ.Confined (Γ.caps n C₁) r
FCdot.rigid_canon        : ⊢ σ : Γ → Γ.lookupCap κ = .star → Γ ⊢ᶜ f : [cvar κ] ⊑ C →
                              Γ.Root (cvar κ) C
FCdot.rigid_target       : ⊢ σ : Γ → Γ.lookupCap κ = .star → Γ ⊢ᶜ f : C ⊑ [cvar κ] →
                              (Γ.caps n C).Subset [cvar κ]
FCdot.lvl_safety         : ⊢ σ : Γ → Γ.IsRoot r → Γ ⊢ᶜ f : C ⊑ [r] →
                              Γ.Confined (Γ.caps n C) r
FCdot.no_inner_escape    : ⊢ σ : Γ → Γ.IsRoot r → (Γ.lookupCap κ).opaque = true →
                              ¬ Γ.LvlLe (cvar κ) r → ¬ ∃ f, Γ ⊢ᶜ f : [cvar κ] ⊑ [r]
```

`Ctx.caps_confined` is the lemma the stage rests on: resolution never lowers the level.  It
is a mutual well-founded induction beside `Ctx.capsAtom_confined`, with the two measures of
`Ctx.caps` and `Ctx.capsAtom` copied over, and every leaf closes by L0 and the weakening
commutations.  `lvl_canon` is a corollary of `cap_canon` over a typed store and not an
induction on the evidence: as an induction on `f` alone the `capvar` case is false, since bad
capture bounds are derivable under a lambda (example C3).  `no_inner_escape` is the sentence
in which the escape of stage B1 is rejected, and its conclusion is about what `C` resolves to
and not about the syntactic atoms of `C`.

Over a typed store `no_inner_escape` is vacuous at B0: a store context has no root binder, so
the only root over it is `⊤ᶜ`, and `Store.Typed.confined` puts every atom at or outside `⊤ᶜ`.
It acquires content in stage B1, where a lambda body becomes a scope and a store slot can sit
under a root the run itself provides.

### The examples X1, X2 and X3

```
Examples.X1_inner_absorbs_outer : X1Ctx ⊢ᶜ level (cvar κ₁) ⊤ᶜ : {κ₁} ⊑ {⊤ᶜ}, and the
                                    same at a program binder
Examples.X2_outer_not_inner     : four parts on κ₁ ⊑ᶜ ∗, κ_S ⊚, κ₂ ⊑ᶜ ∗ --
                                    {κ₁} ⊑ {κ_S} and {⊤ᶜ} ⊑ {κ_S} are derivable,
                                    ¬ LvlLe κ_S ⊤ᶜ and ¬ LvlLe κ₂ ⊤ᶜ
Examples.X3_no_escape           : ⊢ σ : X2Ctx → ¬ ∃ f, X2Ctx ⊢ᶜ f : {κ₂} ⊑ {⊤ᶜ}
Examples.X3_no_store            : ¬ ∃ σ, ⊢ σ : X2Ctx
```

X1 is a platform prefix: it opens no scope, so every one of its binders is at the outermost
level and the universal root absorbs it.  X2 is the nesting of `scoped-capabilities.md:93-106`
with `⊤ᶜ` for the page's outermost `any`: the scope root absorbs what is outside it, the
universal root included, and does not release what is inside it.  Every side condition of X1
and X2 is decided against `Ctx.isRootB` and `Ctx.lvlLeB`, and the checker's verdict on each of
the six coercions is decided in the kernel beside it.  X3 is `no_inner_escape` applied at `κ₂`
and `⊤ᶜ`, with its three level premises decided.  Its second part records why the fourth
premise, a typed store, is unavailable for a scoped context at B0.

Axioms (`#print axioms`): `propext` and `Quot.sound` for every theorem above.  The tree
contains no `sorry`, `axiom`, `partial`, `unsafe`, or `native_decide`, and no Mathlib.

## Stage B1

B1 is the second stage of captures the compiler's way (`plan-5d-captures-cc-stages.md` §B1).
It gives the arrow a capture binder of its own, makes a lambda body and an object body
scopes, and lets the machine enter a body by one substitution.  B0's level rule was true and
unusable, because no rule opened a root.  B1 opens one at every arrow and at every literal,
so the rule fires on a real binder order and the `withFile` escape is decided in Lean.

An arrow is `Π[κ](T) U` and binds three things at its body.  `Ctx.scope Γ` is
`(Γ.consC .root).consC .star`, the body root and then the arrow's capture binder.
`Ctx.body Γ T` is that scope extended by the parameter.  So the binder order at a body is
`κ_body ⊚, κ ⊑ᶜ ∗, x : T`, the parameter and the arrow binder are at one level, and that
level is the body root.  Those four facts compute, and they are `Ctx.body_lvl_param`,
`Ctx.body_lvl_arrow`, `Ctx.body_lvl_root` and `Ctx.body_lookupCap_arrow`, all `rfl`.  This is
"parameter `any`s are at the same level as the function's local `any`" in the target, and it
is what rejects the escape.

The body root comes first for one reason.  With the parameter bound before it, the level of
the parameter is the caller's root, and the escape types.  X5 of `Examples` is that
counterfactual, written on the rejected order and decided, so the order is a checked fact and
not a claim.  The arrow binder comes after the body root for the mirror reason.  With the
arrow binder before it, `level κ κ_outer` fires, and a call from a deeper scope instantiates
`κ` at a capability of that deeper scope and makes the conclusion false.

Every capture binder that a rule of the type-sort block opens sits under a root of its own.
That is the scope discipline, and it is what makes `Atom.HasType.weakenRoot` true.  So
`ShapeCo.pi` and `Form.pi` carry their components at `Sig.scope s` and `Sig.body s`, one
capture binder deeper than the syntax line of the plan, which was the stale half of B1.1.  The
only rootless capture binders left are the platform prefix and the store's instance slots.

A substitution is no longer kind preserving.  `Subst.cvar` returns a `CapAtom`, because a call
instantiates the arrow's capture binder at the argument's root, a term variable, and entering
a body instantiates the body root at `⊤ᶜ`.  So `Subst.root` is gone and `Subst.rootVar` takes
its place on the term component, and six type-sort traversals are new.  The four
instantiations the machine uses are `Subst.singleC`, `Subst.arg`, `Subst.enter` and
`Subst.enterObj`, with `Subst.enterC` for the scope-shaped coercion of a `pi` form.

**The body root goes to `⊤ᶜ`, and that is a departure from the compiler.**  A running program
is the outermost scope.  Keeping the body root as a binder would mean putting it in the store,
and a store binds capabilities and never scopes.  Instantiating it at the lambda's assigned
set would be unsound, since for a caller binder `y` outside `A` the derivable `level y κ_body`
would become the false `{y} ⊑ᶜ A`.  The compiler checks a method body once against its own
level owner and never retargets that level at a call, so it has no counterpart for this move.
It is sound here for a reason the compiler does not need: a store context binds no root
(`Store.Typed.rootFree`), so over a store `Γ.LvlLe e ⊤ᶜ` holds for every atom in scope, and
the image evidence is not only typed but true.  That is what `Subst.Typed.enter` proves, and
it is the hardest lemma of the stage.

The runtime mirrors the new binders as data-free slots, which is the discipline it already
stated for stores.  `Runtime.Tm.lam` and `Runtime.Tm.obj` take bodies over the target's
signatures, and erasure still maps binder to binder.  One generalisation is forced:
`Tm.erase_subst` cannot read `t.erase.rename σ.root` any more, so the runtime gains a map of
term variables, `Runtime.VRen`, with `Runtime.Tm.map` beside `Runtime.Tm.rename`.

| module | what B1 changed |
|---|---|
| `Debruijn` | `Sig.dom s` becomes `s,c`, which moves `Dom`, `Cod`, `Shape.pi`, `ShapeCo.pi`, `Form.pi` and `Value.lam` at once.  Two new reducible names, `Sig.scope s` and `Sig.body s` |
| `Syntax` | `Value.lam` at `Sig.body s`, `Value.obj`'s fields at `((s,c),x)`, `ShapeCo.pi` at `Sig.scope s` and `Sig.body s`, one lift per new binder in `Shape.rename`, `ShapeCo.rename` and `Value.rename`.  `Subst.cvar` returns a `CapAtom`, `Subst.root` is replaced by `Subst.rootVar`, and `Subst.lift` and `Subst.liftC` weaken an atom.  The six type-sort traversals `CapAtom.subst`, `CaptureSet.subst`, `Shape.subst`, `Ty.subst`, `Proposition.subst`, `Telescope.subst`, and `Witnesses.subst` and `CapWitnesses.subst` beside them.  `Dom.underRoot`, `Dom.inBody`, `Cod.underRoot`, `Subst.singleC`, `Subst.arg`, `Subst.enter`, `Subst.enterC`, `Subst.enterObj` |
| `RenameLemmas` | `Subst.rootVar_def` and the pointwise `lift`/`single` equations that replace the old equations of renamings.  The eight new `X.subst_ofRename`, `Subst.compRename` with its fusion lemmas, and the two cancellations `Dom.inBody_enter` and `Cod.underRoot_enter`, with `Dom.underRoot_enterC` beside them.  `Tm.uses_subst` reads `(t.subst σ).uses = t.uses.subst σ` |
| `Context` | the three scope contexts `Ctx.scope`, `Ctx.body`, `Ctx.objBody`, and the four `rfl` theorems of T-B1.8 |
| `Typing` | the rules `ShapeCo.HasType.pi`, `Tm.HasType.app`, `Value.HasType.lam` and `Value.HasType.obj`.  `CapCo.MemberFree` and `Atom.MemberFree`, the two predicates T-B1.10 reads.  `CapCo.HasType` and `Fields.HasType` are unchanged |
| `TypingRename` | `Ctx.RenR`, which is `Ctx.Ren` without `capInner`, with `Ctx.Ren.toRenR` and the eleven `X.HasType.renameR` twins.  `Ctx.Ren.scope`, `.body`, `.objBody`, `Ctx.RenR.scope`, `.scopeR`, `.body`, `.bodyR`, `.consRoot`, `.succScope`.  `Subst.compRen` and its four equations.  Every `rename` statement keeps its form |
| `Transparency` | `Ctx.Refines.scope`, `.body`, `.objBody`.  The three `refine` statements keep their form |
| `TypingSubst` | `Subst.Typed` with `σ.rootVar` and `X.subst σ`.  `Subst.Typed.consRoot`, `.scope`, `.body`, `.objBody`, `.singleC`, `.arg`, `.enter`, `.enterC`, `.enterObj`, and `Atom.HasType.weakenRoot`.  `Binding.subst`, `CapBound.subst`, `Subst.core`, `Subst.compT` |
| `LevelInversion` | the new module: `Ctx.mem_caps_root`, `level_inversion` and `atom_level_inversion` |
| `Normalizer` | `Form.pi` follows `ShapeCo.pi`.  No clause of the normalizer changed |
| `FormTyping` | `FormTyped.pi` reads its two premises at `Γ.scope` and `Γ.body S₂` |
| `FormAlgebra` | `Subst.Typed.selfCastOpaque` reads the substitution where it read the induced renaming.  Composition of two `pi` forms is untouched |
| `Store` | `Store.Typed.rootFree` moves here from `Consistency`, verbatim, because the four entering steps consume it |
| `Machine` | the four steps `appVar`, `appCastRefl`, `appCast` and `proj` enter by substitution.  `Tm.selfAt` is deleted.  The other seven steps and all of `Store.Ext` are untouched |
| `Preservation` | `Subst.selfCast_core` and the four `X.subst_selfCast` replace `Subst.selfCast_root`.  `lam_of_lookup`, `lam_inv`, `lam_closing`, `obj_inv`, `beta`, `Store.Typed.beta`, `betaCast`, `FormsTyped.pi`, `projField`, `projFieldFull` restated at the new binders.  `Atom.HasType.castDom`, `Subst.arg_core_congr`, `Ty.arg_congr`.  `preservation` and `preservation'` keep their statements |
| `Checker`, `CheckerCompleteness` | `Dom.underRoot?` and `Cod.underRoot?` with their soundness and completeness, the `pi`, `lam` and `obj` cases of the synthesiser, and `tmApp` at the instantiated domain.  `checkTm_iff` and every other completeness statement keeps its form |
| `CanonicalForms` | `closed_has_field` at the new field signature.  Items 1 to 7, `cap_canon`, `atom_canon`, `closedAtomForm_pi` and `closed_box_inversion` are byte for byte what B0 left |
| `Progress` | byte for byte unchanged |
| `Consistency` | only the move of `Store.Typed.rootFree`.  Every theorem keeps its statement and its proof |
| `Prediction` | `app_uses` and `proj_uses` at the terms the two steps now produce.  The five prediction theorems are unchanged |
| `Erasure` | textually unchanged, every byte.  `Tm.erase` keeps its type and its clauses re-index for free |
| `ErasureMetatheory` | `Tm.erase_subst` reads `t.erase.map σ.rootVar`.  `Tm.erase_enter` and `Tm.erase_enterObj` replace `Tm.selfAt_erase`, with the six `Subst.rootVar_*` bridges.  `erase_step`, `erase_reflect` and `erase_reflect'` keep their statements |
| `Examples` | every example re-indexed for the new arrow, five new definitions, and the new examples `scope_order`, `C2_typed`, `X4_no_level`, `X4_no_escape`, `X5_fires`, `C5a_level` and `S2_level` |

`Runtime.lean` sits outside this directory and B1 reshaped it too: `Runtime.Tm.lam` and
`Runtime.Tm.obj` at the target's signatures, `Runtime.VRen` with its five combinators,
`Runtime.Tm.map` and `Runtime.Fields.map`, and the two step rules `Step.app` and `Step.proj`
continuing at a map.

B1 adds no notation.

### The rules

```
FCdot.ShapeCo.HasType.pi   : Γ.scope ⊢ e : T2.underRoot ≤ T1.underRoot →
                             Γ.body T2 ⊢ f : U1.underRoot ≤ U2.underRoot →
                             Γ ⊢ˢ .pi e f : Π(T1) U1 ≤ Π(T2) U2
FCdot.Tm.HasType.app       : Γ ⊢ₐ a : (Π(T) E) ^ C →
                             Γ ⊢ₐ b : T.subst (Subst.singleC (.var b.root)) →
                             Γ ⊢ .app a b : E.subst (Subst.arg b)
FCdot.Value.HasType.lam    : Γ.body T ⊢ t : U.underRoot →
                             Γ.body T ⊢ᶜ g : t.uses ⊑ (A↑↑↑ ∪ [.var .here]) →
                             Γ ⊢ᵥ .lam A T t g : (Π(T) U) ^ A
FCdot.Value.HasType.obj    : Γ.objBody ((μ (Telescope.ofLiteral W Wc F.labels)) ^ A) W Wc
                               F.labels ⊢ᶠ[A↑] F →
                             Γ ⊢ᵥ .obj A W Wc F : (μ (Telescope.ofLiteral W Wc F.labels)) ^ A
```

Both arrows' capture binders are opened at one scope, which is the standard reading of a rule
relating two binders.  The argument premise is at the instantiated domain, which for a
top-level parameter `any` is the singleton type `S ^ {b}`, and a caller reaches it with
`recap` and reflexivity.  The conclusion of `lam` mentions neither the body root nor the arrow
binder, which is the de Bruijn form of the widening obligation.  The witnesses of a literal
stay over `(s,x)`, because they generate the literal's own type and that type must not mention
the class root, and the self is bound after the root because `this` is owned by its class.

The four steps that enter a body:

```
appVar      : ⟨σ, K, .app (.var x) b⟩ ⟶ ⟨σ, K, t₀.subst (Subst.enter b)⟩
appCastRefl : ⟨σ, K, .app a b⟩ ⟶ ⟨σ, K, t₀.subst (Subst.enter b)⟩
appCast     : ⟨σ, K, .app a b⟩ ⟶
                ⟨σ, K, .cast (t₀.subst (Subst.enter (.cast b (d.subst (Subst.enterC b)))))
                             (c.subst (Subst.enter b))⟩
proj        : ⟨σ, K, .proj a ℓ h⟩ ⟶ ⟨σ, K, t.subst (Subst.enterObj a.root)⟩
```

`appCast` instantiates the domain coercion before it casts the argument.  Its domain component
lives at `Sig.scope s` under the scope discipline, so the instantiation is the two-binder
`Subst.enterC` and the codomain component takes `Subst.enter b`.

### Statements restated

Nothing was weakened.  These are the statements of B0 and of the DOT way, restated where B1
changed the representation, with the reason each means what it meant.

```
FCdot.ShapeCo.pi, FCdot.Form.pi : components at Sig.scope s and Sig.body s
                                    the same contravariant domain and covariant codomain
                                    coercion, read under the root the discipline opens
FCdot.Value.lam, FCdot.Value.obj : body and fields at Sig.body s and ((s,c),x)
                                    one field per binder the value now opens
FCdot.Subst                     : cvar returns a CapAtom, root is replaced by rootVar
                                    a call instantiates the arrow binder at a term variable
FCdot.Tm.uses_subst             : (t.subst σ).uses = t.uses.subst σ
                                    a use set holds only .var atoms, so the two agree
FCdot.Tm.inspects_subst         : ... = t.inspects.map σ.rootVar, the same map
FCdot.Ctx.Ren, FCdot.Subst.Typed : same six and three fields, at rootVar and X.subst σ
FCdot.Tm.HasType.app            : argument at the instantiated domain, result at Subst.arg b
                                    with no capture binder on the arrow, singleC is the
                                    identity and Subst.arg b is Subst.single b
FCdot.Value.HasType.lam         : three weakenings on the closing set, one per binder
FCdot.FormTyped.pi              : the pi rule of the type sort read at a form
FCdot.Store.Typed.lam_of_lookup, .lam_inv, .lam_closing, .obj_inv : the fields of the value
FCdot.Value.HasType.beta        : conclusion at Subst.enter b, gains Γ.root? = none, which
                                    the machine discharges by Store.Typed.rootFree
FCdot.Store.Typed.beta          : gains nothing, it reads rootFree off the store typing
FCdot.Tm.HasType.betaCast       : the same, plus the scope-shaped d and c
FCdot.Tm.HasType.projField, .projFieldFull : at the term the proj step now produces
FCdot.Store.Typed.app_uses, .proj_uses : the same inclusions at the same terms
FCdot.Tm.erase_subst            : (t.subst σ).erase = t.erase.map σ.rootVar
                                    erasure keeps roots and drops everything else, and the
                                    capture component of a substitution is everything else
FCdot.Runtime.Tm.lam, .obj      : bodies at the target's signatures, data-free slots
FCdot.Runtime.Step.app, .proj   : the same variable substituted, the new binders dropped
FCdot.preservation, .preservation' : unchanged
FCdot.progress, FCdot.not_stuck : unchanged
FCdot.closedAtomForm_pi, FCdot.closed_pi_inversion : unchanged
FCdot.cap_canon, FCdot.atom_canon, FCdot.closed_box_inversion : unchanged
FCdot.erase_step, FCdot.erase_reflect, FCdot.erase_reflect' : unchanged
FCdot.checkTm_iff and the completeness block : unchanged
the five Prediction theorems    : unchanged
FCdot.lvl_canon, .rigid_canon, .rigid_target, .lvl_safety, .no_inner_escape : unchanged
```

`Ctx.Ren.selfObj` keeps its statement and its proof and has no caller any more, because the
projection step goes through `Subst.Typed.enterObj`.

### New theorems

```
FCdot.Ctx.body_lvl_param      : (Γ.body T).lvl .here = some (.there (.there .here))
FCdot.Ctx.body_lvl_arrow      : (Γ.body T).lvl (.there .here) = some (.there (.there .here))
FCdot.Ctx.body_lvl_root       : (Γ.body T).lvl (.there (.there .here))
                                  = some (.there (.there .here))
FCdot.Ctx.body_lookupCap_arrow : (Γ.body T).lookupCap (.there .here) = .star
FCdot.Dom.inBody_enter        : (T.inBody).subst (Subst.enter a)
                                  = T.subst (Subst.singleC (.var a.root))
FCdot.Cod.underRoot_enter     : (E.underRoot).subst (Subst.enter a) = E.subst (Subst.arg a)
FCdot.Dom.underRoot_enterC    : (T.underRoot).subst (Subst.enterC a)
                                  = T.subst (Subst.singleC (.var a.root))
FCdot.Subst.Typed.singleC     : Γ.IsRoot a ∨ b.isRoot = false →
                                  Subst.Typed (Γ.consC b) (Subst.singleC a) Γ
                                  B2 adds the premise b.instSet? = none, see its own section
FCdot.Subst.Typed.scope       : Subst.Typed Γ σ Γ' → Subst.Typed Γ.scope σ.liftC.liftC Γ'.scope
FCdot.Subst.Typed.arg         : Γ ⊢ₐ b : T.subst (Subst.singleC (.var b.root)) →
                                  Subst.Typed ((Γ.consC .star).cons (.opaque T)) (Subst.arg b) Γ
FCdot.Subst.Typed.enter       : Γ.root? = none →
                                  Γ ⊢ₐ b : T.subst (Subst.singleC (.var b.root)) →
                                  Subst.Typed (Γ.body T) (Subst.enter b) Γ
FCdot.Subst.Typed.enterC      : Γ.root? = none → Subst.Typed Γ.scope (Subst.enterC b) Γ
FCdot.Subst.Typed.enterObj    : Subst.Typed (Γ.objBody T W Wc ls) (Subst.enterObj y) Γ
FCdot.Atom.HasType.weakenRoot : Γ ⊢ₐ a : T →
                                  Γ.scope ⊢ₐ a.rename (Rename.succ.comp Rename.succ) : ...
FCdot.Ctx.mem_caps_root       : Γ.IsRoot r → r ∈ Γ.caps n [r]
FCdot.level_inversion         : Γ ⊢ᶜ f : C ⊑ D → f.MemberFree →
                                  (∀ m, Γ.Confined (Γ.caps m D) r) →
                                  ∀ n, Γ.Confined (Γ.caps n C) r
FCdot.atom_level_inversion    : the atom half of the same induction
FCdot.Runtime.Tm.rename_eq_map : t.rename ρ = t.map (fun x => ρ.var x)
```

`Subst.Typed.enter` is the hardest lemma of the stage.  Its three capture fields are what B0's
`level` rule consumes.  The root atoms of `Γ.body T` are `⊤ᶜ` and the body root and no others,
because a root binder of `Γ` would contradict `Γ.root? = none`, the arrow binder is `.star`
and the parameter is a term binder.  `Subst.enter b` sends both to `⊤ᶜ`, so `capRoot` holds.
For `capLvl`, every level fact of the body context has one of the two on its right, so its
image asks that the image of its left side be at the outermost level of `Γ`, which is
`Store.Typed.confined`.  `Atom.HasType.weakenRoot` is the one crossing of a fresh root, proved
by the type-sort block's own mutual induction, and it is true only under the scope discipline.
No corresponding lemma is needed or true for `Tm.HasType` or `Cont.Typed`.

**Where the content of scope safety lives.**  Over a typed store a context is root free, so
`lvl_safety` and `no_inner_escape` hold vacuously there: the only root is `⊤ᶜ` and
`Store.Typed.confined` puts every atom at the outermost level.  Their content lives in rooted
contexts, and no store types one.  What carries the content instead is `level_inversion`,
which is store free: member-free capture evidence never lowers a level.  Bad capture bounds
enter capture evidence only through `member` and `eqToLe`, which example C3 exhibits under a
lambda, so the restriction to member-free evidence is exactly what an induction on the
evidence alone needs to be true.  The escape of B1.9 is rejected through `level_inversion`
and not through `no_inner_escape`.

### The examples of B1

```
Examples.scope_order   : (Γ.body T).lvl .here = some (.there (.there .here)) ∧ three more
Examples.C2_typed      : C2LitCtx ⊢ᵥ C2lit C2κ₁ : C2LitTy C2κ₁
Examples.X4_no_level   : ¬ X4Ctx.LvlLe (var f) ⊤ᶜ ∧ ¬ X4Ctx.LvlLe (cvar κ_f) ⊤ᶜ ∧
                           ¬ X4OuterCtx.LvlLe (var f) (cvar κ_out)
Examples.X4_caps       : X4Ctx.caps n [var f] = [cvar κ_f]
Examples.X4_no_escape  : ¬ ∃ g, (X4Ctx ⊢ᶜ g : {f} ⊑ {⊤ᶜ}) ∧ g.MemberFree
Examples.X5_fires      : X5Ctx ⊢ᶜ level (var f) ⊤ᶜ : {f} ⊑ {⊤ᶜ}
Examples.C5a_level_step : C5aCtx ⊢ᶜ C5aLevelCo : {fs, u} ⊑ {κ_S}
Examples.C5a_level     : C5aCtx ⊢ᵥ C5aVal : (C5Obj fs) ^ {κ_S}
Examples.S2_level      : S2aCtx ⊢ S2aTm : (C5Obj fs) ^ {κ_S}
```

`scope_order` is T-B1.8 in one line, and it is `rfl`.

**C2, the literal.**  The client half of C2 is unchanged by the arrow, because it reads
`{x.C}`, a capture name.  The literal half is new here, and it is where the new binders show.
`Ctx.objBody` binds the class root and then the self, so the fields sit under both and the
witnesses, which generate the literal's own type, sit under neither.  `Wᶜ` is
`[C ↦ {κ₁}, run ↦ {self∙C}]` and the literal carries the assigned set `{κ₁}`.  Nothing in the
literal names the class root, which is the point: C2 is the regression test that the new
binders are inert where nothing names them.  Two decided facts beside it record that in the
object body the innermost root is the class root and the self is at that level.

**X4, the `withFile` escape, rejected.**  The page's program is
`withFile[() => File^]("test.txt"): f => () => f`.  The outer lambda's body is typed in
`Ctx.body Γ (File ^ {κ_f})`, and the inner lambda's closing evidence forces its assigned set to
hold `f`, so reaching the expected type needs `{f} ⊑ᶜ {r}` for the root `r` of the scope
outside the whole call, which is `⊤ᶜ` at the top level.  `X4_no_level` decides that the premise
of the level rule is false there, at `⊤ᶜ` and at an older root alike, and the checker's verdict
is decided in the kernel beside it.  `X4_no_escape` is stronger and is an instance of
`level_inversion`: no member-free evidence at all puts `{f}` below `{⊤ᶜ}`.  Its content is
`X4_caps`, the binder set of `f` resolving to the arrow binder `κ_f`, whose level is the body
root.  Evidence that is not member free would need a telescope in scope with a capture
proposition whose left side resolves to `κ_f`, and no binder of this context declares one.
Both theorems are store free.  The page's own consequence for the program is
`escaped().read()`, a use after close.

**X5, the counterfactual.**  Under the rejected order `κ_f, f, κ_b`, with the parameter bound
before the body root, the level of `f` is the nearest root older than `f`, which at the top
level is the outermost one.  So `level (var f) ⊤ᶜ` fires and the escape types.  X5 is a
`decide` on the hand-written context, so the binder order of B1.1 is a checked fact.

**S2 and C5a.**  Both are written with the concrete assigned set `{fs, u}` in the result type,
which is what the source's result `any` expands to.  The step that puts that set below a scope
root `{κ_S}` is `level`, which B0 supplies: `fs` is bound outside the scope, so its level
encloses `κ_S`, and `u` is bound inside it, so its level is `κ_S` itself.  `C5a_level` is the
callee's side, the packed literal read at the scope root, and `S2_level` is the caller's side,
the iterator read at the scope root.  Both contexts are the contexts of C5 with the second
capture binder read as a root, and nothing else moves.  The `fresh` halves of both are stage
B2's.

Axioms (`#print axioms`): `propext` and `Quot.sound`, or `propext` alone, for every theorem
above.  The tree contains no `sorry`, `axiom`, `partial`, `unsafe`, or `native_decide`, and no
Mathlib.

## Stage B2

B2 is the third stage of captures the compiler's way (`plan-5d-captures-cc-stages.md` §B2).
It makes a result `fresh` a per-call existential.  An arrow's codomain and the type index of
term typing move to an **answer sort** `ETy`, with two constructors: a plain type, and a type
under one capture binder bounded by a capture set of the enclosing scope.  Nothing else in the
tree sees an answer.  Not a domain, not a telescope, not a proposition, not a capture set, not
the body of a `μ`, and not the body of a box.  So `Form`, the views and every telescope
function are untouched, and the normal forms of the stage are the normal forms of B1 with one
component re-sorted.

The existential carries a declared bound, `∃ᶜ[C₀] T`.  Neither Capless nor the sketch has one.
Capless does not need one, because a Capless `letex` body may not use the unpacked variable at
all.  D6 relaxes that to a declared use set plus avoidance evidence, and then the body's use of
the unpacked variable has to be charged to something.  Without a bound the only rule that
lowers the opened binder is `level`, whose right side is a root, so a lambda containing such a
`letex` cannot close and a top-level `letex` puts `⊤ᶜ` into the state's use set, which makes
`effect_safety` vacuous.  With the bound the charge goes to an ordinary capture set of the
caller's scope and no root enters any use set.

Packing is syntactic and it is a subtyping step.  `Value.pack C h e v` and `PAtom.pack C h e a`
are wrappers carrying the witness, the evidence that the witness is below the declared bound,
and one residual type inclusion.  `ELeCo` is the inclusion relation on answers, with `plain`,
`pack`, `cong` and `trans`.  So a plain answer is widened to an existential wherever a
coercion goes, the codomain of an arrow included, and that is what makes the third widening
step of the page's own `withFile` derivation expressible.  `Value.HasType` gains no rule for a
pack, so a packed value has an existential answer and no other, and a packed value is never
stored, because `Store.Typed.cons` premises `Γ ⊢ᵥ v : T`.

The pack rule opens a root of its own.  `Ctx.scopeInst Γ C` is `(Γ.consC .root).consC (.inst C↑)`,
the pack's root and then the witness binder, and the residual inclusion is read there.  Without
the root the type-sort block's renaming theorem is false and not merely unproven, because every
judgment of that block is renamed at `Ctx.RenR`, which has no `capInner` field, and a rule that
opens a bare capture binder reads the level of that binder relative to an outer root.  With the
root, `Ctx.RenR.scopeInst` is `(h.consRoot).liftC (.inst C↑)`, one line of the tree's own idiom.
The unpack collapses that root by `Subst.instRoot`, which sends the witness binder to the
store's instance binder and the pack's root to `⊤ᶜ`, for the reason B1 sends a body root to
`⊤ᶜ`.

The pack rule cannot be typed without one new capture equality.  `freshCell` needs
`{κ₁}↑↑ ⊑ᶜ {κ}` under an instance binding `κ := {κ₁}↑↑`, and no rule of `CapCo.HasType` derives
it.  `capvar` reads an atom's type, `member` and `eqToLe` read a telescope, `level` needs a
root on the right and an instance binder is not a root, and `elem` is syntactic.  So `CapEq`
gains `instC a C`, which types when `Γ.instSet? a = some C`, and both directions come from it
through `symm` and `eqToLe`.  That is finding F-1.  Its price is finding F-2: `Ctx.Ren`,
`Ctx.RenR` and `Subst.Typed` gain a fourth capture field, `capInst`, which every instance the
tree builds proves by one weakening commutation of `Ctx.lookupCap`.

The machine grows a frame and six steps.  `Frame.castE g` holds the answer coercion itself and
not a head form.  It cannot hold a head form: `castRedex_steps` and `castRedex_normalize` are
stated over untyped states, so a step with a normalisation premise at an answer-cast focus
makes both false.  So the three answer-cast steps are unconditional, and what composes is
`Value.applyE` and `PAtom.applyE`, total and structural on the coercion.  There is no `EForm`,
no `EForm.comp`, no `hnfE`, no answer-form typedness and no fifth `FormsTyped` field.
`Frame.letex u U h f` is the unpacking frame, and `letex`, `unpackAtom` and `unpackVal` are its
three steps.  Neither unpack has a premise and neither takes fuel, which is what the syntactic
wrapper buys.

`letex` does not erase to `let`.  The runtime gains `Runtime.Tm.letex`, `Runtime.Cont.consE`
and the three steps `Step.letex`, `Step.allocE` and `Step.unpack`, and the unpacking steps push
a data-free capture slot onto the runtime store, which `Runtime.Store.consC` already had and no
step produced.  A pack erases to what it wraps, so the erasure cannot tell a packed atom from a
plain one.  What tells them apart is the continuation that accepts the focus, and that is why
`erase_reflect` and `erase_reflect'` now take the focus's answer together with the continuation
that accepts it.

| module | what B2 changed |
|---|---|
| `Debruijn` | nothing |
| `Syntax` | `ETy` with `∃ᶜ[C] T`, its traversals and `Cod s = ETy (Sig.cod s)`, with `Shape.pi` spelling the same type out.  `ELeCo` and `PAtom` in the evidence block, with `PAtom.root`.  `ShapeCo.pi`'s codomain component at `ELeCo (Sig.body s)`.  `Value.pack`, `Tm.atom` at a `PAtom`, `Tm.castE`, `Tm.letex`, `CapEq.instC`.  The `uses` and `inspects` clauses of the two new formers.  `Value.annot` reads through a pack.  `Subst.instRoot` |
| `RenameLemmas` | the five `Ty` lemmas one sort up as `ETy` lemmas, the `ELeCo` and `PAtom` twins, `PAtom.root_rename` and `PAtom.root_subst`, and the two cancellations `Dom.underRoot_instRoot` and `Ty.weakenC_two_instRoot`.  `Cod.underRoot_enter` keeps its statement one sort up |
| `Context` | `Ctx.scopeInst`, `CapBound.instSet?`, `Ctx.instSet?`, and the `abbrev Ctx.InstOf`, so that `Decidable` is synthesised and the checker's case decides |
| `Typing` | `ELeCo.HasType`, `PAtom.HasType`, `Value.HasTypeE`, `CapEq.HasType.instC`.  `Tm.HasType` at `ETy s`, with `abbrev Tm.HasTy` carrying the old notation.  The rules `Tm.HasType.atom`, `.val`, `.let`, `.castE`, `.letex`, and `Value.HasType.lam` at an answer codomain.  `ShapeCo.HasType.pi`'s codomain premise at the answer sort |
| `TypingRename` | the `capInst` field on `Ctx.Ren` and `Ctx.RenR`, `Ctx.RenR.scopeInst`, `Ctx.Ren.instC`, the `renameR` and `rename` twins of the three new judgments, and the four facts every `capInst` field is proven from |
| `TypingSubst` | the `capInst` field on `Subst.Typed`, `Subst.Typed.scopeInst`, `Subst.Typed.instRoot`, the `ETy` substitution lemmas, and the `subst` twins of the three new judgments.  `Subst.Typed.singleC` gains one premise.  The `selfCast` block moves here from `Preservation` |
| `Transparency` | `Ctx.Refines` gains `capInstEq`, with `Ctx.Refines.scopeInst` and `.instOf`, and the three new `refine` twins |
| `Checker` | `synthTmE`, `checkTmE`, `synthPAtom`, `checkPAtom`, `synthELe`, `checkELe`, `synthValueE`, `checkValueE` with their soundness.  `checkTm Γ t T` is `checkTmE Γ t (.ty T)`.  `ETy.rename?`, `ETy.strengthen?`, `Ty.strengthenC2?`, `ETy.strengthenVC2?`.  `synthCapEqCore` decides `Γ.InstOf`.  `Cod.underRoot?` one sort up |
| `CheckerCompleteness` | the completeness of the four new judgments and the twelve public `_iff` theorems beside them.  `checkTm_iff` and every older `_iff` keeps its statement |
| `Normalizer` | `Form.pi`'s codomain component at `ELeCo (Sig.body s)`.  That is the whole diff.  `Form.combine`'s `pi` case is unchanged text |
| `FormTyping` | `FormTyped.pi`'s codomain premise at the answer sort.  `Value.precView_noBnd` gains one case and `Value.precView` gains no clause |
| `FormAlgebra` | `Subst.Typed.selfCastOpaque` gains its `capInst` field, and the module imports `TypingSubst` |
| `Store` | `Value.witnesses`, `Value.capWitnesses` and `Value.fieldLabels` read through a pack.  `Value.IsLiteral` gains no clause.  `Value.isLiteral_rename` and `Store.Typed.lookup_isLiteral` live here now |
| `Machine` | `Frame.castE` and `Frame.letex`.  `Cont.Typed` accepts an `ETy s` and gains two constructors.  `State.Typed`'s existential witness is an answer and `State.Final` reads a `PAtom`.  `usesK` gains two clauses, `Cont.weakenC` and `usesK_weakenC` stand beside their term twins.  `Value.applyE`, `PAtom.applyE`, `PAtom.root_applyE`.  `appCast` builds a `.castE`, and the six new steps `castEPush`, `castEVal`, `castEAtom`, `letex`, `unpackAtom`, `unpackVal` |
| `CanonicalForms` | `capeq_canon` gains the `instC` case.  Four theorems gain a packed-stored-value case, each closed by inverting `Value.HasType`.  The module imports `Preservation` and `erase_reflect'` moves out |
| `Preservation` | `ex_stays_ex`, `no_ex_le_ty`, `pack_canon`, `pack_canon_val`, `Value.HasTypeE.applyE`, `PAtom.HasType.applyE`, the two `ty_inv` inversions, the two `unpackPayload` lemmas, `LeCo.HasType.atScopeInst`, the four answer-sort instantiation lemmas, `preservation_unpackAtom`, `preservation_unpackVal`.  `Cont.Typed.weaken` at the answer sort with `Cont.Typed.weakenC` beside it.  `Tm.HasType.betaCast` at the answer sort.  `preservation` keeps its statement |
| `Progress` | `closed_pi_inversion` gains one case.  `progress` keeps its statement and decides the new shapes frame kind by frame kind |
| `Consistency` | nothing beyond what B1 left |
| `Prediction` | `CapCo.HasType.instHere`, `CaptureSet.letexCharge_substVar`, and the two unpack cases of `step_uses`.  The five prediction theorems keep their statements |
| `Resolution` | `Ctx.Root_inst`, the instance twin of `Ctx.Root_name` |
| `Erasure` | `State.CastRedex` gains two disjuncts and `State.isCastRedex` four clauses.  `Tm.erase` gains `.castE` and `.letex`, `Value.erase` a pack, `Cont.erase` the two frames |
| `ErasureMetatheory` | the three runtime inversions, `Cont.erase_weakenC`, `Value.erase_applyE`, `Store.Typed.lookup_notPack`, the two measure lemmas of the answer cast, `State.CastTyped` with `castRedex_steps_typed` and `castRedex_normalize_typed`, and the three reflection lemmas of the new runtime steps.  `erase_reflect` and `erase_reflect'` take the focus's answer with the continuation that accepts it.  `erase_step` keeps its statement |
| `Examples` | the five examples Y1 to Y5, the store that types Y1's body context, and the target side of the three source `fresh` examples |

`Runtime.lean` sits outside this directory and B2 reached it too: `Runtime.Tm.letex`,
`Runtime.Cont.consE`, and the three steps `Step.letex`, `Step.allocE` and `Step.unpack`.

### Notation added by B2

| | |
|---|---|
| `∃ᶜ[C] T` | the existential answer with its declared bound |
| `Γ ⊢ t :ᵉ E` | term typing at an answer.  `Γ ⊢ t : T` is `Tm.HasTy`, which is `Tm.HasType Γ t (.ty T)` |
| `Γ ⊢ᵉ g : E ≤ E'` | inclusion between answers |
| `Γ ⊢ₚ p : E` | a packed atom at an answer |
| `Γ ⊢ᵥᵉ v : E` | a value at an answer |

### The rules

```
FCdot.CapEq.HasType.instC   : Γ.InstOf a C → Γ ⊢ᶜ .instC a C : [a] ≡ C
FCdot.ELeCo.HasType.plain   : Γ ⊢ e : T ≤ T' → Γ ⊢ᵉ .plain e : .ty T ≤ .ty T'
FCdot.ELeCo.HasType.pack    : Γ ⊢ᶜ h : C ⊑ C₀ →
                              Γ.scopeInst C ⊢ e : (T'↑)↑ ≤ T.underRoot →
                              Γ ⊢ᵉ .pack C h e : .ty T' ≤ ∃ᶜ[C₀] T
FCdot.ELeCo.HasType.cong    : Γ ⊢ᶜ h : C₀ ⊑ C₀' →
                              Γ.scope ⊢ e : T.underRoot ≤ T'.underRoot →
                              Γ ⊢ᵉ .cong h e : ∃ᶜ[C₀] T ≤ ∃ᶜ[C₀'] T'
FCdot.ELeCo.HasType.trans   : the transitive closure of the three
FCdot.PAtom.HasType.plain   : Γ ⊢ₐ a : T → Γ ⊢ₚ .plain a : .ty T
FCdot.PAtom.HasType.pack    : Γ ⊢ₐ a : S → Γ ⊢ᶜ h : C ⊑ C₀ →
                              Γ.scopeInst C ⊢ e : (S↑)↑ ≤ T.underRoot →
                              Γ ⊢ₚ .pack C h e a : ∃ᶜ[C₀] T
FCdot.Value.HasTypeE.plain  : Γ ⊢ᵥ v : T → Γ ⊢ᵥᵉ v : .ty T
FCdot.Value.HasTypeE.pack   : the value twin of PAtom.HasType.pack
FCdot.Tm.HasType.atom       : Γ ⊢ₚ p : E → Γ ⊢ .atom p :ᵉ E
FCdot.Tm.HasType.val        : Γ ⊢ᵥᵉ v : E → Γ ⊢ .val v :ᵉ E
FCdot.Tm.HasType.castE      : Γ ⊢ t :ᵉ E → Γ ⊢ᵉ g : E ≤ E' → Γ ⊢ .castE t g :ᵉ E'
FCdot.Tm.HasType.letex      : Γ ⊢ t :ᵉ ∃ᶜ[C₀] T → Γ ⊢ᶜ h : C₀ ⊑ U' →
                              (Γ.consC .star).cons (.opaque T) ⊢ u :ᵉ (E↑)↑ →
                              (Γ.consC .star).cons (.opaque T) ⊢ᶜ f :
                                u.uses ⊑ (U'↑)↑ ∪ [.cvar (.there .here)] →
                              Γ ⊢ .letex t u U' h f :ᵉ E
```

The opened capture binder of a `letex` is `.star`, with no scope of its own.  So it is opaque
to resolution and two `letex`es open two incomparable binders, which is Y1.  The answer avoids
both opened binders, which is Capless's `E.cweaken.weaken` verbatim.  The declared use set
avoids both binders and the body's own use set is put below it by evidence, which is the
departure D6 names.  And the body may charge a use to the opened binder itself, which is what
the second premise pays for: the head's bound is already below `U'`, and at run time the opened
binder resolves to the witness, which is below the bound.  Both facts are consumed by
`step_uses`.

The six new steps of the machine.

```
FCdot.Step.castEPush  : ⟨σ, K, .castE t g⟩ ⟶ ⟨σ, K ▹ .castE g, t⟩
FCdot.Step.castEVal   : ⟨σ, K ▹ .castE g, .val v⟩ ⟶ ⟨σ, K, .val (v.applyE g)⟩
FCdot.Step.castEAtom  : ⟨σ, K ▹ .castE g, .atom p⟩ ⟶ ⟨σ, K, .atom (p.applyE g)⟩
FCdot.Step.letex      : ⟨σ, K, .letex t u U h f⟩ ⟶ ⟨σ, K ▹ .letex u U h f, t⟩
FCdot.Step.unpackAtom : the wrapper is opened, the store gains .inst C, the body is
                          substituted by the payload atom
FCdot.Step.unpackVal  : the same with the payload allocated first
```

### Statements restated

Nothing was weakened.  These are the statements of B0, B1 and the DOT way, restated where B2
changed the representation, with the reason each means what it meant.

```
FCdot.Cod, FCdot.Shape.pi   : the codomain is an ETy
                                a plain codomain is .ty T, Cod is an abbrev, and no proof in
                                the tree cases on the head of a codomain
FCdot.Cod.underRoot         : result written ETy (Sig.body s), the same renaming one sort up
FCdot.ShapeCo.pi, FCdot.Form.pi, FCdot.FormTyped.pi : codomain component at the answer sort
                                the same contravariant domain and covariant codomain, the
                                codomain half read at ELeCo where it was read at LeCo
FCdot.Tm.atom               : takes a PAtom, and every Tm.atom a is spelled Tm.atom (.plain a)
                                PAtom.root (.plain a) = a.root, so uses and inspects read the
                                same root and every old term is the term it was
FCdot.Tm.HasType            : indexed by ETy s, with Tm.HasTy Γ t T = Tm.HasType Γ t (.ty T)
                                carrying the notation Γ ⊢ t : T, so every statement written
                                that way is the proposition it was
FCdot.Tm.HasType.let        : the body may have an answer
                                a let whose body is plain is the rule as it stands
FCdot.Value.HasType.lam     : body typed at U.underRoot, an answer
                                one premise re-sorted, the same obligation on the same body
FCdot.CapEq, FCdot.CapEq.HasType : one constructor and one rule more, additive
FCdot.Ctx.Ren, FCdot.Ctx.RenR, FCdot.Subst.Typed : one capture field more, additive
FCdot.Ctx.Refines           : one field more, capInstEq, additive
                                refinement never touches the capture spine, so all nine
                                instances prove it by rfl or one weakening commutation
FCdot.Value.annot, .witnesses, .capWitnesses, .fieldLabels : one clause each, reading through
                                a pack, as they read through a cast
FCdot.Value.core, .coercions, .IsLiteral : no clause, a pack falls into the catch-all
FCdot.Value.core_isLiteral  : unchanged, with one more rfl case
                                a packed value is kept out of the store by Store.Typed.cons,
                                which premises Value.HasType, and Value.HasType has no pack rule
FCdot.Frame, FCdot.usesK, FCdot.Cont.rename, FCdot.Cont.erase : two constructors more, additive
FCdot.Cont.Typed            : accepts an ETy s and produces a Ty s
                                nil accepts .ty T, so a continuation still produces a type and
                                only what it accepts is widened
FCdot.State.Typed           : the existential witness is an ETy s, the index U : Ty s is not
                                so preservation, progress, not_stuck, capture_prediction and
                                returned_capture_bound keep their statements verbatim
FCdot.State.Final           : the second disjunct reads a PAtom
                                in a typed state the answer at nil is plain, so no packed atom
                                is ever final
FCdot.Step.appCast          : builds a .castE frame
                                on a plain codomain the frame applies a .plain coercion and
                                applyE emits Value.cast or Atom.cast, the same two states
FCdot.Step.castAtom         : hands back .atom (p.applyE (.plain e))
                                on a plain wrapper PAtom.applyE at a .plain coercion is
                                Atom.cast, and the step stays unconditional
FCdot.Tm.HasType.betaCast   : builds a .castE and its codomain coercion is an ELeCo
                                the same lemma at the answer sort, it is what appCast now
                                produces, and its old form has no other caller
FCdot.Store.Typed.beta, FCdot.Value.HasType.beta : conclusions at an answer, the same map
FCdot.State.CastRedex, .isCastRedex : two disjuncts more, additive
                                the predicate still says that the next step erases to no
                                runtime step
FCdot.State.CastInv         : first disjunct reads ∃ E, Γ ⊢ st.t :ᵉ E
                                an answer is what a focus has
FCdot.Tm.castDepth, FCdot.Cont.castDepth : one counting clause each and one zero clause each
FCdot.Subst.Typed.singleC   : gains the premise b.instSet? = none
                                see the finding below
FCdot.erase_reflect, .erase_reflect' : hty becomes the focus's answer together with the
                                continuation that accepts it
                                see the finding below
FCdot.Value.erase_eq_lam, .erase_eq_obj, .erase_eq_box : gain a premise that the value is not
                                a pack
                                see the finding below
FCdot.Tm.inspects_reflect   : gains a second exclusion, ∀ t₀ g, t ≠ .castE t₀ g
                                see the finding below
FCdot.preservation, .preservation', .progress, .not_stuck : unchanged
FCdot.erase_step, FCdot.final_erase, FCdot.final_reflect : unchanged
FCdot.castRedex_steps, .castRedex_normalize and their inverses : unchanged
FCdot.checkTm_iff and the completeness block : unchanged
FCdot.step_uses, .capture_prediction, .inspects_covered, .effect_safety,
  .returned_capture_bound : unchanged
FCdot.cap_canon, .atom_canon, .closed_box_inversion, .closed_pi_inversion : unchanged
FCdot.lvl_canon, .rigid_canon, .rigid_target, .lvl_safety, .no_inner_escape,
  .level_inversion : unchanged
```

**Four findings, each a statement whose form changed for a reason the stage discovered.**

`Subst.Typed.singleC` is false as B1 stated it once `capInst` lands.  The lemma instantiates an
arbitrary capture binder by an arbitrary atom under the single side condition
`b.isRoot = false ∨ (Γ.IsRoot a ∧ ∀ e, Γ.LvlLe e a)`.  The bound `.inst C` satisfies
`isRoot = false`, so the statement covers replacing an instance binder by `⊤ᶜ`, and then
`capInst` asks for `Γ.InstOf ⊤ᶜ C`, which is `none = some C`.  The counterexample is machine
checked.  The repair is one premise, `b.instSet? = none`, the exact analogue of B0's
`b.isRoot = false` on the ten `weakenC` theorems.  Its price is nil: the lemma has no user
anywhere in the tree, and its five siblings all move `.star` or `.root` and never `.inst`.

`erase_reflect'` is false once an unpacking frame exists.  A typed store with a `letex` frame
at a plain atom focus satisfies the old hypotheses, the runtime steps by `Step.unpack`, and no
target step fires.  The erasure cannot tell the three failing shapes apart, because a pack
erases to what it wraps.  What tells them apart is the continuation's typing, and that is what
the new hypothesis supplies.  Every caller already holds a `State.Typed` two lines above the
call and threw the continuation half away.

`Value.erase_eq_lam` and its two siblings are false once a packed value exists, because
`Value.IsLiteral` gains no clause, so a packed lambda is a literal whose erasure is a runtime
lambda and which is not a lambda.  The three lemmas ask their value not to be a pack, and
`Store.Typed.lookup_notPack` discharges the premise at the one place any of them is used.

`Tm.inspects_reflect` needs a second exclusion.  An answer cast erases to its body, so an
answer cast whose body is an application erases to a term that reads a root, while
`(Tm.castE t g).inspects` is `none`.  The old hypothesis excluded exactly the one former with
that property, and B2 adds a second.  Its only caller is `State.inspects_reflect`, whose
hypothesis is `¬ st.CastRedex`, and `State.CastRedex` already has the `.castE` disjunct.

### New theorems

```
FCdot.ex_stays_ex        : Γ ⊢ᵉ g : E₁ ≤ E₂ → E₁.isEx = true → E₂.isEx = true
FCdot.no_ex_le_ty        : Γ ⊢ᵉ g : ∃ᶜ[C₀] T₁ ≤ .ty T₂ → False
FCdot.pack_canon         : Γ ⊢ₚ p : ∃ᶜ[C₀] T → ∃ C h₀ e a S, p = .pack C h₀ e a ∧
                             Γ ⊢ₐ a : S ∧ Γ ⊢ᶜ h₀ : C ⊑ C₀ ∧
                             Γ.scopeInst C ⊢ e : (S↑)↑ ≤ T.underRoot
FCdot.pack_canon_val     : the value twin
FCdot.Value.HasTypeE.applyE : Γ ⊢ᵥᵉ v : E → Γ ⊢ᵉ g : E ≤ E' → Γ ⊢ᵥᵉ v.applyE g : E'
FCdot.PAtom.HasType.applyE  : the atom twin
FCdot.PAtom.root_applyE  : (p.applyE g).root = p.root
FCdot.Value.erase_applyE : ⌊v.applyE g⌋ = ⌊v⌋
FCdot.Ctx.Ren.instC      : Ctx.Ren (Γ.scopeInst C) Rename.id (Γ.scopeInst C) at .inst and .star
FCdot.Subst.Typed.instRoot : Γ.root? = none →
                             Subst.Typed (Γ.scopeInst C) Subst.instRoot (Γ.consC (.inst C))
FCdot.Dom.underRoot_instRoot : (Dom.underRoot T).subst Subst.instRoot = T
FCdot.Ty.weakenC_two_instRoot : ((T↑)↑).subst Subst.instRoot = T↑
FCdot.Ctx.RenR.scopeInst : Ctx.RenR Γ ρ Γ' → Ctx.Ren (Γ.scopeInst C) ρ.lift.lift
                             (Γ'.scopeInst (C.rename ρ))
FCdot.Ctx.Root_inst      : Γ.InstOf a C → RootsEq Γ [a] C
FCdot.Cont.Typed.weakenC : the capture-kind twin of Cont.Typed.weaken
FCdot.CapCo.HasType.instHere : the declared bound, consumed: the opened binder is an instance
                             of the witness set, the wrapper puts that set below the declared
                             bound, and the frame puts the declared bound below the set the
                             body declares
FCdot.Store.Typed.lookup_notPack : a stored value is never a pack
FCdot.State.CastTyped    : the typed invariant carried along cast-frame normalisation, with
                             castRedex_steps_typed and castRedex_normalize_typed
FCdot.preservation_unpackAtom, .preservation_unpackVal : the two unpack cases, packaged
FCdot.checkTmE_iff, .checkPAtom_iff, .checkELe_iff, .checkValueE_iff : the four new judgments
                             are decided, and each is sound and complete
```

`unpackAtom` is the hardest case of the stage, and it uses every new piece at once.
Preservation runs in eight steps.  Invert `Cont.Typed.letex` for the three body premises.
Invert `Tm.HasType.atom` and `pack_canon` for the witness, the bound evidence and the residual,
with no normalisation and no fuel.  Extend the store by `Store.Typed.consC` at `.inst C`, with
no obligation to discharge.  Type the payload in the extended scope by `Atom.HasType.weakenC`
at a non-root bound and by the residual substituted along `Subst.Typed.instRoot`, whose two
cancellations are `Ty.weakenC_two_instRoot` and `Dom.underRoot_instRoot`.  Transport the body
and its evidence along `Ctx.Ren.instC` lifted by the payload binder.  Substitute the atom by
`Subst.Typed.single`, where `((E↑)↑).substVar y = E↑` is the avoidance the rule wrote into its
premise.  Weaken the continuation by `Cont.Typed.weakenC`.  Assemble `State.Typed` at the
extended context.  For `step_uses` the embedding is `Store.Ext.consC` at `.inst C`, which
`.star` could not supply.

### The examples of B2

```
Examples.Y1_freshCell    : Y1Ctx ⊢ᵥ YFreshCell Y1κ₁ : YFreshCellTy Y1κ₁
Examples.Y1_caller       : Y1CCtx ⊢ Y1caller : Ty.pure tArrow
Examples.Y1Store_typed   : ⊢ Y1Store : Y1BodyCtx
Examples.two_calls_incomparable :
                           (¬ ∃ f, Y1BodyCtxO ⊢ᶜ f : [cvar κ₁'] ⊑ [cvar κ₂']) ∧
                           (¬ ∃ f, Y1BodyCtxO ⊢ᶜ f : [var x₁] ⊑ [var x₂])
Examples.Y2_makeLogger   : Ctx.nil ⊢ᵥ Y2MakeLogger : Y2MakeLoggerTy
Examples.Y2_client       : Y2Ctx ⊢ᵥ Y2Client : Y2ClientTy
Examples.Y3_mk           : Ctx.nil ⊢ᵥ Y3Mk : Y3MkTy
Examples.Y3_caller       : Y3CtxO ⊢ Y3caller : Ty.pure .top
Examples.c5b_caller_uses : Y3CtxO ⊢ᶜ Y3useCo : Y3caller.uses ⊑ [var fs]
Examples.c5b_no_witness  : ¬ ∃ f, Y3BodyCtxO ⊢ᶜ f : [cvar κ'] ⊑ [var fs]
Examples.Y4_pack_under_pi : Y1Ctx ⊢ Y4packUnderPi : (Π(Unit) (.ty (Cell ^ {κ₁}))) ^ {κ₁}
                              ≤ YFreshCellTy Y1κ₁
Examples.Y4_isolation    : ¬ ∃ g, X4Ctx ⊢ᵉ g : (∃ᶜ[C₀] T) ≤ .ty T'
Examples.Y4_no_escape    : ¬ ∃ g, (X4Ctx ⊢ᶜ g : {f} ⊑ {⊤ᶜ}) ∧ g.MemberFree
Examples.Y5_packed       : C5Ctx ⊢ᵥᵉ Y5ExVal : Y5ExTy
Examples.Y5_caller       : C5Ctx ⊢ Y5caller : Ty.pure tArrow
Examples.Z1_translated, .Z2_translated, .Z3_translated : the three source fresh examples,
                           translated and typed at the translated type
Examples.Z1_caller_translated : a source letex, translated
Examples.Z1_erase, .Z1_caller_erase, .Z2_erase, .Z3_erase : the translation runs the source
                           program
```

**Y1, `freshCell`, and two calls that are incomparable.**  Under the platform prefix `κ₁`, with
`Cell = μ(c. {set : (Π(⊤) ⊤) ^ {c}})`, the callee allocates a cell and packs it at the witness
`{κ₁}`.  The residual inclusion of that pack is the one place the stage needs F-1: its capture
half is `.eqToLe (.symm (.instC (.cvar .here) {κ₁}↑↑))`, read at `Γ.scopeInst {κ₁}`.  A caller
unpacks each of two calls where it stands, since the `letex` rule's head premise is on an
arbitrary term while `Tm.HasType.let`'s is at a plain answer.  In the body's context the two
opened binders are `.star`, `x₁ : Cell ^ {κ₁'}` and `x₂ : Cell ^ {κ₂'}`, and neither of the two
inclusions is derivable.  Both halves go through `cap_canon`: an inclusion gives
`Γ.roots n [cvar κ₁'] ⊆ Γ.roots m [cvar κ₂']`, `Ctx.capsAtom` at a `.star` binder is the binder
itself and `Ctx.expandAtom` is the identity on a non-root atom, so the two singletons would
have to be equal.  D11's warning is respected: the argument is stated at `roots`, and
`Y1_caps_κ₁'` and its three siblings are the named step from `caps` to `roots`.  What is
**not** claimed: at run time both binders carry `.inst {κ₁}`, so in the store's context each is
below the other.  That is sound, it is D12's point, and it means Y1 reproduces the page's
sentence in the compile-time reading only.

`cap_canon` reads a typed store, which is decision 12, so `two_calls_incomparable` needs a
store for the body's context.  A store types transparent term bindings, and the `letex` rule
builds opaque ones, so the theorem is stated at the opaque context `Y1BodyCtxO` and transported
into the transparent `Y1BodyCtx` by `Ctx.Refines`.  A transparent context knows everything the
opaque one knows, so refusing the inclusion there refuses it in the opaque one.  `Y1Store_typed`
exhibits the store rather than assuming one, which is what keeps the theorem from being
vacuous.  The one cost is that the unit of the B2 examples is a pure closure and not `⊤`, since
`⊤` is not a type a store can hold.

**Y2, `makeLogger`.**  The parameter's `any` is the arrow's own capture binder, which is D7, and
the result is packed at the witness `{x}`, the parameter itself.  The witness is the parameter
and not a platform binder, and that is the example's point, "this `any` has to be defined in a
scope in which `fs` is visible".  `Y2_client` is the caller, written as a closure over `fs`: it
unpacks, charges its use to `{fs}` and to the callee it called, and closes.  That it closes is
F-3 in one line, and it is what the declared bound buys.

**Y3, C5b.**  The callee of Y2 with the caller of C5a: the caller unpacks with `letex`, projects
a field off the unpacked object, applies it through `{κ}`, and charges the use to the
instantiated bound.  `c5b_caller_uses` says the caller's use set is the argument it passed and
nothing more.  `c5b_no_witness` says the caller never learns that the witness is the argument,
and it goes through `cap_canon` over the same kind of exhibited store as Y1.

**Y4, the `withFile` escape, rejected twice over.**  The page widens the callback's inferred
type in three steps, and all three exist in the target: `capvar`, then `level`, then
`ELeCo.pack` under `ShapeCo.pi`.  `Y4_pack_under_pi` is the third step, decided by the checker.
`Y4_isolation` is `no_ex_le_ty`, and it is the step the page names, "the capture checker
prevents the existentially bound `fresh` from flowing into this outer `any`".  `Y4_no_escape` is
B1's theorem, unchanged, and it is the level check after a `letex`: even if the caller unpacks,
the unpacked binder's level is the caller's and the level rule runs only inward.  The page's
consequence for the program is `escaped().read()`, a use after close.

**Y5, the `fresh` halves of S2 and C5a.**  The same two programs with the callee's result
declared `fresh`, read through a `letex` instead of through `{κ_S}`.  `Y5_packed` is C5a's
literal at an existential answer bounded by the concrete assigned set `{fs, u}`, and
`Y5_caller` is S2's program read through a `letex`: the iterator is unpacked, `next` is read
off the abstract member, and the call is charged through the member's upper bound.

Axioms (`#print axioms`): `propext` and `Quot.sound`, or less, for every theorem above.  The
tree contains no `sorry`, `axiom`, `partial`, `unsafe`, or `native_decide`, and no Mathlib.

## Stage B3

B3 is the fourth and last stage of captures the compiler's way
(`plan-5d-captures-cc-stages.md` §B3).  It is the source's stage: the reading of `any` by position,
the source's own level machinery with one rule, the source's term-level expansion, and T17.  The
target moves in two files only, and that is decision 33.

`FCdot/LevelInversion.lean` gains the renaming of the two member-free families,
`CapCo.MemberFree.rename` and `Atom.MemberFree.rename`, with the `Rename.succ` instances beside
them.  They go there and not into `TypingRename.lean` because that is where the rest of the
member-free metatheory already lives, next to `level_inversion` itself.  They are one mutual block,
structural on the member-free proof, and the one case with content is `Atom.MemberFree.cast`, where
`LeCo.rename` at `.capt` reduces so that the induction hypothesis on the capture half applies.  They
exist because the translation's `Ctx.varAtom` weakens at every `.there` clause, and
`Ctx.varAtom_memberFree` has to weaken with it.

`FCdot/Examples.lean` gains the target side of the source examples of B3.9 and nothing else.  No
rule, no judgment, no normal form and no theorem of the target changed, and `lake build` of every
other module of this directory is the build it was.

| module | what B3 changed |
|---|---|
| `LevelInversion` | `CapCo.MemberFree.rename`, `Atom.MemberFree.rename`, `CapCo.MemberFree.weaken`, `Atom.MemberFree.weaken`, after `Ctx.mem_caps_root` and before the inversion itself |
| `Examples` | the target side of W2 to W5.  `W5_caps` and `W5_no_escape`, which is T17 at `⊤ᶜ`.  The translations of the two repaired source programs S1 and S2, unchanged in form |
| every other module | nothing |

### Statements restated

Nothing in this directory was weakened and nothing gained a hypothesis.  `level_inversion`,
`no_inner_escape`, `lvl_safety`, `cap_canon`, `two_calls_incomparable`, `X1` to `X5` and `Y1` to
`Y5` are the theorems they were, with the proofs they had.

### New in this stage

```
FCdot.CapCo.MemberFree.rename, FCdot.Atom.MemberFree.rename
FCdot.CapCo.MemberFree.weaken, FCdot.Atom.MemberFree.weaken
FCdot.Examples.W2BodyCtxWf, .W2CallCtxWf
FCdot.Examples.W2_translated, .W2_call_translated, .W2_erase
FCdot.Examples.W3_translated, .W4_translated
FCdot.Examples.W5_caps, .W5_no_escape
```

### The examples

X1, X2 and X3 state the level hierarchy over a spine written by hand, and the source's W1 states the
same hierarchy over two real lambda bodies, so the nesting there is the binder order the rules
produce.  T-B1.8, `scope_order`, is the three `rfl` facts about `Ctx.body`, and the source's W2 is
the expansion that puts the arrow's capture binder in the parameter's set together with the call
that instantiates it.  X4 rejects the `withFile` escape and W5 rejects it on the source side, in two
settings.  X5 is the counterfactual binder order and W6 is the source's own.  Y1 is `freshCell` with
two calls whose opened binders are incomparable, and W4 is the source callee of it.  Y2 is
`makeLogger` and W3 is that callee with its parameter written `any`.

```
FCdot.Examples.W2_translated      : platCtx.translate ⊢ ⟦W2_typed⟧ : ⟦W2Ty⟧
FCdot.Examples.W2_call_translated : W2CallCtx.translate ⊢ ⟦W2_call⟧ : ⟦⊤ ^ {}⟧
FCdot.Examples.W2_erase           : ⌊⟦W2_typed⟧⌋ = ⌊W2Tm⌋
FCdot.Examples.W3_translated      : makeLogger, the witness the parameter
FCdot.Examples.W4_translated      : freshCell, at the type the result fresh expands to
FCdot.Examples.W5_caps (n)        : W2BodyCtx.translate.caps n {f} = {κ_f}
FCdot.Examples.W5_no_escape       : no member-free source subcapturing puts {f} below {κ₁}
```

**W5 at the target.**  `W5_no_escape` is T17 at `r = ⊤ᶜ`, and it is the twin of `X4_no_escape` one
calculus over.  The binder set of the callback's parameter resolves to the arrow binder, whose level
is the body root, so it is not at the outermost level.  The platform capability is, because the
platform prefix opens no scope.  And member-free evidence never lowers a level.  The statement is on
the target because it names `⊤ᶜ`, which the source has no atom for, and it is about source evidence,
which is what T17 is for.

Axioms (`#print axioms`): `propext` and `Quot.sound`, or less, for every theorem above.

## Stage K0

K0 is the first stage of classifiers (`plan-5f-classifiers-stages.md` §K0).  It is the target only,
and it adds no evidence rule.  The classifier tree and the kinds arrive as data in
`Coercions.Classifiers.Cls`, which this directory imports from `Syntax.lean` and which imports
nothing of the tree.  A capture bound gains the flavour `cls c`, a capture atom gains the projection
`a ↾ φ`, resolution and expansion gain one clause each, and the semantic side is `Ctx.KindLe` with
the four theorems T1 to T4.

Four sentences shape the whole stage.  A classifier is closed data, so every new congruence case of
the renaming and substitution blocks is one `rfl` over the kind argument and every commutation of a
projection with a rename is `List.map_map`.  Resolution lands in capture binders and in the universal
root, which is why a classifier rides on `CapBound` and nowhere else.  A filter is only meaningful
after expansion and must not be followed by one, so it is consumed inside `Ctx.expandAtom`, the
second and final stage of `Ctx.roots`.  And expansion therefore produces projection-free atoms, so
`Ctx.roots`, `Ctx.Root`, `CapLe` and `RootsEq` never see a projection and keep their bodies, their
statements and their proofs.

| module | what K0 changed |
|---|---|
| `Syntax` | the constructor `CapAtom.proj` with the notation `a ↾ φ`, `CapAtom.base`, `CapAtom.kindOf`, `CapAtom.projBy`, `CaptureSet.proj`, one clause in `CapAtom.rename` and one in `CapAtom.subst`, and the import of `Coercions.Classifiers.Cls` |
| `Context` | the flavour `CapBound.cls`, `CapBound.classifier`, one clause in `CapBound.opaque` and one in `CapBound.rename`, `Ctx.classOf`, `Ctx.admitsB`, one clause in `Ctx.lvlAtom` |
| `RenameLemmas` | six proofs move from `cases` to `induction`, with their statements unchanged |
| `Levels` | the `cls` and `proj` alternatives, `Ctx.lvlLe_proj_left`, `CapAtom.base_ne_proj`, `CapAtom.base_base`, `CapAtom.base_rename`, `Ctx.lvlAtom_base`, `Ctx.lvlLe_base_left`, `Ctx.lvlAtom_isRoot` |
| `Resolution` | the two new clauses of `Ctx.capsAtom` and the one of `Ctx.capsBound` and of `Ctx.expandAtom`, the `sizeOf` measures, L1 to L5, the weakening commutations of a classifier, `Ctx.admitsB_top`, `Ctx.filter_map_base_eq_self`, `Ctx.mem_expandAtom_base`, and K0.5 and K0.6 in full |
| `TypingRename`, `TypingSubst`, `Transparency` | one alternative per atom or bound analysis, `Ctx.lvlLe_rename_of_base` and `Ctx.lvlLe_subst_of_base`, `CapBound.subst` at `cls`, `CapAtom.cons_cases` and `CapAtom.consC_cases` with one more disjunct |
| `Checker` | one clause in `CapAtom.rename?` and in its soundness and completeness, one alternative in three case analyses |
| `Store` | nothing.  `Store.Typed.consC` asks only that the bound is not a scope root, and `cls` is not one |
| `Machine` | `Rename.InjectiveOnAtoms.comp_succ` by induction, and K0.7 and T4 |
| `CanonicalForms` | the `cls` and `proj` alternatives of `Ctx.caps_of_isRoot`, and one step in the level case of `cap_canon` |
| `Consistency` | the `cls` alternative of `Ctx.caps_of_opaque`, and the restatements of `lvl_canon`, `lvl_safety` and `rigid_target` |
| `LevelInversion`, `Preservation` | one alternative each, and the wrapper `Ctx.lvlLe_rename_of_base` in the self-object renaming |
| `Examples` | the three classifier examples K1x, K2x and K3x, and the two call sites that read a restated lemma |
| every other module | nothing |

### Notation

One token is new, and it is `scoped` in namespace `FCdot` like the rest.

| | |
|---|---|
| `a ↾ φ` | the capture atom `a` projected by the kind `φ`.  `notation:max`, so `(CapAtom.cvar κ) ↾ φ` needs its parentheses |

`ᶜ` is not a legal identifier character, so `⊤ᶜ` stays a notation token and the classifier data is
written `Cls.Classifier`, `Cls.Kind`, `Cls.Subtree` inside this directory.

### Statements restated

Nothing was weakened.  Each row below is a statement of the copy that changed form, with the sentence
that says why its meaning is the same.  A premise reading `a.base = a` is vacuous on the copied
representation, where every atom is its own base.

| statement | change | why the meaning is the same |
|---|---|---|
| `CapBound` | one constructor, `cls` | additive, and `star` reads as `cls ⊤` through `CapBound.classifier` |
| `CapBound.opaque` | one clause, `true` | a classified rigid capability stands for itself, which is what `star` already said |
| `CapAtom` | one constructor, `proj` | additive, and a bare atom is `a ↾ ⊤` up to roots by `Ctx.rootsEq_proj_top` |
| `Ctx.lvlAtom` | one clause | a projection is at the level of what it projects, so `Ctx.Confined` means what it meant |
| `Ctx.capsAtom` | one clause, and the measure counts `sizeOf` where it counted list length | the old clauses are textually unchanged and `Ctx.caps_nil` and `Ctx.caps_cons` keep their statements and their `simp` proofs |
| `Ctx.capsBound` | one clause, `[.cvar κ]` | the `star` clause verbatim, for a flavour that is `star` with a classifier |
| `Ctx.expandAtom` | an `if` becomes a `match` with one clause before it | the wildcard branch is the old body, and `Ctx.expandAtom_of_root` keeps its statement and its proof |
| `Ctx.expandAtom_of_not_root` | gains the premise `a.base = a` | a projection is never a root and its expansion is a filter of its base's, so the old form is false at `⊤ᶜ ↾ ∅` |
| `Ctx.expand_eq_self` | gains the premise `∀ a ∈ C, a.base = a` | the same reason, set-wise |
| `Ctx.OpaqueAtom`, `Ctx.caps_opaque` | the disjunction reads `a.base` where it read `a` | `base` is the identity on every atom of the copied representation |
| `Ctx.mem_expandAtom_self` | conclusion `a.base ∈ Γ.expandAtom a` under `Γ.admitsB a.base a.kindOf = true` | on an unprojected atom `base a = a` and the premise is the fact that every kind contains `⊤` |
| `Ctx.subset_expand`, `Ctx.caps_subset_roots`, `Ctx.Root.of_mem_caps` | the same restatement, base and admission | a projected atom of `Γ.caps` that its own kind excludes is not a root, and on a projection-free set the three are the old statements |
| `Ctx.roots_eq_caps_of_rootFree` | the conclusion is the admitted sublist of `Γ.caps n C` mapped by `base`, and the hypothesis reads `CapAtom.top ∉ (Γ.caps n C).map CapAtom.base` | on a projection-free set the filter is all true and `base` is the identity, which is `Ctx.filter_map_base_eq_self` |
| `CapAtom.cons_cases`, `CapAtom.consC_cases` | one more disjunct, `∃ e₀ φ, e = e₀ ↾ φ` | no premise is added, and on the copied representation the new disjunct is uninhabited |
| `lvl_canon`, `lvl_safety`, `rigid_target` | the conclusion moves from `Γ.caps n C` to `Γ.roots n C`, and `lvl_canon`'s hypothesis with it | on a projection-free set `Γ.caps n C ⊆ Γ.roots n C`, so the new conclusion implies the old one, and the two readings of the hypothesis are interderivable by `Ctx.confined_expand`, which is the step the old proof took inline |
| `Rename.InjectiveOnAtoms.comp_succ` | statement kept, the proof becomes an induction | `CapAtom` is recursive now, so `cases a <;> cases b` no longer closes the projection case |
| `Ctx.roots`, `Ctx.Root`, `CapLe`, `RootsEq`, `Ctx.expand`, `Ctx.caps`, `cap_canon`, `atom_canon`, `preservation'`, `progress`, `not_stuck`, `Store.Ext.roots`, `Store.Ext.capLe`, the five `Prediction` theorems | nothing at all | expansion consumes every projection and produces projection-free atoms, so the layers above `expandAtom` never see one |

### New in this stage

The five lemmas that make resolution and expansion work with a filter.

```
FCdot.Ctx.expandAtom_proj     : Γ.expandAtom (a ↾ φ) = (Γ.expandAtom a).filter (Γ.admitsB · φ)
FCdot.Ctx.expandAtom_projBy   : the same at the smart constructor, by the kind intersection
FCdot.Ctx.capsAtom_kindOf     : every atom resolution produces carries a kind below the atom's own
FCdot.Ctx.expandAtom_kinded   : every atom an expansion produces is admitted by the kind it came from
FCdot.Ctx.expandAtom_base     : every atom an expansion produces is its own base
```

The kinding proposition and the four theorems.

```
FCdot.Ctx.KindLe Γ C φ        : ∀ a, Γ.Root a C → φ.Contains (Γ.classOf a)

FCdot.Ctx.roots_proj          : Γ.roots n (CaptureSet.proj C φ)
                                  = (Γ.roots n C).filter (fun b => Γ.admitsB b φ)
FCdot.Ctx.Root_proj           : Γ.Root a (CaptureSet.proj C φ) ↔ (Γ.Root a C ∧ Γ.admitsB a φ = true)
FCdot.Ctx.rootsEq_proj_top    : RootsEq Γ (CaptureSet.proj C Cls.Kind.top) C

FCdot.Ctx.kindLe_of_kinds     : (∀ a ∈ C, ∀ c, a.kindOf.Contains c → φ.Contains c) → Γ.KindLe C φ
FCdot.Ctx.kindLe_proj         : Γ.KindLe (CaptureSet.proj C φ) φ

FCdot.Ctx.KindLe.mono         : CapLe Γ C D → Γ.KindLe D φ → Γ.KindLe C φ
FCdot.Ctx.KindLe.sub          : Γ.KindLe C φ → φ.Subkind ψ → Γ.KindLe C ψ
FCdot.Ctx.KindLe.union        : Γ.KindLe C φ → Γ.KindLe D φ → Γ.KindLe (C ∪ D) φ

FCdot.Store.Ext.kindLe        : Store.Ext σ σ' ρ → ⊢ σ : Γ → ⊢ σ' : Γ' → Γ.KindLe C φ →
                                  Γ'.KindLe (C.rename ρ) φ
```

T1 needs no induction on the context and none on the fuel.  `Ctx.roots` is `Ctx.expand` of
`Ctx.caps`, `Ctx.caps` distributes over `cons`, `Ctx.expand` is a `flatMap` and `CaptureSet.proj` is
a `map`, so both sides are `flatMap`s over `C` and `List.filter` distributes over `++`.  The
statement reduces to one atom, which is `Ctx.expand_capsAtom_projBy`, and its projected case is the
only use of the kind algebra in the whole stage.  T2 is L3 followed by L4, and `Ctx.kindLe_proj`
falls straight out of `Ctx.Root_proj`, which is the point: a projected set is kinded by construction,
and that is what a design filtering before expansion could not have.  T3 is one unfolding each, and
`KindLe.sub` is the only consumer of subkinding in K0.  T4 needs `Store.Ext.roots`, which keeps its
statement, and `Store.Ext.classOf`, which is Fact 1 at the level of a whole extension.

The store and the machine.

```
FCdot.CapBound.cls_opaque              : (CapBound.cls c).opaque = true
FCdot.CapBound.cls_not_appendable      : (CapBound.cls c).opaque ≠ false
FCdot.Store.Typed.consC_cls            : ⊢ σ : Γ → ⊢ σ.consC (.cls c) : Γ.consC (.cls c)
FCdot.CapBound.classifier_of_not_opaque: b.opaque = false → b.classifier = .top
FCdot.Store.Ext.classOf                : Γ'.classOf (a.rename ρ) = Γ.classOf a
```

`Store.Ext.consC` asks for a bound that is not opaque and `cls` is opaque, so no step of the machine
allocates a classified capability: a classified capability sits in the platform prefix.  Store typing
asks only that a bound is not a scope root, so a classified platform store is well typed with no
change to store typing.  And every capability a run does append carries the root classifier `⊤`,
which is the strict reading of the stage at run time: a kind that does not contain `⊤` forbids every
capability the run allocates.

### The examples

Three, and each is read off an equation for `Ctx.caps` proved by `simp` over the clause lemmas and an
expansion decided in the kernel.  `Ctx.caps` is a well-founded recursion, so it is never handed to
`decide`.

```
FCdot.Examples.K1x_roots_ctl  : K1Ctx.roots 0 [(cvar κ_ctl) ↾ only Control] = [cvar κ_ctl]
FCdot.Examples.K1x_roots_io   : K1Ctx.roots 0 [(cvar κ_io) ↾ only Control] = []
FCdot.Examples.K2x_roots      : K2Ctx.roots 0 [⊤ᶜ ↾ except ThreadLocal] = [⊤ᶜ]
FCdot.Examples.K2x_kindLe     : K2Ctx.KindLe [⊤ᶜ ↾ except ThreadLocal] (except ThreadLocal)
FCdot.Examples.K3x_roots      : K3Ctx.roots 0 [(cvar κ_S) ↾ except ThreadLocal] = [⊤ᶜ, cvar κ_S]
FCdot.Examples.K3x_not_capLe  : ¬ CapLe K3Ctx [cvar κ_ctl] [(cvar κ_S) ↾ except ThreadLocal]
```

K1x is the whole of the atom case, over two classified capabilities and no scope root.  K2x is the
shape the adversarial check broke: `Control` lies below `ThreadLocal`, so `except ThreadLocal`
excludes both classified binders while the universal root itself is admitted, and the projected set
is kinded by T2.  The refuted design derived the same kinding and kept the `ThreadLocal` binder among
the roots.  K3x puts a scope root between the two capabilities.  The root opens into `⊤ᶜ` and every
opaque binder at its level or outside it, the filter then keeps only `⊤ᶜ` and the root itself, and
the `Control` capability opened inside the scope is therefore not below the projected root.  That is
the sentence E2 will make about a program.

Axioms (`#print axioms`): `propext` and `Quot.sound`, or less, for every theorem above.

---

## Stage K1

K1 is the second stage of classifiers (`plan-5f-classifiers-stages.md` §K1).  It is the target only.
It adds the capture-kinding proposition `C ⊑ᵏ φ`, the evidence family `KindCo` with its nine rules,
three new subcapturing rules, the kinding slot of the normal forms, the checker for kinding evidence,
and the canonical form T5.

The shape of the stage is one sentence: a kinding judgment is a *checking* judgment, and its
canonical form is `Ctx.KindLe`, whose algebra K0 already proved.  Every rule of the family concludes
about a **general** atom and reads it through `CapAtom.base` and `CapAtom.kindOf`, which is
`Kind.top` at an unprojected atom.  That is what makes the family cover exactly what Capless(K)'s
covers: rules stated at `[a ↾ ψ]` would kind no bare atom at all.  Two of Capless(K)'s four label
rules are one rule here, `kcls`, whose premise is the implication `a.kindOf ∋ c → φ ∋ c`: the
non-vacuous branch is `k-label` and the vacuous branch is `k-label-absurd`.

| module | what K1 changed |
|---|---|
| `Syntax` | the constructor `Proposition.kindC` with the notation `⊑ᵏ`, the evidence type `KindCo` with its nine constructors and its `rename` and `subst` traversals, three constructors of `CapCo` (`unprojC`, `projC`, `projMono`), and the constructor `Morphism.kindC` with its two traversal clauses |
| `RenameLemmas` | one match case per new constructor in the `Proposition`, `CapCo`, `KindCo` and `Morphism` traversal lemmas, every statement unchanged |
| `Context` | `CapBound.clsOf?`, `CapBound.setOf?`, `Ctx.clsOf?`, `Ctx.setOf?`, the two `abbrev` propositions `Ctx.ClsOf` and `Ctx.SetOf`, and the three readings `CapBound.opaque_of_clsOf?`, `isRoot_of_clsOf?`, `classifier_of_clsOf?` |
| `Typing` | `Telescope.HoleAtK`, the judgment `KindCo.HasType` with the notation `Γ ⊢ᵏ g : C ⊑ᵏ φ`, three rules of `CapCo.HasType`, one rule of `Morphism.HasType`, and `KindCo.MemberFree` beside `CapCo.MemberFree` |
| `Resolution` | `Ctx.roots_of_base` and `Ctx.Root_of_base`, `Ctx.Root_of_clsOf`, `Ctx.roots_of_setOf` and `Ctx.Root_of_setOf`, and `Ctx.KindLe.admits` |
| `TypingRename`, `TypingSubst`, `Transparency` | two new fields on `Ctx.Ren` and `Ctx.RenR`, three on `Subst.Typed`, one on `Ctx.Refines`, `Telescope.HoleAtK.rename` and `.subst`, `KindCo.HasType.renameR`, `.rename`, `.subst` and `.refine`, the commutations `CapAtom.kindOf_rename`, `CapAtom.base_subst`, `CaptureSet.proj_rename`, `CaptureSet.proj_subst`, and `Ctx.clsOf_cons_eq` and `Ctx.setOf_cons_eq`, which are the `capCls` and `capSet` fields of every self-cast substitution |
| `Checker`, `CheckerCompleteness` | `KindChecked`, `kindMember`, `checkKindCore`, `checkKindCo`, `checkKindCo_sound`, `KindCo.HasType.complete`, `checkKindCo_iff` and `checkKindCo_iff_hasType`, three cases of `synthCapCore` and one of `synthMorCore` |
| `Normalizer` | the entry `Entry.kindC`, the view slot `PropForm.kindC`, one clause each in `Entry.through`, `Entry.at`, `Telescope.identityEntries` and `entries` |
| `FormTyping` | `EntriesTyped.kindC`, `EntryTyped.kindC`, `ViewTyped.kindC`, `ViewTyped.kindC_entry`, and one case per existing inversion lemma |
| `FormAlgebra` | `Telescope.HoleAtK.open`, `EntriesTyped.At_kindC`, and one case per existing lemma of the composition and application blocks |
| `CanonicalForms` | `kind_canon`, three cases of `cap_canon`, one case of `mor_canon` |
| `Cls/Ops` | `Kind.Admits` with its reflexivity and transitivity, `Kind.Subkind.admits`, and `Kind.admitsStepB` with `Kind.AdmitsStep`, its reflexivity and `AdmitsStep.admits` |
| `LevelInversion` | three cases of `level_inversion` and of `CapCo.MemberFree.rename`, `KindCo.MemberFree.rename`, and four resolution lemmas about a projection up to the base, every statement unchanged |
| `Examples` | the two kinding examples K4x and K5x |
| `Preservation`, `Progress`, `ErasureMetatheory`, `Consistency`, `Prediction` | nothing but the new alternatives of existing case analyses.  The new evidence is inert at run time: it carries no term and erases to nothing |

### Notation

Two tokens are new, both `scoped` in namespace `FCdot`.

| | |
|---|---|
| `C ⊑ᵏ φ` | the kinding proposition: every capability `C` reaches carries a classifier `φ` admits.  `infix:70`, beside `⊑ᶜ` and `≐ᶜ` |
| `Γ ⊢ᵏ g : C ⊑ᵏ φ` | `g` is kinding evidence for `C ⊑ᵏ φ` over `Γ`.  `notation:40`, beside the four judgments of the evidence block |

### The rules

The nine rules of `KindCo.HasType`.  `a` is a general atom throughout: `a.base` is the atom under its
projections and `a.kindOf` is the intersection of the kinds they carry, which is `Kind.top` when
there are none.

```
nil    : Γ ⊢ᵏ .nil : [] ⊑ᵏ φ
cons   : Γ ⊢ᵏ g : [a] ⊑ᵏ φ → Γ ⊢ᵏ h : C ⊑ᵏ φ → Γ ⊢ᵏ .cons g h : (a :: C) ⊑ᵏ φ
kproj  : a.kindOf.Subkind φ → Γ ⊢ᵏ .kproj a : [a] ⊑ᵏ φ
kcls   : Γ.ClsOf a.base c → (a.kindOf.Contains c → φ.Contains c) → Γ ⊢ᵏ .kcls a : [a] ⊑ᵏ φ
kvar   : Γ ⊢ₐ b : S ^ C → a.base = CapAtom.var b.root →
           Γ ⊢ᵏ g : C.proj a.kindOf ⊑ᵏ φ → Γ ⊢ᵏ .kvar b g : [a] ⊑ᵏ φ
kcvar  : Γ.SetOf a.base C → Γ ⊢ᵏ g : C.proj a.kindOf ⊑ᵏ φ → Γ ⊢ᵏ .kcvar a g : [a] ⊑ᵏ φ
kmember: Γ ⊢ₐ b : S ^ D → Γ ⊢ˢ e : S ≤ μ Tel → Telescope.HoleAtK Tel i C φ →
           Γ ⊢ᵏ .kmember b e i : C⟦b.root⟧ ⊑ᵏ φ
kprojS : Γ ⊢ᵏ g : C ⊑ᵏ φ → Γ ⊢ᵏ .kprojS g C ψ : C.proj ψ ⊑ᵏ φ
ksub   : Γ ⊢ᵏ g : C ⊑ᵏ φ₁ → φ₁.Subkind φ₂ → Γ ⊢ᵏ .ksub g φ₁ : C ⊑ᵏ φ₂
```

`kproj` at a bare atom asks `Kind.top.Subkind φ`, that is, that `φ` admit every classifier.  That is
not a weakness, it is the only sound rule: the roots of a bare root atom are `⊤ᶜ` and every opaque
binder at its level or outside it, whose classifiers are arbitrary and grow under store extension.
There is no kind-bounded capture binder in this development, for the reason K1.1 gives: the encoding
`upper [⊤ᶜ ↾ φ]` is empty inside a scope, and a capture member with a kind bound is a proposition.

The three new subcapturing rules of `CapCo.HasType`.

```
unprojC : Γ ⊢ᶜ .unprojC C φ : C.proj φ ⊑ C
projC   : Γ ⊢ᵏ g : C ⊑ᵏ φ → Γ ⊢ᶜ .projC g C φ : C ⊑ C.proj φ
projMono: Γ ⊢ᶜ f : C ⊑ D → Γ ⊢ᶜ .projMono f ψ : C.proj ψ ⊑ D.proj ψ
```

`sc-var` at a projection is `projMono` composed with `capvar` and needs no rule of its own.
Capless(K)'s `s-merge` is not carried: it is needed for completeness of algorithmic subcapturing, and
this development claims none.

And the morphism template for a target kinding proposition.

```
Morphism.HasType.kindC : Γ ⊢ m : src ⇒ Tel → src ∋ (j ↦ C ⊑ᵏ φ₁) →
    SideC.HasType Γ q D C → φ₁.AdmitsStep φ₂ → Γ ⊢ .kindC m q j φ₂ : src ⇒ Tel ▹ D ⊑ᵏ φ₂
```

### Statements restated

Nothing was weakened, and no theorem that consumes one of the four context-map records gained a
hypothesis.  Each row is a statement whose form changed, with the sentence that says why its meaning
is the same.

| statement | change | why the meaning is the same |
|---|---|---|
| `Proposition`, `CapCo`, `Entry`, `PropForm`, `Morphism` | new constructors | additive: every old term is still a term of the type and reads the same |
| `KindCo.HasType.kcls` | the three premises about `Γ.lookupCap` become the one premise `Γ.ClsOf a.base c`, and the rule therefore applies at the `cls` flavour and not at the `star` one | `Γ.ClsOf b c` holds exactly at a capture binder whose bound is `cls c`, and `CapBound.opaque_of_clsOf?`, `isRoot_of_clsOf?` and `classifier_of_clsOf?` recover the three facts.  The `star` binder is covered by `kproj`, which is Capless(K)'s rule for a kind-bounded capture variable.  The `star` flavour cannot be added: `Ctx.Ren.instC`, the instantiation lemma T-B2.1, reads a `star` binder as an instance of an arbitrary set, and K6x of `FCdot/Examples.lean` shows the kinding fact such a rule would derive is true at the source of that map and false at its target, so the kinding family would lose its renaming lemma.  The K1 g6 counterexample checks both halves |
| `KindCo.HasType.kcvar` | the two premises become the one premise `Γ.SetOf a.base C` | `Ctx.setOf?` is `none` at every atom that is not a capture binder, and `CapBound.setOf?` is `some C` exactly at `.upper C` and at `.inst C`, which is the disjunction |
| `CapCo.projC`, `KindCo.kprojS`, `KindCo.ksub` | each evidence term carries the data the checker has to be told: the source set, the source kind | the *rules* are unchanged premise for premise and conclusion for conclusion, so the set of derivable judgments is the same.  Without the annotation `CapCo.HasType.endpoints_unique` is false |
| `Ctx.Ren`, `Ctx.RenR` | two new fields, `capCls` and `capSet` | a strengthening of the record, of the shape the `capInst` field already has.  Every construction the tree builds proves both, in the lines that already prove `capInst` |
| `Subst.Typed` | three new fields, `capCls`, `capSet`, `capProjFree` | the first two as above.  `capProjFree` says a substitution puts a capability, and never a *filtered* capability, at a capture binder, which every substitution the tree builds does |
| `Subst.Typed.singleC` | three new premises, `b.clsOf? = none`, `b.setOf? = none`, `a.base = a` | the same premise the B1 stage's `b.instSet? = none` is, one flavour further.  Each intended instantiation supplies a `star` or `root` binder and a projection-free atom |
| `Ctx.Refines` | one new field, `capBoundEq` | a refinement adds block definitions and field labels to term binders and rewrites no capture binding, which is what the three existing capture fields already say piecewise |
| `Entry.kindC` | carries a `SideC` as well as the index | `EntriesTyped` types an entry between *closed* telescopes over the self binder, where `CapLe Γ` cannot be stated, so the chain lowering the target set to the source set rides on the entry exactly as `Entry.leC`'s two chains do.  The slot still carries no kind, which is what makes it data free |
| `EntriesTyped.kindC`, `EntryTyped.kindC` | the admission step is `Cls.Kind.Admits`, not `Cls.Kind.Subkind` | `Kind.Admits φ ψ` is `∀ c, φ ∋ c → ψ ∋ c`, which `Kind.Subkind.admits` derives from subkinding.  Composing two entries composes two admission steps, and `Kind.Subkind` is not known to be transitive without the converse of the subtraction bridge, which is decision 6 |
| `Morphism.HasType.kindC` | the step is `Cls.Kind.AdmitsStep`, the disjunction of equality and subkinding | the same reason at reflexivity: the identity template on a kinding proposition needs `φ.AdmitsStep φ`, and `Kind.Subkind` is not known to be reflexive either.  The disjunct is decidable, so the checker still decides the rule |
| `cap_canon` | statement kept, three cases added, and it joins a mutual recursion with `kind_canon` | the recursion is on evidence size, as the block already was |
| `level_inversion`, `CapCo.MemberFree.rename`, `CapCo.HasType.renameR`, `.subst`, `.refine`, `Proposition.subst_rename`, `checkTm_iff`, `CapCo.HasType.complete`, `CapCo.HasType.endpoints_unique` | statements unchanged, cases added | additive, one case per new constructor |
| `preservation'`, `progress`, `not_stuck`, `erase_step`, `erase_reflect'`, `closed_le_shapes` | nothing | the new evidence is inert at run time: it carries no term and erases to nothing |

### New in this stage

The proposition, the hole reader and the member-free predicate.

```
FCdot.Proposition.kindC       : CaptureSet s → Cls.Kind → Proposition s        -- C ⊑ᵏ φ
FCdot.Telescope.HoleAtK       : src ∋ (j ↦ C ⊑ᵏ φ) → Telescope.HoleAtK src j C φ
FCdot.KindCo.MemberFree       : kinding evidence that reads no telescope
```

The readers of a capture bound, which is what the rules premise.

```
FCdot.CapBound.clsOf?         : some c at `.cls c`, none elsewhere
FCdot.CapBound.setOf?         : some C at `.upper C` and at `.inst C`, none elsewhere
FCdot.Ctx.ClsOf Γ a c         : Γ.clsOf? a = some c
FCdot.Ctx.SetOf Γ a C         : Γ.setOf? a = some C
```

The resolution facts the canonical form needs, all in `Resolution.lean` beside T1.

```
FCdot.Ctx.roots_of_base       : Γ.roots n [a] = (Γ.roots n [a.base]).filter (Γ.admitsB · a.kindOf)
FCdot.Ctx.Root_of_base        : Γ.Root r [a] ↔ (Γ.Root r [a.base] ∧ Γ.admitsB r a.kindOf = true)
FCdot.Ctx.Root_of_clsOf       : Γ.ClsOf a c → Γ.Root r [a] → r = a ∧ Γ.classOf a = c
FCdot.Ctx.roots_of_setOf      : Γ.SetOf a C → Γ.roots n [a] = Γ.roots n C
FCdot.Ctx.KindLe.admits       : Γ.KindLe C φ → φ.Admits ψ → Γ.KindLe C ψ
```

`Ctx.roots_of_base` is T1 read at one atom and at `CapAtom.base`, and it is the fact that lets every
rule of the family speak about a general atom.

The checker.

```
FCdot.checkKindCo Γ g C φ     : Bool, one structural match, no search
FCdot.checkKindCo_sound       : checkKindCo Γ g C φ = true → Γ ⊢ᵏ g : C ⊑ᵏ φ
FCdot.checkKindCo_iff         : checkKindCo Γ g C φ = true ↔ ∃ _ : Γ ⊢ᵏ g : C ⊑ᵏ φ, True
FCdot.checkKindCo_iff_hasType : checkKindCo Γ g C φ = true ↔ Γ ⊢ᵏ g : C ⊑ᵏ φ
```

Both directions hold, and decision 6's hedge does not bite here: the premises of the kinding *rules*
are `Kind.Subkind` and `Kind.Contains`, which are `abbrev`s over the `Bool` functions `subkindB` and
`containsB`, and the checker calls those very functions.  The subtraction bridge stands between
`Kind.Subkind` and the *semantic* `Ctx.KindLe`, which is T5's business and not the checker's, and
that is where only the sound direction is proved, as `Kind.Subkind.contains`.  Kinding is also the
one evidence family that checks rather than synthesises: there is no `synthKindCo`, because `nil`
holds at every kind and `kvar`'s conclusion leaves the kind the atom carries free.

### New theorems

**T5, the canonical form of closed kinding.**  Every root of a kinded set carries a classifier the
kind admits.  It runs in the `CanonicalForms` mutual block, because `kvar` and `kmember` read
`atom_canon` and `cap_canon`'s `projC` case reads it back.

```
FCdot.kind_canon : ⊢ σ : Γ → Γ ⊢ᵏ g : C ⊑ᵏ φ → Γ.KindLe C φ
```

Case by case: `nil` is vacuous, `cons` is `Ctx.KindLe.union`, `kproj` is `Ctx.kindLe_of_kinds` with
`Kind.Subkind.contains`, `kcls` is `Ctx.Root_of_clsOf`, since a `cls` binder is opaque and is no root
and therefore stands for itself, so the only root of the singleton is the binder, `kvar` is
`atom_canon`'s capture conjunct with `Ctx.Root_of_base` and `Ctx.Root_proj`, `kcvar` is the same
through `Ctx.Root_of_setOf`, `kmember` is `cap_canon`'s `member` case with `ViewTyped.kindC` in place
of `ViewTyped.leC`, `kprojS` is `Ctx.KindLe.mono` along `unprojC`, and `ksub` is `Ctx.KindLe.sub`.

**T6, the three new capture rules are sound.**  `cap_canon` keeps its statement and gains three
cases: `unprojC` is `Ctx.Root_proj` forwards, `projC` is `Ctx.Root_proj` backwards with `kind_canon`,
and `projMono` is `Ctx.Root_proj` on both sides.

```
FCdot.cap_canon   : ⊢ σ : Γ → Γ ⊢ᶜ f : C ⊑ D → CapLe Γ C D            -- statement unchanged
FCdot.atom_canon  : ⊢ σ : Γ → Γ ⊢ₐ a : S → AtomConcl σ Γ a S          -- statement unchanged
FCdot.preservation', FCdot.progress, FCdot.not_stuck                  -- statements unchanged
```

**T7, kinding is decidable evidence.**  `checkKindCo_iff` above.

### The examples

Three: two decided through the checker in the kernel, and one that marks the boundary of the
evidence family.

```
FCdot.Examples.K4x_ctl_accept        : checkKindCo K1Ctx (.kcls K4ctl) [K4ctl] (only Control) = true
FCdot.Examples.K4x_ctl_reject        : checkKindCo K1Ctx (.kcls K4ctl) [K4ctl] (only IO) = false
FCdot.Examples.K4x_io_absurd_control : checkKindCo K1Ctx (.kcls K4io) [K4io] (only Control) = true
FCdot.Examples.K4x_io_absurd_threadLocal : the same evidence at `only ThreadLocal`, also true
FCdot.Examples.K4x_ctl_hasType       : K1Ctx ⊢ᵏ .kcls K4ctl : [K4ctl] ⊑ᵏ only Control

FCdot.Examples.K5x_kind    : checkKindCo K1Ctx K5kind [cvar κ_ctl] (only Control) = true
FCdot.Examples.K5x_projC   : checkCap K1Ctx (.projC K5kind ..) [cvar κ_ctl] K5proj = true
FCdot.Examples.K5x_unprojC : checkCap K1Ctx (.unprojC ..) K5proj [cvar κ_ctl] = true
FCdot.Examples.K5x_roots   : K1Ctx.roots 0 K5proj = K1Ctx.roots 0 [cvar κ_ctl]

FCdot.Examples.K6x_kindLe       : K6Ctx.KindLe [κ_p] (except ThreadLocal)
FCdot.Examples.K6x_not_kindLe   : ¬ K6Ctx.KindLe [κ_p] (only Control)
FCdot.Examples.K6x_kcls_reject  : checkKindCo K6Ctx (.kcls κ_p) [κ_p] (except ThreadLocal) = false
FCdot.Examples.K6x_kproj_reject : checkKindCo K6Ctx (.kproj κ_p) [κ_p] (except ThreadLocal) = false
```

K4x is `kcls` over the context of K1x.  The `Control` capability projected at `only Control` is
kinded at `only Control`, and it is *also* kinded at `only ThreadLocal`, because `Control` lies below
`ThreadLocal`, so the rejecting kind is `only IO`.  The `IO` capability projected at `only Control`
is kinded at every kind, because the projection it carries already excludes its own classifier: that
vacuous branch of the implication is Capless(K)'s `k-label-absurd`, and it is what the write-up's
single rule could not express.  K5x is subcapturing through a projection: `projC` puts the kinded
singleton below its own projection, `unprojC` puts the projection back below the set, and the two
sets therefore have the same roots.

K6x is the rigid binder that declares no classifier.  Its classifier is the root one, so the
canonical form kinds it at `except ThreadLocal`, which contains the root classifier, and not at
`only Control`, which does not: that is decision 9 read on the semantics.  No evidence term reaches
the first fact, and the last two lines decide that in the kernel.  The gap is forced by T-B2.1, as
the row on `KindCo.HasType.kcls` says, so the kinding family is sound and is not complete for the
`star` flavour.

Axioms (`#print axioms`): `propext` and `Quot.sound`, or less, for every theorem above.

## Stage K2

K2 is the third stage of classifiers (`plan-5f-classifiers-stages.md` §K2).  Its subject is the
classified source and the translation, and the target's share of it is small: two additive evidence
rules and the two headline theorems.  Both rules land here rather than in a stage of their own,
which is decision 18, and the report names them as target additions.

The two theorems are the point of the whole development.  `classified_prediction` says that a
program whose use set is kinded at `φ` keeps a use set kinded at `φ` along every run, and
`classified_effect_safety` says that such a program never reads a capability whose classifier lies
outside `φ`.  Neither needs a new induction.  The first is `capture_prediction` with `Ctx.KindLe`
carried to the new context by `Store.Ext.kindLe` and pulled back along the predicted inclusion by
`Ctx.KindLe.mono`, in that order, and the second is the first composed with `inspects_covered`.  The
reason no case analysis on the step is needed is `State.uses`: a `letex` frame contributes its closed
declared set at the outer signature, so a program that unpacks demands exactly what one that does not
demands, and `Store.Ext.consC` accepts only a non-opaque bound, so a run appends no rigid capability
of any flavour at all.

| module | what K2 changed |
|---|---|
| `Syntax` | the constructors `KindCo.kle` and `Morphism.kindCle`, with their `rename` and `subst` clauses |
| `RenameLemmas` | one case per new constructor in the `KindCo` and `Morphism` traversal lemmas, every statement unchanged.  Each is the congruence of its premises with the `Cls.Kind` and `HoleC` arguments carried, which is Fact 1 |
| `Typing` | the rules `KindCo.HasType.kle` and `Morphism.HasType.kindCle`, and `KindCo.MemberFree.kle` beside `ksub` |
| `TypingRename`, `TypingSubst`, `Transparency` | `KindCo.HasType` and `Morphism.HasType` at the two new rules, with `CaptureSet.weaken_rename` and `CaptureSet.weaken_subst` on the post chain |
| `Normalizer` | the entry `Entry.kindCle`, with the clauses of `Entry.through`, `Entry.at` and `entries` |
| `FormTyping` | `EntriesTyped.kindCle` and `EntryTyped.kindCle` |
| `FormAlgebra` | `kindCle_semantic` and one case per existing lemma of the composition and application blocks, including both halves of `EntriesTyped.At_kindC` |
| `Checker`, `CheckerCompleteness` | `checkKindCore` at `kle`, `synthMorCore` at `kindCle`, `CaptureSet.strengthen?` and `strengthenW?` with their soundness and weakening lemmas, and the two completeness cases |
| `CanonicalForms` | `kind_canon`'s `kle` case and `mor_canon`'s `kindCle` case |
| `Consistency` | `EntryTyped.bnd_of_bndsOnly` at the new entry, whose hole names a capture proposition that a bounds-only telescope has none of |
| `LevelInversion` | `KindCo.MemberFree.rename` at `kle` |
| `Prediction` | `classified_prediction` and `classified_effect_safety`, stated beside `capture_prediction` and `effect_safety`, neither of which moves |

### The rules

```
KindCo.HasType.kle      : Γ ⊢ᶜ f : C ⊑ D → Γ ⊢ᵏ g : D ⊑ᵏ φ → Γ ⊢ᵏ .kle f g : C ⊑ᵏ φ

Morphism.HasType.kindCle: Γ ⊢ m : src ⇒ Tel → src.HoleAtC h C₁ C₂ →
    SideC.HasType Γ q D C₁ → SideC.HasType Γ q' C₂ E↑ → Γ ⊢ᵏ g : E ⊑ᵏ φ →
    Γ ⊢ .kindCle m q h q' g φ : src ⇒ Tel ▹ D ⊑ᵏ φ
```

`kle` is subcapturing composed into kinding, whose canonical form is `Ctx.KindLe.mono`.  It makes
`kprojS` derivable through `unprojC`, and `kprojS` is kept all the same, because the checker reads
the source set off the evidence term and `CaptureSet.proj` is not invertible.

`kindCle` is the morphism template that produces a kinding entry from a capture hole of the source
telescope, and it is `Morphism.HasType.leC`'s shape with one closed kinding premise appended.  It is
the repair the K2 refutation forced: the expansion note wrote a rule carrying a `SideC` chain from
the target set to a closed set and no hole, and at `SubShape.capkI` the target set is
`[name .here A]`, a chain out of it must hold that atom in its right end, and the right end is a
weakened closed set whose every term variable is a `.there _`.  So no such chain exists for any
context and any bound, which was machine checked before the rule was written.

### Statements restated

Two rows, and nothing else.  No theorem gains a hypothesis and no conclusion is weakened.

| statement | change | why the meaning is the same |
|---|---|---|
| `KindCo`, `KindCo.HasType`, `Morphism`, `Morphism.HasType`, `Entry`, `EntriesTyped`, `EntryTyped` | one constructor each | additive: every copied constructor and every copied rule is untouched, and `PropForm` gains nothing, because the slot the new entry produces is the data-free `PropForm.kindC` |
| `EntriesTyped.At_kindC` | the conclusion becomes a disjunction, whose left disjunct is the K1 conclusion word for word and whose right one says the entry is a `.kindCle` | forced by the new `EntriesTyped.kindCle` constructor and by nothing else.  An inversion lemma over an inductive that gains a constructor enumerates one more way.  On every derivation the K1 tree can build the right disjunct is uninhabited, so the lemma is the K1 one, and its one caller splits on the disjunction and discharges both halves |
| `Entry.through` | gains a second branch inside the existing `.kindC` clause, beside the new `.kindCle` clause | a `.kindC` template names a kinding proposition of the middle telescope by index, and that proposition may now come from a `.kindCle` entry.  The composite is a `.kindCle` entry whose chain is the concatenation and whose closed kinding is carried through the outer admission step by `Ctx.KindLe.admits`.  Without the branch `Form.combine` is no longer total.  The copied match and the wildcard are untouched, and no copied entry reaches the branch |
| `capture_prediction`, `effect_safety`, `inspects_covered`, `preservation'`, `progress`, `not_stuck`, `erase_step`, `kind_canon`, `cap_canon`, `atom_canon`, `checkKindCo_iff`, `checkTm_iff` | nothing | the new evidence is inert at run time, it carries no term and erases to nothing, and the two new theorems are stated beside the old ones |

### New in this stage

The checker's two set readers, which the plan did not name.  The `post` chain synthesises its target
at `(s,x)` while the kinding premise is checked at a closed set at `s`, so the checker has to undo
one weakening.  Annotating the constructor with the closed set instead would have put a redundant
annotation on every `kindCle` term.

```
FCdot.CaptureSet.strengthen?   : undo one weakening on a set, through `PartialRename.unshift`
FCdot.CaptureSet.strengthenW?  : the same, weakening-aware
FCdot.kindCle_semantic         : the semantic step the new entry's application takes
```

### New theorems

**The two headline theorems of the development.**  Both are stated in `Prediction.lean` beside the
two they refine, and neither of those two moves.

```
FCdot.classified_prediction :
  State.Typed st U → ⊢ st.σ : Γ → Γ.KindLe st.uses φ → st ⟶* st' →
    ∃ ρ, Store.Ext st.σ st'.σ ρ ∧ ∀ Γ', ⊢ st'.σ : Γ' →
      CapLe Γ' st'.uses (st.uses.rename ρ) ∧ Γ'.KindLe st'.uses φ

FCdot.classified_effect_safety :
  State.Typed st U → ⊢ st.σ : Γ → Γ.KindLe st.uses φ → st ⟶* st' →
    st'.inspects = some x → ⊢ st'.σ : Γ' →
      ∀ a, Γ'.Root a [CapAtom.var x] → φ.Contains (Γ'.classOf a)
```

Read aloud, this is Capless(K)'s `Eval.capture_prediction` refined by the classifier, whose
canonical-form half there is `CaptureKind.runtime_labels`.  Where the reference bounds a set of
runtime labels by a projected set, this bounds the classifier of every root by a kind.

Axioms (`#print axioms`): `propext` and `Quot.sound` for both, and for every theorem of the stages
above.
