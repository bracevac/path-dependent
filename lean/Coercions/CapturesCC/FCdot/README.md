# FCdot, at stage A3b of captures (CapturesCC copy, unchanged)

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
| `Typing` | the judgments `Γ ⊢ e : S ≤ T`, `Γ ⊢ φ : S ≡ T`, `Γ ⊢ h : x ∋ ℓ`, `Γ ⊢ m : src ⇒ Tel`, `Γ ⊢ₐ a : T`, `Γ ⊢ t : T`, `Γ ⊢ᵥ v : T`, `Γ ⊢ᶠ[A] F` |
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
| `CanonicalForms` | the canonical-forms theorem, including item 6 (`cap_canon`) and item 7 (an atom's root is below the capture set of its type); the chain of casts; `closed_box_inversion`; `preservation'`, `erase_reflect'` |
| `Progress` | `progress`, `not_stuck` |
| `Consistency` | shapes of closed inclusions; no closed `⊤ ≤ ⊥`; block names are defined; stores stay typed along runs (`reachable_consistent`) |
| `Prediction` | the use-set half of preservation (`step_uses`), `capture_prediction` along a run, `inspects_covered`, `effect_safety`, `returned_capture_bound` |
| `Examples` | the examples E1 to E8 and the capture examples C3, C4, C1, C6, decided in the kernel; the target side of the A3a source examples S3, C2, C7; and the target side of the A3b ones, `S1_client` (an operation declared at `{fs}` recaptured at `{cp.C}` by the lower bound of a capture member), `S1_translated`, `S1_erase`, `S2_translated`, `S2_erase`, and C5, the packing of an existential result: `C5_capWitnesses`, `C5_witnesses` and `C5_litMorphism` read off the translation, `C5_literal` and `C5_packing` decided by `checkValue` and `checkLe`, and `C5_client`, the caller that reaches `{fs}` only through the member's upper bound |

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
