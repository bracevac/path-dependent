# FCdot, at stage P1 of paths

FCdot is the explicit-evidence coercion target of Plan III.  This directory is stage P1 of
`plan-5g-paths-stages.md`.  The target grows a real notion of path, `x.a.b`, in place of the
base's single-step block name `x ∙ ℓ`, and every judgment that read a binder now reads the block
the table gives a path, following no unjustified elimination on the way.  A field can hold a
value, a path, or a computation.  Only a field whose body is an object literal is stable, and only
a stable field extends the block forest that resolution and field selection both read.

Decisions 23 to 26 of the plan are the shape this stage lands in.  A singleton is introduced at a
path (`PathCo.sngl`) and at an atom (`Atom.sngl`), never by widening a type in place.  A path is
typed at the precise type of a *node* of the forest, read off `Ctx.nodeBlock`, the walk that
follows no forwarding.  The field coercion of a stable field is itself evidence, closed by a
path substitution on the field's typing.  A field is stable when its body is an object literal
under casts that eliminate nowhere outside `pi`, and that restriction is what keeps the
canonical-forms recursion structural in two strata.

## Reading order

| module | contents |
|---|---|
| `Debruijn` | signatures `s`, bound variables `BVar s k`, renamings, copied unchanged |
| `Syntax` | types, propositions, telescopes, `Path` with `root`, `depth`, `rename`, `substVar`, `substPath`, and the parallel `PathSubst`.  `Ty.sel` on a path, the two new propositions `∋ᵛ ℓ` and `≈ q`, the two new sides `bot`/`top`, the three new morphisms.  Evidence (`LeCo`, `EqCo`, `Has`, `Morphism`, `PathCo`, `AliasCo`).  The block forest `Block`/`Children`, `Fields.valLabels` and `Fields.children`.  `Tm.isStable`, `LeCo.tableOnly` and its three companions, `Value.isStableLit` |
| `RenameLemmas` | the functorial laws on every syntactic family, extended to paths, to the block forest, and to the table-only predicates |
| `Context` | bindings (`opaque`/`transparent`, a transparent binder records one `Block`).  `Ctx.blockAt`, `Ctx.blockFuel`, `Ctx.lookupBlock` (the walk, budget `Ctx.fwdCount + 1`), `Ctx.lookupDefP`, `Ctx.nodeBlock` (the walk that follows no forwarding), `Ctx.nodeTy` |
| `Typing` | the judgments `Γ ⊢ e : S ≤ T`, `Γ ⊢ φ : S ≡ T`, `Γ ⊢ h : x ∋ ℓ`, `Γ ⊢ m : src ⇒ Tel`, `Γ ⊢ₐ a : T`, `Γ ⊢ᵖ P : T`, `Γ ⊢ α : p ≋ q`, `Γ ⊢ t : T`, `Γ ⊢ᵥ v : T`, `Γ ⊢ᶠ F`.  `PathCo.HasType.sngl`, `.node`, `Tm.HasType.letPath` |
| `TypingRename` | renaming of typing derivations, `Ctx.Ren` with the `blocks` and `budget` fields folded into `Ctx.blockFuel_budget`'s stability |
| `TypingSubst` | atom substitution of typing derivations, `Subst.Typed` with `lookupB` and `nodeB` |
| `TypingPathSubst` | `PSub`, the substitution that sends every variable to a `PathCo`.  The `psubst` family on the seven evidence judgments, closing a field's coercion at the path it is read from |
| `Transparency` | `Ctx.Refines`, a context refinement.  The two path-typed families gain `refine` cases |
| `Store` | stores, store typing `⊢ σ : Γ` (records `v.blocksAt (.var .here)`), `LeCo.composite`, `Tm.castList`, `Tm.fieldCo`, `Store.litAt`, `Store.fieldCo` |
| `Normalizer` | head normal forms of closed evidence, `Entry`/`PropForm` with `hasVal`/`alias`/`aliasTo`, the view of a path `pathView`/`pathChainForm`, the fuel-indexed normalizer over the path family |
| `Resolution` | `Ctx.resolve`, alias-tolerant resolution through the block forest, the pigeonhole of P1.4 over `Ctx.defPairs`, budget `defPairs.length + 2` |
| `FormTyping` | typedness of forms `FormTyped`, entries, and views `ViewTyped`, each moded on `Option (Path s)`.  `SideTyped` |
| `Machine` | continuations `Cont.Typed`, states, the step relation.  `Cont.Typed.letPath` at the singleton |
| `Checker`, `CheckerCompleteness` | the decision procedure, extended to paths, aliases and the node rule.  `checkTm_iff` and friends unchanged |
| `Preservation` | inversion lemmas, `preservation`, `FormsTyped` with its `sngl` and `noSngl` fields |
| `FieldCo` | the three invariants at nodes, `Store.Typed.blockOf_node`, `Store.Typed.nodeBlock_child`, `Store.Typed.fieldCo`.  The table-only transports (`LeCo.tableOnly_psubst` and its three companions, `Store.Typed.fieldCo_tableOnly`) |
| `FormAlgebra` | composition and application of typed forms over the path family, fuel monotonicity and determinism |
| `Erasure` | erasure into the shared runtime, unchanged, since a deep path is never a running term |
| `ErasureMetatheory` | forward and backward simulation, unchanged in statement |
| `CanonicalForms` | `le_canon_ne` and its three companions (table-only evidence, no store hypothesis), the mutual block for T1 to T5, `Store.Typed.fieldForms`, `fieldFormsHold`, and the base names as one-line corollaries |
| `Consistency` | closed shapes, no closed `⊤ ≤ ⊥`, block names are defined, the base names beside their `_of` twins |
| `Progress` | `progress`, `not_stuck`, the base names beside their `_of` twins |
| `Examples` | E1 to E8 ported to paths, and the path examples Y1 to Y9 |

## Notation

All notation is `scoped` in namespace `Paths.FCdot`.  Beyond the base calculus:

| | |
|---|---|
| `p ∙ ℓ` | a member name at a path.  A `BVar s .var` coerces to `Path s`, so `x ∙ ℓ` still reads `.var x ∙ ℓ` |
| `Γ ⊢ᵖ P : T` | a typed stable path, one of a binder, a step through a stable presence, a cast, an alias, a fold or unfold of the self, an `And-I` pairing, a singleton introduction, or a node of the forest |
| `Γ ⊢ α : p ≋ q` | the two paths name one block of the forest |
| `∋ᵛ ℓ`, `≈ q` | a stable presence and an alias, as telescope propositions |

## Design

* **The paths row.**  `Ty.sel` takes a `Path s`, not a `BVar s .var`.  A path is a variable under a
  sequence of field selections, `Path.root` and `Path.depth` read it apart, and `Path.substPath`
  replaces the whole path a self binder stands for.  Every base type is a type: `.var x ∙ ℓ` is
  `x ∙ ℓ`, and the coercion makes the base's own notation keep parsing.
* **Block.**  A transparent binder no longer carries a bare pair of witnesses and field labels.  It
  carries one `Block`, an object node `obj W ls vls ch` or a forwarding `fwd q`.  `Ctx.lookupBlock`
  walks a path through the table, following a forwarding, at a budget `Ctx.fwdCount + 1` that a
  pigeonhole argument (`Ctx.blockFuel_budget`) shows always suffices, so an alias is a forwarding
  node and not a block of its own (decision 1, decision 9).  `Ctx.nodeBlock` is the same walk with
  the forwarding step turned off.  It answers only at a real object node, which is what a path's
  precise type is read off.  `Ctx.lookupDefP` and `Ctx.lookupBlock_sel` are the two readings a field
  step gives, one for a definition and one for the block one level in.
* **P1.**  The stage keeps every base statement it can state at all.  `LeCo.member`, `EqCo.member`,
  `Has.member` and `EqCo.def` are the base's rules, unchanged, and `memberP`, `defP` are stated
  beside them for a path receiver.  What is additive stays additive: the two propositions, the two
  sides, the three morphisms of P1.2 read nothing a base telescope contains.  What had to change
  changed in the smallest way the argument allows, `Ctx.resolve`'s budget gaining one unit and
  `Ctx.defPairs` enumerating the forest in place of the context spine.
* **Singletons at a path.**  `PathCo.sngl P q α : μ [≈ q↑]` introduces a singleton at the path `P`,
  given `α : P.path ≋ q`.  `Atom.sngl` is its twin at an atom.  A `let` over such a path,
  `Tm.HasType.letPath`, binds the forwarding binder `Binding.fwdAt q = .transparent (Ty.snglOf q)
  (.fwd q.weaken)`, so the frame's incoming type pins the block the substitution lemma needs
  (`substAtom_fwd`).  There is no rule that introduces `≈ q` by widening a type in place.  Every
  occurrence of the proposition is copied from a source by a template morphism or produced by this
  one rule, which is decision 23 and what makes `alias_eq`, T2's strong form, a theorem and not an
  assumption.
* **Nodes and the field coercion.**  `PathCo.node p W ls vls` types a path at the precise type of
  the object node the table wrote at `p`, read off `Ctx.nodeBlock`.  The rule carries the premise
  `p.isSel = true` (decision 24).  A node is a field step, never a binder by itself, because the
  block of a closure's own binder is `obj nil [] [] nil`, whose literal type is not the closure's
  function type, so a `node` rule with no such restriction lets T1 read a coercion that has no
  typing at all.  A binder is typed at its declared type by `PathCo.var` instead, and
  `Store.fieldCo` only ever builds a `node` at a `sel` path.  `Store.Typed.fieldCo` is invariant C
  of P1.8.  At a node whose stable label `a` is listed, the field's coercion `σ.fieldCo p a` exists,
  is typed from the child's precise type to `p ∙ a`, and its source resolves exactly where the
  table's own type at `p ∙ a` resolves.
* **Stable fields.**  A stable body is an object literal under casts that eliminate nowhere outside
  `pi` (`Tm.isStable`, `LeCo.tableOnly` and its three companions, `Value.isStableLit`, decision 26).
  `member` and `memberP` are the only evidence that reads a view, so a table-only coercion has none,
  at any depth of its morphisms and sides, except inside a `pi` coercion, whose two components the
  normalizer keeps raw.  A stable field's own coercion is therefore table-only (invariant
  C′, `Store.Typed.fieldCo_tableOnly`), so it normalizes by `le_canon_ne`, structural on the evidence
  with **no store hypothesis at all**.  `le_canon_ne` and its three companions are proved before the
  canonical-forms recursion that reads the store, and T1's `sel` case calls that block in one line
  rather than recursing on the store itself.  This is what keeps the whole development
  well founded.  The store-reading recursion never calls into a coercion that itself justifies a
  node the recursion has not yet reached, because such a coercion is never table-only.  A later
  stage that wants to normalize the *parts* of a `pi` coercion has to make `LeCo.tableOnly` recur
  into `pi` first (decision 26 (b)), or the same circularity the field-forms round found reopens
  one level up.

## Main theorems

```
le_canon                  : ⊢ σ : Γ → Γ ⊢ e : S ≤ T → ∃ n F, σ ⊢ e ⇓[n] F ∧ Γ ⊨ F : S ≤ T
eq_canon                  : ⊢ σ : Γ → Γ ⊢ φ : S ≡ T → …
has_canon                 : ⊢ σ : Γ → Γ ⊢ h : x ∋ ℓ → …
mor_canon                 : ⊢ σ : Γ → Γ ⊢ m : src ⇒ Tel → …
atom_canon                : ⊢ σ : Γ → Γ ⊢ₐ a : S → …
closedAtomForm_typed      : ⊢ σ : Γ → Γ ⊢ₐ a : S → …
Store.Typed.pathView (T1) : ⊢ σ : Γ → Γ ⊢ᵖ P : T → ∀ Tel, Γ.resolve T = μ Tel →
                              ∃ n V, pathView σ n P = some V ∧ Γ ⊨[P.path, σ] V : Tel
alias_eq (T2)              : ⊢ σ : Γ → Γ ⊢ α : p ≋ q → p = q
EqCo.ofAlias_derivable     : ⊢ σ : Γ → Γ ⊢ α : p ≋ q → ∃ φ, Γ ⊢ φ : (p ∙ ℓ) ≡ (q ∙ ℓ)  -- at every ℓ
le_canon_ne                : Γ ⊢ e : S ≤ T → e.tableOnly = true → LeConcl σ Γ e S T   -- no store
Store.Typed.fieldCo        : ⊢ σ : Γ → Γ.nodeBlock p = some (.obj W ls vls ch) → a ∈ vls →
                              ∃ E S, σ.fieldCo p a = some E ∧ Γ ⊢ E : S ≤ (p ∙ a) ∧ …
Store.Typed.fieldForms, fieldFormsHold : ⊢ σ : Γ → σ.FieldForms Γ  -- discharges every _of theorem
closed_le_shapes           : ⊢ σ : Γ → Γ ⊢ e : S ≤ T → (eight-way disjunction on Γ.resolve)
Store.Typed.no_top_le_bot  : ⊢ σ : Γ → ¬ ∃ e, Γ ⊢ e : ⊤ ≤ ⊥
preservation'               : st.Typed U → st ⟶ st' → ∃ ρ, st'.Typed (U.rename ρ)
progress                   : st.Typed U → st.Final ∨ ∃ s' (st' : State s'), st ⟶ st'
not_stuck                  : st.Typed U → ¬ st.Stuck
erase_step                 : st ⟶ st' → (cast-frame step ∧ ⌊st⌋ = ⌊st'⌋) ∨ Runtime.Step ⌊st⌋ ⌊st'⌋
erase_reflect'              : ⊢ st.σ : Γ → (∃ T, Γ ⊢ st.t : T) → Runtime.Step ⌊st⌋ r →
                              ∃ st', st ⟶* st' ∧ ⌊st'⌋ = r
reachable_consistent        : st.Typed U → st ⟶* st' → ∃ Γ, ⊢ st'.σ : Γ ∧ (no closed ⊤ ≤ ⊥) ∧
                              (block names are defined)
```

Every theorem above is stated at its base name.  `Store.Typed.fieldForms` and `fieldFormsHold`
prove the hypothesis every other theorem here needs, so each is a one-line corollary of its `_of`
twin (`le_canon_of`, `eq_canon_of`, and so on), which stays in the tree beside it.  Axioms
(`#print axioms`): `propext` and `Quot.sound` for all of the above, checked by a metaprogram over
namespace `Paths.FCdot`.  The tree contains no `sorry`, `axiom`, `partial`, `native_decide`, or
Mathlib.

## The P3 pages

Stage P3 (`plan-5g-paths-stages.md` §P3) checks translated terms of the source pages in
`../DotToFCdot/Pages.lean` and `../DotToFCdot/Acceptance.lean`.  No file of this directory changes:
every judgment and theorem above already covers the checked terms, since the P3 pages read the
same `checkTm`, `checkLe` and `checkPath` this directory states and decides.  `Examples.lean`'s Y3
and Y5 stay the hand-written twins of P3's E7p and E1p: each is the same program written directly
at `Paths.FCdot`, ahead of the source page.  The one difference is an index: Y5's hand-written telescope lists
the bound entry before `∋ᵛ lf`, while E1p's page reads its telescope through `Ty.translate`, whose
`vfld` clause lists `∋ᵛ` before the bound.  Both telescopes hold the same three entries, and the
order is a presentation choice `Ty.translate` makes for every `{val a : T}` alike.

## What is not here

`Paths/DotToFCdot/` does not build until P2, since the translation reads this target and the two
are developed in sequence.  No open-evidence normalization, as in the base.  The machine only ever
normalizes closed evidence over the store.

## Statements restated

Every row of P1.9 as amended by decisions 24, 25 and 26, plus the rows the groups' own reports
add along the way.  "Additive" means every base derivation is still a derivation of the same
statement.  The other entries say in one clause why the restated statement carries the base's
meaning.  Base names are used throughout.  A `_of` twin means the same statement plus the
field-forms hypothesis, which `Store.Typed.fieldForms`/`fieldFormsHold` now discharge
unconditionally.

| statement | change | why the meaning is the same |
|---|---|---|
| `Ty.sel` | first argument a `Path` | `x ∙ ℓ` reads `.var x ∙ ℓ` through the `BVar → Path` coercion |
| `Proposition` | `hasVal`, `alias` added | additive, no base telescope contains either |
| `Side` | `bot`, `top` added | additive, both self-independent |
| `Morphism` | `hasVal`, `hasOfVal`, `aliasCopy` added | additive, all three copy by index |
| `Telescope.ofLiteral` | one more list, appended last | with an empty list the function is the base's |
| `Binding.transparent` | carries one `Block` | `Block.obj W labels [] .nil` is the base's pair |
| `Ctx.lookupDef`, `Ctx.lookupFields` | unchanged, `lookupDefP` etc. stated beside them | one-unfolding lemma at a variable path with an object-node binder |
| `Ctx.defPairs` | over `Path s × Label`, enumerates the forest | on a base-shaped context the list is longer by the head names of the witnesses (the P1.9 deviation g4 recorded), and the length feeds only `Ctx.resolveFuel_stable`, so the answer is unaffected |
| `Ctx.resolve` | budget `defPairs.length + 2` | one unit of unused fuel changes no answer |
| `Ctx.next` | `.sel` clause calls `lookupDefP` | at a variable path this is `lookupDef` |
| `Ctx.lookupDefP_defPairs` (`Ctx.lookupDef_defPairs`) | conclusion gains a third disjunct | uninhabited on a forwarding-free forest |
| `Ctx.resolveAt`, `resolveAt?`, `Ty.unfoldAt` | root a `Path` | the atom chain is typed at `.var a.root`, the base's root |
| `LeCo.member`, `EqCo.member`, `Has.member`, `EqCo.def` | unchanged, `memberP`/`defP` beside them | additive |
| `LeCo` | `intoSngl` (landed at g5) removed | g5's constructor, not the base's.  The derivations it admitted at another inhabitant of `S` were unsound (`alias_blocks_false`) |
| `Atom`, `PathCo` | `sngl` added to each, `PathCo` gains `node` | additive, `root`/`path`/`rename`/`subst` pass through as for `foldSelf` |
| `AliasCo`, `AliasCo.HasType` | `fwd` and its rule removed | its premise compared block values, which are not objects (`eq_canon_false_twin`).  Its one use is `AliasCo.member` at a singleton |
| `Subst.Typed` | `blocks` becomes `lookupB`, `nodeB` added | `lookupB` was derived from `blocks`, so every instance is stronger.  `nodeB` holds in every instance |
| `FormsTyped` | `sngl`, `noSngl` added | both discharged in `Store.Typed.formsTyped`.  `preservation` already took the structure |
| `Cont.Typed` | `letPath` beside `let` | additive |
| `alias_blocks`, `EqCo.ofAlias_derivable` | each carries `⊢ σ : Γ`, and `alias_eq` is stated as T2's strong form | plan statements, false without the store typing (`t2_without_store_false`).  `alias_blocks` is `alias_eq` read through `rw` |
| `Store.Typed.pathView` (T1) | universal over the telescopes the type resolves to, `pathChainForm_typed`/`root_node` beside it | its existential form is false at a function type (`t1_pi_false`), and it was false at an alias root and at depth two on the g8 rules |
| `Tm.isStable`, `Tm.childAt` | a field whose body is an atom or a lambda is not stable (decision 24), and a literal under a cast that eliminates outside `pi` is not stable (decision 26) | g3's functions, not the base's.  The base has no stable fields, and an atom body keeps its forwarding child |
| `Fields.valLabels`, `Fields.children` | read the last field at each label (decision 25) | on a literal with distinct labels the lists are g3's.  `Fields.mem_valLabels_iff_children`/`Value.valLabels_children` are restated with no hypothesis on the literal |
| `HasConcl` | normal form read at `.var x` | `hasView` takes a path since g5, and `.var x` is the base's block |
| `ViewTyped.alias_entry`, `.bnd_entry`, `EntriesTyped.At_alias`, `ViewTyped.aliasTo`, `EntryTyped.at_typed`, `entriesAtBnds_typed`, `entriesAt_typed` | alias condition is the identity `p = q`, and `Γ.nodeTy r` replaces `Γ.lookupTy r.root` | decision 24.  At a variable root the two agree by `rfl` |
| `pathView`, `pathChainForm` | `sel` clauses read the field's coercion through `Store.fieldCo`, a `node` clause each, and the `.thru` clause of `pathEntryAt` reads the node through `C.combine H` | g5's definitions, not the base's.  The routed-entry fix (g9b) is what makes T1 true through a pairing |
| `Ctx.nodeBlock`, `Ctx.nodeTy`, `Store.litAt`, `Store.fieldCo`, `PSub`, `PSub.Typed`, `FormTyped.congr_src` | new | additive |
| `Store.Typed.cons` | records `v.blocksAt (.var .here)` | on a value with no stable field this is the base's pair |
| `Value.HasType.obj` | telescope `ofLiteral W F.labels F.valLabels` | the base's telescope is a prefix, so no derivation is lost |
| `Tm.HasType.let` | unchanged, `letPath` beside it | additive.  `let` at a singleton is `letPath`'s opaque twin |
| `Entry`, `PropForm`, `EntriesTyped`, `EntryTyped`, `BndsTyped`, `ViewTyped`, `identityEntries` | new constructors per new proposition sort, plus `aliasTo` | additive, no base normal form mentions them |
| `le_canon`, `eq_canon`, `has_canon`, `mor_canon`, `atom_canon` | cases added, `Store.Typed.pathView`/`pathChainForm_typed`/`root_node`/`alias_eq` join the block, and the recursion is table-only evidence (`le_canon_ne`) below the store-reading block | decision 26.  Two strata, and `le_canon_ne` never calls the block that calls it |
| `closed_le_shapes`, `no_top_le_bot`, `preservation'`, `progress`, `not_stuck`, `erase_step`, `erase_reflect'` | unchanged in statement | each consumes canonical forms abstractly |
| `PathCo.HasType.node` | premise `p.isSel = true` | decision 24, confirmed by decision 26.  The derivations removed are nodes at variables, which made T1 false at a closure's binder |
| `pathNode`, `pathNode_eq` | decide `p.isSel` first | the checker follows the rule |
| `FormTyped.noAlias` | source resolves to no `⊥` and to no telescope with an alias or a bound entry | "alias-free" alone is not enough, since the bound case passes through a bound's type |
| `LeCo.tableOnly`, `EqCo.tableOnly`, `Side.tableOnly`, `Morphism.tableOnly`, `Value.isStableLit`, `le_canon_ne` and its three companions, `Store.Typed.fieldCo_tableOnly`, `Store.Typed.fieldForms`, `fieldFormsHold` | new (decision 26) | additive |
| `Tm.childAt_of_castList`, `Ctx.nodeBlock_sel_child` | premise `v.isObjLit = true` becomes `t.isStable = true` | a literal under an eliminating cast has no child.  Every caller now holds `t.isStable` |
| `Store.FieldForms`, `FieldFormsHold`, every `_of` statement of the field-forms round | kept, both propositions proved, base name stated beside each twin | the base names carry the base statements, with no hypothesis beyond `⊢ σ : Γ` or `State.Typed` |
| `Ty.rename_id`, `Ty.rename_comp`, `Ty.rename_inj` | statement kept, the `.sel` case an induction on the path | the leaf case is now an induction step, by `Path.rename_id`/`rename_comp`/`rename_inj` |
| `Side.HasType.bot`, `.top` | each constructor carries the endpoint it leaves free | the annotation is read off the derivation, no derivation is added.  The checker needs it to synthesise the free endpoint |
| `Has.HasType` | subject a `Path`, not a `BVar` | a binder is the path of depth zero |
| a block name written `x ∙ ℓ` | reads `.sel (.var x) ℓ` throughout `Examples.lean` | row `Ty.sel`, applied at the file that writes source terms |
| `Telescope.ofLiteral W ls` (in `Examples.lean`) | becomes `Telescope.ofLiteral W ls []` | the third list is empty wherever the example's field has no stable body |

## Axioms

The stage report (`p1-report.md`) quotes the full list this README's theorems and the twenty-five
modules produce.  Every theorem printed by the metaprogram over namespace `Paths.FCdot` is inside
`[propext, Quot.sound]`.
