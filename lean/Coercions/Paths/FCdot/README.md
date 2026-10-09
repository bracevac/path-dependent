# FCdot with paths

The coercion target, extended so that a type selection can name a block at any path. In the base a
selection names the block of a binder, `x ∙ ℓ`. Here it names `p ∙ ℓ` for a path `p = x.a.b`. The
binder of an object literal carries a forest of blocks: one node for the literal, a child node for
each stable field, and a forwarding node for a field that holds a variable. Two new kinds of
evidence use the forest: path evidence `Γ ⊢ᵖ P : T` and alias evidence `Γ ⊢ α : p ≋ q`.

## Modules

| module | contents |
|---|---|
| `Debruijn` | signatures, bound variables, renamings, unchanged |
| `Syntax` | `Path`, path substitution `PathSubst`, `Ty.sel` at a path, the propositions `∋ᵛ ℓ` and `≈ q`, path and alias evidence `PathCo`, `AliasCo`, the forest `Block`, the stability tests `Tm.isStable`, `LeCo.tableOnly` |
| `RenameLemmas` | renaming laws on every syntactic family, extended to paths and blocks |
| `Context` | binders carrying a `Block`. The walks `Ctx.lookupBlock` (follows forwarding) and `Ctx.nodeBlock` (does not), `Ctx.lookupDefP`, `Ctx.nodeTy` |
| `Typing` | the judgments of the base plus `Γ ⊢ᵖ P : T` and `Γ ⊢ α : p ≋ q`, and `Tm.HasType.letPath` |
| `TypingRename` | renaming of typing derivations |
| `TypingSubst` | substitution of atoms in typing derivations |
| `TypingPathSubst` | `PSub`, substitution of variables by path evidence, and its typing. It closes a field's coercion at the path it is read from |
| `Transparency` | `Ctx.Refines`: typing is monotone in block definitions |
| `Store` | stores, store typing `⊢ σ : Γ`, the field coercion `Store.fieldCo` and the literal lookup `Store.litAt` |
| `Normalizer` | head normal forms of closed evidence, views of atoms and of paths (`pathView`, `pathChainForm`) |
| `Resolution` | `Ctx.resolve`: alias-tolerant resolution through the forest, with a fixed fuel `defPairs.length + 2` |
| `FormTyping` | typedness of forms and views (`FormTyped`, `ViewTyped`, `ChainTyped`), at a root path |
| `Machine` | continuations, states, the step relation |
| `Checker`, `CheckerCompleteness` | the decision procedure, extended to paths and aliases, `checkTm_iff` |
| `Preservation` | inversion lemmas, `preservation` |
| `FieldCo` | the store invariants at nodes and the typing of a stable field's coercion (`Store.Typed.fieldCo`) |
| `FormAlgebra` | composition and application of typed forms, fuel monotonicity |
| `Erasure` | erasure into the shared runtime, unchanged |
| `ErasureMetatheory` | forward and backward simulation, `erase_step`, `erase_reflect` |
| `CanonicalForms` | canonical forms for evidence, atoms and paths, `preservation'`, `erase_reflect'` |
| `Consistency` | shapes of closed inclusions, no closed `⊤ ≤ ⊥`, `Store.Typed.realized` (a block name of a store binder reads its literal's witness, `⊤` when the literal declares none) |
| `Progress` | `progress`, `not_stuck` |
| `Examples` | E1 to E8 ported to paths, and the path examples Y1 to Y9 |

## New notation

| | |
|---|---|
| `p ∙ ℓ` | the member `ℓ` of the block at path `p`. `x ∙ ℓ` still parses for a variable |
| `∋ᵛ ℓ` | stable presence: field `ℓ` holds an object, so `self.ℓ` is a path |
| `≈ q` | alias: the object is the one at path `q`. `μ [≈ q]` is the singleton `q.type` |
| `Γ ⊢ᵖ P : T` | path evidence `P` types the path `P.path` at `T` |
| `Γ ⊢ α : p ≋ q` | alias evidence: `p` and `q` name one block |

## How paths are typed

A path extends by one field only through a stable presence `∋ᵛ a` (`PathCo.HasType.sel`). A field
that holds a computation gives `∋ a` and no step, so a name below it stays abstract in the
literal's own type. A binder assumed at the singleton of that path, with a stable presence of its
own, can still type the path (`PathCo.HasType.alias`).
A singleton is introduced at a path or an atom (`PathCo.sngl`, `Atom.sngl`), never by widening a type. So over a
store, alias evidence relates a path only to itself (`alias_eq`).

A field is stable when its body is an object literal under casts that use no `member` evidence
outside a function coercion (`Tm.isStable`, `LeCo.tableOnly`). Such a coercion normalizes without
the store (`le_canon_ne`), which keeps canonical forms over the store well-founded. Example Y9
shows why: a field cast through its own declared type would make `⊤ ≤ ⊥` derivable over the
store. The checker rejects it.

## Main theorems

- `le_canon`, `has_canon`, `mor_canon`, `atom_canon`: over a typed store, typed normal forms of
  closed evidence.
- `eq_canon`: over a typed store, closed equality evidence relates two types with one resolution.
- `Store.Typed.pathView`: over a typed store, typed path evidence has a view of its object. The view
  is typed at every object type that the path's type resolves to.
- `alias_eq`: over a typed store, `Γ ⊢ α : p ≋ q` implies `p = q`.
- `le_canon_ne`: table-only evidence normalizes with no hypothesis on the store.
- `Store.Typed.fieldCo`: over a typed store, a stable field of a node has a typed coercion into `p ∙ a`.
- `Store.Typed.no_top_le_bot`, `closed_le_shapes`: over a typed store there is no closed
  `⊤ ≤ ⊥`, and closed inclusions relate compatible shapes.
- `checkTm_iff`: the checker accepts a term exactly when it is typed.
- `preservation'`, `progress`, `not_stuck`: type safety of the machine, for typed states.
- `erase_step`, `erase_reflect'`: a machine step erases to a runtime step or to a cast shuffle. Over
  a typed store and a typed term, a runtime step is realized by a run of the machine.
- `reachable_consistent`: from a typed state, along a run, the store stays typed and has no closed
  `⊤ ≤ ⊥`. Its third conjunct, that every block name is defined, holds in every typed store, because
  a label the literal does not declare reads `⊤`.

`EqCo.ofAlias_derivable` states that over a typed store, when `α` proves `p ≋ q`, some `φ` proves
`p ∙ ℓ ≡ q ∙ ℓ` at every label `ℓ`. It is a corollary of `alias_eq` and holds trivially. Over a
typed store aliased paths are equal, so `EqCo.refl` closes it.

The canonical-form twins (`le_canon_of`, `eq_canon_of`, `alias_eq_of`, `closed_le_shapes_of`) assume
`σ.FieldForms Γ`. The machine twins (`preservation'_of`, `progress_of`, `not_stuck_of`,
`reachable_consistent_of`) assume `FieldFormsHold`. `Store.Typed.fieldForms` and `fieldFormsHold`
prove them for every typed store.

## Base statements whose form changed

- `Ty.sel` and `Has.HasType` take a `Path`. A `BVar` is a path of depth zero, so `x ∙ ℓ` keeps its meaning.
- `Binding.transparent` carries one `Block`. The base's witnesses and labels form a childless node.
- `Telescope.ofLiteral` takes a third list, the stable labels. With `[]` it is the base's.
- `Ctx.resolve` runs at fuel `defPairs.length + 2`, one unit more than the base. No answer changes.
- `LeCo.member`, `EqCo.member`, `Has.member`, `EqCo.def` stay. `memberP`, `defP` take a path.

## Examples

E1 to E8 keep their names and statements. Y1 to Y9 exercise the forest: multi-hop block names,
forwarding, alias cycles, elimination at a path under a lambda, the fuel budget, the field
coercion at `x.a.b`, and the store Y9 rejects. The kernel decides checker verdicts.
