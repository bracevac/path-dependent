# FCdot, capture checking the compiler's way

The target calculus.  It is the vanilla FCdot (`../../FCdot/`) with capture sets in types and the
scoping discipline of the Scala 3 compiler.  A type is a shape with a capture set, `S ^ C`.  Capture
sets have their own inclusion and equality evidence, and a telescope may hold capture members and
capture propositions.  A lambda body and an object body open a scope root, a level is the innermost
root enclosing a binder, and the evidence rule `level` lets a root absorb a capability only if the
capability's level is that root or encloses it.  An arrow binds its parameter's `any` as a capture
binder, and an answer may be an existential `∃ᶜ[C₀] T`, which is how a `fresh` result is typed.

## Reading order

| module | contents |
|---|---|
| `Debruijn` | signatures with term and capture binders (`s,x`, `s,c`), bound variables, renamings |
| `Syntax` | capture atoms with the universal root `⊤ᶜ`, capture sets, shapes, types `S ^ C`, the answer sort `ETy`, evidence (`ShapeCo`, `CapCo`, `CapEq`, `LeCo`, `ELeCo`), atoms, packed atoms `PAtom`, terms with `letex`, values, substitutions |
| `Context` | bindings, capture bounds (`root`, `star`, `upper`, `inst`), lookup, levels (`Ctx.lvl`, `Ctx.lvlLeB`), the scope contexts `Ctx.scope`, `Ctx.body`, `Ctx.objBody`, `Ctx.scopeInst` |
| `Levels` | order lemmas for levels, and their stability when a binder is appended |
| `Typing` | all judgments, including the `level` and `instC` rules, and the member-free predicates `CapCo.MemberFree` and `Atom.MemberFree` |
| `RenameLemmas` | renaming and substitution laws for syntax, use sets and inspected roots |
| `TypingRename` | renaming of typing derivations along `Ctx.Ren` and `Ctx.RenR` |
| `Transparency` | refining an opaque binder to a transparent one (`Ctx.Refines`) |
| `TypingSubst` | typed substitutions (`Subst.Typed`), including `Subst.Typed.enter` for entering a body |
| `Store` | stores, store typing `⊢ σ : Γ`, `Store.Typed.rootFree` (a store binds no scope root) |
| `Normalizer` | head forms of closed evidence, views of atoms, the fuel-indexed normalizer |
| `Resolution` | `Ctx.resolve`, capture resolution `Ctx.caps`, root expansion `Ctx.expand`, `Ctx.roots`, `CapLe` |
| `LevelInversion` | `level_inversion`: member-free capture evidence never lowers a level |
| `Checker` | a structural checker for every judgment |
| `CheckerCompleteness` | soundness and completeness of the checker (`checkTm_iff` and friends) |
| `Machine` | continuations, states, steps, use sets of states, `Value.applyE` and `PAtom.applyE` for answer casts |
| `Erasure` | erasure into the shared runtime |
| `Preservation` | inversion lemmas, `preservation`, the existential lemmas `no_ex_le_ty` and `pack_canon` |
| `FormTyping` | typedness of forms, entries and views |
| `FormAlgebra` | composition and application of typed forms |
| `CanonicalForms` | `cap_canon`, `atom_canon`, `closed_box_inversion`, `preservation'` |
| `ErasureMetatheory` | forward simulation `erase_step`, backward simulation `erase_reflect'` |
| `Progress` | `progress`, `not_stuck` |
| `Consistency` | shapes of closed inclusions, `lvl_canon`, `lvl_safety` and `no_inner_escape` (trivial over a store), `reachable_consistent` |
| `Prediction` | `step_uses`, `capture_prediction`, `inspects_covered`, `effect_safety`, `returned_capture_bound` |
| `Examples` | the examples below, decided in the kernel where they are decidable |

## New notation

All notation is `scoped` in namespace `FCdot`.  Lean identifiers cannot contain `ᶜ`, so names
spell it `C` (`Ctx.consC`, `Proposition.leC`), while notation keeps it.

| | |
|---|---|
| `S ^ C`, `□ T` | a shape with a capture set, the box shape |
| `⊤ᶜ` | the universal root, the outermost scope of a program |
| `C ⊑ᶜ D`, `C ≐ᶜ D` | capture propositions in a telescope |
| `Γ ⊢ˢ e : S ≤ T` | inclusion between shapes (the vanilla judgment) |
| `Γ ⊢ᶜ f : C ⊑ D`, `Γ ⊢ᶜ φ : C ≡ D` | inclusion and equality evidence between capture sets |
| `∃ᶜ[C₀] T` | an existential answer, a capture binder bounded by `C₀` |
| `Γ ⊢ᵉ g : E ≤ E'` | inclusion between answers |
| `Γ ⊢ₚ p : E`, `Γ ⊢ᵥᵉ v : E`, `Γ ⊢ t :ᵉ E` | a packed atom, a value and a term at an answer |
| `Γ ⊢ᶠ[A] F` | fields of a literal with assigned capture set `A` |
| `σ ⊢ e ⇓ˢ[n] F` | head form of a shape coercion |

## How scopes work

A body opens three binders in this order: the body root, then the arrow's capture binder, then the
parameter.  So the parameter and the arrow binder sit at the level of the body root.  This order
matters.  With the parameter bound before the root, the level rule puts the parameter below `⊤ᶜ`
(`X5_fires`).  For the actual order `X4_no_level` shows that step underivable.
The machine enters a body by one substitution (`Subst.enter`), which sends the body root to `⊤ᶜ`.
That is sound because a running program is the outermost scope and a store binds no root.

`Ctx.roots` resolves a capture set and then expands each root into the capabilities at or outside
its level.  On a context with no root, and for a set whose resolution does not mention `⊤ᶜ`, it
agrees with plain resolution (`Ctx.roots_eq_caps_of_rootFree`).  So the prediction theorems mean
what they meant in the base for use sets that do not mention `⊤ᶜ`.

A `fresh` result is packed: `ELeCo.pack` widens a plain answer to `∃ᶜ[C₀] T` with a witness set
below the bound.  `letex` unpacks it and opens a rigid capture binder, so two unpackings open two
unrelated binders.  The bound lets the body charge its use of the unpacked value to an ordinary
capture set of the caller.  A pack erases to what it wraps.

## Main theorems

- `checkTm_iff`, `checkTmE_iff`, `checkELe_iff`: the checker decides typing.
- `cap_canon`: over a typed store, capture evidence implies inclusion of resolved roots.
- `atom_canon`: over a typed store, a typed atom has a typed view, and its root is below its
  type's capture set.
- `preservation'`, `progress`, `not_stuck`: type safety.
- `erase_step`, `erase_reflect'`: the machine and the runtime simulate each other.
- `level_inversion`: for member-free capture evidence, if the resolution of the upper set is
  confined to `r` at every depth, so is the resolution of the lower set.  No store is needed.
- `no_ex_le_ty`: no evidence includes an existential answer in a plain type.
- `pack_canon`: an atom at an existential answer is a pack, read with no normalization.
- `capture_prediction`: from a typed state, the roots of the use set only shrink along a run.
- `effect_safety`: from a typed state and a typed store, a capability that is not a root of the
  use set is not the root of the variable a later state reads, up to the renaming of the store
  extension.
- `reachable_consistent`: every store reachable from a typed state is typed and consistent.

Member-free evidence uses neither `member` nor `eqToLe`, the two rules that read a capture bound.
Bad capture bounds can be assumed under a lambda (example C3), so only member-free evidence can be
inverted without a store.

`lvl_canon`, `lvl_safety` and `no_inner_escape` carry no content over a typed store, and are not
listed as results.  A store context has no root other than `⊤ᶜ`.  So the conclusions of
`lvl_canon` and `lvl_safety` hold for every capture set, and the hypotheses of `no_inner_escape`
cannot hold together.  `level_inversion` carries the content.

Statements of the base that changed form:

- `erase_reflect'` also takes the continuation that accepts the focus, because a pack erases to
  what it wraps and only the continuation tells a packed atom from a plain one.
- `Store.Typed.consC` asks that the new binder is not a root: a store binds capabilities, never scopes.
- `Tm.erase_subst` reads `t.erase.map σ.rootVar`, because a substitution may send a capture binder
  to a term variable.

## Examples

- `X4_no_escape`: no member-free evidence puts the `withFile` callback's parameter below the
  universal root.  `X4_no_level` shows the level premise fails.  Neither states that a program is
  ill typed.
- `X5_fires`: with the other binder order, one `level` derivation puts the parameter below `⊤ᶜ`.
  It is the step that `X4_no_level` shows underivable for the actual order.
- `X1_inner_absorbs_outer`, `X2_outer_not_inner`: `level` derivations that go outward, and failed
  premises of `level` for the inward direction.  They do not rule out other evidence.
- `two_calls_incomparable`: for `freshCell` called twice at a caller with no scope root, no
  evidence puts the first binder below the second or the first cell below the second.
  `Y1_freshCell` and `Y1Store_typed` give the typed value and a typed store.  The reverse
  direction is not stated.
- `Y2_makeLogger`: a `fresh` result packed at the parameter itself.
- `Y4_isolation`: `no_ex_le_ty` stated at the callback context `X4Ctx`.  `Y4_no_escape`: the
  statement of `X4_no_escape` again.  Neither mentions a `fresh` result or a `letex`.
- `W2_translated`, `W2_erase`: the translation of the `W2` term is typed at the translated type
  and erases to the source term.  The translated type is one arrow (`Shape.translate_all`).
- `W5_no_escape`: no member-free source subcapturing puts the callback's parameter below the
  platform capability, as an instance of `source_lvl_safety` over the body context of `W2`.
- `C1_typed`: a closure over a console capability is typed.  `C6_safe`: `effect_safety` for the
  second C6 program, given a run to a state that reads `x` and a typed final store.
