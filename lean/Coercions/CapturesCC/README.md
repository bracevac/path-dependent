# CapturesCC

Captures, the compiler's way: the second capture project of plan V (`plan-5-extensions.md` §3,
`plan-5b-captures-cc-note.md`, with the stages of `plan-5d-captures-cc-stages.md`), namespace
`CapturesCC`.  The tree started as a verbatim copy of `lean/Coercions/Captures/` at the commit in
`BASE`, the end of captures the DOT way, and grows the compiler's scope roots, levels, the capture
binder on the arrow, and `fresh` as a per-call existential.  Every statement of the DOT way is kept,
restated where the representation changed, never weakened.

Stage B0 added the universal root as a capture atom, written `⊤ᶜ`: the local root of the whole
program, the compiler's `caps.any` as a constant rather than as a binder.  It added levels, and a
level is a position on the spine and not a field on a binding.  The level of a binder is the
innermost root binder of the prefix that precedes it, a root is its own level, and a binder with no
enclosing root is at the outermost level, which is `⊤ᶜ`.  The order `Ctx.lvlLeB e r` says that the
level of `e` is `r` or encloses it, so an inner root absorbs an outer capability and never the
reverse.  One evidence rule reads that order, `Γ ⊢ᶜ level e r : {e} ⊑ {r}`, which is the compiler's
`acceptsLevelOf`.  For it to be sound `Ctx.roots` became resolution followed by expansion, where
expansion opens a root into the universal root and every opaque binder at its level or outside it.
`Ctx.roots` kept its name, its signature and its fuel argument, and on a root-free context whose
resolution mentions no `⊤ᶜ` expansion is the identity, so every roots-statement of the DOT way means
on a store context and on the platform prefix exactly what it meant before.

Stage B1 is complete, and it is what makes the level rule of B0 usable.  The arrow binds the
parameter's `any` as one capture binder for the whole domain, and a lambda body and an object body
are scopes.  A body opens three binders in this order: the body root, then the arrow's capture
binder, then the parameter.  So the parameter and the arrow binder are at one level and that level
is the body root, which is the compiler's sentence that parameter `any`s sit at the level of the
function's own local `any`.  The order is load bearing in both directions.  With the parameter bound
before the body root the level of the parameter would be the caller's root and the `withFile` escape
would type, and the counterfactual is written down and decided.  With the arrow binder bound before
the body root, `level κ κ_outer` would fire and a call from a deeper scope would make the conclusion
false.  Every capture binder that a rule of the type sort opens sits under a root of its own, which
is the scope discipline, and it is what makes the one crossing of a fresh root true.

The machine enters a body by one substitution.  A substitution is therefore no longer kind
preserving: its capture component returns an atom, because a call instantiates the arrow's capture
binder at the argument's root, a term variable.  The body root is instantiated at `⊤ᶜ`, and that is
a departure from the compiler, recorded as one.  The compiler checks a method body once against its
own level owner and never retargets that level at a call.  The move is sound here for a reason the
compiler does not need: a running program is the outermost scope, a store binds capabilities and
never scopes, so a store context has no root binder, and over such a context every atom in scope is
at the outermost level.  The image evidence is then not only typed but true.  The alternative,
keeping the body root as a binder, would mean putting a scope into the store, and instantiating it
at the lambda's assigned set would be unsound.

The runtime mirrors the two new binders as data-free slots, which is the discipline it already
stated for stores.  A runtime lambda and a runtime object take bodies over the same signatures the
target uses, so erasure still maps binder to binder and every erasure statement keeps its form.  One
generalisation is forced by the widened substitution: erasure of a substitution can no longer be a
renaming of the runtime term, so the runtime gained a map of term variables and a traversal for it,
and `(t.subst σ).erase = t.erase.map σ.rootVar` is the restated equation.

What the stage proves about escapes is `level_inversion`, and it is store free: member-free capture
evidence never lowers a level.  Over a typed store the older `lvl_safety` and `no_inner_escape` hold
vacuously, because a store context is root free and its only root is `⊤ᶜ`, so their content lives in
rooted contexts and no store types one.  Bad capture bounds enter capture evidence only through
`member` and `eqToLe`, which example C3 exhibits under a lambda, so naming member-free evidence is
exactly what makes an induction on the evidence alone true.  The `withFile` escape is then rejected
twice over on the real binder order of a lambda: the premise of the level rule is decided false at
the root outside the call, and no member-free evidence at all puts the file below that root, because
the file's binder set resolves to the arrow binder whose level is the body root.

**`FCdot/`** is the target, FCdot^cc.  Its README lists the modules, what each stage changed in them,
the notation, and the theorems.  B0 reached it everywhere and B1 reached it again.  `Syntax` carries
the arrow's new binders and the whole substitution block, `Context` the levels and the three scope
contexts, `Levels` the order lemmas, `Resolution` the expansion and the lemma that resolution never
lowers a level, `Typing` the four reshaped rules and the two member-free predicates, the new module
`LevelInversion` the theorem that carries the content of scope safety, `TypingSubst` the entering
substitutions and the one crossing of a fresh root, `Machine` the four steps that enter a body,
`Preservation` the inversion lemmas restated at the new binders with `preservation` unchanged, and
`Examples` every old example re-indexed beside the new ones: the C2 literal with the class root
outside the self, the escape rejected, the counterfactual order, and the two acceptance tests that
put a concrete assigned set below a scope root.

**`DotMNF/`** is the source, `DOT-MNF^cc`, with `any` by position since A3b.  A shape is the vanilla
type former, a type is a shape with a capture set, and the new shapes are the capture member and the
box.  `any` is read before typing by the function `expand`, whose reading is by position and needs no
level, and an expanded program is a program of stage A3a.  B0 changed nothing here.  B1 moved the
source arrow in step with the target's, because the two calculi have to bind the same binders in the
same places: the source gains a scope root constructor beside its rigid capture binder, its own three
scope contexts, and its own substitution with an atom-valued capture component, which writes `any`
where the target writes `⊤ᶜ`.  Every derivation of the example file keeps its name and its
conclusion.

**`DotToFCdot/`** is the translation.  A source type is a shape with a capture set and so is a target
type, so the translation splits the same way, and use sets are carried by the derivation, so the
translation of a derivation carries the evidence for them.  The source's safety, consistency and
capture prediction are all borrowed from the target through it.  B0 changed one lemma here, the
platform premise that a capture set does not mention `⊤ᶜ`, which every translated set satisfies by
computation.  B1 changed almost nothing, which was the point of moving the source arrow: the
translation of an arrow is textually what it was, the translation at a lambda and at an application
did not have to be rewritten, and `Ctx.translate` gained one clause for the source's scope root.  The
one new file says that the type translation commutes with substitution and not only with renaming,
which is what the application case now needs.

**`Runtime.lean`** is the shared untyped runtime with a data-free capture slot in its store, an
inspected root on its terms, and an inert box that both calculi erase their boxes to.  B0 changed
nothing here, since levels are static.  B1 reshaped a runtime lambda and a runtime object to take
bodies over the target's signatures, added a map of term variables with its traversal, and let the
two step rules that enter a body continue at that map.

Identifiers the plan spells with a `ᶜ` suffix carry the ASCII suffix `C` here (`Ctx.consC`,
`Store.consC`, `Subst.liftC`, `Ctx.lookupDefC`, `Proposition.leC`, `CapEq.defC`, `SideC`, `HoleC`),
since `ᶜ` is not a legal identifier character.  Notation tokens such as `⊑ᶜ`, `≐ᶜ`, `⊢ᶜ` and `⊤ᶜ`
are unaffected.

Axioms throughout: `propext` and `Quot.sound`.  No `sorry`, `axiom`, `partial`, `unsafe`, or
`native_decide`, and no Mathlib.

## What is not here yet

`fresh` as a per-call existential, stage B2: an answer sort, packing as a wrapper whose premise is an
instance binding, and a `letex` binder that is rootless by design.  Then stage B3, the source
`DOT-MNF^cc'` with `any` by position the compiler's way, its translation, and the mandatory examples,
among them the four worked programs of the compiler's own write-up, the two halves of C5, and two
calls whose capabilities are incomparable.
