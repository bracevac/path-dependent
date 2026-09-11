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

Stage B2 makes a result `fresh` a per-call existential.  An arrow's codomain and the type index of
term typing move to an answer sort, which is either a plain type or a type under one capture binder
bounded by a capture set of the enclosing scope.  An answer occurs in those two places and nowhere
else: not in a domain, not in a telescope, not in a proposition, not in a capture set, not under a
`μ` and not under a box.  So the normal forms of the stage are B1's with one component re-sorted,
and every telescope function and every view is untouched.  The bound is what makes the existential
usable.  Without it the only rule that lowers the binder a `letex` opens is the level rule, whose
right side is a root, so a lambda containing such a `letex` cannot close and a top-level one puts the
universal root into the program's use set.  With the bound the body's use of the unpacked variable is
charged to an ordinary capture set of the caller's scope, and no root enters any use set.

Packing is syntactic and it is a coercion.  A packed value and a packed atom are wrappers carrying
the witness, the evidence that the witness is below the declared bound, and one residual type
inclusion, and the relation `ELeCo` between answers has `plain`, `pack`, `cong` and `trans`.  So a
plain answer is widened to an existential wherever a coercion goes, the codomain of an arrow
included, which is what makes the third widening step of the page's own `withFile` derivation
expressible.  Value typing has no rule for a pack, so a packed value has an existential answer and no
other, and a packed value is never stored, because store typing premises value typing.  The pack rule
opens a root of its own and reads its residual under an instance binding for the witness, and the
unpack collapses that root by one substitution.  Neither unpack step has a premise and neither takes
fuel, and that is what the syntactic wrapper buys.

The unpacking former is `letex`, and its opened capture binder is rigid with no scope of its own, so
two `letex`es open two incomparable binders.  The answer-cast frame holds the coercion itself and not
a head form, because the two cast-redex theorems are stated over untyped states and a step with a
normalisation premise at an answer-cast focus would make both false.  What composes instead is
`applyE`, total and structural on the coercion.  The pack rule cannot be typed without one new
capture equality, an instance rule that says an instance binder stands for the set it was opened at,
and that rule is the one place the stage pays for the compiler's instantiation.  Its price is one
more capture field on renamings and substitutions, which every instance the tree builds proves by one
weakening commutation.

`letex` does not erase to `let`.  The runtime gains an unpacking term, an unpacking continuation
frame and three steps, and the two unpacking steps push a data-free capture slot onto the runtime
store, which the store already had and no step produced.  A pack erases to what it wraps, so the
erasure cannot tell a packed atom from a plain one, and what tells them apart is the continuation
that accepts the focus.  On the source side `fresh` is a capture atom that no rule mentions, read
before typing by a function that expands a result `fresh` to the callee's own assigned capture set
united with its parameter, exactly as `any` is read by `expand`.  The source gains the same answer
sort, the same instance binding, the same `letex` and a subsumption rule that carries the pack.

Four departures of B2 are recorded as decisions.  The existential carries a declared bound, which
neither Capless nor the sketch has, and without it D6's relaxed `letex` is unusable.  Packing is a
subtyping step and not a term former, which is what lets a plain codomain be widened under an arrow.
The pack rule opens a root of its own, without which the type-sort block's renaming theorem is false
and not merely unproven.  And the answer-cast frame holds the coercion rather than a head form, so
the stage has no answer-form normalizer, no answer-form typedness and no fifth field on the form
invariant of the store.

Stage B3 is the source read the compiler's way, and it is the last stage.  The notation `any` is
unchanged and no rule of either calculus mentions it, but the reading is by position now.  `expand`
threads the set that the root enclosing the position stands for, and passes it under an arrow's
codomain and under a `μ` body untouched.  It is reset at exactly two kinds of place, the positions
where `any` is forbidden and an arrow's domain, and a domain reads `any` as the arrow's own capture
binder, which is what turns the arrow into a capture-parameter arrow with no member encoding and no
extra application in the translated term.  A3b recomputed the reading at every former, so an `any`
was read by what stood at its position.  The compiler's way reads it by where it stands.

The source has no universal root, and it must not have one.  If a top-level `any` read as `⊤ᶜ`, a
program could declare its own use set to be `{⊤ᶜ}` by the source's own level rule, and the platform
premise that `dot_effect_safety` supplies would be lost, because over the platform prefix every
platform binder is a root of `{⊤ᶜ}` while the membership the theorem reads still holds.  Two halves
of that are machine checked and the step from there to a false theorem is an argument, but the hard
constraints forbid the theorem gaining a premise either way, so the source names no `⊤ᶜ` and a
top-level `any` reads as the program's platform set.  `Ctx.reading` is the statement of where a
reading comes from: the innermost root binder of the context as a singleton, and the platform set
where the context has none.

B3 gives the source the target's level machinery and one rule.  A level is a position on the spine
here too, `Ctx.lvlLeB` is the same order, and `Subcap.level` is the compiler's `acceptsLevelOf` on
the source side.  Because the source names no universal root, a notation is below no root, so the
order is false at `any` and at `fresh` on either side.  The source has also never had a term-level
expansion and has one now: a lambda's domain annotation may hold `any` in its outer set and nowhere
else, and `Tm.expand` descends at `let`, at `letex` and through a value into a lambda's body, so a
notation written inside a program is read and not left standing.

The translation gains one clause, its typedness one case, and five spine commutations that say
`Ctx.translate` commutes with `Ctx.root?`, `Ctx.lvl` and `Ctx.rootB`.  The type translation does not
move at all, which is the source's lack of a universal root seen in the diff.  T17,
`source_lvl_safety`, is the theorem of the stage and it is one line on top of `level_inversion`:
member-free source subcapturing never lowers a level.  It needs the source's own member-free
predicate, which excludes exactly the three source rules whose translation is `eqToLe` or `member`,
and those are exactly the two target rules the target's member-free predicate excludes.

### The decisions of B3

**22.**  The reading of `any` is one capture set threaded down, not a set recomputed at every former.
**23.**  The source has no universal root, and a top-level `any` reads as the program's platform set.
**24.**  A parameter `any` is the arrow's own capture binder, and it is legal only at the top of a
domain.  **25.**  A result `any` does not reset the reading, because a source arrow type binds no body
root.  **26.**  A class member `any` reads as the root enclosing the object type, not the class root of
the literal, so a field that captures the self writes `{self}`.  **27.**  Terms are expanded, and the
term-level expansion needs no reading set: `Tm.expand` descends at `let`, at `letex` and through a
value into a lambda's body, and a lambda's domain is read at the arrow's own binder.  **28.**  A
literal's definitions hold no `any` (`Defs.noAny`, required by the term-level `AnyOk`).  **29.**  The
source gains B0's level rule, with its own level machinery over its five context constructors and no
universal root.  **30.**  A notation is below no root: `Ctx.lvlLeB` is `false` at `any` and at `fresh`
in either position.  **31.**  `any` is expanded before `fresh`.  **32.**  T17 is stated through the
translation, as `level_inversion` applied to a translated derivation, and the `withFile` escape at the
source context is an example.  **33.**  B3 touches one file under `FCdot/` besides `Examples.lean`,
`LevelInversion.lean`.  **34.**  The level order relates a parameter and its body root in both
directions, but only one direction is a rule instance, because the rule asks for a root on its right
and the arrow binder is a rigid capture binder.  **35.**  A call instantiates a parameter `any` with
the argument variable rather than with a fresh capability, one instance per call, more precise than
the compiler.  **36.**  `any` is forbidden in a type-member bound, so the page's fourth worked example
is written monomorphically, and W5's two halves live at two contexts.

## The tree

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
put a concrete assigned set below a scope root.  B2 reached it again.  `Syntax` carries the answer
sort with its declared bound, the two wrapper families and the two new term formers, `Context` the
instance scope and the instance reader, `Typing` the answer-inclusion judgment with its three thin
wrappers and the instance rule, `Machine` the answer-cast frame, the unpacking frame and the six
steps, `Preservation` isolation, the two canonical-forms theorems at an existential answer and the
two unpack cases, `Prediction` the one lemma that consumes the declared bound, `ErasureMetatheory`
the typed invariant the backward simulation now needs, and `Examples` the five programs Y1 to Y5
with the store that makes Y1's negative theorem non-vacuous.  B3 reached two of its files and no
more: `LevelInversion` gained the renaming of the two member-free families, which the translation's
reader of a variable weakens with, and `Examples` gained the target side of the source's own worked
programs, among them T17 at `⊤ᶜ`.

**`DotMNF/`** is the source, `DOT-MNF^cc`, with `any` by position since A3b.  A shape is the vanilla
type former, a type is a shape with a capture set, and the new shapes are the capture member and the
box.  `any` is read before typing by the function `expand`, whose reading is by position and needs no
level, and an expanded program is a program of stage A3a.  B0 changed nothing here.  B1 moved the
source arrow in step with the target's, because the two calculi have to bind the same binders in the
same places: the source gains a scope root constructor beside its rigid capture binder, its own three
scope contexts, and its own substitution with an atom-valued capture component, which writes `any`
where the target writes `⊤ᶜ`.  Every derivation of the example file keeps its name and its
conclusion.  B2 gives the source `fresh`, the answer sort with the same declared bound, an instance
binding, the `letex` former with its three machine steps, and a subsumption rule that carries the
pack.  `FreshOk` decides and `expandFresh` computes, so a written type is checked and its reading is
stated by `rfl`, exactly as `AnyOk` and `expand` are at A3b.  B3 is this directory's own stage: the
reading of `any` becomes the root enclosing the position, three clauses of `Shape.expand` and one of
`Ty.expand` are rewritten, an arrow's domain becomes a legal place for `any` and a place deeper in a
domain stops being one, the source gains the target's level machinery with one rule, `Subcap.level`,
and it gains a term-level expansion it never had.

**`DotToFCdot/`** is the translation.  A source type is a shape with a capture set and so is a target
type, so the translation splits the same way, and use sets are carried by the derivation, so the
translation of a derivation carries the evidence for them.  The source's safety, consistency and
capture prediction are all borrowed from the target through it.  B0 changed one lemma here, the
platform premise that a capture set does not mention `⊤ᶜ`, which every translated set satisfies by
computation.  B1 changed almost nothing, which was the point of moving the source arrow: the
translation of an arrow is textually what it was, the translation at a lambda and at an application
did not have to be rewritten, and `Ctx.translate` gained one clause for the source's scope root.  The
one new file says that the type translation commutes with substitution and not only with renaming,
which is what the application case now needs.  B2 changed three things and nothing else: the answer
translation, the answer-inclusion translation, and one clause of the context translation for the
source's instance binding.  A source `fresh` is dropped as `any` is, which is sound because the
source gives it no power and vacuous on expanded programs.  B3 changed one clause, one case, and
added the five commutations that say the context translation commutes with the level machinery, plus
T17.  The type translation did not move at all, which is the source's lack of a universal root seen
in the diff.

**`Runtime.lean`** is the shared untyped runtime with a data-free capture slot in its store, an
inspected root on its terms, and an inert box that both calculi erase their boxes to.  B0 changed
nothing here, since levels are static.  B1 reshaped a runtime lambda and a runtime object to take
bodies over the target's signatures, added a map of term variables with its traversal, and let the
two step rules that enter a body continue at that map.  B2 added an unpacking term, an unpacking
continuation frame and three steps, and the two unpacking steps are the first to push the store's
data-free capture slot.

Identifiers the plan spells with a `ᶜ` suffix carry the ASCII suffix `C` here (`Ctx.consC`,
`Store.consC`, `Subst.liftC`, `Ctx.lookupDefC`, `Proposition.leC`, `CapEq.defC`, `SideC`, `HoleC`),
since `ᶜ` is not a legal identifier character.  Notation tokens such as `⊑ᶜ`, `≐ᶜ`, `⊢ᶜ` and `⊤ᶜ`
are unaffected.

Axioms throughout: `propext` and `Quot.sound`.  No `sorry`, `axiom`, `partial`, `unsafe`, or
`native_decide`, and no Mathlib.

## What the compiler's way delivers

*Levels, as a judgment.*  The DOT way reads `any` by position and level free, and it has no notion of
one scope enclosing another.  The compiler's way has one.  `Ctx.lvl` reads the nearest enclosing root
off the spine, the `level` rule of `Subcap` and of `CapCo` is `acceptsLevelOf`, and `{any₂} <: {any₃}`
holds while `{any₃} <: {any₂}` does not, in both calculi, decided in the kernel.  X1, X2 and X3 state
it over a spine written by hand and W1 states it over two real lambda bodies, so the nesting there is
the binder order the rules produce.  Nothing in the DOT way can state that.

*The escape, rejected by the write-up's own mechanism.*  `withFile[() => File^]("test.txt")(f => () => f)`
is rejected because the level of `f` is the callback's body root and the expected type names a root
outside the call, and separately because no member-free evidence at all can lower a level.  X4 and W5
are the two halves on the two sides, `level_inversion` and `source_lvl_safety` are the store-free
theorems behind them, and the counterfactual binder order is checked too, X5 and W6, so the rejection
is a property of the rules and not of one example.  In the DOT way the same program is refused only
because one set does not hold one atom, which is not the write-up's mechanism and does not survive a
program that widens on the way out.

*A parameter `any` as a capture parameter.*  The arrow binds it, a call instantiates it at the
argument, and the callee's type stays one arrow, so erasure equality is free.  W2 is that in four
theorems: the reading, the level step inside the body, the instantiation at the call, and the erasure
of the translation.  The member encoding the DOT way would have needed puts one extra application per
call into the target term.

*A result `any` that two calls share, and a `fresh` that they do not.*  Both readings exist and both
are checked.  A result `any` reads as the enclosing root, so two calls agree, while a result `fresh`
is an existential and two calls open binders that nothing relates.  Isolation is the step the
write-up itself names, and it is `no_ex_le_ty`.  That nothing relates them is
`FCdot.Examples.two_calls_incomparable` on the target and
`FCdot.Examples.Z_two_calls_incomparable` on the source, the second over the translation of the
source's own two-call context `DotMNF.Examples.Z1BodyCtxTop`, with its own typed store, its own
refinement and `cap_canon`.  The source-side context unpacks each answer at `⊤`, by the source
subtyping step `Z1_widen`, because no target literal has the translated type of a source object type
(`FCdot.Examples.Z_no_literal_at_file`) and so no store binds a variable at one.  The two opened
capture binders and the two cells are unmoved by that widening, and they are what the theorem talks
about.

*A store that is the outermost scope.*  A store binds capabilities and never scopes, which is what
makes entering a body sound with no level numbers anywhere and no level data on any binder.

**What it costs.**  *Proof engineering.*  Levels are positions, and positions move.  `Ctx.Ren`,
`Ctx.RenR` and `Subst.Typed` carry four capture fields, ten `weakenC` theorems gained a premise, and
one dedicated lemma exists only to cross a freshly opened root.  That is the single largest item of
the four stages.  *Binders.*  A lambda opens three binders where it opened one, an object literal
two.  Every example on both sides was re-indexed, the runtime grew by six definitions and five steps,
and the erasure of a substitution had to be generalised because a substitution's capture component
has no runtime content.  *The source moved.*  `DotMNF` gained a capture binder on its arrow, three
context constructors, an answer sort on `HasTy`, `ESub`, `letex`, and now a level rule with its own
level machinery.  The platform prefix never moved, which is what kept the translation, the platform
and every A3a example intact.  *Six recorded departures from the compiler.*  The machine sends a
lambda's body root to `⊤ᶜ` at every call, where the compiler never retargets a level.  The source has
no universal root, so a top-level `any` reads as the platform set.  A class member `any` reads as the
root enclosing the object type and not as the class root.  The level order relates a parameter and
its body root both ways, but only one direction is a rule instance.  A call instantiates a parameter
`any` at the argument itself rather than at a fresh capability.  And `any` is not allowed in a
type-member bound, so the write-up's fourth example is written monomorphically.  The first two are
sound because a running program is the outermost scope.  The third is sound because the rendering is
stricter than the write-up's.  The last three are restrictions or refinements, so each is sound by
being narrower.

**What is not claimed.**  Tunneling and outer-bound `fresh` are not modelled.  Neither are the
`Unscoped` and shared-capability classifiers the level check consults, nor separation checking's
hidden sets, nor the narrowing step that folds a call's result back into the caller's own
capabilities, which is type inference and has no place in a calculus.  The argument that a source
universal root would make effect safety false is an argument and not a checked fact: its two halves
are checked and the program that would exploit them is not exhibited.

**The one line for the user.**  The DOT way types the same programs and rejects the escape for the
wrong reason.  The compiler's way costs a level order, four capture fields on every renaming, and two
binders per lambda, and in exchange the four worked examples of the write-up are theorems in Lean
with `propext` and `Quot.sound` and nothing else.
