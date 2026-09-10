# CapturesCC

Captures, the compiler's way: the second capture project of plan V (`plan-5-extensions.md` §3,
`plan-5b-captures-cc-note.md`, with the stages of `plan-5d-captures-cc-stages.md`), namespace
`CapturesCC`.  The tree started as a verbatim copy of `lean/Coercions/Captures/` at the commit in
`BASE`, the end of captures the DOT way, and grows the compiler's scope roots, levels, the capture
binder on the arrow, and `fresh` as a per-call existential.  Every statement of the DOT way is kept,
restated where the representation changed, never weakened.

Stage B0 is complete.  It touches the target only and adds no term former.  It adds the universal
root as a capture atom, written `⊤ᶜ`: the local root of the whole program, the compiler's `caps.any`
as a constant rather than as a binder.  It adds levels, and a level is a position on the spine and
not a field on a binding: the level of a binder is the innermost root binder of the prefix that
precedes it, a root is its own level, and a binder with no enclosing root is at the outermost level,
which is `⊤ᶜ`.  The order `Ctx.lvlLeB e r` says that the level of `e` is `r` or encloses it, so an
inner root absorbs an outer capability and never the reverse, and the universal root absorbs only
what sits inside no scope at all.  Everything is computed by recursion on the spine and is `Bool`
valued, so a level side condition on a concrete context is decided in the kernel.

One evidence rule reads the order.  `Γ ⊢ᶜ level e r : {e} ⊑ {r}` holds when `r` is a scope root and
the level of `e` is `r` or encloses it, which is the compiler's `acceptsLevelOf` reached from
`maxSubsumes`.  Both sides are singletons and the right side is an atom, since the universal root is
an atom and a rule with a variable on the right could not name it.  For the rule to be sound the
roots of a capture set have to say what a root stands for, so `Ctx.roots` becomes resolution followed
by expansion: expansion opens a root into the universal root and every opaque binder at its level or
outside it, and leaves every other atom alone.  `Ctx.roots` keeps its name, its signature and its
fuel argument, so subcapturing, the root predicate, root equality and the five prediction theorems
keep their statements literally, and on a root-free context whose resolution mentions no `⊤ᶜ`
expansion is the identity, so on a store context and on the platform prefix `roots` is `caps` again
and every roots-statement of the DOT way means there exactly what it meant before.

The theorems of the stage are about what closed evidence can do to a level.  Resolution never lowers
the level (`Ctx.caps_confined`), so canonical forms gains its level case and closed evidence never
lowers the level of what a capture set resolves to (`lvl_canon`).  A rigid binder is a root of
everything closed evidence puts it below, and nothing else resolves below it (`rigid_canon`,
`rigid_target`).  What closed evidence puts below a scope root resolves to capabilities at or outside
that root (`lvl_safety`).  And no closed derivation at all puts a capability introduced strictly
inside a scope below that scope's root (`no_inner_escape`).  A store binds capabilities and never
scopes, which is now a premise of `Store.Typed.consC` and gives the two run-time facts: a store
context has no root binder (`Store.Typed.rootFree`) and every capability of it is at the outermost
level (`Store.Typed.confined`).  Over a store `no_inner_escape` is therefore vacuous at B0, since the
only root is the universal one.  It acquires its content in stage B1, where a lambda body becomes a
scope.  Three examples are the observable content of the stage, all decided.  X1 is a platform
prefix, whose binders the universal root absorbs.  X2 is the nesting of a rigid capability, a scope
root and an inner rigid capability, where the scope root absorbs the outer capability and the
universal root alike and releases neither itself nor the inner capability.  X3 is the escape rejected
at the inner binder.

The source and the translation are untouched by B0 but for one lemma.  `Platform.root_iff` gains the
premise that its capture set does not mention `⊤ᶜ`, which every set the translation produces
satisfies by computation, so its sole caller supplies the premise and `dot_effect_safety` keeps its
statement.  Nothing else in `DotMNF/` or `DotToFCdot/` moved.

**`FCdot/`** is the target, FCdot^cc.  Its README lists the modules, what each stage changed in them,
the notation, and the theorems.  From the DOT way it carries the canonical-forms theorem with
`cap_canon` and item 7, `closed_box_inversion`, the five prediction theorems, and the capture
examples C1 and C6.  B0 reached it everywhere: `Syntax` gained the atom and the coercion, `Context`
the level block, the new module `Levels` the order lemmas and the weakening commutations, `Resolution`
the expansion and the hardest lemma of the stage, `Typing` the one rule, renaming and substitution
three capture fields each, the checker one case that reduces in the kernel, `Store` and `Machine`
their premises about what a store may bind, `CanonicalForms` and `Consistency` the theorems, and
`Examples` the three new examples beside every old one unchanged.

**`DotMNF/`** is the source, `DOT-MNF^cc`, with `any` by position since A3b.  A shape is the vanilla
type former, a type is a shape with a capture set, and the new shapes are the capture member and the
box.  `any` is read before typing by the function `expand`, whose reading is by position and needs no
level, and an expanded program is a program of stage A3a.  B0 changed nothing here: the source has no
atom for the universal root, so every capture set it writes is still a list of concrete atoms.

**`DotToFCdot/`** is the translation.  A source type is a shape with a capture set and so is a target
type, so the translation splits the same way.  Use sets are carried by the derivation, so the
translation of a derivation carries the evidence for them.  The source's safety, consistency and
capture prediction are all borrowed from the target through it.  The target has no atom for `any`, so
the translation of an atom is partial and the translation of a capture set drops what has no target
atom, which is also why no translated set mentions `⊤ᶜ`.  B0 changed one lemma here, the platform
premise above, and added `CaptureSet.top_not_mem_translate` and `Platform.rootFree` to prove it.

**`Runtime.lean`** is the shared untyped runtime with a data-free capture slot in its store, an
inspected root on its terms, and an inert box that both calculi erase their boxes to.  B0 changed
nothing here: levels are static and no term former was added.

Identifiers the plan spells with a `ᶜ` suffix carry the ASCII suffix `C` here (`Ctx.consC`,
`Store.consC`, `Subst.liftC`, `Ctx.lookupDefC`, `Proposition.leC`, `CapEq.defC`, `SideC`, `HoleC`),
since `ᶜ` is not a legal identifier character.  Notation tokens such as `⊑ᶜ`, `≐ᶜ`, `⊢ᶜ` and `⊤ᶜ`
are unaffected.

Axioms throughout: `propext` and `Quot.sound`.  No `sorry`, `axiom`, `partial`, `unsafe`, or
`native_decide`, and no Mathlib.

## What is not here yet

Scopes and the arrow, stage B1: the arrow binds its own root, a lambda body and an object body are
scopes, and the machine enters a body by one substitution.  That is what makes the level rule of B0
usable on a real binder order and what decides the `withFile` escape in Lean.  After it, `fresh` as a
per-call existential and the capture-set parameter.
