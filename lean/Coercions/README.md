# Coercions

Lean formalizations of type-preserving translations from DOT into
explicit-coercion calculi: a source calculus with path-dependent types, a
target calculus in which every use of subtyping is a proof term that erases
to nothing, and a translation between them that transports the target's
type safety back to the source.

## The main line: DOT-MNF → FCdot

```
 DotMNF (source)          DotToFCdot (translation)       FCdot (target)
 DOT in monadic           derivations ↦ terms,           explicit-evidence
 normal form              evidence, atoms                coercion calculus
        \                                                       /
         \______________ Runtime (untyped, shared) _____________/
```

**`DotMNF/`** is WadlerFest DOT in monadic normal form: objects with type and
term members, recursive self types, unrestricted intersections, type
selections on variables, and bad bounds admitted.  The body of a recursive
self type is still restricted to declaration shapes.  It has subtyping, term
and definition typing, a store machine, and an erasure into the runtime.
It has no metatheory of its own.

**`FCdot/`** is the target.  Types are `⊤`, `⊥`, block names `x ∙ ℓ`,
dependent functions, and object types, i.e. telescopes of propositions
(inclusions, equalities, field presence) over a self block.  Evidence is a
proof-term language for inclusion, equality, and presence; there is no
subsumption.  Object literals carry witnesses and fields only, and the
store binds each location transparently, so a block name is defined by the
stored literal.  The metatheory: a checker with completeness, preservation,
progress, erasure simulations in both directions, and canonical forms of
closed evidence over a typed store, obtained by a structural normalizer that
turns any closed inclusion into a head form and any atom into a view of its
object type.  Canonical forms are what makes application through casts
executable and progress provable without inverting evidence syntactically.

**`DotToFCdot/`** translates derivations: types homomorphically, with
declaration-shaped types becoming object types over a fresh self and every
other shape becoming the single self-bound proposition `⊑ ⟦B⟧`, which is
what makes an intersection with a non-declaration operand translatable;
subtyping derivations to closed evidence; variable typings to atoms rooted
at the variable; terms to terms with the same erasure.  Its theorems are
typedness of the translation, erasure equality `⌊h.translate⌋ = ⌊t⌋`,
coherence, `dot_safety` (a closed well-typed DOT-MNF program never gets
stuck, proven by running the translation alongside), and the consistency of
every store reachable by a translated program.

**`Runtime.lean`** is the untyped language both machines erase into, with
objects that keep their term members.

**`Frontend/`** is a front end for the source language and is not part of the
metatheory.  A program is written in the paper's notation inside a `dot%`
quotation.  Name resolution and let-insertion turn it into DOT-MNF in monadic
normal form, a budgeted typer returns the `DotMNF.HasTy` derivation rather than
an answer, and the pipeline sends that derivation through the translation, past
the target's checker, and into either machine written as a function.  What the
front end proves is that composition and nothing about the calculus.  Its own
results are the totality of resolution, decision procedures for the side
conditions a derivation carries, monotonicity of the search in its budget, and
agreement of both executable machines with the frozen step relations.  The typer
is sound by construction, because it returns the derivation, and incomplete by
necessity, because DOT subtyping is undecidable.  The examples of
`DotMNF/Examples.lean` are written again as surface programs and compared
against the hand-written derivations on three decidable things: the resolved
term, the synthesized type, and the checker's verdict on the translation.  It
builds as the library `Frontend`, which is not a default target, so the
metatheory does not wait on it.

Axioms throughout: `propext` and `Quot.sound`.  No `sorry`, `axiom`, `partial`,
or `native_decide` in the main line; the mandatory examples E1–E5 and the
acceptance test E8 (the refinement `x.A ∧ {a : ⊤}` of an abstract type) are
decided in the kernel on both sides and have equal erasures.

## Extensions

Each extension has the shape of the main line, a source, a target, a translation and a runtime, in
a namespace of its own.  It starts as a copy of its base at the commit its `BASE` file names, and it
keeps every theorem of the base, restated where the representation changed and never weakened.  The
axioms are the same, `propext` and `Quot.sound`.

**`Captures/`** is capture checking the DOT way, a copy of the main line.  A type is a shape with a
capture set, `S ^ C`, and a capture-set parameter is a capture member `{C : c₁..c₂}` of an object, as
a type parameter is a type member.  The target gains an inert box, the source reads Scala's `any` by
its position, and terms carry use sets.  Its results are `cap_canon`, item 7 of `atom_canon`,
`closed_box_inversion`, and the prediction theorems `capture_prediction`, `inspects_covered`,
`effect_safety` and `returned_capture_bound`, which the source inherits as `dot_capture_prediction`
and `dot_effect_safety`.  It builds as the library `Captures`, a default target.  Its README says what
it does not read: a parameter `any` in the style of Decap, and tunneling.

**`CapturesCC/`** is capture checking the compiler's way, a copy of `Captures/`.  A lambda body and
an object body are scopes with a root of their own, a level is a position on the binder spine, and
one evidence rule, `level`, is the compiler's `acceptsLevelOf`.  A parameter `any` is a capture
binder on the arrow, and a result `fresh` is a per-call existential opened by `letex`.  Its results
are `level_inversion` and `no_inner_escape`, which reject the `withFile` escape by the compiler's own
mechanism, `source_lvl_safety` on the source, `two_calls_incomparable`, and every prediction theorem
of `Captures/`.  It builds as the library `CapturesCC`, a default target.  Its README ends with what
the compiler's way costs and what it does not claim.

**`Classifiers/`** is a copy of `CapturesCC/` with the classifiers of Capless(K).  A classifier is a
closed tree, a kind is a list of subtrees with exclusions, and a capture atom can be projected by a
kind, as in `cap.only[Control]`.  The projection is filtered at the end of expansion, so roots and
subcapturing do not move.  Telescopes carry a kinding proposition `C ⊑ᵏ φ`, with closed evidence and
a checker that is sound and not proved complete.  Its results are `classified_prediction` and
`classified_effect_safety` on the target, and `dot_classified_prediction` and
`dot_classified_effect_safety` on the source.  It builds as the library `Classifiers`, a default
target.  Its README lists what it leaves out, first of all control effects.

**`Paths/`** is a copy of the main line with paths `x.a.b`.  The source types a path by a judgment
of its own with pDOT's singleton rules.  The target keys blocks by paths, and an alias is a
forwarding node of a block forest.  Its results are canonical forms at every depth, with
`le_canon_ne` needing no store, `Store.Typed.pathView`, `alias_eq`, `dot_safety` in its old
statement, and two acceptance tests: `acceptance_fig2` types gDOT's Fig. 2 with no later modality,
and `acceptance_gdot3_any` shows that no literal has the bad bounds of gDOT's Sec. 3.  It builds as
the library `Paths`, a default target.  It is combined with none of the capture extensions, and its
README lists the pDOT and gDOT rules it gives up.

Separation, after CoreCapybara, is parked on the branch `separation` and is not on this branch.  Its
soundness needs an invariant on a mutable store whose locations a `consume` masks, and canonical
forms do not give that.  Its first stage proved that invariant, then found machine-checked
counterexamples to the typing rules around it: an argument can escape through a closure the callee
returns, and a substitution lemma fails past a claimed name.  So its canonical forms and
preservation do not build there.

## Earlier targets, standalone

**`FCsub/`** is System F-sub with explicit coercions, telescope-constrained
quantifiers, and guarded recursive projections, with preservation, progress,
and a complete checker.

**`ManySortedFC/`** is the static layer of a two-sorted target with type and
capture sorts: syntax, checked logical evidence, sound and complete
checkers, theory models and maps, consistency models, and a classifier-kind
algebra.  It has no operational semantics.

Each directory's README lists its modules.

**`paper/`** is the write-up of the main line (acmart, `latexmk -pdf main.tex`), with a table mapping its results to the Lean declarations.
