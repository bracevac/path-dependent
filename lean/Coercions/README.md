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

## The second line: Oopsla16 → FCdotR

**`Oopsla16/`** ports the Rompf–Amin OOPSLA 2016 DOT calculus, which has
recursive subtyping, from its Coq artifact (`minidot`, `oopsla16/dot.v`).
**`FCdotR/`** is its explicit-evidence target, with `Oopsla16`'s own types.
Headline: `Oopsla16.oopsla16_safety`, a closed program typed over the empty
store never gets stuck, proved through elaboration into FCdotR.  An executable
checker decides FCdotR typing, proved sound and complete.  The line shares only
`FCdot/Debruijn.lean` with the main line.  See
[`Oopsla16/README.md`](Oopsla16/README.md) and [`FCdotR/README.md`](FCdotR/README.md).


Axioms throughout: `propext` and `Quot.sound`.  No `sorry`, `axiom`, `partial`,
or `native_decide` in either line; the mandatory examples E1–E5 and the
acceptance test E8 (the refinement `x.A ∧ {a : ⊤}` of an abstract type) are
decided in the kernel on both sides and have equal erasures.

## Extensions

Each extension copies a base tree, named in its `BASE` file, into a library of its own, keeps
every theorem of that base, and is a default target.

**`Captures/`** models Scala 3's capture checking the DOT way.  A type is a shape with a capture
set, `S ^ C`, and a capture parameter is a capture member of an object.  The target proves that a
run reads only what its use set predicts (`capture_prediction`) and that a capability left out of
the use set is never read (`effect_safety`).  The source inherits both as `dot_capture_prediction`
and `dot_effect_safety`.  Library `Captures`, see [Captures/README.md](Captures/README.md).

**`CapturesCC/`** models capture checking the way the Scala 3 compiler does it, with scopes, levels
and fresh capabilities, as a copy of `Captures/`.  `no_inner_escape` says that no capability leaves
the scope that introduced it, which rejects the `withFile` escape.  Every prediction theorem of
`Captures/` still holds.  Library `CapturesCC`, see [CapturesCC/README.md](CapturesCC/README.md).

**`Classifiers/`** adds the capability classifiers of Capless(K) to a copy of `CapturesCC/`.  A
library can classify its capabilities, say as `Control`, and `cap.only[Control]` then stands for
the capabilities of that class alone.  `classified_effect_safety` says that a program whose use set
has kind `φ` never reads a capability classified outside `φ`, and the source inherits it as
`dot_classified_effect_safety`.  Library `Classifiers`, see [Classifiers/README.md](Classifiers/README.md).

**`Paths/`** adds pDOT's paths `x.a.b` and singleton types to a copy of the main line.  Scala types
mention such paths all the time, as in `x.a.T`, while WadlerFest DOT selects types on variables
only.  It keeps `dot_safety` and passes two of gDOT's tests, `acceptance_fig2` and
`acceptance_gdot3_any`.  Library `Paths`, see [Paths/README.md](Paths/README.md).

## Earlier targets, standalone

**`FCsub/`** is System F-sub with explicit coercions, telescope-constrained
quantifiers, and guarded recursive projections, with preservation, progress,
and a complete checker.

**`ManySortedFC/`** is the static layer of a two-sorted target with type and
capture sorts: syntax, checked logical evidence, sound and complete
checkers, theory models and maps, consistency models, and a classifier-kind
algebra.  It has no operational semantics.

Each directory has a README.

**`paper/`** is the write-up of the main line (acmart, `latexmk -pdf main.tex`), with a table mapping its results to the Lean declarations.
