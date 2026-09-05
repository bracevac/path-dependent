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
term members, recursive self types, intersections of declarations, type
selections on variables, and bad bounds admitted.  It has subtyping, term
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
declaration-shaped types becoming object types over a fresh self;
subtyping derivations to closed evidence; variable typings to atoms rooted
at the variable; terms to terms with the same erasure.  Its theorems are
typedness of the translation, erasure equality `⌊h.translate⌋ = ⌊t⌋`,
coherence, `dot_safety` (a closed well-typed DOT-MNF program never gets
stuck, proven by running the translation alongside), and the consistency of
every store reachable by a translated program.

**`Runtime.lean`** is the untyped language both machines erase into, with
objects that keep their term members.

Axioms throughout: `propext` and `Quot.sound`, plus `Classical.choice` in
FCdot's `progress`, `erase_reflect'`, and `dot_safety`.  No `sorry`, `axiom`, `partial`,
or `native_decide` in the main line; the mandatory examples E1–E5 are
decided in the kernel on both sides and have equal erasures.

## Earlier targets, standalone

**`FCsub/`** is System F-sub with explicit coercions, telescope-constrained
quantifiers, and guarded recursive projections, with preservation, progress,
and a complete checker.

**`ManySortedFC/`** is the static layer of a two-sorted target with type and
capture sorts: syntax, checked logical evidence, sound and complete
checkers, theory models and maps, consistency models, and a classifier-kind
algebra.  It has no operational semantics.

Each directory's README lists its modules.
