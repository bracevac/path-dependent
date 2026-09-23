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

## The second line: Oopsla16 → FCdotR

**`Oopsla16/`** is the Rompf--Amin calculus of *Type Soundness for Dependent
Object Types* (OOPSLA 2016), transcribed from the authors' pinned Coq artifact
`TiarkRompf/minidot` at `ef1143dc1875d389c47083cd324971b1b86686d1`,
`oopsla16/dot.v`. It is the source specification for recursive subtyping,
which WadlerFest DOT deliberately omits: it has `stp_bindx` and `stp_bind1`,
and its soundness is proved in the artifact. The port is intrinsically scoped
in the discipline of `FCdot/Debruijn.lean`, which removes the reference's
`closed` predicate, its locally nameless bound variables, and its derivation
size index. It keeps what carries the soundness: two variable zones, positional
labels, context entries that may mention their own binder, and a variable
typing judgment `Htp` with no packing rule.

The reference's context truncation in `htp_sub` — `length GL = S x` and
`GH = GU ++ GL`, the restriction that makes recursive subtyping sound — becomes
the *type* of `Htp`, which records a variable at a type of its own prefix
scope. The rule then has no side conditions at all.

**`FCdotR/`** is its explicit-evidence target.  It keeps `Oopsla16`'s types
unchanged and turns subtyping, and the variable typings that type selections
rely on, into evidence: observation evidence scoped at its subject's prefix,
packing only at store locations, and recursive subtyping over the opened body.
Every source typing elaborates into a typed FCdotR term.  The FCdotR machine
has preservation up to evidence, progress, and canonical forms of closed
evidence, obtained by eliminating transitivity with an induction on packings.
An operational correspondence between the two machines carries safety back:
`Oopsla16.oopsla16_safety` says a closed program typed over the empty store
never gets stuck on `Oopsla16`'s own substitution machine, with no hypothesis.
There is no checker yet.  The line is independent of the main line above and
shares only `FCdot/Debruijn.lean` with it; see
[`FCdotR/README.md`](FCdotR/README.md) and [`FCdotR/STATUS.md`](FCdotR/STATUS.md).


Axioms throughout: `propext` and `Quot.sound`.  No `sorry`, `axiom`, `partial`,
or `native_decide` in either line; the mandatory examples E1–E5 and the
acceptance test E8 (the refinement `x.A ∧ {a : ⊤}` of an abstract type) are
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

**`paper/`** is the write-up of the main line (acmart, `latexmk -pdf main.tex`), with a table mapping its results to the Lean declarations.
