# Lean developments

Lean 4 formalizations of path-dependent types. There are two lines of
work: a family of small calculi of paths through dependent pairs, and a
type-preserving translation of DOT into an explicit-evidence coercion
calculus. Every directory is self-contained, with its own syntax, typing,
store machine, and proof, and nothing here depends on a library beyond
Lean's core.

## Paths through dependent pairs

A minimal calculus in which immutable dependent pairs are the only
structured values and paths select through them. A pair's second component
may depend on its first, a member may be a term or a type definition, and
term singleton types and abstract type selections are kept distinct. The
five directories are one calculus grown in two directions, and each proves
that no finite run of a closed, well-typed program gets stuck.

**`LambdaP/`** is the original calculus, with pair subtyping restricted to
pairs whose first component has singleton type. Its proof keeps the store
at exact introduction types, mirrors every source judgment by a structural
runtime judgment, and interprets pair subtyping by semantic realization
maps, because a syntactic canonical-forms argument fails for the rule that
widens a member. The unrestricted pair rule is left open here.

**`LambdaPFC/`** is the same calculus with the general covariant pair rule.
Subtyping derivations are compiled into store-indexed coercions, dependent
premises are suspended until a stored pair supplies the location they
bind, and termination follows the allocation order of the store.

**`LambdaPFCI/`** adds binary intersection and union types to `LambdaPFC`,
with a recursive merge of two views of the same record spine, and leaves
`LambdaPFC` unchanged as the baseline.

**`LambdaPCC/`** adds capture checking to `LambdaPFC`: capturing types,
use sets, and abstract capture-set members, with the same coercion
architecture over capture-aware stores. Beyond type safety it proves that
every application's operands are covered by the use set and that a
returned value's capture set is bounded by its type's.

**`LambdaPCCI/`** adds intersections, unions, and capture-aware merges to
`LambdaPCC`, and leaves `LambdaPCC` unchanged as the baseline.

## DOT into explicit evidence

**`Coercions/`** translates DOT in monadic normal form into a coercion
calculus in the spirit of System FC, in which every use of subtyping is a
proof term that erases to nothing. The target has a decidable and complete
checker, its safety proof is store typing plus normalization of closed
evidence, and the source's type safety is a corollary of the translation.
The directory also keeps two earlier targets and the write-up. Its README
is the map of that line.

The headline theorems everywhere depend on `propext` and `Quot.sound`
only, except progress, the backward erasure simulation, and DOT safety in
`Coercions`, which also use `Classical.choice` for a case split. Nothing
uses `sorry`, `axiom`, `partial`, or `native_decide` outside example
files. Rocq ports of `LambdaP`, `LambdaPFC`, and `LambdaPCC` live in
`../rocq/` and lag behind. From the repository root, `lake build` builds
everything, and each directory's README lists its modules, main theorems,
paper, and build target.
