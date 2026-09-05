# Lean developments

Six Lean 4 developments on path-dependent types, in two lines. Each
directory is self-contained: its own syntax, typing, store machine, and
proof, with no imports between siblings. All of them are intrinsically
scoped (terms and types are indexed by their scope), run on a store machine
with an append-only store, and depend on no library beyond Lean's core.

## Paths through dependent pairs

A minimal calculus of paths through immutable dependent pairs, as suggested
by Martin Odersky. A pair's second component may depend on its first, and a
member may be a term or a type definition, so a path `p.fst.A` selects an
abstract type through a chain of pairs. Term singleton types `{p}` and
abstract type selections `p.A` are distinct. Terms are in monadic normal
form and run on a CK machine over a store.

| directory | calculus | proof | lines |
|---|---|---|---|
| `LambdaP/` | the original calculus, with the pair subtyping rule restricted to a singleton-typed first component | exact runtime typing, a structural family of runtime judgments, and semantic realization maps for pair subtyping | 10.5k |
| `LambdaPFC/` | the general covariant pair rule that `LambdaP` leaves open | subtyping derivations compiled to store-indexed coercions, a fundamental theorem, termination by allocation order | 3.4k |
| `LambdaPFCI/` | `LambdaPFC` plus binary intersection and union types and aligned merges of record spines | the same architecture, with plan-directed merges | 5.4k |
| `LambdaPCC/` | `LambdaPFC` plus capturing types, use sets, and abstract capture-set members | the same architecture over capture-aware worlds, plus application coverage and a returned-value capture bound | 5.7k |
| `LambdaPCCI/` | `LambdaPCC` plus intersections, unions, and capture-aware merges | the same | 8.5k |

Every development in this line proves `Tm.Ty.closed_type_safety`: no finite
execution of a closed, well-typed term ends in a stuck state. The two `I`
variants leave their baselines unchanged, so `LambdaPFC` and `LambdaPCC`
stay the calculi of their papers. Rocq ports of `LambdaP`, `LambdaPFC`, and
`LambdaPCC` live in `../rocq/` and typically lag behind.

## Coercions: DOT into explicit evidence

`Coercions/` (48k lines) is the second line: a type-preserving translation
of DOT in monadic normal form into an explicit-evidence coercion calculus,
in the spirit of System FC. Every use of subtyping becomes a proof term that
erases to nothing, the target has a decidable and complete checker, its
safety proof is store typing plus normalization of closed evidence, and the
source's type safety is a corollary of the translation. The directory also
keeps two earlier targets, `FCsub` and `ManySortedFC`, and the write-up in
`Coercions/paper/`. Its README is the map.

## Conventions

* No `sorry`, no `axiom`, no `partial`, and no `native_decide` in any main
  line. The headline theorems depend on `propext` and `Quot.sound` only,
  except progress, the backward erasure simulation, and DOT safety in
  `Coercions`, which also use `Classical.choice` for a case split.
* Examples and regressions in the pair line are hand-built derivations,
  usually driven through the machine to `closed_type_safety`. The examples
  of `Coercions` are decided by the kernel on the target side.
* Each directory's README has its module table, its main theorems, and its
  paper if there is one.

## Building

From the repository root, `lake build` builds everything. The lake
libraries are `LambdaP`, `LambdaPFC`, `LambdaPFCI`, `LambdaPCC`,
`LambdaPCCI`, and, for `Coercions/`, `FCdot`, `DotMNF`, `DotToFCdot`,
`Runtime`, `FCsub`, `ManySortedFC`, and `DotFC` (everything under
`Coercions`), so `lake build LambdaPFC` builds one of them.
