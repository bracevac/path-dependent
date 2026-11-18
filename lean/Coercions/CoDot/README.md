# CoDot: DOT with coercions

CoDot gives a direct safety proof for WadlerFest DOT in monadic normal form
with explicit coercions. It uses the types of [DOT-MNF](../DotMNF/README.md)
and defines its own terms, typing rules and machine. Every state reachable
from a closed well-typed CoDot program is final or can take a step.

A reference `x ▷ c` carries a coercion describing how to use the value at
`x`. Function application and field selection evaluate the receiver's
coercion to a view of that value. Arguments and returned answers retain
their coercions. Substitution carries this evidence into each use while
types continue to refer to the same location. The store contains ordinary
objects and functions; coercions allocate no proxy objects.

The proof combines substitution of coerced references with canonical forms
for views. Stored values have their introduction types. This store invariant
is derived from value typing and preserved by allocation.

## Results

- [`Machine.lean`](Machine.lean): initialization, preservation and progress;
  `CoDot.safety` establishes safety of the coercive calculus.
- [`Elab.lean`](Elab.lean): every DOT-MNF typing derivation admits an
  annotation at the same type whose erasure is exactly the source term.
  This covers unrestricted intersections and recursive bodies, and source
  contexts with bad bounds.
- [`Admin.lean`](Admin.lean) and [`Bridge.lean`](Bridge.lean): administrative
  steps terminate and preserve erasure; real steps erase to source steps.
  Execution lifting establishes `CoDot.source_safety` for ordinary DOT-MNF.
- [`WadlerFest.lean`](WadlerFest.lean): safety for the annotated WadlerFest
  machine, retained-let reduction under every reduction order, and the public
  syntax with separate type and term labels.

Start with [`Core.lean`](Core.lean) for coercions and views, then
[`Term.lean`](Term.lean) and `Machine.lean`. `Subst.lean`, `Eval.lean` and
`Elimination.lean` contain the supporting proofs. `Examples.lean` covers the
source examples E9–E12 through the elaboration theorem.

CoDot is independent of the [FCdot](../FCdot/README.md) safety proof; its
only FCdot dependency is the shared scoping module. [Selective](../Selective/README.md)
studies transitivity-only coercions. CoDot makes structural and selection
evidence explicit as well. Elaboration is an existence theorem; this
development provides no executable annotator or type checker.

## Build

From the repository root:

```sh
lake build CoDot
lake env lean lean/Coercions/CoDot/Axioms.lean
```

The axiom audit uses at most `propext`, `Quot.sound` and `Classical.choice`.
There are no admitted proofs or custom axioms.
