# Selective transitivity

This directory defines coercive calculi for full System F-sub and WadlerFest DOT in
monadic normal form. Primitive subtyping is nontransitive. Coercions record a
primitive comparison or compose two conversions:

```text
c ::= step[S,T] | c ; d
```

Both calculi have their own syntax, typing and operational safety proofs. A supplied
vanilla typing derivation translates to a target term of the same type, and erasing
the coercions recovers the source program. Conversely, erasure preserves typing.

| Directory | Contents |
| --- | --- |
| [Fsub/](Fsub/README.md) | Full F-sub, certificate checking, safety and vanilla correspondence |
| [Dot/](Dot/README.md) | MNF DOT, receiver casts, safety and examples |
| [Dot/Vanilla/](Dot/Vanilla/) | DOT-MNF elaboration, erasure correspondence and agreement of the machines |

In F-sub, a type variable's bound comes directly from the context. DOT also needs
the type of a selection's receiver. The receiver can carry a cast, written inside a
step endpoint as `(x ▷ c).A`. These casts use the same two coercion forms. Contexts
and typing judgments retain ordinary DOT types.

Execution removes all casts. The safety proofs establish that a well-typed closed
program cannot get stuck. F-sub preservation retains the program's type; DOT
preservation maintains a typed-machine-state invariant whose context and types are
existentially quantified. Neither proof computes the annotations of the next state.
The elaborations do compute annotations from supplied source derivations. F-sub has
verified annotation checkers; no DOT checking algorithm is provided.

Build both calculi and their correspondence proofs together:

```sh
lake build Selective
lake env lean lean/Coercions/Selective/Fsub/Axioms.lean
lake env lean lean/Coercions/Selective/Dot/Axioms.lean
lake env lean lean/Coercions/Selective/Dot/Vanilla/Axioms.lean
```

The axiom audits use at most `propext` and `Quot.sound`.
