# Direct full compiler

This directory contains the replacement full compiler from the existing
`LambdaPFC` syntax and static derivations to the unchanged original
`SystemFCo` calculus.

The public compiler boundary is deliberately small:

```text
LambdaPFC.Tm.Ty Γ t T
  -> SystemFCo syntax
  +  a separate SystemFCo.Exp.HasType theorem
```

Compilation is derivation directed because source subsumption and precise
path typing determine emitted target transformations. It is not indexed by
`Fragment`, `OperationallyAdmissible`, semantic coercion action, stores, or
valuations.

Computational transformations are ordinary target functions. Applying an
adapter uses `Exp.app`; impredicative Bottom elimination uses `Exp.tapp`.
Arbitrary transformations are never injected into the target `Co` sort.
Function-valued evidence inside Church packages is represented by ordinary
term fields.

Some private implementation machinery remains necessary for dependent
syntax: a target environment for source variables, focused Church-package
elimination, a canonical value representation, and demand-passing
composition for raw transitivity middles. These are compiler implementation
details, not source-language concepts and not emitted runtime metadata. In
particular, this track does not expose the prototype `Producer`, `Demand`,
`Origin`, `Trace`, `ScopeModel`, or rule-specific `Capability` hierarchy.

The older `Full/` directory is retained temporarily as a source of proved
representation facts and regression cases. Completion of this track requires
the unrestricted GeneralPair and Record programs to compile through this
directory alone, followed by a total theorem for every existing
`LambdaPFC.Tm.Ty` derivation.
