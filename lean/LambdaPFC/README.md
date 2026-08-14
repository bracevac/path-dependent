# LambdaPFC

`LambdaPFC` is a self-contained soundness proof for the current LambdaP
calculus. It contains its own intrinsically scoped syntax, declarative static
semantics, store, generalized path resolution, and CK machine. The static
judgments are proof-relevant, and the soundness proof interprets their
derivations as store-local semantic evidence.

The development proves:

- deterministic path resolution to location and type-definition referents;
- unrestricted covariance for dependent pairs, including proper and interval
  members;
- a finite semantic interpretation of every declarative subtyping derivation;
- a fundamental theorem for path typing, subtyping, and term typing under
  store valuations;
- progress and heterogeneous one-step preservation for the CK machine; and
- non-stuckness of the last state of every finite execution of a closed, well-typed
  program.

The main result is `Tm.Ty.closed_type_safety` in `SemanticSafety.lean`.

## Proof structure

An `Environment` maps each source variable to a store location that realizes
its renamed type. `Path.Ty.resolve` interprets typed paths, and
`Tau.Sub.compile` turns subtyping derivations into finite store-local
`Coercion` evidence.

`Store.Possible` and `Path.Referent.Realizes` describe the observations
available at a path referent. Coercion action
preserves these observations. Function codomain coercions and body typings are
closed over their source environments and instantiated when execution supplies
the argument location. A `MemberClosure` similarly retains a dependent-member
subtyping derivation until a stored pair supplies its first-component
location. Coercions serve as semantic evidence in the proof; the source and
runtime syntax are defined in `Syntax.lean` and `Runtime.lean`.

Dependent pairs are covariant in both components: from `S <: S'` and a member
comparison under a binder of type `S`, the rule derives
`Pair S a d <: Pair S' a d'`. Coercion action instantiates the saved member
derivation at the first component stored in the pair. Its termination follows
from the append-only store order: a pair's first component and member referent
are older than the pair cell. The mechanization uses referent stratum as the
primary termination measure and coercion-tree size for recursive calls at the
same referent.

`TermEvidence` normalizes subsumption into a final coercion at each runtime
constructor. This yields direct inversion for progress and preservation.
Allocation weakens all old evidence and records the corresponding weakening of
the final result type through `Ty.Extends`.

## Files

- `Syntax.lean`, `Context.lean`, and `Typing.lean`: source calculus.
- `Runtime.lean` and `StoreStratification.lean`: stores, path resolution, the
  CK machine, and the allocation-order lemmas used by coercion action.
- `RuntimeEquality.lean` and `Valuation.lean`: runtime path equality,
  conversion, and binder-aware valuations.
- `SemanticEvidence.lean`, `SemanticAction.lean`, and
  `SemanticTyping.lean`: finite coercions, their interpretation, and the
  runtime invariant.
- `SemanticWeakening.lean`, `SemanticTypingWeakening.lean`, and
  `SemanticAllocation.lean`: binder instantiation and store extension.
- `SemanticFundamental.lean`, `SemanticProgress.lean`,
  `SemanticPreservation.lean`, and `SemanticSafety.lean`: the fundamental
  theorem and type safety.
- `GeneralPairRegression.lean`: proper-member, interval-member, and closed
  end-to-end regressions for unrestricted dependent-pair covariance.

## Building

From the repository root:

```sh
lake build LambdaPFC
```

The paper presentation for this proof is `lambda_p.tex`. From the repository
root it can be rebuilt with:

```sh
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error \
  lean/LambdaPFC/lambda_p.tex
```
