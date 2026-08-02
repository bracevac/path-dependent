# LambdaPFC

`LambdaPFC` is a self-contained soundness proof for the current LambdaP
calculus. It contains its own intrinsically scoped syntax, declarative static
semantics, store, path lookup, and CK machine. The proof is organized around
proof-relevant derivations and store-local semantic evidence.

The development proves:

- resolution and determinism for term paths and generalized endpoints;
- a finite semantic interpretation of every declarative subtyping derivation;
- a fundamental theorem for path typing, subtyping, and term typing under
  store valuations;
- progress and heterogeneous one-step preservation for the CK machine; and
- non-stuckness at every finite execution endpoint of a closed, well-typed
  program.

The main result is `Tm.Ty.closed_type_safety` in `SemanticSafety.lean`.

## Proof structure

`Derivations.lean` gives proof-relevant counterparts of the declarative
judgments. An `Environment` maps each source variable to a store location that
realizes its renamed type. `PathCode.resolve` interprets typed paths, and
`SubCode.compile` turns subtyping derivations into finite store-local
`Coercion` evidence.

`Store.Possible` and `Path.Endpoint.Realizes` describe the observations
available at a location or generalized path endpoint. Coercion action
preserves these observations. Function codomain coercions and body typings are
closed over their source environments and instantiated when execution supplies
the argument location. Coercions serve as semantic evidence in the proof; the
source and runtime syntax are defined in `Syntax.lean` and `Runtime.lean`.

`TermEvidence` normalizes subsumption into a final coercion at each runtime
constructor. This yields direct inversion for progress and preservation.
Allocation weakens all old evidence and records the corresponding weakening of
the final result type through `Ty.Extends`.

The dependent-pair member rule remains the restricted source rule from
`Typing.lean`: changing the member requires a singleton first component and an
explicit comparison after opening at that path. Soundness of a generalized
rule for an arbitrary first-component type remains open.

## Files

- `Syntax.lean`, `Context.lean`, and `Typing.lean`: source calculus.
- `Runtime.lean`: stores, path lookup, and the CK machine.
- `Derivations.lean`, `StaticMetatheory.lean`, and `CodeMetatheory.lean`:
  proof-relevant elaboration and scoped renaming.
- `RuntimeEquality.lean` and `Valuation.lean`: runtime path equality,
  conversion, and binder-aware valuations.
- `SemanticEvidence.lean`, `SemanticAction.lean`, and
  `SemanticTyping.lean`: finite coercions, their interpretation, and the
  runtime invariant.
- `SemanticWeakening.lean`, `SemanticTypingWeakening.lean`,
  `SemanticClosure.lean`, and `SemanticAllocation.lean`: binder instantiation
  and store extension.
- `SemanticFundamental.lean`, `SemanticProgress.lean`,
  `SemanticPreservation.lean`, and `SemanticSafety.lean`: the fundamental
  theorem and type safety.

## Building

From the repository root:

```sh
lake build LambdaPFC
```

The paper presentation for this proof is `lambda_p.tex`. From the repository
root it can be rebuilt with:

```sh
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error \
  LambdaPFC/lambda_p.tex
```
