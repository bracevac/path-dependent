# LambdaPFCI

`LambdaPFCI` is `../LambdaPFC` with binary intersection and union types.
It is self-contained and leaves `LambdaPFC` unchanged as the baseline. An
intersection of proper types is realized simultaneously at one store
location, a union as a tagged realization of one alternative, and two views
of the same record spine are reconciled by a plan-directed recursive merge:
aligned proper members meet, the lower bounds of abstract members join
while their upper bounds merge recursively, and later member signatures are
interpreted under the merged prefix. A merge is an explicit structural plan
rather than a row-reordering algorithm, and it supplies no well-formedness
proof for its result, which remains a separate typing obligation.

## Main theorems

All depending on `propext` and `Quot.sound` only.

```
Tm.Ty.interpret                   the fundamental theorem                 (SemanticFundamental)
State.Evidence.progress           a state with evidence is final or steps (SemanticProgress)
State.Evidence.preservation       one heterogeneous step preserves evidence, up to Ty.Extends (SemanticPreservation)
Tm.Ty.closed_progress             the initial state of a closed well-typed term progresses (SemanticSafety)
Tm.Ty.closed_finite_preservation  every reached state keeps evidence at a weakened type (SemanticSafety)
Tm.Ty.closed_type_safety          no finite run of a closed well-typed term gets stuck (SemanticSafety)
```

## Design

The architecture is that of `LambdaPFC`: subtyping derivations compile to
store-local coercions, dependent premises are suspended until a stored pair
supplies a location, termination follows the allocation order, and runtime
typing normalizes subsumption into one coercion per constructor. What is
new is the merge judgment `Tau.Merge`, which at each matching pair label
first merges the stored predecessor, then extends the environment with the
merged location and continues with the dependent member. It subsumes the
one-slot term-member, type-member, and first-component rules of earlier
versions.

## Modules

| module | contents |
|---|---|
| `FinFun` | finite renamings between scopes |
| `Syntax`, `Context`, `Typing` | intrinsically scoped syntax, contexts, and the static semantics with intersections, unions, and aligned merges |
| `Runtime`, `StoreStratification` | stores, path resolution, the CK machine, allocation-order lemmas |
| `RuntimeEquality`, `Valuation` | proof-relevant runtime path equality and type conversion, valuations |
| `SemanticEvidence`, `SemanticAction`, `SemanticTyping` | coercions and closures, their action and the compilation of subtyping and merges, store-local typing |
| `SemanticWeakening`, `SemanticTypingWeakening`, `SemanticAllocation` | allocation weakening, evidence for a freshly stored value |
| `SemanticFundamental`, `SemanticProgress`, `SemanticPreservation`, `SemanticSafety` | the fundamental theorem and type safety |
| `GeneralPairRegression` | dependent-pair covariance with proper and interval members |
| `RecordRegression` | a three-member record with selection through non-adjacent members |
| `IntersectionRegression` | a closed self-application using one closure through two incomparable function views |
| `RecordIntersectionRegression` | a same-label record intersection selected through two aliases, then merged into one |
| `AlignedRecordIntersectionRegression` | a two-member telescope whose aligned outer views merge their record tails |
| `RecursiveRecordMergeRegression` | a recursive merge combining record tails and outer signatures at once |
| `TypeMemberIntersectionRegression` | an abstract-member merge used through the shared lower bound and both upper views |
| `TypeMemberUnionRegression` | an abstract-member merge with distinct lower bounds, used through their union |

The regressions are hand-built derivations driven to `closed_type_safety`.

## Paper

`lambda_p.tex`, "Semantic Coercions for Paths through Dependent Pairs", in
its intersection-and-union version. From the repository root:

```sh
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error lean/LambdaPFCI/lambda_p.tex
```

## Building

From the repository root, `lake build LambdaPFCI`.
