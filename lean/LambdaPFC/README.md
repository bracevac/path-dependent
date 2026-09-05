# LambdaPFC

`LambdaPFC` is the calculus of paths through immutable dependent pairs with
the general covariant pair rule that `../LambdaP` leaves open. A pair holds
a first-component location and a member, which is a term member with a
proper-type signature or a type member with an interval signature, and the
signature may mention the first component. The pair subtyping rule is
covariant in both components and compares member signatures under the
source first-component type, so its dependent premise cannot be read until
a stored pair supplies the location it binds. Typing is proof-relevant, and
subsumption is folded into the typing rules.

## Main theorems

All in `SemanticSafety.lean`, all depending on `propext` and `Quot.sound`
only.

```
Tm.Ty.closed_progress             the initial state of a closed well-typed term progresses
Tm.Ty.closed_finite_preservation  every reached state keeps semantic typing evidence, at a weakened type
State.Steps.preservation          evidence is preserved across any finite run, up to Ty.Extends
Tm.Ty.closed_type_safety          no finite run of a closed well-typed term gets stuck
```

## Design

* **Coercions as evidence.** An `Environment` maps each source variable to a
  store location that realizes its renamed type. `Path.Ty.resolve`
  interprets typed paths, and `Tau.Sub.compile` turns every subtyping
  derivation into finite, store-local `Coercion` evidence. `Store.Possible`
  and `Path.Referent.Realizes` describe the observations available at a
  referent, and coercion action preserves them.
* **Suspended dependent premises.** Function codomain coercions and body
  typings are closed over their environments and instantiated when
  execution supplies the argument location. A `MemberClosure` keeps a
  dependent-member subtyping derivation until a stored pair supplies its
  first-component location.
* **Termination by allocation order.** A pair's first component and member
  referent are older than the pair cell. Coercion action recurses on the
  referent's stratum first and on coercion size at the same stratum
  (`StoreStratification`).
* **Normalized runtime typing.** `TermEvidence` pushes subsumption into one
  final coercion at each runtime constructor, so progress and preservation
  invert the runtime syntax directly. Allocation weakens all evidence and
  records the weakening of the result type through `Ty.Extends`.

## Modules

| module | contents |
|---|---|
| `FinFun` | finite renamings between scopes |
| `Syntax`, `Context`, `Typing` | intrinsically scoped syntax, contexts, and the proof-relevant static semantics with interval members |
| `Runtime`, `StoreStratification` | stores, path resolution to a location or a type definition, the heterogeneous CK machine, allocation-order lemmas |
| `RuntimeEquality`, `Valuation` | proof-relevant runtime path equality and type conversion, valuations of source variables |
| `SemanticEvidence`, `SemanticAction`, `SemanticTyping` | finite coercions and closures, their action and the compilation of subtyping, store-local typing of values, terms, and states |
| `SemanticWeakening`, `SemanticTypingWeakening`, `SemanticAllocation` | allocation weakening of evidence, and evidence for a freshly stored value |
| `SemanticFundamental` | the fundamental theorem `Tm.Ty.interpret` |
| `SemanticProgress`, `SemanticPreservation`, `SemanticSafety` | progress, one-step heterogeneous preservation, and closed type safety |
| `GeneralPairRegression` | dependent-pair covariance with proper and interval members |
| `RecordRegression` | a three-member record whose function consumes a value at an earlier path-dependent type member, run to `closed_type_safety` |

The regressions are hand-built derivations.

## Paper and notes

`lambda_p.tex`, "Semantic Coercions for Paths through Dependent Pairs", is
the paper presentation of this proof. `Metatheory.md` is a complete
TAPL-style walkthrough of progress and preservation, and
`MetatheorySlides.md` a condensed version that places the architecture
next to DOT and pDOT. Both also explain how `../LambdaPFCI` reuses the
architecture for intersections and unions. From the repository root:

```sh
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error lean/LambdaPFC/lambda_p.tex
```

## Building

From the repository root, `lake build LambdaPFC`. A Rocq port lives in
`../../rocq/LambdaPFC`.
