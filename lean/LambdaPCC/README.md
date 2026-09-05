# LambdaPCC

`LambdaPCC` is the calculus of paths through immutable dependent pairs with
capture checking. A type pairs a capture set with a shape, and term typing
assigns a use set, an upper bound on the capabilities used during
evaluation. Capture sets contain term paths of any length and selections of
abstract capture-set members. A pair member may be a term, an abstract type
member, or an abstract capture-set member, the latter two given by lower and
upper bounds, and a member signature may depend on the first component,
capture sets included. Pair covariance is uniform across the three member
kinds and compares the member under the source first-component type.
Subcapturing places the singleton capture set of a term path below the
capture set of its type, relates a capture-set selection to its bounds,
and contracts projections and selections to their root.

The runtime has no primitive capability operations, so the coverage result
below accounts for the paths inspected by application and makes no
platform-effect claim. The capture set recorded for a value is the one its
introduction rule assigns, and the static semantics does not require it to
be minimal.

## Main theorems

All depending on `propext` and `Quot.sound` only.

```
Tm.Ty.closed_progress                          the initial state progresses                        (CaptureSafety)
Tm.Ty.closed_finite_preservation               every reached state keeps joint type-and-use evidence (CaptureSafety)
Tm.Ty.closed_type_safety                       no finite run of a closed well-typed term gets stuck (CaptureSafety)
Cap.Tm.Ty.closed_finite_application_coverage   both operand paths of every application step are covered by the transported use set (CaptureBounds)
Cap.Tm.Ty.closed_finite_returned_capture_bound the capture set assigned to a returned value subcaptures that of its result type (CaptureBounds)
```

## Design

The architecture is that of `../LambdaPFC`: subtyping and subcapturing
derivations are interpreted as store-indexed coercions and relations, and
coercion action is well founded in the allocation order of the store. An
annotated store records, for each allocated value, the capture set assigned
by its introduction rule, and value typing keeps that set together with a
subcapturing derivation to the capture set of the assigned type. Coercion
action preserves the assigned set through dependent functions, pairs, and
abstract members. The general pair rule applies its first-component
coercion at the stored component and instantiates its member coercion at
the same location.

## Modules

| module | contents |
|---|---|
| `FinFun` | finite renamings between scopes |
| `Syntax`, `Context`, `Typing` | syntax with capture sets and member kinds, contexts, path typing, subcapturing, subtyping, well-formedness, and term typing with use sets |
| `Runtime`, `StoreStratification` | stores, resolution of paths to locations, type definitions, or capture-set definitions, the CK machine, allocation-order lemmas |
| `RuntimeEquality`, `Valuation` | proof-relevant runtime path equality and type conversion, valuations |
| `CaptureEvidence`, `CaptureAction`, `CaptureStatic`, `CaptureCoercion` | capture-aware evidence and worlds, composition and capture relations, environments and path interpretation, member closures and termination measures |
| `CaptureWeakening`, `CaptureAllocation`, `CaptureTyping` | weakening across a fresh cell, valid store entries, and the joint type-and-use invariant `TermEvidence` |
| `CaptureInterpretation`, `CapturePreservation`, `CaptureSafety` | interpretation of source typing, progress and one-step preservation, finite preservation and closed type safety |
| `CaptureBounds` | application coverage and the returned-value capture bound |
| `CaptureRegression` | capture-set-member selection, capture-set-member pair covariance, capture-dependent result types, root contraction |
| `GeneralPairRegression` | closed allocation traces for pair covariance at both interval-member forms and for selection of a stored capture-set member |
| `RecordRegression` | a right-nested record whose function consumes a value at an earlier path-dependent type member, run to `closed_type_safety` |

The regressions are hand-built derivations.

## Paper

`paper/paper.tex`, "Capture Checking for Path-Dependent Pairs", presents
this calculus and its proof, and its abstract's claims are the five
theorems above. Build it with `make -C lean/LambdaPCC/paper` from the
repository root.

## Building

From the repository root, `lake build LambdaPCC`. A Rocq port lives in
`../../rocq/LambdaPCC`.
