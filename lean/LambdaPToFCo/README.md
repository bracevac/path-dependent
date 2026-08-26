# LambdaPToFCo

This directory contains three derivation-directed compilation tracks:

- the established restricted compiler targets the original `SystemFCo`;
- `Full/` is the proof-first prototype for the existing `LambdaPFC` calculus
  and targets the separate experimental `SystemFCoExt` library; and
- `Direct/` is the replacement constructor-complete compiler. It targets the
  unchanged original `SystemFCo` and emits ordinary target syntax directly.

The original `SystemFCo` is intentionally frozen. The earlier Full prototype
forced every source subtyping derivation into the target coercion sort and
therefore introduced computational `Co.adapter` and `Co.bottom` constructors
in `SystemFCoExt`. That restriction was unnecessary. In the direct compiler,
dependent unpack/repack transformations are ordinary typed target functions,
and impredicative Bottom elimination is ordinary type application. Target
typing is proved separately from syntax generation. `SystemFCoExt` remains as
an experiment and source of proved representation lemmas, not as the target
required by the final compiler.

## Restricted compiler

The representation is syntactic and object-language based. An abstract type
member with bounds `L..U` is compiled to a Church package containing:

- a hidden target type `X`;
- an explicit coercion `L => X`;
- an explicit coercion `X => U`; and
- the first-component payload.

When a source package is bound, the compiler unpacks it once. Subsequent uses
of `p.A`, its lower bound, its upper bound, and `p.fst` are lexical target
type/coercion/term variables. Source subsumption is compiled to `Exp.cast`.
There is no store-indexed realization judgment, semantic coercion action, or
runtime subtyping in this translation.

Current milestones:

- `Source.lean` isolates exact abstract-member packages and embeds the small
  proof-relevant source layer back into `LambdaPFC`.
- `ExactPackage.lean` compiles exact package construction to
  `Exp.packMember`; its regression exposes literal lower/upper target coercion
  variables and uses their composition in a cast.
- `Fragment.lean` defines a proof-relevant source fragment and embeds every
  fragment rule into `LambdaPFC`.
- The static compiler handles fixed-first, fixed-label abstract intervals.
  It unpacks each package once and gives its selected type, lower coercion,
  upper coercion, and payload stable lexical target slots. Its coherence
  theorem is preserved by ordinary and interval-package binders.
- `CoercionTranslation.lean` compiles every fragment subtyping derivation to
  an actual `SystemFCo.Co` term. `TermTranslationSoundness.lean` proves that
  every fragment typing derivation compiles to a well-typed target term.
- Package introduction remains exact. The source package-covariance rule
  widens `[L1,U1]` to `[L2,U2]` from `L2 <: L1` and `U1 <: U2`; it compiles
  to the real target syntax `Co.member`, with reflexive payload evidence
  because this milestone keeps the first path and label fixed.
- `IntervalPackageRegression.lean` checks a closed program whose lower and
  upper adapters both compile to non-reflexive `Co.arrow` trees containing
  `Co.top`, and whose package conversion is literally a `Co.member` node.
- `TermTranslationSoundnessRegression.lean` checks the closed compiler on a
  program that constructs an exact member, selects through both bounds, and
  applies a function. `OperationalMacros.lean` proves the seven target steps
  by which an exact package binding opens its five lexical interface slots.
- `OperationalAdmissibility.lean` selects a smaller executable core from the
  static `Fragment`. Its proof-relevant evidence exposes the canonical value
  and result-shape assumptions needed to invert native CK steps; it does not
  restrict the static translation theorem.
- `OperationalStateImage.lean` relates a source CK state to a closed target
  expression with an execution zipper, recursive store/environment
  coherence, and the result capabilities needed across allocation, return,
  and wrapper-aware function application.
- `OperationalOneStepPreservation.lean` proves unconditional one-step image
  preservation for every CK constructor in that executable core. Its public
  theorem `source_not_goesWrong` rules out a stuck endpoint for every closed,
  well-typed, operationally admissible program.

The static fragment includes nondependent functions, lets, exact package
construction, flat abstract type-member intervals, direct selection,
fixed-first package covariance, and subsumption. Changing a pair's first
component, dependent member transport, nested record spines, full dependent
function results, and intersections/unions remain later extensions. The
operationally admissible core is narrower still: applications and lets have
direct typing heads, package values are exact, and its explicit shape/spine
evidence makes CK inversion total.

Every preserved source step carries `SystemFCo.Exp.Steps` between the target
images, so the operational development proves compiler correspondence rather
than merely target typability. The source-progress fact used to rule out
`GoesWrong`, however, is proved directly from the source origin, store, and
environment evidence retained by `StateImage`. Standalone `SystemFCo` safety
is available, but it is not a logical premise of this source-safety proof.
No runtime realization judgment or runtime subtyping is used.

## Full compiler track

`Full.lean` aggregates the new compiler development. It does not assume
`Fragment` or `OperationallyAdmissible`: its source views cover every existing
`LambdaPFC.Tm.Ty` constructor, and its producer/demand interfaces retain the
hidden identities needed by dependent selections, functions, and pairs.

The full track is still a draft. It currently includes the separate target
metatheory, faithful mixed-telescope value models, scoped path packages,
demand-directed subtyping kernels, direct term introductions, and a
one-suffix normalized term-compilation boundary. Construction-certified
proper paths cover variables, both forms of `fst`, proper-member `sel_r`, and
`sel_l` while retaining their exact zipper and model history.

The existing unrestricted `GeneralPairRegression.term` now compiles
end-to-end to a closed, well-typed `SystemFCoExt` expression, including both
dependent interval-pair subsumptions and final `let` closure. The nested
record acceptance chain has compiled its implementation abstraction and
first type-member value through the literal source rule
`.pair (.widen .var) .refl`, with each actual package threaded into the next
`let` scope.

Remaining work is explicit: certify the actual Church package behind
interval-member `sel_r`; finish the later nested-record values and
application; turn the sealed path/subtyping/introduction pieces into total
dispatchers; and then lift unrestricted CK image preservation. None of those
claims is implied merely by the completed GeneralPair regression.

## Capture-aware target follow-up

After the full `LambdaPFC` compiler is complete, capture-bearing source
versions will target a separate, future `SystemFCoCap` calculus. This leaves
both the original `SystemFCo` and the current `SystemFCoExt` unchanged. The
following is a design boundary, not an implemented target or compiler claim.

Capture expressions use one pair of same-category metavariables throughout:

```text
C, D ::= empty | κ | atom(α) | C union D
```

Here `α, β` range over target identity types, `κ` is a bound capture variable,
and `ε` ranges over evidence. The target propositions distinguish identity
equality `α ≡ β`, capture equality `C ≡ D`, and subcapturing `C ⊆ D`. A source
singleton capture `{p}` translates to `atom(I_p)`, where `I_p` is the stable
hidden identity type assigned to `p`. Identity equality entails atom
congruence,

```text
α ≡ β  implies  atom(α) ≡ atom(β),
```

There is no automatic converse deriving `α ≡ β` from
`atom(α) ≡ atom(β)`: captures may also contain variables and unions. Thus `C`
and `D`, and only those letters, serve as capture-expression metavariables.
