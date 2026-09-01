# Coercions

Lean formalizations of type-preserving translations from DOT fragments into
explicit-coercion calculi.

- `FCsub` is the standalone type-constraint target.
- `ManySortedFC` is the standalone target for type and capture names,
  constraint telescopes, checked evidence, structural adapters, packages, and
  existential opening.
- `DOT` contains the source calculi.
- `Translation` contains derivation-directed compiler case studies.

The cumulative compiler's M10/M11 core covers a closed, acyclic,
captured-intersection general-expression fragment. Ordinary applications may
contain computations. Object-producing computations must be opened explicitly
before member selection or negative object application; only canonical object
literals and already-open stable roots are direct object arguments. That
nonrecursive core does not include objects nested inside member bounds or
runtime representations, or dependent object-consumer results.

Positive objects compile to existential models and one runtime payload.
Negative object parameters compile to static model abstraction followed by an
ordinary runtime function. Every cumulative payload has an explicit capture
name `C_rep`, with independently checked exactness and containment evidence.
Generated terms are rechecked by the standalone ManySortedFC checker and are
related to the source language's independently defined erasure. Direct object
application introduces no package/open redex. The tested identity-like direct
paths preserve erasure literally; the general statement is administrative
equality because structural function and modal adapters can eta-expand values.

`Translation/ManySorted/RecursiveObjects` extends that cumulative compiler
with guarded recursive object signatures. Recursive type members compile to
recursive projections and checked fold/unfold evidence. Recursive capture
members are interpreted as simultaneous equations: construction chooses
finite capture expressions from the ambient context and independently proves
every instantiated equation before packaging. This gives existential model
semantics; the target does not manufacture a least, greatest, or generative
capture fixed point.

Recursive payloads may be ordinary values, including functions whose types
refer to the chosen recursive model. Their actual capture is represented by
the existing unique `C_rep` name. The object theory checks `C_rep` against the
advertised capture, which may itself be a recursive member. Positive packaging
separately checks `C_rep` against an ambient package envelope; this envelope
controls evaluation of the existential package but is not the capture exposed
to negative consumers. A recursive literal is introduced positively as one
existential model and one payload. Negative or path-dependent use requires a
source `objectLet`, whose target open establishes one stable identity for every
member. Packaging, evidence, and opening add no runtime computation beyond
that source binding, and emitted artifacts are checked by ManySortedFC.
Member references take source paths, so selecting from an unbound recursive
literal is not representable in the typed source AST.
Recursive finalization erases literally to the already compiled payload, so
an exact payload compilation gives exact recursive-object erasure. The
representative package/open programs satisfy literal source-to-target
erasure; the unrestricted cumulative compiler still states administrative
equality because older function and modal adapters may eta-expand values.
The recursive exactness layer proves packaging and explicit opening preserve
literal equality compositionally, and includes a checked adapter
counterexample showing why no unconditional theorem can cover every inherited
typing derivation. Artifact-level conservativity relates exact cumulative
results to independently accepted M10 and M11 results by literal erasure.

This stage does not add recursive runtime records, a runtime self/letrec
binder, projections from unstable expressions, or a generative capture
fixed-point primitive. It also does not prove semantic consistency of every
recursive type equation or a full DOT tight-typing theorem: only supplied,
independently checkable models can be packaged.

The classifier-projection extension adds a closed classifier tree, ground
kind intersection and subtraction, and `Capture.project` to ManySortedFC.
The standalone checker recomputes equivalence, subkind, emptiness, and
disjointness conditions for projection evidence. A small source layer lowers
each `.only`/`.except` chain to one projection. Its target witness is checked
independently; the paired source and target programs have literally equal
erasures and perform beta and zeta steps.
This layer is not a general source-term compiler and does not include
kind-bounded capture variables, classifier inference, handlers or intercepts,
or full Capless(K) typing.

`All.lean` imports the complete development.
