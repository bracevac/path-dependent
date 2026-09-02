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

`Translation/ManySorted/CheckedFrontend` puts an executable checked boundary
in front of the cumulative compiler. Its inputs are intrinsically scoped but
explicitly annotated. First-order certificate syntax supplies inclusions,
intervals, value adapters, modes, and all ordered separation pairs; the front
end checks these trees structurally without proof search and returns an
ordinary source typing derivation. The supported fragment includes runtime
and static functions, application, plain and package-opening lets, packages,
modal lock/unlock, and explicit use widening. Object construction, member
selection, and recursive objects are outside the raw syntax; their explicit
unsupported sentinels test only boundary diagnostics. Enclosing-lock lookup
and quantifier/modal adapter certificates are also deferred. Lexical static
lower and upper bounds are checked by exact named lookup. A successful
pipeline result retains the exact source-checking equation and records
standalone ManySortedFC checker acceptance.
Global compiler correctness remains `AdministrativeEq`.

`Translation/ManySorted/CertificateStudy` measures emitted artifacts rather
than estimating them from source syntax. Its checked normalization pass first
checks each logical certificate, removes only administrative proof structure,
then rechecks the result at the same proposition. The rechecked corpus shrinks
from 94 to 6 evidence nodes; the real compiler-emitted certificate in that
corpus is already minimal at 3 nodes. A separate whole-artifact traversal
reports a syntax-only opportunity of 76 to 72 nodes over 51 evidence trees.
Adapter measurements compare ordinary erasure with a clearly labeled
identity-adapter baseline, so eta-expansion is counted rather than hidden.
These are structural AST counters, not serialized sizes or execution-time
measurements.
`Tools/checker-footprint.sh` reproducibly reports 1,699 physical lines and
78,142 bytes for its explicit executable-checker module list; this is a
selected module footprint, not a dependency closure or minimized trusted
computing base.

The Capybara-inspired benchmark checks two nonempty, same-root read-only
callback captures, invokes both callbacks sequentially, and passes through a
repeated-label object package/open before runtime execution. The emitted
artifact is independently checked and its erasure performs genuine force,
beta, and zeta steps. A writable view of the same root is rejected. This is a
static access-separation case study: the shared runtime still has no
concurrency, mutation, allocation, consumption, or freshness semantics.

The classifier extension follows the classifier paper's distinction between
nodes, kinds, and captures. A `Classifier` is a nominal tree node. A
`Classifier.Kind` is a closed region of that tree, represented by finite
unions of subtrees with exclusions. Classifier kinds occur as filters on
captures; they are not variables or a third `StaticSort`.

Surface `.only[A].except[B]` chains lower to one ground `Capture.project`.
A kind-bounded source capture variable `c : K` lowers to an ordinary target
capture symbol plus the checked proposition `captureHasKind(c, K)`. From that
evidence the checker can certify projection completeness,
`c.project(K) = c`. Ground equivalence, subkind, emptiness, and disjointness
side conditions are recomputed by the standalone checker. The access model
tests a nonempty capture containing an IO capability and a Control capability:
`only[Shared].except[Control]` retains the former and removes the latter. The
checked term regression uses the retained callback as a real free root, has
literal source/target erasure equality, and performs three beta steps.

This is not the complete Capless(K) calculus: it does not implement the full
source kind-inference/subcapturing system, labels, handlers or intercepts, or
the paper's safety semantics. Scala classifier declarations are also outside
this formal layer. A name such as `this.C` would first have to resolve to a
concrete nominal node; abstract or generative classifier members require a
separate design for ancestry, aliasing, and identity.

`All.lean` imports the complete development.
