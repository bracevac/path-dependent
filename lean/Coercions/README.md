# Coercions

Lean formalizations of type-preserving translations from DOT fragments into
explicit-coercion calculi.

- `FCsub` is the standalone type-constraint target.
- `ManySortedFC` is the standalone target for type and capture names,
  constraint telescopes, checked evidence, structural adapters, packages, and
  existential opening.
- `DOT` contains the source calculi.
- `Translation` contains derivation-directed compiler case studies.

The cumulative compiler in `Translation/ManySorted/ModalIntersections` covers
a closed, acyclic, captured-intersection general-expression fragment. Ordinary
applications may contain computations. Object-producing computations must be
opened explicitly before member selection or negative object application;
only canonical object literals and already-open stable roots are direct object
arguments. Recursive objects, and objects nested inside member bounds, runtime
representations, or dependent object-consumer results, are not in this
compiler fragment.

Positive objects compile to existential models and one runtime payload.
Negative object parameters compile to static model abstraction followed by an
ordinary runtime function. Every cumulative payload has an explicit capture
name `C_rep`, with independently checked exactness and containment evidence.
Generated terms are rechecked by the standalone ManySortedFC checker and are
related to the source language's independently defined erasure. Direct object
application introduces no package/open redex. The tested identity-like direct
paths preserve erasure literally; the general statement is administrative
equality because structural function and modal adapters can eta-expand values.

`All.lean` imports the complete development.
