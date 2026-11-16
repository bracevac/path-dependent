# Selective subtyping

Selective subtyping separates the comparisons a type checker performs automatically
from the compositions a program must supply. The automatic relation, written
`Γ ⊢ S ≤₀ T`, is decidable and is not transitive. A cast carries a certificate for
the additional reasoning. Composing certificates records the intermediate type of a transitivity
derivation, so checking composition does not search for it.

The aim is a self-contained calculus of this kind for each of two source
systems: full System F-sub, and WadlerFest DOT in monadic normal form. Each
calculus should have only the two certificate forms `step[S,T]` and `c ; d`, a
safety proof from its own typing, and a correspondence with the plain source
system. For F-sub this is done. For DOT it is open: the DOT part of this
directory is a first design, called `H`, that does not meet the aim.

## F-sub

[`Fsub/`](Fsub/README.md) defines the calculus for full F-sub, with its own
syntax, typing and reduction. Its certificates are exactly `step` and `;`, and
its primitive relation is not transitive (`primitive_nontrans`). Term typing has
no subsumption rule. One primitive comparison is implicit at the argument of an
application and at the bound of a type application.

Progress, preservation and safety are proved directly on erased terms, for terms
typed in the empty term context under any type context. Preservation proves that
the reduct has an annotation; it does not compute one.

`typability_iff` relates the calculus to declarative F-sub, whose typing has a
subsumption rule over subtyping with transitivity:

```text
Γ; Δ ⊢F e : T    ↔    ∃ h, erase(h) = e ∧ Γ; Δ ⊢ h : T
```

From left to right this is an elaboration that keeps the type and the program.
For terms it is a theorem that an annotated term exists, and not a function,
because declarative typing is a proposition. For subtyping, `Sub.toCert` is a
function from derivations to certificates. A computable elaborator for terms is
not built.

## DOT: the explored design `H`

`H` uses the existing `DotMNF` types and contexts, including dependent
functions, recursive objects, intersections, and type members with both bounds.
Every DOT-MNF typing has an annotated term at the same type whose erasure is the
original program. The annotations change what the checker is given; they erase
before execution on the DOT-MNF machine.

`H` differs from the calculus aimed at in two ways. Its certificates are not
only `step` and `;`: a type selection carries evidence for its receiver, as
described below. And it has no safety proof of its own: `compiled_safety` erases
the program and uses the DOT-MNF theorem. The receiver examples below concern the
primitive relation that `H` fixes. They do not show that `step` and `;` are too
weak for DOT under another primitive relation or other implicit rules.

### Primitive subtyping and composition

`Prim` contains structural subtyping rules and rules for the bounds exposed by a
variable's declared type. Exposing a member can pass through intersections and
open a recursive type at that variable. A selection step uses the exposed bound
itself: from a declaration `{A : L..U}`, it gives `L ≤₀ x.A` or `x.A ≤₀ U`.
There is no rule that guesses an intermediate type. Transitivity is not admissible,
as witnessed by a context with a closed realization.

The two basic certificate forms are:

```text
Γ ⊢ S ≤₀ T                         Γ ⊢ c : S ⇒ M    Γ ⊢ d : M ⇒ T
──────────────────────             ──────────────────────────────
Γ ⊢ step[S,T] : S ⇒ T              Γ ⊢ c ; d : S ⇒ T
```

The endpoints of a certificate are determined by its syntax. Checking `c ; d`
checks both certificates and requires their middle types to agree syntactically.

Term typing uses primitive subtyping implicitly at two places: the argument of
an application, and the subject of a term cast before its written certificate.
Each such boundary permits one primitive comparison. There is no general
subsumption rule. A variable otherwise has its declared type. The callee’s atom
must already have function type; a projection reads fields exposed by its atom’s
type, including through intersections and recursive types. Further conversions
require annotations.

For example, consider:

```text
b : {B : ⊥..⊤}, c : {C : ⊥..⊤}, x : {A : b.B..c.C},
k : ∀(_ : c.C) ⊤, z : b.B
```

Here `b.B ≤₀ x.A` and `x.A ≤₀ c.C`, but `b.B ≤₀ c.C` fails. The application
`k z` is rejected. Both of the following are accepted and erase to `k z`:

```text
k (z ▷ (step[b.B,x.A] ; step[x.A,c.C]))
k (z ▷ step[b.B,x.A])
```

The first writes the whole chain. The second writes the first step and leaves
the second to the application's primitive comparison. A source transitivity
derivation translates to `;`, but an annotation of the same program need not
write every step of that derivation. These examples are checked in
[`Hybrid.lean`](Hybrid.lean).

### Type selections need receiver evidence

DOT's selection rules depend on the type of the receiver. Its declared type
need not expose the member used in a derivation. For example:

```text
R = {A : ⊥..{a : ⊤}}
w : {B : ⊥..R}, y : w.B, u : y.A
```

DOT derives `y.A <: {a : ⊤}` by first typing `y` at `R`. The primitive relation
only reads members exposed by the declared type `w.B`, so it cannot take that
selection step. For this `Prim`, no chain of primitive steps connects the two
endpoints either.

The certificate therefore records the receiver's view:

```text
r = y ▷ step[w.B,R]
(u ▷ selU(r,A,{a : ⊤})).a
```

`selU` checks that `r` is evidence for the required member of `y`. The whole term
erases to `u.a`. Receiver evidence always refers to the same variable: casts,
folding and unfolding recursive types, and combining intersection views do not
introduce a new path. The certificate language also places these member steps
under structural type constructors, including dependent function binders. These
forms account for the DOT reasoning that the two constructors `step` and `;`
alone do not express with this primitive relation.

### Formal results of `H`

The central equivalences are `coercion_iff` and `typability_iff`:

```text
(∃ c, Γ ⊢ c : S ⇒ T)                 ↔  Γ ⊢DOT S <: T
(∃ h, erase(h) = t ∧ Γ ⊢H h : T)     ↔  Γ ⊢DOT t : T
```

They range over the full DOT-MNF judgments. `Annotate.lean` also constructs
certificates and annotated terms from source derivations. Its translation of
`Sub.trans d₁ d₂` is definitionally `d₁.toCert ; d₂.toCert`.

`prim?_iff`, `synthC_iff`, and `synthTm_iff` prove that the primitive, certificate,
and annotated-term checkers are sound and complete for their judgments. This is
checking supplied annotations: it does not search for a certificate for an
arbitrary DOT subtyping goal. The term checker returns a finite list of possible
types; no efficiency bound is claimed.

`compiled_safety` proves that a closed, well-typed annotated program cannot get
stuck after erasure. It uses the existing DOT-MNF safety theorem. Typed variable
substitution preserves the existence of an annotation by translating through
DOT-MNF and annotating again; it does not establish a local repair algorithm for
the original certificates.

## Sources and build

[`Hybrid.lean`](Hybrid.lean) collects the main statements and examples of `H`.
`Prim.lean`, `Syntax.lean`, and `Typing.lean` define the calculus;
`Check.lean` and `Typer.lean` implement its checkers;
`Sound.lean`, `Complete.lean`, and `Annotate.lean` relate it to DOT-MNF.
[`REFERENCE.md`](REFERENCE.md) lists every module and theorem.

[`Fsub/`](Fsub/README.md) is the F-sub calculus. It proves certificate
substitution, narrowing, inversion, and type safety. [`Bridge/`](Bridge/README.md)
preserves F-sub primitive steps and certificates in `H`, mapping composition to
composition. The encoding does not
reflect subtyping: DOT relates some encoded types that F-sub keeps separate.
[`FsubDeclarative/`](FsubDeclarative/README.md) contains the matched declarative safety proof, and
[`FsubCompare/`](FsubCompare/README.md) compares certificates with the existing FCsub development.

From the repository root:

```sh
lake build Selective
lake env lean lean/Coercions/Selective/Axioms.lean
lake build SelectiveFsub SelectiveFsubDeclarative SelectiveFsubCompare SelectiveBridge
```

The axiom audits use at most `propext` and `Quot.sound`.
