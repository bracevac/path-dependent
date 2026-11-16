Selective subtyping with explicit transitivity for F-sub and DOT

DOT’s declarative subtyping includes transitivity through an arbitrary
intermediate type. Selective subtyping makes the automatic relation
nontransitive and has casts carry certificates for further reasoning. This
change adds a self-contained calculus of this kind for full F-sub and for
WadlerFest DOT in monadic normal form. Each has only the certificate forms
`step[S,T]` and `c ; d`, a type safety proof from its own typing, and a
correspondence with the plain source system whose elaboration is a function on
typing derivations.

`lean/Coercions/Selective/Fsub` is the F-sub calculus. Progress, preservation
and safety are proved directly on erased terms. `typability_iff` shows that
declarative F-sub types a term exactly when it is the erasure of an annotated
term of the same type, and `FDer.elab` computes the annotated term from a
typing derivation.

`lean/Coercions/Selective/Dot` is the DOT calculus. A type selection reads its
bounds from a type of its receiver, and that type may need a conversion. The
conversion is a cast on the receiver: a receiver is a path `x ▷ c ▷ …`, and the
endpoints written in a step select on such paths. Path typing keeps DOT's
`Rec-I`, `Rec-E` and `And-I` and has no subsumption. Progress, preservation and
safety are proved directly on the machine of erased terms, by way of inert
contexts and tight typing, without the existing DOT-MNF or FCdot theorems.
`Dot/Vanilla` proves `typability_iff` and `coercion_iff` against the DOT-MNF of
this repository; `Sub.toCert` and `HasTy.elab` compute certificates and
annotated terms from DOT-MNF derivations, with `Sub.trans` mapped to `;`. The
two machines take the same steps, which gives `dot_safety_direct`: type safety
of DOT-MNF without the translation to FCdot. No algorithm for the primitive
relation or for typing is given for this calculus.

Both preservation theorems prove that an annotation of the reduct exists; they
do not compute it.

The modules directly in `lean/Coercions/Selective` are an earlier design for
DOT, `H`, kept as explored work. It covers DOT-MNF exactly and has verified
checkers, but it needs receiver evidence beyond `step` and `;`, and its safety
uses the existing DOT-MNF theorem. The directory also has the declarative
comparison for F-sub, a comparison with FCsub evidence, and a translation of
F-sub certificates into `H`. The READMEs describe the rules and results.
Exploratory designs and run logs are not part of this change.

Checked with Lean 4.29.1: `lake build`, all seven Selective targets, and the
axiom audits. All pass, and the audits use at most `propext` and `Quot.sound`.
The READMEs give the build commands.
