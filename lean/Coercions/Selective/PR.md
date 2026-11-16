Selective subtyping with explicit transitivity: F-sub, and a first design for DOT

DOT’s declarative subtyping includes transitivity through an arbitrary
intermediate type. Selective subtyping makes the automatic relation decidable
and nontransitive, and has casts carry certificates for further reasoning. The
aim is a self-contained calculus of this kind for full F-sub and for WadlerFest
DOT in monadic normal form, each with only the certificate forms `step[S,T]` and
`c ; d`, a safety proof from its own typing, and a correspondence with the plain
source system. The F-sub calculus is done. The DOT calculus is still open, and
work on it continues in this pull request.

`lean/Coercions/Selective/Fsub` is the F-sub calculus. Its certificates are
exactly `step` and `;`. Progress, preservation and safety are proved directly on
erased terms. `typability_iff` shows that declarative F-sub types a term exactly
when it is the erasure of an annotated term of the same type. The elaboration is
a function from typing derivations to annotated terms (`FDer.elab`).

`lean/Coercions/Selective` holds a first design for DOT, called `H`. It preserves
the full DOT-MNF typing and subtyping judgments up to annotation, with the same
types and erased programs, and its checkers are sound and complete for supplied
annotations. It is not the calculus aimed at: a type selection carries evidence
for its receiver beyond `step` and `;`, and safety of erased programs uses the
existing DOT-MNF theorem.

The directory also includes the declarative comparison for F-sub, a comparison
with FCsub evidence, and a translation preserving F-sub certificates in `H`. That
translation does not reflect subtyping. The README describes the rules and
results. Exploratory designs and run logs are not part of this change.

Checked with Lean 4.29.1: `lake build`, all five Selective targets, the examples in
`Hybrid.lean`, and all five axiom audits. All pass. The audit outputs match those
before the move and use at most `propext` and `Quot.sound`. The README gives the
build commands.
