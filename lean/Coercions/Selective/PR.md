Add selective subtyping with explicit transitivity for DOT

DOT’s declarative subtyping includes transitivity through an arbitrary
intermediate type. This change adds a hybrid typing discipline for WadlerFest DOT
in monadic normal form: a decidable, nontransitive relation handles implicit comparisons,
and casts carry certificates for further reasoning. Certificate composition
records transitivity; receiver annotations record the views needed by DOT's
type-selection rules.

The development lives under `lean/Coercions/Selective`. It preserves the full
DOT-MNF typing and subtyping judgments up to annotation, with the same types and
erased programs. Lean proves soundness and completeness of the checkers for
supplied annotations, and safety of erased programs using the existing DOT-MNF
theorem.
Checked examples show a conversion rejected by primitive subtyping and a type
selection that needs receiver evidence. They also show how one written step can
combine with the implicit comparison at an application.

The directory includes the full F-sub companion, its declarative comparison,
and a translation preserving F-sub certificates in DOT. That translation does
not reflect subtyping. The README describes the rules and results. Exploratory
designs and run logs are not part of this change.

Checked with Lean 4.29.1: `lake build`, all five Selective targets, the examples in
`Hybrid.lean`, and all five axiom audits. All pass. The audit outputs match those
before the move and use at most `propext` and `Quot.sound`. The README gives the
build commands.
