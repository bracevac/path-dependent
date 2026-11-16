# Declarative F-sub: the same safety theorem, proved directly

This directory proves type safety of plain full F-sub on the declarative system: typing `FTy` with
its ordinary subsumption rule, over subtyping `Sub` with its transitivity rule. The proof uses no
results about certificate typing, certificate repair or `HTy`. The syntax, the reduction relation, `FTy`
and `Sub` are imported from [`../Fsub`](../Fsub/README.md), not copied, so the theorems
`fsub_progress`, `fsub_preservation` and `fsub_safety_direct` are about the same terms and the same
machine as the certificate route's `progress`, `preservation` and `safety`.

It is here as a matched control for one question: is the safety argument shorter with selective
subtyping? Counted the same way on both sides, the declarative proof takes 199 lines of declarations
and the certificate route 459. The largest part of the difference is
substitution, because a `step` stores only its two endpoints and has to be rebuilt after a
substitution. In this comparison, decidable annotation checking does not shorten the safety proof.

`Deps.lean` checks the claim that the proof here is independent of the certificate layer: it computes
the constants that the three theorems depend on and tests them against the certificate typing, the
certificate operations and their lemmas. None is reached. The shared term syntax stores a `Cert` in
its cast constructor, so the syntax of certificates and its renaming are reached, but no certificate
typing, no other operation on certificates and no lemma about them.

[`REFERENCE.md`](REFERENCE.md) has the lemmas, the dependency check and the line-by-line comparison.
From the repository root:

```sh
lake build SelectiveFsubDeclarative
lake env lean lean/Coercions/Selective/FsubDeclarative/Axioms.lean
lake env lean lean/Coercions/Selective/FsubDeclarative/Deps.lean
```
