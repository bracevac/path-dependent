# Oopsla16

The DOT calculus of Rompf and Amin, *Type Soundness for Dependent Object
Types* (OOPSLA 2016), ported from the authors' Coq artifact
(`TiarkRompf/minidot` at `ef1143d`, `oopsla16/dot.v`). Unlike WadlerFest DOT it
has recursive subtyping (`stp_bindx`, `stp_bind1`). It is intrinsically scoped
and shares only `FCdot/Debruijn.lean` with the rest of the development.

| module | contents |
|---|---|
| `Syntax`, `Structural`, `SubstLemmas`, `Context` | two-zone variables (store and local), types, terms, stores; renaming and one simultaneous substitution; contexts indexed by prefixes |
| `Semantics` | the reference's four reduction rules |
| `Typing` | the reference's 32 typing rules, under its names |
| `Lemmas`, `Examples` | reflexivity; example derivations |
| `PackingCounterexample` | adding packing to `htp` is unsound: a well-typed stuck program |

Type safety is proved in [`../FCdotR`](../FCdotR/README.md) and carried back:
`Oopsla16.oopsla16_safety` says a closed program typed over the empty store
never gets stuck.

## Deviations from `dot.v`

* **Same rules.** The four judgments have the reference's 32 rules and `Step`
  its 4, one for one, under the reference's names. Nothing is added.
* **Written differently.** Intrinsic scoping replaces `closed`, `TVarB` and
  `open`; weakening is explicit; `htp_sub`'s truncated context is a prefix
  scope; the size index is dropped; `Step` carries a store-growth index. That
  this is faithful is argued, not proved: Coq and Lean definitions cannot be
  related formally. The step relation is also tested against a transcription
  of the reference (`coq/oopsla16/deviations/step_differential.py`).
* **Lean admits less, in three places.** A context entry may mention only
  itself and older variables (harmless: proved in Coq on the reference's own
  rules). Stored objects must be well scoped (the reference covers stores the
  port cannot express, proved in Coq; that this costs the empty-store theorems
  nothing is argued). Out-of-range syntax cannot be written (argued harmless:
  typing in the empty context puts every variable in range, and the Coq steps
  on out-of-range syntax apply to terms no rule types).
* **The theorems prove less than `type_safety`.** There is no preservation for
  the source, and the starting store is empty or honest, its methods annotated
  and applying only variables to variables (`oopsla16_safety_honest`).
  Reading the reference's one-step statement as "every run is safe" needs
  `step` to be deterministic, which holds by inspection and is proved in
  neither artifact.

The Coq proofs are in [`coq/oopsla16`](../../../coq/oopsla16/README.md).
