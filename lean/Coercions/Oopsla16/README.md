# Oopsla16

The DOT calculus of Rompf and Amin, *Type Soundness for Dependent Object Types* (OOPSLA 2016),
ported to Lean from the authors' Coq artifact: `oopsla16/dot.v` in `TiarkRompf/minidot` at commit
`ef1143d`.  It is the source calculus of the second line of this tree.
[`../FCdotR`](../FCdotR/README.md) gives it a target calculus in which every use of subtyping is a
term of the program, and proves it type safe through that target.

The calculus differs from the WadlerFest DOT of the main line ([`../DotMNF`](../DotMNF/README.md))
above all in how it compares recursive types.  The rule `stp_bindx` proves `μ(z. S) <: μ(z. T)`
from `S <: T` under the assumption `z : S`.  WadlerFest DOT has no subtyping rule between recursive
types.  It can only pack a variable into a recursive type or unpack it.  The other differences are
smaller.  An object holds type members and methods, and a method may leave out its parameter type
or its result type.  Types include unions.  A term is a variable, an object literal or a method
call on arbitrary terms, so terms are not in normal form.  A variable is either a store location or
a variable of the typing context.  Labels are positions in an object and are shared by type members
and methods.

Two judgments of the reference matter for what follows.  `htp` types a context variable `x` for a
type selection `x.A` inside subtyping.  It has three rules: read the context, unpack a recursive
type, and widen the type in the part of the context that is no younger than `x`.  It has no rule
for *packing*, which types `x` at `μ(z. T)` from `x : T[x/z]`.  The ordinary typing judgment does
have packing (`T_VarPack`).  `T_Vary` types a store location by typing the object stored there
again, at a type the derivation chooses.

## What is proved

The safety proofs are in `../FCdotR` and conclude in namespace `Oopsla16`.

- `oopsla16_safety`: a closed program typed over the empty store never reaches a stuck
  configuration of this calculus's own machine.  `oopsla16_not_stuck` is the positive form: every
  configuration it reaches is an answer or takes a step.
- `oopsla16_safety_honest`, `oopsla16_not_stuck_honest`: the same from an honest initial store.  A
  store is honest for a store typing, which records a type for each location, when `T_Vary` gives
  each location its recorded type.  The theorems also ask that the object each location was typed
  from calls methods on variables only and annotates every method.
- `stp_consistent`: over any store, subtyping in the empty context derives no `⊤ <: ⊥`.
- `PackingCounterexample.packing_is_unsound`: adding packing to `htp` breaks safety.  Over a
  two-object store a closed program is typed at `⊤`, is not an answer, and cannot step.
  `coq/oopsla16/packing` proves the same in the reference's own definitions.
- `Stp.refl`: subtyping is reflexive, by structural recursion on the type.

## Where it departs from `dot.v`

- **The same rules.**  The four judgments `has_type`, `dms_has_type`, `stp` and `htp` have the
  reference's 32 rules, and the machine has its 4 reduction rules.  They match one for one, under
  the reference's names.  Nothing is added.
- **Written differently.**  Variables are intrinsically scoped de Bruijn indices
  (`../FCdot/Debruijn.lean`).  They replace the reference's `closed` premises, its bound variables
  `TVarB` and its `open`.  Weakening is explicit, and the truncated context of `htp_sub` is a
  prefix scope.  The size index of derivations is dropped, and `Step` carries an index for store
  growth.
  Cost: that this is faithful is argued, not proved, because Coq and Lean definitions cannot be
  related formally.  A differential test, `coq/oopsla16/deviations/step_differential.py`, compares
  the step relation with a transcription of the reference's.
- **Contexts.**  A context entry may mention only its own variable and older ones.  The reference
  admits any list of types.  Cost: none for typings in the empty context.  Coq proves on the
  reference's own rules that a context of this shape loses no judgment (`restriction_harmless`),
  and the empty context has this shape.
- **Stores.**  A stored object must be well scoped.  The reference types closed terms over stores
  the port cannot express (`store_restriction_is_real` in Coq), and the port's theorems say nothing
  about them.  That this costs the empty-store theorems nothing is argued.
- **Out-of-range syntax** cannot be written.  This is argued harmless.  Typing in the empty context
  puts every variable in range.  The reference's steps on out-of-range syntax apply to terms no rule
  types.
- **Weaker theorems than `type_safety`.**  The reference proves preservation and progress together
  for any store (`dot_soundness.v:1131`).  Here there is no preservation for the source, and a run
  starts from the empty store or from an honest one.  The reference's statement covers one step.
  It covers every run only if `step` is deterministic, which holds by inspection and is proved in
  neither artifact.

## Building

`lake build Oopsla16` builds the library, which is a default target.  It contains no `sorry`,
`axiom` or `native_decide`, and every theorem depends on `propext` and `Quot.sound` at most
(`../FCdotR/audit/AxiomAudit.lean` checks this).  `../FCdotR/audit/Oopsla16Fingerprint.lean`
prints a hash of every definition here, so any change to the calculus shows.  The Coq proofs are
described in [`coq/oopsla16`](../../../coq/oopsla16/README.md).

## Modules

| module | contents |
|---|---|
| `Syntax` | variables in two zones (store locations and context variables), types, terms, definition lists, stores |
| `Structural` | one simultaneous substitution, with renaming and weakening as instances |
| `SubstLemmas` | the identity and fusion laws of that substitution |
| `Context` | contexts whose entries may mention their own variable, and the prefix of a context at a variable |
| `Semantics` | the reference's four reduction rules over a growing store |
| `Typing` | the reference's 32 typing rules, under its names |
| `Lemmas` | reflexivity of subtyping |
| `Examples` | example derivations, among them recursive subtyping through a method whose result type mentions the self |
| `PackingCounterexample` | packing in `htp` is unsound: a well-typed program that is stuck |
