# FCdotR

FCdotR is a coercion calculus with explicit evidence for the OOPSLA 2016 DOT of
[`../Oopsla16`](../Oopsla16/README.md).  In the source a derivation uses subtyping silently, through
the subsumption rule `T_Sub`.  In FCdotR every such use is *explicit evidence*: a proof term in the
program, called a *coercion*, which a `cast` applies.  There are two sorts of coercion.  Inclusion
evidence is the image of a subtyping derivation.  Observation evidence is the image of an `htp`
derivation, which types a variable for a type selection.  *Erasure* deletes every coercion and
returns a term of `Oopsla16` itself, so coercions do nothing at runtime.  Types, contexts and stores
are `Oopsla16`'s own, and the type translation is the identity.  Method calls take *atoms*.  An
atom is a variable or a location under casts and under *packing* and unpacking, which move a
variable's type into and out of a recursive type.  `let` binds intermediate results.

The line has a target of its own because of recursive subtyping.  `stp_bindx` proves
`μ(z. S) <: μ(z. T)` from `S <: T` under the assumption `z : S`, and FCdotR's coercion `bindx`
takes exactly that premise.  The main line's target FCdot compares two object types in another
way, by templates built from the facts of the source type and from closed coercions.  None of
FCdot's coercions is checked under an assumption about the self.  `Examples.recursive_typed` is a
`bindx` coercion for a method whose result type mentions the self.

A few terms recur below.  The source types a store location by `T_Vary`, which types the object
stored there again, at a type the derivation chooses.  A *store typing* records a type for each
location.  The store is *honest* for it when `T_Vary` gives each location its recorded type.  A method is
*annotated* when it carries both its parameter type and its result type.  The source lets a method
leave either out.  The two *location rules*, `VcTy.vcLocAny` and `AtomTy.varConcAny`, type a
location at any type that matches its stored object member by member (`LitMatch`).  A type member
must be the stored one exactly, and a method member must equal the stored method's annotations.
They are the target's counterpart of `T_Vary`.

## What is proved

- `Oopsla16.oopsla16_safety`, `Oopsla16.oopsla16_not_stuck` (`SourceSafety`): a closed `Oopsla16`
  program typed over the empty store never gets stuck on `Oopsla16`'s own machine.  The proof
  elaborates the program into FCdotR, simulates the source run on FCdotR's machine, and uses
  FCdotR's safety.  `oopsla16_safety_honest` starts from an honest store instead.
- `safety'`, `preservation'`, `progress'` (`MethodInversion`): FCdotR is type safe.  Preservation
  holds up to evidence: the reduct has the skeleton of a typed state, because the machine drops the
  casts of an atom it substitutes.
- `consistency_honest` (`Inversion`): over an honest store no closed coercion proves `⊤ ≤ ⊥`.
- `elabSpecGen` (`ElaborationFull`): every `Oopsla16` typing elaborates to a typed FCdotR term
  related to the source term, over a store whose methods are annotated.  `elabSpec` is the case of
  the empty store.  `elabHasType_erase` (`ElaborationErasure`): over an annotated store, when every
  call has variable operands and every method is annotated, the elaborated term erases to the
  source term itself.
- `checkTm_iff` and its siblings (`CheckerCompleteness`): an executable checker decides every
  FCdotR judgment.  `CheckerExamples` runs it in the kernel, on the reference's examples `ex1`,
  `ex2` and `paper_lst` among others.
- `Store.Honest.varConcAny_admissible`, `Store.Honest.vcLocAny_admissible` (`Admissibility`): over
  an honest store the location rules give a location no type the source does not give it.
- `Counterparts` states for this line the corollaries the main line proves.  Stores stay consistent
  along runs (`reachable_consistent`).  Every reachable source configuration is related to a typed
  target state (`Oopsla16.reachable_related`).  Two elaborations of one source term reach the same
  answers (`Corr.coherent`).  Source subtyping is consistent over every store
  (`Oopsla16.stp_consistent`).

## Where it departs from the source

- **A different calculus by design.**  Evidence is explicit, casts are syntax, calls take atoms,
  `let` exists, methods always carry both types, and the machine keeps a store and a
  continuation.  Typing from source to target is proved (the elaboration).  The converse is proved
  only for the location rules over honest stores.
- **The location rules are not `T_Vary`.**  They do not type method bodies again and take a stored
  method's annotations on trust.  Cost: over a store that is not honest they type more than the
  source.  Over `{def 0(y:⊤):⊥ = y}` they type `l.0(l)` at `⊥` (`Coverage.UncheckedBody`).  Machine
  stores are always honest, so safety is not affected.
- **Elaborating `T_Vary` needs annotated stored methods**, so `ElabSpecGen` assumes
  `Store.Annotated G`.  The empty store is annotated, so the headline theorems carry no such
  hypothesis.  Cost: no safety theorem here covers a run that starts from a store holding a method
  without both types, although the reference's `type_safety` does (`Coverage.CurryGap`).
- **`vcLoc` reads the store typing.**  A store typing that lies proves `⊤ ≤ ⊥`
  (`CanonicalForms.DishonestStore`).  Cost: consistency needs an honest store.  Every store a closed
  typed program reaches is honest and consistent (`reachable_consistent`).
- **Erasure and coherence are weaker.**  `let` erases to an object encoding, so the elaborated term
  erases to the source term only when calls have variable operands.  Elsewhere a simulation
  relation (`Correspondence.Corr`) ties the two.  Two elaborations of one term may differ after
  erasure, so coherence says they compute the same answers, not that they erase alike.

## Building

`lake build FCdotR` builds the library and `Oopsla16`, which it imports.  Both are default targets.
Neither contains `sorry`, `axiom` or `native_decide`.  The two files under `audit/` belong to no
library.  After the build, `lake env lean lean/Coercions/FCdotR/audit/AxiomAudit.lean` checks that
every constant of both libraries depends on `propext` and `Quot.sound` at most.
`lake env lean lean/Coercions/FCdotR/audit/Oopsla16Fingerprint.lean` prints a hash of every
`Oopsla16` constant, so a change to the source calculus shows.

## Modules

| module | contents |
|---|---|
| `Prefix`, `Structural` | the prefix of a context at a variable of either zone, and substitutions that respect prefixes |
| `Syntax` | inclusion and observation evidence, atoms, terms, definition lists |
| `Typing` | typing of the two evidence sorts, and the match `LitMatch` of the location rules |
| `Locality` | an observation of a variable depends only on that variable's prefix |
| `Subst`, `SubstTyping` | substitution on evidence and terms, and the typing of evidence kept under it |
| `TermTyping`, `TermSubst` | typing of atoms, terms and definition lists, and its stability under substitution |
| `StoreTyping` | store typings, honest stores, annotated stores |
| `Examples` | recursive subtyping through a method, as a closed coercion |
| `Machine` | the machine with a store and a continuation |
| `Erasure` | erasure into `Oopsla16` terms, and a step without `let` frames that erases to at most one source step |
| `Forms`, `Normalizer` | measures and normal forms of closed evidence, and the normalization of observations |
| `CanonicalForms` | the head shapes of closed inclusions, and consistency reduced to one hypothesis |
| `Inversion` | transitivity elimination over an honest store, and `consistency_honest` |
| `Admissibility` | over an honest store the location rules derive nothing the source cannot |
| `Elaboration`, `ElaborationErasure` | elaboration of source derivations, and erasure back to the source term |
| `Preservation`, `Progress` | preservation and progress, given canonical forms for methods |
| `MethodInversion` | canonical forms for methods, and `safety'` with no hypothesis |
| `Correspondence` | the relation between source configurations and machine states, the forward simulation, the transport of safety |
| `ElaborationFull` | elaboration of every source typing over an annotated store |
| `Simulation` | the backward simulation, and the correspondence of answers and stuck states |
| `SourceSafety` | `Oopsla16.oopsla16_safety` and its variants |
| `Counterparts` | the main line's corollaries for this line: consistency along runs, coherence, consistency of source subtyping |
| `Coverage` | what the safety theorems rule out, and what the location rules trust |
| `Checker`, `CheckerCompleteness` | the executable checker, its soundness and completeness, unique derivations |
| `CheckerExamples` | the checker run in the kernel on elaborated source examples, and its rejections |
| `audit/AxiomAudit`, `audit/Oopsla16Fingerprint` | the axiom audit of both libraries, and the fingerprint of `Oopsla16` |
