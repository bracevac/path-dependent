# DotMNF

DOT in monadic normal form, the source of the translation in `../DotToFCdot`.
Recursive introduction and elimination accept arbitrary type bodies. Function
annotations and let result types are also unrestricted.

| module | contents |
|---|---|
| `Syntax` | paths, types (`⊤ ⊥ {A:S..T} {a:T} p.A μ ∀ ∧`), terms, values, definitions; `Decl` and its decision procedure `isDecl` classify translations only; `Distinct` excludes duplicate definitions |
| `Typing` | contexts (`cons`, `consSelf`); `Sub`, `HasTy`, `DefsTy` (Type-valued); unrestricted intersections and recursive bodies; object definitions may contain same-block aliases |
| `Structural` | renaming of all three judgments under lookup preservation; weakening under ordinary and object self binders |
| `Machine` | store, continuations, `Step`, `Steps`, `Final`, `Stuck` |
| `Erasure` | erasure to `Runtime`; `erase_step`, `erase_reflect`, `final_erase`, `final_reflect` |
| `Examples` | E1 to E12 as `HasTy` derivations; E9 executes a function folded through a recursive type; E10 to E12 exercise self-dependent intersections, nested recursion, and a bare self selection |

## Correspondence with WadlerFest DOT

`WadlerFest/Syntax` and `WadlerFest/Typing` give an independent, intrinsically
scoped presentation of the annotated calculus in
[Amin et al., Figures 1--2](https://namin.seas.harvard.edu/files/dot_wadlerfest.pdf).
Object values retain their self annotation. Ordinary contexts admit the
opened self type, and definition typing enforces distinct labels.

`WadlerFest.HasTy.eraseAnnotations_closed` proves that every closed program
typed by these rules has a DOT-MNF derivation at the same type after removing
object annotations. The general theorem interprets each source context
assumption by a variable-typing derivation. At an object self binder, one
recursive elimination derives the opened body from DOT-MNF's recursive self
assumption. This construction needs no inertness or good-bounds premise.
The correspondence is from annotated typing to DOT-MNF typing; reverse
annotation synthesis is not formalized.

`WadlerFest/Machine` retains the annotations in the store machine.
`WadlerFest/Erasure` proves that annotation erasure preserves and reflects
steps, finite runs, finality, and stuckness. The composition with FCdot in
`../DotToFCdot/WadlerFest` proves safety for closed programs of this machine.

### Retained-let operational correspondence

`WadlerFest/Reduction` independently states the retained-let rules from the
paper. Its ambient store records enclosing value bindings; those bindings
remain in the term. At the top level the ambient store is empty. Both
evaluation-context rules are present, and reassociation has no priority over
other reductions. Projection uses relational definition membership.

`WadlerFest/Readback` turns a machine continuation into pending let contexts
and its store into enclosing value lets. Every machine step induces a finite
retained-let reduction. Pushing a frame changes no term; allocation may
reassociate a binding across several pending frames.

The converse argument in `WadlerFest/OperationalCorrespondence` preserves
finite machine behavior backwards through every retained-let step and every
continuation. Reassociation corresponds to fusing two continuation frames.
The observable answer is the exact annotated term obtained by readback,
including retained bindings. Consequently, for a closed term with distinct
labels in all its objects:

- An answer is reachable by retained-let reduction exactly when a reachable
  final machine state reads back to that same answer (`answer_iff_machine`).
- A stuck term is reachable exactly when a stuck machine state is reachable
  (`stuck_iff_machine`).

Distinctness reconciles relational membership with deterministic machine
lookup. `WadlerFest/WellFormed` proves that typing supplies this syntactic
invariant and that reduction preserves it; it imposes no restriction on types
or recursive dependencies. `../DotToFCdot/RetainedSafety` then proves that
every term reachable from a closed typed program is an answer or reduces,
for all retained-let reduction orders. This proof uses target safety and
operational correspondence without a source type-preservation proof.

`WadlerFest/OperationalExamples` checks self-dependent projection and a
nested-let application whose overlapping reduction orders reconverge. Its
machine run reads back to the same retained answer.

### Public syntax with separate label categories

`WadlerFest/Sorted` exposes types, terms, definitions, contexts, and stores
whose constructors distinguish `TypeLabel` from `TermLabel`. This frontend
uses subtypes of the internal syntax. `WadlerFest/LabelSorted` establishes
closure under renaming, substitution, and retained-let reduction.

Public typing and subtyping derivations carry a recursive certificate that
checks every context and intermediate type, including those introduced by
transitivity and subsumption. Thus sorted endpoints cannot conceal an
ill-sorted intermediate judgment. Every source rule has a public constructor.
`../DotToFCdot/SortedSafety` supplies the typed, exactly erasing translation
and retained-let safety for this frontend. Its safety conclusion quantifies
over public terms, so reduction stays within the sorted syntax.

The public examples construct and type a self-dependent object, check its
projection step, and reject labels used in the wrong category. The internal
syntax still uses a shared `Label` representation to reuse the existing
proofs. Scoping is intrinsic; a conversion from named syntax modulo
alpha-equivalence is not formalized.

## Further extensions

Recursive subtyping is absent from the WadlerFest rules themselves. Adding
the recursive subtyping of
[Rompf and Amin's OOPSLA 2016 calculus](https://namin.seas.harvard.edu/files/soundness_oopsla16.pdf)
is a separate extension: it requires a translation of assumptions under the
recursive self binder, beyond the variable-level folding and unfolding
proved here. Its restrictions on type selection must be considered together
with those rules.

[pDOT](https://mrapoport.com/publ/pdot.pdf) also requires a separate account of
stable field paths and singleton aliases. Merely extending `Path` is
insufficient: different field paths must retain distinct identities, and
the metatheory must justify lookup for paths used as objects or functions.
