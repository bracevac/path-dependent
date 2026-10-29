# PDot

Full pDOT (Rapoport and Lhoták, OOPSLA 2019) by coercions.  pDOT types paths of any length, as in
`x.a.b`, and singleton types `p.type`.  A field may hold a path, a lambda or a nested literal, and a
path may be replaced by its alias inside a type.  This line transcribes pDOT from its Coq
formalization as the source, translates every source derivation into the coercion calculus FCp, and
proves FCp type safe.  The source and one untyped runtime agree step for step.  The FCp machine
agrees with the runtime up to steps that keep the erasure.  So pDOT's safety is proved about pDOT's
own reduction and lookup, carried from the target.  The design is plan X (`plan-10-pdot.md`).

## What is proved

- `PDot.safety`: let `d : HasTy .nil t T` type a closed source term and `Reds ⟨[], .nil, t⟩ c` be a
  run.  Then the term of `c` is a normal form or `c` takes a step.  If the term of `c` is a path
  `p`, every lookup sequence of `p` in the store of `c` ends at a value or takes one more step
  (`PathSafe`).  The first conjunct is the progress half of pDOT's `safety` (`Safety.v:416-424`),
  the second the constructive content of `path_safety` (`Safety.v:442-447`).
- `PDot.reachable_typed`: under the same hypotheses, the erasure of `c` is the erasure of an FCp
  state typed at `⟦T⟧` renamed into the signature of `c`, and every typing of that state's store
  proves no `⊤ ≤ ⊥`.  It takes the place of the clause `G ⊢ u : T ∧ γ ⫶ G ∧ wf G ∧ inert G` of
  pDOT's `safety`.
- `PDot.reachable_run`: under the same hypotheses, the FCp machine runs the image of `d` to a state
  whose erasure is the erasure of `c`.
- `HasTy.translate_typed`: in related contexts `G ≈ Δ`, the image of a source derivation of `t : T`
  is an FCp term of type `⟦T⟧`.  `HasTy.translate_erase`: the image erases to the source's erasure
  of `t`.
- FCp's theorems.  On typed states of the machine: preservation, progress, `not_stuck` and the
  erasure simulation `erase_reflect'`.  On every step of the machine: `erase_step`, since the
  application view is sound.  Over a typed store `⊢ σ : Γ`: the canonical forms of closed evidence
  (`alias_canon`, `eq_canon`, `le_canon`, `path_view`), `lookup_step_typed` and `path_safe` for
  typed paths, and `no_top_le_bot`.  The checker decides typing (`checkTm_iff`).  The FCp README
  states them with their hypotheses.
- The examples of plan X on both sides.  The FCp checker accepts the images of the programs E1 to
  E8 and E13 and of the path typings E9 to E11, decided in the kernel.  E5, E7 and E8 run on the
  source and on the FCp machine to one runtime configuration.  The FCp literals that a derivation
  of N1, N2 or N3 would build have no type.  The Translation README states them.

## What it leaves out

- pDOT's disjunctive `safety` and `extended_safety`, that a run ends at a normal form or diverges,
  are not stated.  Their Coq proof reads excluded middle (`Sequences.v`, `infseq_or_finseq`), and
  the line admits no axiom beyond `propext` and `Quot.sound` (plan X, decision 3).  `PDot.safety`
  is the constructive half: no reachable configuration is stuck.  Both follow from it with excluded
  middle, by the argument of `Safety.v:485-556`.
- pDOT's own preservation with its seven typing relations is not proved.  The source has no `inert`,
  `wf` or store typing, so the typed conclusion `G ⊢ u : T` of Coq's `safety` for a reached normal
  form is not stated, and pDOT's `path_safety` for every typed path of a well-typed store has no
  counterpart.  `PDot.safety` states path safety for the path in focus only, which is the use Coq's
  own theorem makes of the lemma.  A reachable configuration is typed through its image in FCp
  (`PDot.reachable_typed`).
- FCp types some terms that pDOT rejects: the reflexive singleton `x : x.type` (N4,
  `N4_target_refl`), the empty literal, and `lift` along a symmetric path equality (plan X,
  decision 21).  FCp's theorems hold of these terms too.  The transport reads only images of
  derivations.
- The source derivations of the examples are written by hand.  There is no derivation search and no
  front end.  The front ends that plan X adds after X7, in DOT notation and in Scala syntax, are
  later stages.
- The canonical walk, resolution and the normal type (`canon`, `res`, `norm`) are a closed reading
  used in the metatheory only.  The checker never computes them.
- The Lean syntax holds ill-sorted terms that Coq has not, such as a type member selected at a term
  label.  The fidelity table of the Source README is on the well-sorted fragment.

## Layout

`Source/` is pDOT as its Coq formalization states it, in the de Bruijn signatures of the Paths
target.  Each Coq constructor is one Lean constructor with the Coq name, and the judgments `HasTy`,
`DefTy`, `DefsTy` and `Sub` are one mutual block of `Type`-valued families.  It holds lookup,
reduction, the examples E1 to E13 with three Coq lemmas replayed under their names, the negative
examples N1 to N5, and the erasure into the runtime.  Its README has the fidelity table, one row per
Coq definition.

`Runtime.lean` is untyped pDOT.  It substitutes paths, never copies an object, and addresses a nested
literal by its path from the enclosing top-level self.  Both the source and FCp erase into it, and
it computes lookup and reduction with fuel.

`FCp/` is the target.  Paths are terms, path equality is evidence, and replacement is a type
equality along that evidence.  A literal declares a telescope of bounds, fields, aliases and self
bounds.  The machine applies a path through its application view, as pDOT's `red_app` looks the
closure up.  It holds the checker with its completeness, the canonical forms of closed evidence over
a typed store, lookup safety, consistency, preservation, progress and the erasure simulations.

`Translation/` is the translation of the source into FCp, one case per source rule, with its
typedness and erasure theorems, the transport `PDot.safety` and `PDot.reachable_typed`, and the
examples on both sides.  Every translation function is structural, so the kernel runs the
translation of a whole derivation.

`Frontend/` is the front end, the library `PDotFrontend`, which is not a default target.  A program
is written in the paper's notation under `pdt%`, and may leave out a lambda's domain, a literal's
self type and the declared type of a lambda field.  The front end resolves names, fills those slots
and searches for a `HasTy` derivation.  The FCp checker accepts its translation, and both machines
run it.  Its theorems restate the ones above at a compiled program.  Its checks type E1 to E8 and
E13 by search at the types of their hand derivations, and run E5, E7 and E8 on both machines.  See
[Frontend/README.md](Frontend/README.md).

## Building

`lake build PDot` builds the library, and `PDot` is a default target.  The path layer (`Sig`,
`BVar`, `Label`, `Rename`, `Path`, `PathSubst`) is imported from `Paths/FCdot`, not copied, and the
Paths tree does not change.  The line has no `sorry`, `axiom`, `native_decide`, `partial`,
`unsafe`, `implemented_by`, Mathlib or `aesop`, and no command elaborator or `IO`.  An axiom audit
at stage X7, a metaprogram kept with the stage notes and not in the repository, swept the 10328
constants that the modules of the library then declared, 4732 of them theorems.  None depended on
an axiom outside `[propext, Quot.sound]`, and no definition recursed through `WellFounded.fix`.  It
printed the axioms of every theorem that this README, the FCp README and the Translation README
name.  `#print axioms` repeats that check for any one of them.
