# Resume state: Oopsla16 → FCdotR

Branch `fcdot-recursive-subtyping`.  The line is finished up to the checker.
Last commit of the line: `aa7ca71` (type safety of `Oopsla16`, transported from
FCdotR).  `FCdotR/Deliverables.lean` and the documentation pass came after it.

## Done

* `Oopsla16/`: the Rompf--Amin OOPSLA'16 calculus with recursive subtyping,
  intrinsically scoped, ported from the Coq artifact; `PackingCounterexample`,
  also mechanized in Coq at `coq/oopsla16-packing/`.
* `FCdotR/`: the explicit-evidence target.  Elaboration of every source typing;
  substitution; canonical forms of closed evidence (transitivity elimination by
  pack count); preservation of the FCdotR machine up to evidence; progress; the
  simulation between the two machines in both directions.
* **The headline**, in `FCdotR/SourceSafety.lean`, namespace `Oopsla16`, with no
  hypothesis: `oopsla16_safety` (a closed program typed over the empty store
  never reaches a stuck configuration of `Oopsla16`'s machine) and
  `oopsla16_not_stuck` (every configuration it reaches is an answer or steps).
* The remaining WadlerFest counterparts, in `FCdotR/Deliverables.lean`:
  consistency and recorded type members along runs, `Oopsla16.reachable_related`,
  `Oopsla16.stp_consistent`, coherence as equal answers.

## Open

A checker with completeness (blocked on carrying the source premise of
`vcLocAny`/`varConcAny` as target evidence); preservation for the source; safety
from a store whose objects are outside `DmsFrag`; determinism.  Details in
`FCdotR/STATUS.md`, *What remains*.

## Where to read

`FCdotR/README.md` (overview, modules, main theorems, design),
`FCdotR/STATUS.md` (full inventory, WadlerFest comparison, review findings),
`Oopsla16/README.md` (the source and its correspondence with `dot.v`).

## How to build

From the repository root:

```
lake build FCdot DotMNF DotToFCdot Oopsla16 FCdotR
```

Sessions have used a copy of the root `lakefile.toml` in a scratch directory,
with `srcDir` set to the absolute path of `lean/`, run as
`lake -d <scratch> build …` so that build output stays out of the repository.
Either way the build needs the sandbox disabled, since `~/.elan` is outside it.
It completes in 119 jobs; the only warning is the pre-existing unused
`termination_by` at `FCdot/Syntax.lean:221`.

The axiom audit is a scratch file that imports `Coercions.FCdotR` and
`Coercions.Oopsla16`, runs `Lean.collectAxioms` on every constant whose module
is under either prefix, and reports those using anything beyond `propext` and
`Quot.sound`.  Its current output is `checked 6323 constants; offending: 0`.
