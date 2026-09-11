# Frontend

The vanilla front end of plan V §7, specified in `plan-5e-frontend-stages.md`: a direct-style surface
syntax embedded in Lean, name resolution and let-insertion into DOT-MNF, a derivation-producing typer,
executable machines with agreement lemmas, and the pipeline through the FCdot checker to a run.  A
program is written in the paper's notation inside `dot%`, `resolve` turns it into an annotated DOT-MNF
term in monadic normal form, `synthTop?` types it and hands back the `DotMNF.HasTy` derivation, and
`compile` is the two of them together.  Not part of the metatheory.  It imports the frozen tree
`../DotMNF`, `../FCdot`, `../DotToFCdot` and `../Runtime.lean` and changes nothing in it.

## What is proved

Resolution is total on scoped, well-labelled programs: `resolveTy_isSome`, `resolveTm_isSome`,
`resolveDefs_isSome`.  Let-insertion inserts nothing at a variable: `atomize_var`.  Renaming commutes
with erasure: `ATm.erase_rename`, `ADefs.erase_rename`.

The side conditions the typer discharges by computation are decided, each with its own `iff`:
`tyWf?_iff`, `defsDistinct?_iff`, `tyStrengthen?_iff`, `tyStrengthenW?_weaken`.

The search grows with its budget and never loses ground: `views_mono`, `decls_mono`, `sub?_le`,
`synth?_le`.  There is no soundness theorem, because soundness is the result type, and no completeness
theorem, because there is none to have.

The source machine agrees with the frozen step relation in both directions and classifies the states
with no step: `final?_iff`, `step?_sound`, `step?_complete`, `step?_eq_none_iff`,
`step?_none_classify`, `run_steps`.  The target machine agrees at every fuel, monotonically, and up to
the existence of a fuel: `fcStep?_sound`, `fcStep?_le`, `fcStep?_complete`, `fcRun_steps`.

The pipeline is five compositions of frozen results: `compile_checks`, `compile_erase`, `compile_safe`,
`compile_not_stuck`, `compile_run_progress`.  The target checker accepts the translation of the
derivation, the translation erases to the source term, every reachable state is final or steps, no
reachable state is stuck, and the driver never answers at a state the machine is stuck at.  Each of the
twelve example programs carries that first theorem at its own budget: `E1_checks` to `E11_checks`.

`#print axioms` of every theorem named here reads `[propext, Quot.sound]`.  No `sorry`, `axiom`,
`native_decide`, `unsafe` or `partial` anywhere, and no Mathlib.

## Five things that are not theorems

**1.  The front end is not part of the metatheory.**  It imports the frozen tree and changes nothing in
it.  No statement of the vanilla line is restated, weakened or re-proved here, and no definition of this
library is placed in the `DotMNF` or `FCdot` namespaces.  `Frontend` is not in `defaultTargets`, so a
build of the metatheory does not wait on it.

**2.  The typer is sound by construction and incomplete by necessity.**  Sound because `synth?` returns
a `Synth`, whose second field is the `DotMNF.HasTy` derivation, so soundness is the result type and
there is no soundness theorem to prove.  Incomplete because DOT subtyping is undecidable.  What the
typer will not find is a list and not a theorem, and it is the list of F1.4.  A subtyping whose middle
is outside the one family of F1.3, for instance through a `μ` or through an intersection the goal does
not mention.  A `recI` folding other than the goal's own body, since the typer never invents a `μ`.  An
`andI` at a position where neither conjunct is separately checkable.  An avoidance result other than the
annotation, the strengthening, or `⊤`.  An object literal without a self annotation.  An application
whose function variable reaches `.all` only through a subtyping step the view closure does not perform.
Anything past the budget.  And, DOT subtyping being undecidable, a proper superset of these in general.

**3.  The search and the typer are opaque to the kernel.**  Both are well-founded, so neither reduces
by `rfl` and neither is decided by `decide`.  Every test that touches them runs compiled code through
the `expect` helper of `Surface.lean`, which throws when its argument is false.  No side condition of a
derivation is discharged through them.  Everything upstream of the search, resolution and let-insertion
and the decision procedures and the source machine, is structural and does reduce in the kernel, and
its tests are written `by decide` or `rfl`.

**4.  Let-insertion has no semantic statement.**  It is total on scoped programs, it inserts nothing at
a variable, and monadic normal form is by construction.  What relates the surface program's meaning to
the meaning of the MNF term is the direct-style calculus with its type-preservation theorem under
avoidance, which `plan-5-extensions.md` §7 parks as a separate small development.  Until that exists,
the surface program is defined by what the resolver returns and by nothing else.

**5.  Three annotations, and why each is forced.**  The lambda domain, by the calculus: `Value.lam`
carries its domain type (`../DotMNF/Syntax.lean:93`).  The object self type, by `HasTy.obj`'s premise
`DefsTy (Γ.consSelf d T) d T` against `Value.obj`'s lack of a slot for it
(`../DotMNF/Typing.lean:97-101`), which is why the annotated term syntax `ATm` exists at all and erases
to `DotMNF.Tm`.  The `let` result type, optionally, because `HasTy.let` does not determine the type the
body is generalized at and the avoidance ladder has to guess: the annotation, then the strengthening of
the body's type, then `⊤`.  The third rung always applies and always loses information, so a program
that needs a sharper result writes the annotation.

| module | contents |
|---|---|
| `Surface` | `SType`, `STm`, `SDefs`, the unindexed named syntax; `LabelTable` and `labelsOfProgram`; `Scoped` and `LabelsIn`; the `expect` helper |
| `Notation` | the syntax categories `dotTy`, `dotTm`, `dotDefs` and the entry points `dotTy%`, `dot%`, `dotDefs%`; the paper's notation, with `{type A = T}` for a type member definition and a dotted name split inside the macro |
| `Ann` | `ATm` and `ADefs`, DOT-MNF with the two annotations; `erase`, `rename`, `erase_rename`, `sizeATm` |
| `Resolve` | `NameEnv`, `Spine`, `atomize`, `resolveTy`, `resolveTm`, `resolveDefs`; totality on scoped well-labelled programs; the ten surface programs E1 to E10 with their resolutions |
| `Decide` | `tyWf?`, `defsDistinct?`, `tyStrengthen?`, each with an `iff` and a `Decidable` instance; `ctxVars` |
| `Search` | `View`, `Decl`, `DeclTable`, `Budget`; the view closure and the declaration table in rounds with deduplication; `sub?`, the eleven-rule subtyping search; round and fuel monotonicity |
| `Typer` | `Synth`; `synth?`, `check?`, `checkVar?`, `checkDefs?` and `synthTop?`; the avoidance ladder; fuel monotonicity; the measured budget of E1 to E8 |
| `Step` | the DOT-MNF machine as `step?`, with `final?`, agreement in both directions, the classification of the states with no step, and the driver `run` |
| `StepFC` | the FCdot machine as `fcStep?`, which takes the normalizer's fuel; soundness at every fuel, fuel monotonicity, completeness up to a fuel, and the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `compileAndRun`, and the five theorems that say what a compiled program is worth |
| `Pretty` | the way back out: `ppTy`, `ppTm`, `ppDefs`, `ppATm`, `ppSTm`, `ppStateWith`, `ppRun`; names for binders and labels; no theorem |
| `Examples` | the ten surface programs end to end against the vanilla derivations, four checks each, plus E10t and E11; three runs of `compileAndRun` |
