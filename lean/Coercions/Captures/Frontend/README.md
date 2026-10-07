# Captures front end

A way to write, type and run programs of the `Captures` development without
assembling derivations by hand. A program is written in the paper's notation
inside `cap%`, with capture sets `S ^ C`, capture members `{C^ : c₁..c₂}`,
boxes `□ T` and unboxings `C ⊸ x`. The front end resolves names and inserts
`let`s to reach monadic normal form, finds a typing derivation with its use
set, inserts the boxes and unboxings the program left out, translates the
derivation to FCdot, and runs the program. It proves nothing new about the
calculi. It imports `../DotMNF`, `../FCdot`, `../DotToFCdot` and
`../Runtime.lean` and changes nothing in them.

```lean
def C7scalaSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}). λ(u : ⊤).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in e u
```

This is a container of two capabilities in the form a Scala program has. No
box is written. The typer boxes `f1` and `f2` where the fields ask for a box,
and unboxes `e` at `{k1}` before the call. The type it finds charges `{k1}`
to the innermost function and nothing to the two outer ones.

A program runs over a platform, a prefix of capture binders, one per
capability it may use. `πc` of `Resolve.lean` names two, `k1` and `k2`.
`compile` runs the resolver and then the typer at the platform's context. It
returns the resolved term and a `Compiled`, which holds the elaborated term,
its use set, its type, the `DotMNF.HasTy` derivation about its erasure, and
the proof that the elaborated term has the skeleton of the resolved one.
`compileAndRun` adds the machine at a step budget.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax `SCap`, `SType`, `STm`, `SDefs`, the `LabelTable`, the conditions `Scoped`, `LabelsIn` and `AnyPlaced`, the test helper `expect`, and the command `#assert_no_wf` |
| `Notation` | the entry points `capCap%`, `capTy%`, `cap%`, `capDefs%` for the paper's notation, and the surface programs of the version's examples |
| `Ann` | `ATm` and `ADefs`, DOT-MNF terms with the annotations the typer needs, their `erase`, and the skeleton `ATm.skel` |
| `Resolve` | name resolution over two kinds of binder and let insertion (`resolveTop`, `resolveIn`, `atomize`), platforms (`PlatformNames`, `πc`), and totality |
| `Decide` | decision procedures for well-formedness (`tyWf?`), distinct labels (`defsDistinct?`) and strengthening (`tyStrengthen?`), and the union of capture sets `capJoin` |
| `Search` | the `Budget`, the views of a variable, the declaration table, and the search `subShape?`, `subcap?`, `sub?` |
| `Adapt` | the result types `Elab` and `Checked`, the box and unbox rules, and box inference at a variable, `adaptVar?` |
| `Typer` | `synth?`, `check?`, `checkVar?`, `checkDefs?`, the entry points `synthIn?`, `synthTop?`, `checkIn?`, and the typer's checks |
| `Step` | the DOT-MNF machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdot machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `compileAndRun` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation (`ppTy`, `ppATm`, `ppRun`, `ppRunOver`), no theorems |
| `Examples` | 23 programs taken end to end and compared with the hand written derivations of `../DotMNF/Examples.lean`, and the two effect theorems |

## The typer

The typer is sound by construction. Every result carries the
`DotMNF.HasTy` derivation of the term it typed, so soundness is the result
type, and there is no soundness theorem to state. The typer is incomplete by
necessity, since subcapturing goes through subtyping and DOT subtyping is
undecidable. It runs on a `Budget` of five counters: rounds of the
declaration table, rounds of the view closure, the fuel of the search, the
fuel of the typer, and passes of the object rule. More typer fuel never
loses an answer (`synth?_le`). No such claim is made for the other counters.

The typer computes the least use set and the least capture set the rules
allow. A variable at a pure type is used at `{}`, any other one at `{x}`. A
binder that leaves scope is replaced in a set by the set it was declared at,
or by the upper bound of its capture member, and the result is followed by
evidence from the search. For a `let`, the result type is the annotation if
there is one, else the body's type strengthened past the binder, else `⊤` at
the avoided set.

Box inference is part of the typer. Where a variable `x` is checked against
a goal, plain checking comes first. If it fails and no view of `x` is a box,
the value `□ x` is checked by synthesis and subsumption. If a view of `x` is
a box `□(S ^ C)`, the unboxing `C ⊸ x` is checked. A function or a receiver
with a box view and no function or field view is unboxed before the call or
the projection. An insertion at an argument, a function or a receiver is
bound by a new `let`. So the elaborated term differs from the written one,
and `compile` checks that the two have the same skeleton. The skeleton
forgets annotations, capture sets, boxes, the set of an unboxing and
ascriptions, and inlines a `let` of a variable.

The user writes these annotations. A lambda carries its domain type, as in
the calculus. An object literal carries its self type, because
`DotMNF.Value.obj` has no slot for it and the typing rule needs it. It may
carry its own capture set, else the typer finds one in passes. A `let` may
carry its result type when `⊤` would lose too much. An ascription `(t : T)`
names the type of a bound term, since a `let` annotation types the whole
`let`. S1 and S2 bind their signatures this way. A capturing type written
as a type member bound is boxed by the resolver, the Scala rule that a type
argument is boxed.

What the typer will not find.

- A middle type of a transitivity step that the context does not declare. The search tries only declarations of the declaration table, and never invents a `μ`.
- A subcapturing whose chain leaves the five rules of `subcap?`: inclusion, union, `sc-var`, the upper bound of a capture member, and the lower bound of a capture member.
- An avoidance through a member bound that does not strengthen past the binder.
- An object whose definitions are not stable after `Budget.obj` passes of the object rule.
- A box at a variable whose first box view does not carry the goal's set.
- Anything past the budget.

## Main theorems

The pipeline theorems take a successful `compile` and apply results of the
`Captures` development to the derivation it returned. The platform is
`π.plat` and the compiled term is the erasure of the elaborated one.

- `compile_checks`: the FCdot checker accepts the translated derivation.
- `compile_uses_checks`: the FCdot checker accepts the use set evidence the translation emits.
- `compile_erase`: the translation erases to the compiled term.
- `compile_faithful`: the elaborated term has the skeleton of the resolved term. It is the field `Compiled.skel`, which `compile` decides.
- `compile_safe`: every state a run from the platform's initial store reaches is final or can step.
- `compile_not_stuck`: no reachable state is stuck.
- `compile_run_progress`: at any step budget, `run` stops at a final state or at one where `step?` still has a step.
- `compile_capture_prediction`: along any run, the matched target state uses no more than the translation of the use set the typer found.
- `compile_effect_safety`: a platform capability that is not in the use set the typer found is never a root of a variable a run reads.
- `compile_checks_get`, `compile_effect_safety_get`: the same two at a program whose compile succeeds by a decided test.
- `E1_checks` to `E11_checks`, `C7_checks`, `C7nb_checks`, `C7scala_checks`, `S3_checks`, `S3nb_checks`, `C2asc_checks`, `C2_checks`, `S1_checks`, `S1bare_checks`, `S2_checks`: the checker accepts the translation of each example program, with no hypothesis. E10 is rejected by the typer and has none.
- `C5_checks`: the checker accepts the translation of C5, typed at the version's open context `S2Ctx3`.
- `S1_never_reads_fs`: a run of the version's `S1tm` from the platform's initial store never reads a variable rooted at `k1`, the file system. The typer finds the use set `{}` for S1 without its ascription.
- `C2_never_reads_k1`: a run of the version's `C2tm` never reads a variable rooted at `k1`. The typer finds the use set `{k2}` for C2.

Supporting results:

- `resolveT_isSome`, `resolveTm_isSome`, `resolveDefs_isSome`: resolution succeeds on scoped programs whose labels are in the table, whose `any` is placed where the version reads it, and whose capturing types sit where a set may be written.
- `resolve_noAny`: every type the resolver puts in an annotation holds no `any`.
- `atomize_var`: let insertion inserts nothing at a variable.
- `tyWf?_iff`, `defsDistinct?_iff`, `tyStrengthen?_iff`: the side conditions are decided.
- `views_mono`, `decls_mono`, `sub?_le`, `subcap?_le`, `synth?_le`: more fuel never loses an answer.
- `step?_sound`, `step?_complete`, `step?_none_classify`: `step?` agrees with the DOT-MNF step relation, and a state with no step is final or stuck.
- `fcStep?_sound`, `fcStep?_le`, `fcStep?_complete`, `fcStep?_none_classify`: `fcStep?` agrees with the FCdot step relation, at every fuel and up to a fuel, and a state with no step at any fuel is final or stuck.

## The examples

`Examples.lean` takes every program through the pipeline. Each one is
compared with the version's hand written derivation on four decidable
things: the resolved or elaborated term, the use set and the type, the
checker's verdict on the translation, and its verdict on the use set
evidence. The term, the use set and the type are read off the version's
derivation, not copied. The typer is structural, so the kernel reduces it,
and every comparison but the two checker runs is a `decide +kernel`.

Without the ascriptions that name the version's types, the typer finds
judgments more precise than the version's. S1 then types at `{}` against the
version's `{k1}`, and C2 at `{k2}` against `{k1, k2}`. The two effect
theorems rest on these least use sets. Two runs, S2 and C2, are printed with
the platform's names and pinned at their step counts, fifteen and twelve.

## What it leaves out

- No completeness theorem for the typer. E10, `λ(f : ⊤). λ(g : ⊤). f (g f)`, is rejected because `f` is not a function. Its variant `E10t` at `∀(x : ⊤) ⊤` is accepted.
- No semantic statement for let insertion or for box inference. The meaning of a surface program is the term the resolver returns. What relates it to the elaborated term is the skeleton equation.
- No safety theorem at an open context. C5 is typed through `synthIn?` at `S2Ctx3` and its translation is checked, but the version's safety and effect theorems speak of a program over a platform.
- `any` in the outer set of a parameter type, and reach capabilities. The version leaves them out and the resolver rejects them.
- Scopes, levels and fresh capabilities. They are the `CapturesCC` development.

## Building

`lake build CapturesFrontend`. It is not a default target, so building the
metatheory does not wait on it. Every definition is structural, and
`#assert_no_wf CapturesFrontend` at the end of the root module fails the
build on a definition compiled by well-founded recursion. Every theorem
depends on `propext` and `Quot.sound` at most. No proof is left open, the
library declares no axiom, and there is no Mathlib.
