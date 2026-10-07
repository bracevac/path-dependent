# CapturesCC front end

A way to write, type and run programs of the `CapturesCC` development
without assembling derivations by hand. `CapturesCC` is capture checking the
way the Scala 3 compiler does it, with scopes, levels and fresh
capabilities. A program is written in the paper's notation inside `cc%`,
with capture sets `S ^ C`, the atoms `any` and `fresh`, arrows that may name
their own capture binder, `∀[c](x : T) U`, existential answers
`∃[c ⊑ C] T`, boxes `□ T`, unboxings `C ⊸ x` and unpackings
`let ⟨c, x⟩ = t in u`. The front end resolves names, inserts the scope
roots and binders a lambda and an object open, and inserts `let`s to reach
monadic normal form. It then finds a typing derivation with its use set,
inserts the boxes, unboxings and unpackings the program left out,
translates the derivation to FCdot, and runs the program. It proves nothing
new about the calculi. It imports `../DotMNF`, `../FCdot`, `../DotToFCdot`
and `../Runtime.lean` and changes nothing in them.

```lean
def EscSrc : STm :=
  cc% λ(g : ⊤).
    let cb : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
                (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ^ {any}) ^ {}
      = λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). f
    in cb
```

This is the `withFile` escape. The callback `cb` takes a file and returns
a closure that holds it. Its annotation is written in the body of
`λ(g : ⊤)`, so the parameter `any` reads as the arrow's own binder and the
two result `any`s read as the root of `g`'s body. The closure the callback
returns holds its parameter, but the annotation charges that closure to the
root of `g`'s body, a scope outside the parameter's. The typer rejects the
program with the goal `{f} <: {κ_g}` at the context that binds `cb` and
opens the callback's scope, and a certificate that no member-free
subcapturing proves that goal. Annotated with its result at `{f}`, the same
callback is accepted.

A program runs over a platform, a prefix of capture binders, one per
capability it may use. `πc` of `Resolve.lean` names two, `k1` and `k2`, and
`πz` names the same two binders `fs` and `k2`. `compile` runs the resolver
and then the typer at the platform's context. Its result is a verdict. `ok`
holds the resolved term and a `Compiled`, which holds the elaborated term,
its use set, its type, the `DotMNF.HasTy` derivation about its erasure, and
the proof that the elaborated term has the skeleton of the resolved one.
`rejected` holds a reason with its proof. `unknown` says that nothing was
found. `compileAndRun` adds the machine at a step budget.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax `SAtom`, `SCap`, `SShape`, `SType`, `SAns`, `STm`, `SDefs`, `SProg`, the `LabelTable`, the conditions `Scoped` and `LabelsIn`, the test helper `expect`, and the command `#assert_no_wf` |
| `Notation` | the entry points `ccSet%`, `ccShape%`, `ccTy%`, `ccAns%`, `cc%`, `ccDefs%`, `ccProg%` for the paper's notation, and the surface programs of the version's examples |
| `Ann` | `ATm` and `ADefs`, DOT-MNF terms with the annotations the typer needs, their `erase`, and the skeleton `ATm.skel` |
| `Resolve` | name resolution over two kinds of binder, the inserted scope roots and binders, let insertion (`resolveTop`, `resolveIn`, `atomize`), platforms (`PlatformNames`, `πc`, `πz`), and totality |
| `Decide` | decision procedures for well-formedness (`tyWf?`, `eTyWf?`), distinct labels, literal shapes, strengthening at both kinds of binder, and the reading `readAt` of `any` and `fresh` |
| `Search` | the `Budget`, the views of a variable, the declaration table, the searches `subcap?`, `subShape?`, `sub?`, `esub?`, and the certificate lemma `escape_rejected_at` |
| `Adapt` | the result types `Elab` and `Checked`, the box and unbox rules, and box inference at a variable, `adaptVar?` |
| `Typer` | `Reason` and `Verdict`, `synth?`, `check?`, `checkDefs?`, the certificate builder `certify?`, the entry points `synthIn?`, `synthTop?`, `checkIn?`, and the typer's checks |
| `Step` | the DOT-MNF machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdot machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `compileAndRun`, the log `levelSteps`, and the pipeline theorems |
| `Pretty` | printers back to the paper's notation (`ppTy`, `ppETy`, `ppATm`, `ppRun`, `ppRunOver`), no theorems |
| `Examples` | 23 programs typed end to end and compared with the hand written derivations of `../DotMNF/Examples.lean`, the rejections with their certificates, the level probes, and an effect theorem |

## The typer

The typer is sound by construction. Every result carries the
`DotMNF.HasTy` derivation of the term it typed, so soundness is the result
type, and there is no soundness theorem to state. The typer is incomplete by
necessity, since subcapturing goes through subtyping and DOT subtyping is
undecidable. It runs on a `Budget` of six counters: rounds of the
declaration table, rounds of the view closure, the fuel of the shape search,
the fuel of the set search, the fuel of the typer, and passes of the object
rule. More typer fuel never loses a success (`synth?_le`). No such claim is
made for the other counters, nor for rejections.

The typer computes the least use set the rules allow. A variable at a pure
type is used at `{}`, any other one at `{x}`. A call is charged its function
and its argument, and a projection its receiver. A binder that leaves scope
is replaced in a set by the set it was declared at, and the result is
followed by evidence from the search. The level rule lets a binder of a
scope be absorbed into the root of that scope or of a scope inside it.

Every written type is read where it is written. A lambda domain reads
`any` as the arrow's own binder. A `let` annotation, an ascription and an
object's self shape read `any` as the innermost scope root, or as the
platform set where there is none. A `fresh` in an arrow's result reads as an
existential bounded by the arrow's own set and its parameter. A written type
that puts `any` or `fresh` where the version gives no reading is rejected
with `anyNotOk` or `freshNotOk`.

For a `let`, a written annotation is binding, and only it is tried. Without
one the result is the body's type strengthened past the binder, else `⊤` at
the avoided set. When the bound term's answer is an existential, the `let`
becomes an unpacking `letex`, and the body's answer leaves the witness and
the payload by strengthening or by the level rule into the innermost root.
An ascription `(t : T)` names the type of a bound term. A failed binding
annotation or ascription is examined for a rejection: the typer walks the
two types the way the search does and looks for a set goal it can certify.
The certificate is `escape_rejected_at`, the contrapositive of the
version's `source_lvl_safety`, at the context the walk reached. Otherwise
the verdict is `unknown`.

Box inference is the Captures front end's. A variable checked against a
goal is boxed or unboxed when a view of it calls for it, and an insertion
at an argument, a function or a receiver is bound by a new `let`. So the
elaborated term differs from the written one, and `compile` checks that the
two have the same skeleton. The skeleton forgets annotations, capture sets,
boxes, unboxings, ascriptions and capture binders, inlines a `let` of a
variable, and does not tell `let` from `letex`.

The user writes these annotations. A lambda carries its domain type. An
object literal carries its self shape. A `let` may carry its answer, and an
ascription names the type of a bound term. A type member bound is a shape,
so a capturing type in a member is written boxed, `□ T`.

What the typer will not find.

- A middle type of a transitivity step that the context does not declare.
- A subcapturing through a chain of capture members longer than the set search's fuel.
- A pack whose witness is neither the payload's own set nor the written bound.
- A pack whose payload has the existential's type only after retyping a variable at a recursive type. `mk` with a `fresh` result is found once its body ascribes the literal's variable at the iterator type.
- A `fresh` absorbed into a root other than the innermost one of the unpacking's context.
- A rejection outside the member-free derivations of the goal the walk reached, and a goal whose target set holds an instance binder or a capture member. Both are `unknown`.
- An object whose definitions are not stable after `Budget.obj` passes of the object rule.
- Anything past the budget.

## Main theorems

The pipeline theorems take a successful `compile` and apply results of the
`CapturesCC` development to the derivation it returned. The platform is
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
- `compile_lvl_safety`: at each entry `lo <: hi` of the log `levelSteps` reads off the derivation the typer found, `lo` is confined to every atom that confines `hi`, at every depth of resolution. The log holds the member-free subcapturings of the derivation, each at its own context, so the statement is about the steps the typer took. The log has 126 entries on C2 and 92 on S1, and the log of the caller of `freshCell` at `Z1Ctx` has 23.
- `compile_rejected_goal`: a program rejected by a level escape comes with a goal `C <: D` at the context `Γ` the typer reached, and no member-free subcapturing proves that goal. It is about that goal and the written annotation. It does not say that no other derivation types the program, and the erasure of a rejected program may type at another type.
- `compile_checks_get`, `compile_effect_safety_get`: the same two at a program whose compile succeeds by a decided test.
- `E1_checks` to `E8_checks`, `C7box_checks`, `C7_checks`, `S3_checks`, `C2_checks`, `S1_checks`, `S2_checks`, `Z1_checks`, `Z2_checks`, `Z3_checks`, `W2_checks`: the checker accepts the translation of each example program, with no hypothesis.
- `E6_checks`, `C5_checks`, `Z1caller_checks`, `Z1tail_checks`, `W2call_checks`, `P1_checks`: the checker accepts the translation of each program the version types at an open context, at that context. They are `synthIn_checks_get`, the open twin of `compile_checks_get`.
- `Esc_rejected'`: no member-free subcapturing puts `{f}` below the root of `g`'s body at `EscGoalCtx`, the context the typer reached on the escape, which binds `cb`.
- `top_escape_rejected`: the same at the top of a program, below the platform set, at `TopGoalCtx`. Its root is the universal one, which the source cannot name.
- `W5_escape_rejected`: at the version's `W5Ctx`, no member-free subcapturing puts the callback's parameter below the root of the scope outside the call.
- `C2_never_reads_k1`: a run of the version's `C2tm` never reads a variable rooted at `k1`. The typer finds the use set `{k2}` for C2.

Supporting results:

- `resolveTm_isSome`, `resolveDefs_isSome`, `resolveTy_isSome`, `resolveAns_isSome`: resolution succeeds on scoped programs whose labels are in the table and whose `fresh` is placed where the version reads it.
- `resolve_noAny`: a program that writes no `any` resolves to annotations with none.
- `atomize_var`: let insertion inserts nothing at a variable.
- `ATm.skel_rename_succLift`, `ATm.skel_letex_of_let`: an unpacking has the skeleton of the `let` it replaces.
- `tyWf?_iff`, `eTyWf?_iff`, `defsDistinct?_iff`, `literalShape?_iff`, `distinctLabels?_iff`: the side conditions are decided.
- `tyStrengthenW?_weaken`: strengthening undoes a weakening at either kind of binder.
- `views_mono`, `decls_mono`, `subcap?_le`, `sub?_le`, `esub?_le`, `synth?_le`: more fuel never loses an answer.
- `escape_rejected_at`: at a well formed context, no member-free subcapturing proves `C <: D` when every resolution of `D` is confined to an atom and one resolution of `C` is not.
- `ctxWf?_sound`: a context the decision procedure accepts is well formed.
- `step?_sound`, `step?_complete`, `step?_none_classify`: `step?` agrees with the DOT-MNF step relation, and a state with no step is final or stuck.
- `fcStep?_sound`, `fcStep?_le`, `fcStep?_complete`, `fcStep?_none_iff`, `fcStep?_none_classify`: `fcStep?` agrees with the FCdot step relation, at every fuel and up to a fuel, and a state with no step at any fuel is final or stuck.

## The examples

`Examples.lean` takes the programs of the version's examples through the
pipeline. Each is compared with the version's hand written derivation on
four decidable things: the resolved or elaborated term, the use set and the
type, the checker's verdict on the translation, and its verdict on the use
set evidence. The term, the use set and the type are read off the version's
derivation, not copied. The typer is structural, so the kernel reduces it,
and every comparison but the checker runs is a `decide +kernel`. A program
the version types under a context is typed there, through `synthIn?`.

Without an ascription that names the version's type, the typer finds a
smaller judgment where the rules allow one. C2 then types at `{k2}` against
the version's `{k1, k2}`, C5 at `{it, it.C}` against `{fs, k2}`, and the
caller of `freshCell` at `{fc, fs, un}` against `{fs, un, fs, un}`. Each
time the version's judgment is reached by one `sub` the search finds. The
caller's `let` becomes an unpacking, and its elaborated term erases to the
version's term. Two calls of `freshCell` open two capture binders that the
search does not relate in either direction.

The rejections are tested too. A domain with `any` below a field is rejected
with `anyNotOk` in the kernel. The escape and the escape at the top are
rejected with `levelEscape`, whose certificate reads `Ctx.caps`, which is
defined by well-founded recursion, so the verdict is an `expect` test and
the certificate at the reached goal is the separate theorem. The level
probes W1 and W5 ask the search for the steps of the level order at the
version's contexts. Three runs, S2, C2 and E2, are printed with the
platform's names and pinned at their step counts, fifteen, twelve and six.

## What it leaves out

- No completeness theorem for the typer, and no claim that a rejection is monotone in the budget.
- No semantic statement for let insertion, box inference or the unpacking of a `let`. The meaning of a surface program is the term the resolver returns. What relates it to the elaborated term is the skeleton equation.
- No statement that a rejected program has no derivation at all. A rejection is about the goal the typer reached under the written annotation.
- No run theorem about scopes. The target's `no_inner_escape` asks for a capture variable that is not at or outside the level of an atom, at a context that types a store. Such a context has no root, every binder sits at the outermost level, and that premise never holds. Scopes are spoken of at the contexts the typer opens, by `compile_lvl_safety` for what it accepted and by the certificates for what it rejected.
- No safety theorem at an open context. The open examples are typed through `synthIn?` and their translations are checked, but the version's safety and effect theorems speak of a program over a platform.
- `fresh` in a lambda domain. The version keeps `fresh` out of parameter types, and the resolver rejects it.
- The version's W6, a binder order the rules never produce.

## Building

`lake build CapturesCCFrontend`. It is not a default target, so building
the metatheory does not wait on it. Every definition is structural, and
`#assert_no_wf CapturesCCFrontend` at the end of the root module fails the
build on a definition compiled by well-founded recursion. Every theorem
depends on `propext` and `Quot.sound` at most. No proof is left open, the
library declares no axiom, and there is no Mathlib.
