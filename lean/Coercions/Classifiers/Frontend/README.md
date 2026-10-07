# Classifiers front end

A way to write, type and run programs of the `Classifiers` development
without assembling derivations by hand. `Classifiers` is capture checking
the way the Scala 3 compiler does it, with capability classifiers: a
capability may be declared at a classifier such as `Control` or
`ThreadLocal`, and a capture set may be filtered by a kind, as in
`{ctl, io}.only[Control]`. A program is written in the paper's notation
inside `clsProg%`. Its header declares the classifiers, the platform's
capabilities with their classifiers, and optionally the use set and the
kind of the whole program. The body is written with capture sets `S ^ C`,
projected atoms and sets `a.only[K]` and `{..}.except[K]`, capture members
bounded by a kind `{C^ : K}`, and the forms of the CapturesCC front end.
The front end resolves names, finds a typing derivation with its use set,
moves it to the declared use set, kinds that set, translates the
derivation to FCdot, and runs the program. It proves nothing new about the
calculi. It imports `../Cls`, `../DotMNF`, `../FCdot` and `../DotToFCdot`
and changes nothing in them.

```lean
def CE1src : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [ctl : Control, io : IO]
    uses {ctl, io}.only[Control]
    kind only[Control]
    let b = ((λ(u : ⊤ ^ {}). u) : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}.only[Control]) in
    let f = ((λ(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}).
                ν(z : {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}. {body = λ(u : ⊤ ^ {}). u})) :
              (∀(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io})
                μ(z. {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}) ^ {body.only[Control]}) ^ {}) in
    let r = f b in
    r
```

This is `Try.apply`. The platform has a control capability `ctl` and an
input and output capability `io`. `f` takes a body closure that may hold
both and returns an object holding the body, at the body's set filtered to
`Control`. The program declares that it uses `{ctl, io}.only[Control]`, the
platform filtered the same way. The typer finds exactly that use set. The
call `f b` answers at `{b ↾ only[Control]}`, and the `let` of `b` replaces
the projected atom by the set `b` is declared at. The filtered entry point
reads the use set as a projection at `only[Control]`, and the theorem
`CE1_reads_only_control` says that a run of the program reads no capability
outside `Control`, so it never reads `io`.

A program runs over its platform, a prefix of capture binders, one per
capability it may use, each declared at a classifier or at none. `compile`
resolves the whole program, types the body at the platform's context, and
moves the derivation to the declared use set. Its result is a verdict. `ok`
holds the resolved program and a `Compiled`, which holds the elaborated
term, its use set, its type, the `DotMNF.HasTy` derivation about its
erasure, and the proof that the elaborated term has the skeleton of the
resolved body. `rejected` holds a reason with its proof. `unknown` says
that nothing was found. `compileKinded` adds a kinding of the use set at a
kind `φ`, and `compileFiltered` the proof that the use set is a projection
at `φ`. `compileAndRun` adds the machine at a step budget.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax `SKind`, `SAtom`, `SCap`, `SShape`, `SType`, `SAns`, `STm`, `SDefs`, the program header `SClsDecls`, `SPlatform` and `SProg`, the `LabelTable`, the conditions `Scoped`, `LabelsIn` and `ClassifiersIn`, the test helper `expect`, and the command `#assert_no_wf` |
| `Notation` | the entry points `clsKind%`, `clsAtom%`, `clsSet%`, `clsShape%`, `clsTy%`, `clsAns%`, `cls%`, `clsDefs%`, `clsProg%` for the paper's notation, and the surface programs of the version's examples |
| `Ann` | `ATm` and `ADefs`, DOT-MNF terms with the annotations the typer needs, their `erase`, and the skeleton `ATm.skel` |
| `Resolve` | the classifier table (`clsTableOf`, `resolveKind`), classified platforms (`resolvePlatform`), name resolution over two kinds of binder, projected atoms and sets, let insertion (`resolveTop`, `resolveIn`, `atomize`), whole programs (`resolveProg`), and totality |
| `Decide` | decision procedures for well-formedness, distinct labels, literal shapes, strengthening at both kinds of binder with the avoidance of a projected binder, the reading `readAt` of `any` and `fresh`, and the projection tests `noProj?` and `unprojSet?` |
| `Kind` | the kinding search `kind?`, structural on its fuel, with its oracle of member typings, and fuel monotonicity |
| `Search` | the `Budget`, the views of a variable, the declaration table with its members bounded by kinds, the searches `subcap?`, `subShape?`, `sub?`, `esub?`, and the certificate lemma `escape_rejected_at` |
| `Adapt` | the result types `Elab` and `Checked`, the box and unbox rules, and box inference at a variable, `adaptVar?` |
| `Typer` | `Reason` and `Verdict`, `synth?`, `check?`, `checkDefs?`, the certificate builder `certify?`, the entry points `synthIn?`, `synthTop?`, `checkIn?`, and the typer's checks |
| `Step` | the DOT-MNF machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdot machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `Kinded`, `Filtered`, `compile`, `compileKinded`, `compileFiltered`, `compileAndRun`, the log `levelSteps`, and the pipeline theorems |
| `Pretty` | printers back to the paper's notation, kinds read through the classifier table (`ppTy`, `ppClsKind`, `ppRun`, `ppRunOver`), no theorems |
| `Examples` | the 23 capture programs typed end to end, seven classifier programs, the comparisons with the hand written derivations of `../DotMNF/Examples.lean`, the rejections with their certificates, the level probes, and four effect theorems |

## The typer

The typer is sound by construction. Every result carries the
`DotMNF.HasTy` derivation of the term it typed, and every kinding the
`DotMNF.CapKind` derivation, so soundness is the result type, and there is
no soundness theorem to state. The typer is incomplete by necessity, since
subcapturing goes through subtyping and DOT subtyping is undecidable. It
runs on a `Budget` of seven counters: rounds of the declaration table,
rounds of the view closure, the fuel of the shape search, the fuel of the
set search, the fuel of the typer, passes of the object rule, and the fuel
of the kinding search. More typer fuel never loses a success (`synth?_le`),
and more kinding fuel never loses a kinding (`kind?_le`). No such claim is
made for the other counters, nor for rejections.

The typer computes the least use set the rules allow, as the CapturesCC
front end does. A variable at a pure type is used at `{}`, any other one at
`{x}`. A call is charged its function and its argument, and a projection its
receiver. A binder that leaves scope is replaced in a set by the set it was
declared at. A projected binder `x ↾ K` is replaced by the set `x` is
declared at, with the evidence `unproj` then `sc-var`. A declared use set
is binding. When it differs from the synthesized one, `compile` searches
for a subcapturing from the synthesized set to the declared one and widens
the derivation by one `sub`.

The classifier rules are searched as follows. The set search tries `unproj`,
`proj` and `projMono` on the whole goal, on each atom of the left side, and
into each projected atom of the right side followed by `elem`. A `proj`
step asks the kinding search for a kinding of its left side. The kinding
search tries, in order, `kproj` at an atom whose own kind is below the
goal, `kcls` at a classified capability, `kvar` and `kcvar` down to a
binder's declared set, `ksel` at a member bounded by a kind, `kprojS` at a
projected selection, and `kle` along `Subcap.var` and `Subcap.selUpper`. A member typing that `ksel` or `kle` reads is taken
from the declaration table, so a member the views never display is not
read. The shape search turns a member bounded by sets into one bounded by a
kind by `capkI`, and widens a kind bound by `capk`.

Every written type is read where it is written. A lambda domain reads
`any` as the arrow's own binder, and `any.except[K]` as that binder under
the filter. A `let` annotation, an ascription and an object's self shape
read `any` as the innermost scope root, or as the platform set where there
is none. A `fresh` in an arrow's result reads as an existential. A written
type that puts `any` or `fresh` where the version gives no reading is
rejected with `anyNotOk` or `freshNotOk`. A `let` annotation names the
answer of the whole `let`, and an ascription `(t : T)` names the type of a
bound term, so the programs write the types of their bound functions as
ascriptions.

Box inference, unpacking and the level rule are the CapturesCC front end's.
The elaborated term may differ from the written one, and `compile` checks
that the two have the same skeleton.

What the typer will not find.

- Everything the CapturesCC front end will not find: a middle type of a transitivity step that the context does not declare, a pack whose witness is neither the payload's own set nor the written bound, and the like.
- A kinding through a member typing the declaration table does not hold.
- A kinding along a subcapturing other than `Subcap.var` and `Subcap.selUpper`, and a free-standing `ksub` other than after `ksel`.
- A filtered route for a declared use set the search does not reach from the synthesized one.
- Anything past the budget.

## Main theorems

The pipeline theorems take a successful `compile` and apply results of the
`Classifiers` development to the derivation it returned. The platform is
the classified one the program declares, and the compiled term is the
erasure of the elaborated one.

- `compile_checks`: the FCdot checker accepts the translated derivation.
- `compile_uses_checks`: the FCdot checker accepts the use set evidence the translation emits.
- `compile_erase`: the translation erases to the compiled term.
- `compile_faithful`: the elaborated term has the skeleton of the resolved body.
- `compile_safe`: every state a run from the platform's initial store reaches is final or can step.
- `compile_not_stuck`: no reachable state is stuck.
- `compile_run_progress`: at any step budget, `run` stops at a final state or at one where `step?` still has a step.
- `compile_capture_prediction`: along any run, the matched target state uses no more than the translation of the use set of the result.
- `compile_effect_safety`: a platform capability `κ` is never a root of a variable a run reads, when the use set writes no projection and does not hold `κ`. Both premises are decided tests. Membership alone is not enough under a projection: `{ctl}.only[Control]` does not hold `ctl` and still reaches it.
- `compile_lvl_safety`: at each entry `lo <: hi` of the log `levelSteps` reads off the derivation, `lo` is confined to every atom that confines `hi`, at every depth of resolution. The log holds the member-free subcapturings of the derivation, each at its own context. A `proj` step whose kinding reads a member bounded by a kind through `ksel` is not member free, so it is not an entry, and the walk goes on inside its kinding. The log has 52 entries on CE1, 106 on CE3, 126 on C2 and 92 on S1.
- `compile_rejected_goal`: a program rejected by a level escape comes with a goal `C <: D` at the context the typer reached, and no member-free subcapturing proves that goal. It does not say that no other derivation types the program.
- `compile_checks_get`, `compile_effect_safety_get`: the same two at a program whose compile succeeds by a decided test.

With a successful `compileKinded` at a kind `φ`:

- `compile_kind_checks`: the FCdot checker accepts the translated kinding.
- `compile_classified_prediction`: along any run, the matched target state uses no more than the translated use set, and its use set is kinded at `φ`.
- `compile_classified_effect_safety`: every root of a variable a run reads carries a classifier `φ` admits.
- `compile_run_classified`: the same at the state the driver `run` returns.

`compileKinded` keeps the kinding the search returns, which may take other rules than a hand written one of the same judgment. With a successful `compileFiltered` at `φ`, whose use set is a projection at `φ`, declared as one or synthesized as one:

- `compile_filtered_kindLe`: the translated use set is kinded at `φ` in the target, with no kinding search.
- `compile_filtered_prediction`, `compile_filtered_effect_safety`: the two classified statements on this route.

On the examples:

- `E1_checks` to `E8_checks`, `C7box_checks`, `C7_checks`, `S3_checks`, `C2_checks`, `S1_checks`, `S2_checks`, `Z1_checks`, `Z2_checks`, `Z3_checks`, `W2_checks`, `CE1_checks`, `CE2_checks`, `CE3_checks`, `CE3s_checks`, `CE4_checks`: the checker accepts the translation of each program, with no hypothesis.
- `E6_checks`, `C5_checks`, `Z1caller_checks`, `Z1tail_checks`, `W2call_checks`, `P1_checks`, `E3retype_checks`: the checker accepts the translation of each program the version types at an open context, at that context.
- `CE1_kind_checks`: the checker accepts the kinding the search found for CE1's use set.
- `CE1_reads_only_control`, `CE3_reads_only_control`: a run of the version's E1 or E3 term over its platform reads only capabilities classified `Control`. CE1 is filtered, CE3 is kinded.
- `CE2_no_thread_local`: a run of the version's E2 term reads no thread-local capability.
- `C2_never_reads_k1`: a run of the version's `C2tm` never reads a variable rooted at `k1`.
- `Esc_rejected'`, `top_escape_rejected`, `W5_escape_rejected`: the certificates of the CapturesCC front end, on this tree.

Supporting results:

- `resolveKind_isSome`, `resolvePlatform_isSome`, `resolveProg_isSome`, `resolveTm_isSome`: resolution succeeds on scoped programs whose labels and classifiers are in their tables.
- `resolve_noNestedProj`: a resolved atom carries at most one projection.
- `clsTableOf_examples`: the header of the version's examples gives the classifiers `IO`, `ThreadLocal` and `Control`.
- `noProj?_iff`, `unprojSet?_proj`, `tyWf?_iff`, `eTyWf?_iff`, `distinctLabels?_iff`, `literalShape?_iff`: the side conditions are decided.
- `views_mono`, `decls_mono`, `subcap?_le`, `subShape?_le`, `sub?_le`, `esub?_le`, `synth?_le`, `atomKind?_le`, `capKind?_le`, `kind?_le`: more fuel never loses an answer.
- `memberFree?_sound`, `kindMemberFree?_sound`: the decided test for the log is sound.
- `escape_rejected_at`, `ctxWf?_sound`: the certificate lemma and the decided well-formedness of a context.
- `step?_sound`, `step?_complete`, `step?_none_classify`, `fcStep?_sound`, `fcStep?_complete`, `fcStep?_none_iff`, `fcStep?_none_classify`: the two machines agree with the step relations.

## The examples

`Examples.lean` takes the programs of the version's examples through the
pipeline. The 23 capture programs of the CapturesCC front end are whole
programs over plain platform binders here, and each is compared as there:
the resolved or elaborated term, the use set and the type, the checker's
verdict on the translation, and its verdict on the use set evidence. They
are found at the same budgets.

CE1 and CE2, `Try.apply` and `Future.apply`, reach the version's term, use
set and type, and take the filtered route. Their use sets are also kinded
by the search, by `kproj` at each atom where the version writes `kcls`. The
subcapturing a call of `Future.apply` asks for, at the version's context,
is the version's to the letter. CE3, a client against a member bounded by
`only[Control]`, reaches the version's judgment and takes the kinded route,
with the version's kinding to the letter. Its retyping of a literal at the
kind bound is typed at the version's judgment of that step. CE3 over three
`Control` capabilities compiles with no change to the client, and its use
set has the version's kinding over three capabilities. CE4 hands a closure
read off a kind-bounded member to a domain filtered `only[Control]`, which
the search proves through `ksel`. CE5 passes a thread-local body to
`Future.apply` and is not compiled, while the same program with an input
and output body is. CE1, CE2 and CE3 are run, printed with their
platform's names, and pinned at seven, seven and twelve steps.

## What it leaves out

- No completeness theorem for the typer or the kinding search, and no claim that a failure is monotone in the budget.
- No semantic statement for let insertion, box inference or the unpacking of a `let`. What relates the written program to the elaborated term is the skeleton equation.
- No statement that a rejected or uncompiled program has no derivation at all. CE5 is not compiled, and the version proves its refusal separately.
- No run theorem about scopes, for the reason the CapturesCC front end gives: the target's `no_inner_escape` asks for a premise that never holds at a context that types a store.
- No safety theorem at an open context.
- No printer that reads a kind back in every case. A kind the classifier algebra builds as an `only` minus an exclusion prints in a form the notation does not parse.
- `fresh` under a filter, and `fresh` in a lambda domain, which the version keeps out.

## Building

`lake build ClassifiersFrontend`. It is not a default target, so building
the metatheory does not wait on it. Every definition is structural, and
`#assert_no_wf ClassifiersFrontend` at the end of the root module fails the
build on a definition compiled by well-founded recursion. Every theorem
depends on `propext` and `Quot.sound` at most. No proof is left open, the
library declares no axiom, and there is no Mathlib.
