# CapturesCC front end

A way to write, type and run programs of `CapturesCC`, capture checking
with the Scala 3 compiler's scopes and levels, without assembling
derivations by hand. A program is written in the paper's notation inside
`cc%`. The front end resolves names and inserts `let`s to reach monadic
normal form. It finds a typing derivation with its use set, the set of
capabilities the program may use. It translates the derivation to FCdot, the
target calculus, and runs the program. Like the `Captures` front end, it
inserts the boxes `□ T` and unboxings `C ⊸ x` the program leaves out. It
also reads `any` and `fresh` by the scope they are written in, and it
rejects a program whose capability escapes its scope, with a proof. It
proves nothing new about the calculi. It imports `../DotMNF`, `../FCdot`,
`../DotToFCdot` and `../Runtime.lean` and changes nothing in them.

```lean
def EscSrc : STm :=
  cc% λ(g : ⊤).
    let cb : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
                (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ^ {any}) ^ {}
      = λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). f
    in cb
```

This is the `withFile` escape. The callback `cb` takes a file `f` and
returns a closure that holds it. The `any` in the result stands for the
capability root of the scope the annotation is written in, here the body of
`λ(g : ⊤)`. So the annotation charges the closure to a scope outside the
one of `f`. The typer rejects the program with a proof that no member-free
subcapturing, one that does not go through a capture member of a type, puts
`{f}` below that root. Written with its result at `{f}`, the same callback
is accepted.

A program runs over a platform, one capture binder per capability it may
use, such as `πc` with `k1` and `k2`. `compile` types a program over a
platform and returns a `Verdict`. `ok` holds a `Compiled`: the elaborated
term, its use set, its type and the `DotMNF.HasTy` derivation. `rejected`
holds a `Reason` with its proof, and `unknown` says that nothing was found.
`compileAndRun` adds the machine, which runs from the platform's initial
store, at a step budget.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax, the `LabelTable` of field labels, and the test helper `expect` |
| `Notation` | the entry points `cc%`, `ccTy%` and their kin for the paper's notation |
| `Ann` | DOT-MNF terms with the annotations the typer needs, their `erase`, and the skeleton `ATm.skel` |
| `Resolve` | name resolution, scope roots, let insertion, and the platforms `πc` and `πz` |
| `Decide` | decision procedures for well-formedness, distinct labels and strengthening |
| `Search` | the `Budget`, the subtyping and subcapturing searches, and the certificate lemma `escape_rejected_at` |
| `Adapt` | box inference at a variable |
| `Typer` | `Verdict`, `Reason`, `synth?`, `check?` and the entry points `synthTop?` and `synthIn?` |
| `Step` | the DOT-MNF machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdot machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `compileAndRun` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation, no theorems |
| `Examples` | the programs of `CapturesCC` taken end to end and compared with its hand-written derivations |

## The typer

The typer is sound by construction. Every result carries the `DotMNF.HasTy`
derivation of the term it typed, so there is no soundness theorem to state.
It is incomplete, since DOT subtyping is undecidable, and it runs on a
`Budget` of fuel. More typer fuel never loses a success. It finds the least
use set the rules allow.

Each written type is read where it is written. In a parameter type, `any`
is the arrow's own capture binder. Elsewhere it is the root of the innermost
scope, or the platform set at the top. A `fresh` in an arrow's result is an
existential, and a `let` of such a call becomes an unpacking. A written type
that puts `any` or `fresh` where `CapturesCC` gives it no reading is
rejected. A `Reason` is such a misplaced atom, a level escape, or an
existential answer at the top of a program.

The user writes four kinds of annotation. A lambda carries its domain type.
An object literal carries its self type. A `let` may carry its type, and an
ascription `(t : T)` names the type of a bound term. A type member bound is
a shape, so a capturing type in a member is written boxed, `□ T`. A written
type is binding. When the typer cannot meet it, it looks for a goal it can
refute and returns a rejection, else `unknown`. Box inference changes the
term, so `compile` checks that the typed term has the skeleton of the
resolved one. The skeleton forgets annotations, capture sets, boxes,
unboxings and capture binders.

## Main theorems

The pipeline theorems take a successful `compile` and apply results of the
`CapturesCC` development to the derivation it returned.

- `compile_checks`: the FCdot checker accepts the translated derivation.
- `compile_uses_checks`: the FCdot checker accepts the use set evidence of the translation.
- `compile_erase`: the translation erases to the compiled term.
- `compile_faithful`: the typed term has the skeleton of the resolved one.
- `compile_safe`, `compile_not_stuck`: every state a run from the platform reaches is final or can step, so none is stuck.
- `compile_run_progress`: at any step budget, `run` stops at a final state or at one where `step?` still has a step.
- `compile_capture_prediction`: along any run, the matched FCdot state uses no more than the use set the typer found.
- `compile_effect_safety`: a platform capability outside that use set is never a root of a variable a run reads, in the matched FCdot state.
- `compile_lvl_safety`: in each member-free subcapturing `lo <: hi` of the derivation, every scope root that bounds `hi` also bounds `lo`.
- `compile_rejected_goal`: a program rejected for an escape names a goal at the context the typer reached, and no member-free subcapturing proves it.
- `E1_checks` to `E8_checks`, `C2_checks`, `S1_checks` and the other `_checks`: the checker accepts each example's translation, with no hypothesis.
- `Esc_rejected'`, `top_escape_rejected`: the escape above, and the same callback at the top of a program, are refuted at the goal the typer reached.
- `C2_never_reads_k1`: a run of the example C2 in `Examples` never reads a variable rooted at `k1`.

## What it leaves out

- No completeness theorem for the typer.
- No semantic statement for let insertion or box inference. The meaning of a surface program is the term the resolver returns.
- A rejection is about the goal the typer reached under the written types. It does not say that no other derivation types the program.
- No safety theorem at an open context. Programs that need a context are typed there by `synthIn?`, and only their translations are checked.
- No run theorem about scopes. Scopes are covered by `compile_lvl_safety` and by the certificates of rejections.
- `fresh` in a lambda domain, which `CapturesCC` keeps out of parameter types and the resolver rejects.

## Building

`lake build CapturesCCFrontend`. It is not a default target, so building
the metatheory does not wait on it. Every definition is structural, so the
kernel runs the typer, and the build fails on a definition that is not.
Every theorem depends on `propext` and `Quot.sound` at most. There is no
`sorry`, `axiom` or `native_decide`, and no Mathlib.
