# CapturesCC front end

This front end writes, types and runs programs of `CapturesCC`. That calculus
is capture checking as the Scala 3 compiler does it. A type `S ^ C` is a type
`S` whose values may use the capabilities in the set `C`, and scopes and levels
stop a capability from outliving its scope. A program is written in the
paper's notation inside `cc%`. The front end resolves names, inserts `let`s,
boxes `□ T` and unboxings `C ⊸ x`, and fills the annotations the program
leaves out. It finds a typing derivation together with its use set, the
capabilities the program may use. It translates the derivation to FCdot, the
target calculus with its own checker and machine, and runs the program. A
program whose capability escapes its scope is rejected with a proof. Nothing
here is new metatheory.

```lean
def EscSrc : STm :=
  cc% λ(g : ⊤).
    let cb : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
                (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ^ {any}) ^ {}
      = λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). f
    in cb
```

This is the `withFile` escape. The callback `cb` takes a file `f` and returns
a closure that holds it. The `any` in the result names the root of the body of
`λ(g : ⊤)`, which lies outside the scope of `f`. The typer rejects the program
with a proof that no member-free subcapturing puts `{f}` below that root. A
subcapturing is member-free when it uses no instance binder and no bound of a
selection. With its result written at `{f}`, the callback is accepted. The type
of `cb` is written, so its domains can go: `λf. λu. f` is rejected the same way.

A program runs over a platform, one capture binder per capability it may use,
such as `πc` with `k1` and `k2`. `compile b Λ π e` resolves `e` over `π` with
the label table `Λ` and types it within the fuel of `b : Budget`, by default
`defaultFuel = 2 ^ 15`. It returns a `Verdict`. `ok` holds the filled term and
a `Compiled`: the elaborated term, its use set, its type and its derivation.
`rejected` holds a reason with its proof. `unknown` says the typer found no
type and no such reason, or reached the recursion limit. `compileE` returns
the reason of every rejection and `ppReason` prints it. `compileAndRun` also
runs the program.

## What the programmer may leave out

The domain of a lambda: `λy. y` is enough where the context says what `y` is.
The self shape of an object literal: `ν(z. {a = v})` has no shape written on
it. The type of a field, the box at an argument and the unboxing at a use. A
program that writes every domain and self shape is typed as it is, at the same
fuel.

## Where an expected type comes from

The elaborator checks a term against a goal and passes the goal down. The goal
of a `let` body is its written type, the goal of `t` in `(t : U)` is `U`, and
the goal of `t` in `let x : A = t in x` is `A`. The goal of a call argument is
the dominant formal of the callee, the parameter type that the others of an
intersection of functions lie below, whole, and a box on it is stripped. The
goal of a field is its declaration in the self shape. A lambda takes its
domain from the function part of its goal, looking through a box and an alias
and dropping the capture set, or from `g` when its body is `g x`. An object
literal takes its self shape from a `μ` goal, or else forms it from its
fields. If the attempt at a goal fails, the typer's own route runs.

## The compiler's errors

A lambda with no domain and no goal with a function part is rejected with
"Missing parameter type", as scalac does. Fields without written types that
read each other in a cycle are rejected with "Recursive value a needs type",
the compiler's cyclic reference. A field whose type holds a root capability
the self shape cannot state needs a written type, as
`CheckCaptures.checkInferredResult` asks. The others are candidates with no
least type, a type mismatch, a level escape with its proof, and the recursion
limit. Only a program with an empty slot gets the first four (`compileE_slot`).

## Modules

| module | contents |
|---|---|
| `Surface`, `Notation`, `Ann`, `Resolve` | the surface syntax and `cc%`, terms with annotations and partial terms, name resolution, `let` insertion and the platforms |
| `Decide`, `Search`, `Look` | decision procedures, the first view of a variable, the certificate of an escape, the fuel and member lookup |
| `Sub`, `Alg` | subtyping and subcapturing in the compiler's case order, the judgment `Alg`, its completeness and soundness |
| `Avoid`, `Adapt`, `Typer` | avoidance, box adaptation, the typer and its verdicts |
| `Elab`, `Step`, `StepFC` | the elaborator that fills the empty slots of a partial term, the source and FCdot machines as functions |
| `Pipeline` | `compileE`, `compile`, `compileAndRun`, the pipeline theorems and completeness at the direct sites |
| `Pretty`, `Examples` | printers back to the notation, and the programs end to end, each verdict checked in the kernel |

## The typer

The typer follows the Scala 3 compiler, pinned as scala/scala3 at commit
4dae25087d: the case order of `TypeComparer.firstTry`
and its kin, `CaptureSet.subCaptures`, and the levels of
`LocalCap.acceptsLevelOf` (cc/Capability.scala). It approximates an
unannotated `let` as `TypeOps.avoid` does and inserts boxes as
`CheckCaptures.adaptBoxed` does. It runs on one fuel tank for the whole typing,
the elaborator's included. When the tank runs short, it reports a recursion
limit, which is never a rejection. Up to that limit it is complete with
respect to its algorithmic judgment `Alg`, which its search follows. E1, E3,
E4 and B1 in `Examples` need a middle type the program does not write, and the
typer chooses none, as scalac. What the programmer writes binds. A written
`any` is read at the scope it is written in, and a `fresh` in an arrow's result
is an existential.

## Main theorems

- `compile_checks`, `compile_uses_checks`: the FCdot checker accepts the translated derivation and its use set. `compile_erase`, `compile_faithful`: the translation erases to the compiled term, which has the skeleton of the fill.
- `compile_safe`, `compile_not_stuck`, `compile_run_progress`: no run reaches a stuck state.
- `compile_capture_prediction`: along a run, the matched FCdot state uses no more than the use set the typer found.
- `compile_effect_safety`: a run never reads a variable rooted at a capability outside that use set, as `C2_never_reads_k1` shows in `Examples`.
- `compile_lvl_safety`: at each member-free subcapturing `lo <: hi` of the derivation, if no atom of `hi` lies strictly inside a scope root, none of `lo` does. `compile_rejected_goal`: a program rejected for an escape names a goal no member-free subcapturing proves.
- `shape?_complete`, `subcap?_complete`, `esub?_complete`, `sub?_complete`, `var?_complete` and the `_reject` versions: a goal `Alg` derives is answered unless the tank runs short, and a rejection before the limit means `Alg` derives no such goal. `Alg.sound`: a goal `Alg` derives has a derivation in `CapturesCC`.
- `synthTop?_mono`, `synthTop?_stable`, `elabTop?_mono`, `elabTop?_stable`: an answer, or a rejection before the limit, stays at more fuel.
- `compile_full`, `compileE_fills`: a program with every slot written compiles as the typer's verdict on it, and the fill agrees with every written slot.
- `elab_complete_direct`, `compile_complete_direct`, `compile_complete_canonAt`: where the elaborator runs the typer's own clause on the fill, a canonical fill the typer accepts is found from some fuel on, and an erased program compiles as the written one.
- In `Examples`, for a program `X`: `X_type`, `X_checks`, `X_rejected`, `X_erased` for the erasure tables, `X_complete` where completeness applies, and `LP_limit` and `PF_limit` at the limit.

## What it leaves out

- A derivation through a middle type the program does not write.
- A union of two domains, which scalac forms and the typer rejects as a mismatch, and a merge of two members of one name, where the typer tries each member.
- A judgment whose search needs more than the fuel, such as Pierce's divergence of F<:.
- Completeness over every filling, which fails at a call argument the typer types only at a non-dominant formal (Mid), and for the typer as a whole.
- A semantic statement for `let` insertion or box inference.

## Building

`lake build CapturesCCFrontend`, which is not a default target. Every
definition of the front end is structural, so the kernel runs the typer. That
includes the level-escape verdicts: `certify?` resolves with `capsS`, the
structural form of the well-founded `FCdot.Ctx.caps`. Every theorem depends
on `propext` and `Quot.sound` at most. There is no `sorry`, `axiom`,
`native_decide` or Mathlib.
