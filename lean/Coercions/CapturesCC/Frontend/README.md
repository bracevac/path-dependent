# CapturesCC front end

This front end writes, types and runs programs of `CapturesCC`. That calculus
is capture checking as the Scala 3 compiler does it. A type `S ^ C` is a type
`S` whose values may use the capabilities in the set `C`, and scopes and levels
stop a capability from outliving its scope. A program is written in the
paper's notation inside `cc%`. The front end resolves names, inserts `let`s,
boxes `□ T` and unboxings `C ⊸ x`, and finds a typing derivation together
with its use set, the capabilities the program may use. It translates the
derivation to FCdot, the target calculus with its own checker and machine, and
runs the program. A program whose capability escapes its scope is rejected
with a proof. Nothing here is new metatheory.

```lean
def EscSrc : STm :=
  cc% λ(g : ⊤).
    let cb : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
                (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ^ {any}) ^ {}
      = λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). f
    in cb
```

This is the `withFile` escape. The callback `cb` takes a file `f` and returns
a closure that holds it. The `any` in the result names the root of the scope
the annotation is written in, the body of `λ(g : ⊤)`, which lies outside the
scope of `f`. The typer rejects the program with a proof that no member-free
subcapturing puts `{f}` below that root. A subcapturing is member-free when it
uses no instance binder and no bound of a selection. With its result written
at `{f}`, the callback is accepted.

A program runs over a platform, one capture binder per capability it may use,
such as `πc` with `k1` and `k2`. `compile b Λ π e` types `e` over `π` with the
fuel of `b : Budget` and returns a `Verdict`. The `LabelTable` `Λ` lists the
field labels. `ok` holds the elaborated term, its use set, its type and its
derivation. `rejected` holds a reason with its proof. `unknown` says that the
typer found no type and no reason, or reached the recursion limit.
`compileAndRun` also runs the program.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax and the table of field labels |
| `Notation` | the notation `cc%` and its kin |
| `Ann` | terms with the annotations the typer needs |
| `Resolve` | name resolution, scope roots, `let` insertion and the platforms |
| `Decide` | decision procedures for well-formedness and labels |
| `Search` | the first view of a variable and the certificate of an escape |
| `Look` | the fuel and member lookup |
| `Sub` | subtyping and subcapturing in the compiler's case order |
| `Alg` | the algorithmic judgment `Alg`, its completeness and soundness |
| `Avoid` | avoidance at a `let` and at an unpacking |
| `Adapt` | box adaptation at a variable |
| `Typer` | the typer and its verdicts |
| `Step` | the source machine as a function |
| `StepFC` | the FCdot machine as a function |
| `Pipeline` | `compile`, `compileAndRun` and the pipeline theorems |
| `Pretty` | printers back to the notation |
| `Examples` | the programs end to end, each verdict checked in the kernel |

## The typer

The typer follows the subtype checker of the Scala 3 compiler, pinned as
scala/scala3 at commit 4dae25087d: the case order of `TypeComparer.firstTry`
and its kin, `CaptureSet.subCaptures`, and the levels of
`LocalCap.acceptsLevelOf` (cc/Capability.scala). It approximates an
unannotated `let` as `TypeOps.avoid` does and inserts boxes as
`CheckCaptures.adaptBoxed` does. It runs on one fuel tank for the whole typing.
When the tank runs short, it reports a recursion limit, which is never a
rejection. Up to that limit it is complete with respect to its algorithmic
judgment `Alg`, which its search follows. It rejects what scalac rejects. The
examples E1, E3, E4 and B1 in `Examples` need a middle type the program does
not write, and the typer chooses none. Written with that type, E1 and E3
compile. What the programmer writes binds. A written `any` is read at the
scope it is written in, and a `fresh` in an arrow's result is an existential.

## Main theorems

- `compile_checks`, `compile_uses_checks`: the FCdot checker accepts the translated derivation and its use set.
- `compile_erase`, `compile_faithful`: the translation erases to the compiled term, which differs from the resolved program only in annotations, boxes and ascriptions.
- `compile_safe`, `compile_not_stuck`, `compile_run_progress`: no run reaches a stuck state, and `run` stops at a final state or at one that can still step.
- `compile_capture_prediction`: along a run, the matched FCdot state uses no more than the use set the typer found.
- `compile_effect_safety`: a run never reads a variable rooted at a capability outside that use set, as `C2_never_reads_k1` shows in `Examples`.
- `compile_lvl_safety`: at each subcapturing `lo <: hi` of the derivation that is member-free, if no atom of `hi` lies strictly inside a scope root, none of `lo` does.
- `compile_rejected_goal`: a program rejected for an escape names the goal it reached, which no member-free subcapturing proves.
- `shape?_complete`, `subcap?_complete`, `esub?_complete`, `sub?_complete`, `var?_complete`: a goal `Alg` derives is answered unless the tank runs short.
- `shape?_reject`, `subcap?_reject`, `esub?_reject`, `sub?_reject`, `var?_reject`: a rejection before the limit means `Alg` derives no such goal.
- `Alg.sound`: a goal `Alg` derives has a derivation in `CapturesCC`.
- `synthTop?_mono`, `synthTop?_stable`: an answer, or a rejection before the limit, stays the same at more fuel.

## What it leaves out

- A derivation through a middle type the program does not write.
- A merge of two members of one name, where the typer tries each member.
- A judgment whose search needs more than the fuel, such as Pierce's divergence of F<:.
- A lookup through a cyclic member, which is cut as the compiler cuts it.
- A completeness theorem for the typer as a whole.
- A semantic statement for `let` insertion or box inference, or for `fresh` in a lambda domain, which the resolver rejects.

## Building

`lake build CapturesCCFrontend`, which is not a default target. Every
definition is structural, so the kernel runs the typer. Every theorem depends
on `propext` and `Quot.sound` at most. There is no `sorry`, `axiom`,
`native_decide` or Mathlib.
