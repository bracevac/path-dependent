# CapturesCC front end

A way to write, type and run programs of `CapturesCC`, capture checking with
the Scala 3 compiler's scopes and levels, without assembling derivations by
hand. A program is written in the paper's notation inside `cc%`. The front end
resolves names and inserts `let`s, finds a typing derivation with its use set,
the capabilities the program may use, translates it to FCdot and runs the
program. It inserts the boxes `□ T` and unboxings `C ⊸ x` a program leaves
out, and rejects a program whose capability escapes its scope, with a proof.
It proves nothing new about the calculi and changes nothing in the version.

```lean
def EscSrc : STm :=
  cc% λ(g : ⊤).
    let cb : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
                (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ^ {any}) ^ {}
      = λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). f
    in cb
```

This is the `withFile` escape. The callback `cb` takes a file `f` and returns
a closure that holds it. The `any` in the result is the root of the scope the
annotation is written in, the body of `λ(g : ⊤)`, outside the one of `f`. The
typer rejects the program with a proof that no member-free subcapturing, one
that reads no capture member, puts `{f}` below that root. Written with its
result at `{f}`, the same callback is accepted.

A program runs over a platform, one capture binder per capability it may use,
such as `πc` with `k1` and `k2`. `compile b Λ π e` resolves over `π` and types
at the fuel of `b : Budget`, by default `defaultFuel = 2 ^ 15`. It returns a
`Verdict`. `ok` holds a `Compiled`: the elaborated term, its use set, its type
and the `DotMNF.HasTy` derivation. `rejected` holds a `Reason` with its proof.
`unknown` says that no type and no reason was found, or that the typing
reached the recursion limit. `compileAndRun` adds the machine.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax, the `LabelTable` of field labels, the test helper `expect` and the command `#assert_no_wf` |
| `Notation` | the entry points `cc%`, `ccTy%` and their kin for the paper's notation |
| `Ann` | DOT-MNF terms with the annotations the typer needs, their `erase`, and the skeleton `ATm.skel` |
| `Resolve` | name resolution, scope roots, let insertion, and the platforms `πc` and `πz` |
| `Decide` | decision procedures for well-formedness, distinct labels and strengthening |
| `Search` | the first view of a variable (`varView`) and the certificate lemma `escape_rejected_at` |
| `Look` | `cost`, `defaultFuel`, and member lookup on demand (`look`, `decls`, `capDecls`), on the tank of `../../Frontend/Fuel.lean` |
| `Sub` | the algorithm in the compiler's case order, its four goals and their entry points (`shape?`, `subcap?`, `esub?`, `var?`, `sub?`) |
| `Alg` | the algorithmic judgment `Alg`, completeness up to the recursion limit, and `Alg.sound` |
| `Avoid` | avoidance at a `let` and at an unpacking (`up`, `down`, `capUp`, `capDown`, `avoidLet`, `avoidUses`, `avoidEx`) |
| `Adapt` | the result types of the typer and box adaptation at a variable (`adaptVarF`) |
| `Typer` | `Budget`, `Verdict`, `Reason`, `inferF`, the object fixpoint `objFixF` and the entry points `synthTop?` and `synthIn?` |
| `Step` | the DOT-MNF machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdot machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `compileAndRun`, the log `levelSteps` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation, no theorems |
| `Examples` | the programs taken end to end, each with its verdict in the kernel |

## The typer

The typer follows the Scala 3 compiler's subtype checker, `TypeComparer`, in
its case order, its subcapturing, `subCaptures` and `subsumes`, and its
levels, `acceptsLevelOf`, and takes no middle type from the context. It runs
on one fuel tank for the whole typing and reports a recursion limit when the
tank runs short, which is never a rejection by the rules. It is complete up to
that limit with respect to its algorithmic judgment `Alg`. It rejects E1, E3,
E4, B1 and A1 as scalac does, and E1s and E3s, which write the middle type,
compile.

The algorithm has four goals: `shape` on shapes, `cap` on capture sets, `esub`
on answers, and `var`, which keeps a variable while it widens it. `Sub.lean`
lists where the version's rules force a route other than the compiler's. The
typer returns the `DotMNF.HasTy` derivation, so it is sound by construction,
and it finds the least use set the rules allow. Synthesis returns candidates:
an application tries every function type the lookup finds, and a projection
returns every field. A `let` without a written type approximates the body's
type and use set by ones free of the binder, as the compiler's `avoid` does.
At a variable checked against a goal, the typer boxes or unboxes by the box
status of the two types, as the compiler's `adaptBoxed` does. The capture set
of an object literal is a least fixpoint, grown by the atoms its definitions
use that the set does not account for. Its passes are bounded by `objBound`, a
size of the program not proved to suffice, and a pass that reaches it marks
the tank.

A written type binds. Its `any` is read at the scope it is written in, and a
`fresh` in an arrow's result is an existential. When the typer cannot meet a
written type, it looks for a reason with a proof: a misplaced `any` or
`fresh`, a level escape at the goal it reached, or an existential answer at
the top of a program.

## Main theorems

- `compile_checks`, `compile_uses_checks`, `compile_checks_get`: the FCdot checker accepts the translated derivation and the use set evidence.
- `compile_erase`, `compile_faithful`: the translation erases to the compiled term, which has the skeleton of the resolved one.
- `compile_safe`, `compile_not_stuck`, `compile_run_progress`: every reachable state is final or can step, none is stuck, and `run` stops at a final state or at one that still steps.
- `compile_capture_prediction`, `compile_effect_safety`, `compile_effect_safety_get`: along any run, the matched FCdot state uses no more than the use set the typer found, and a platform capability outside it is never a root of a variable a run reads.
- `compile_lvl_safety`: in each member-free subcapturing `lo <: hi` of the derivation, every scope root that bounds `hi` also bounds `lo`.
- `compile_rejected_goal`: a program rejected for an escape names a goal at the context the typer reached, and no member-free subcapturing proves it.
- `shape?_complete`, `subcap?_complete`, `esub?_complete`, `sub?_complete`, `var?_complete`: a goal `Alg` derives is answered at every fuel at which the run ends with the tank unmarked.
- `shape?_reject`, `subcap?_reject`, `esub?_reject`, `sub?_reject`, `var?_reject`: a rejection with the tank unmarked means `Alg` derives no such goal.
- `Alg.sound`, with `Alg.sound_shape`, `Alg.sound_cap`, `Alg.sound_esub`, `Alg.sound_var`: a goal `Alg` derives has a derivation of the version.
- `shape?_mono`, `subcap?_mono`, `esub?_mono`, `sub?_mono`, `var?_mono`, `synthTop?_mono`, `synthTop?_stable`: an answer, or a rejection with the tank unmarked, stays the same at more fuel.
- `avoidLet_strengthen`, `avoidUses_strengthen`, `avoidEx_strengthen`: where the body's type or use set strengthens past the binder, avoidance returns it.
- `objFix_progress`: a pass of the object fixpoint that goes on adds an atom the set does not account for, or other definitions.
- In `Examples`: `Ek_type`, `Ek_compiles` and `Ek_checks` for each accepted program, `Ek_verdict` and `Ek_rejected` for each rejected one with `Ek_not_alg` where it fails at one core goal, `LP_limit` and `PF_limit` at the recursion limit, the certificates `Esc_rejected'` and `top_escape_rejected` of the escapes, and `C2_never_reads_k1`, which says that a run of C2 never reads a variable rooted at `k1`.

## What it leaves out

- A derivation through a middle type the program does not write, as in E1, E3, E4 and B1.
- A merge of two members of one name. The version has no rule for it, so the typer tries each, at a cost the tank bounds.
- A judgment whose search needs more than the fuel. LP and Pierce's divergence PF end at the recursion limit.
- A lookup through a cyclic member, which is cut as the compiler's cyclic reference. So member premises are phrased through the lookup, and no inductive judgment of lookup comes with a completeness theorem: the cut can remove an answer that a different answer of the same key needed.
- A completeness theorem for the typer as a whole. A rejection with a reason is about the goal the typer reached.
- A semantic statement for let insertion or box inference, a safety theorem at an open context, and a run theorem about scopes, which `compile_lvl_safety` and the certificates of rejections cover.
- `fresh` in a lambda domain, which `CapturesCC` keeps out of parameter types and the resolver rejects.

## Building

`lake build CapturesCCFrontend`. It is not a default target, so building
the metatheory does not wait on it. Every definition is structural, so the
kernel runs the typer, and the build fails on a definition that is not.
Every theorem depends on `propext` and `Quot.sound` at most. There is no
`sorry`, `axiom` or `native_decide`, and no Mathlib.
