# Oopsla16 Frontend

A way to write, type and run programs of `Oopsla16` without assembling
derivations by hand. `Oopsla16` is the DOT calculus of the OOPSLA 2016 paper,
which has subtyping between recursive types. A program is written in the
paper's notation inside `o16%`. The front end resolves names and labels, finds
the `Oopsla16.HasType` derivation, and runs the program on the `Oopsla16`
machine. It also elaborates the derivation into FCdotR, the target calculus in
which every use of subtyping is a term, checks that term and runs it. It
proves nothing new about the calculi and changes nothing in `..` or
`../../FCdotR`.

```lean
def unionCallSrc : STm :=
  o16% new { c ⇒ def g(x : { def f(y : ⊤) : ⊤ } ∨ { def f(y : ⊤) : ⊤ }) : ⊤ = x.f(x) }
```

Both operands of the union have `f`. The compiler looks a member up in the
join of a union, and the join of two structural types keeps none. So the
typer rejects the call, as scalac does. With one operand in place of the
union the program compiles.

A literal is `new { z ⇒ d₁ … dₙ }`, with an optional self type after `z`. A
member is `type L = T` or `def m(x : S) : U = t`. A call is `t.m(u)`, and
`(t : T)` ascribes a type. There is no `let`. A member's label is its position
in the literal, so a name sits at one position in every literal that has it.
`labelsOfProgram` builds the table of positions and fails otherwise.

`compile b Λ e` resolves and types at the fuel of `b : Budget`, by default
`defaultFuel = 2 ^ 15`. It returns the annotated term with the type and the
derivation. `elaborate` gives the FCdotR term, and `compileAndRun` and
`compileAndRunFC` run the source and the target machine at a step budget.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax, the label table, the test helper `expect` and the command `#assert_no_wf` |
| `Notation` | the entry points `o16Ty%`, `o16%`, `o16Dm%`, and the example programs |
| `Ann` | `Oopsla16` terms with a written self type and an ascription, and their `erase` |
| `Resolve` | name and label resolution, totality, and the label table built from a program |
| `Decide` | strengthening past two binders, and membership in the fragment of FCdotR |
| `Look` | `cost`, `defaultFuel`, and member lookup on demand (`look`, `hdecls`), on the tank of `../../Frontend/Fuel.lean` |
| `Sub` | the subtyping algorithm in the compiler's case order (`sub?`, `var?`) |
| `Alg` | the algorithmic judgment `Alg`, completeness up to the recursion limit, and `Alg.sound` |
| `Avoid` | avoidance of a method's parameter at a call (`up`, `down`, `avoidArg`) |
| `Typer` | `Budget`, the candidate lists, `synthF`, `checkF` and the entry point `synthTop?` |
| `Step` | the `Oopsla16` machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdotR machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `elaborate`, the two drivers and the pipeline theorems |
| `Pretty` | printers back to the paper's notation, no theorems |
| `Examples` | the programs taken end to end, each with its verdict in the kernel |

## The typer

The typer follows the subtype checker of the Scala 3 compiler,
`TypeComparer`, in its case order, and takes no middle type from the context.
It runs on one fuel tank for the whole typing and reports a recursion limit
when the tank runs short, which is never a rejection by the rules. It is
complete up to that limit with respect to its algorithmic judgment `Alg`. It
rejects a call on a receiver at a union or at `⊥`, as scalac does, since
neither has members there.

The typer returns the `Oopsla16.HasType` derivation, so it is sound by
construction. Lookup opens a recursive type at the variable, searches both
operands of an intersection, and goes on in the upper bounds of a selection.
At two recursive types the algorithm tries `stp_bindx`, then `stp_bind1`,
since `Oopsla16` has recursive types whose self is unused. A call tries every
method type the lookup finds. When the argument is not a variable, the
codomain is approximated by a type free of the parameter, and a recursive
type stays recursive. A method may carry its parameter and result types. A
literal with an unannotated method writes its self type. Every definition is
structural, so each program's verdict is a `decide +kernel` theorem.

## Main theorems

- `compile_safe`, `compile_not_stuck`, `compile_target_safe`: no state a source or target run reaches is stuck.
- `compile_checks`, `compile_checks_get`: the FCdotR checker accepts the elaboration.
- `compile_corr`, `compile_adequate`: the elaboration matches the program up to annotations and `let`, and reaches a final state exactly when the program reaches an answer.
- `compile_run_progress`, `compile_fcRun_progress`, `compile_drivers_agree`: each driver stops at an answer or at a state that steps, and the two terminate together.
- `compile_frag_erase`, `compile_frag_checks`: on the fragment `FCdotR.TmFrag` a simpler elaboration erases to the program, and the checker accepts it.
- `sub?_complete`, `var?_complete`: a goal `Alg` derives is answered at every fuel at which the run ends with the tank unmarked.
- `sub?_reject`, `var?_reject`: a rejection with the tank unmarked means `Alg` derives no such goal.
- `Alg.sound`: a subtyping goal `Alg` derives has an `Oopsla16.Stp` derivation. It is a corollary of `Alg.answer`.
- `sub?_mono`, `var?_mono`, `synthTop?_mono`, `synthTop?_stable`: an answer, or a rejection with the tank unmarked, stays the same at more fuel.
- `avoidArg_weaken`: a codomain free of the parameter is the type of the call.
- In `Examples`: `_type` and `_checks` for each accepted program, `_verdict` and `_rejected` for each rejected one, `P2_not_alg`, and `LP_limit` at the recursion limit.

Supporting results: `resolveTy_isSome`, `resolveTm_isSome`,
`resolveDms_isSome` and `labelsOfProgram_positioned` (resolution succeeds on scoped programs that fit
the table), `strengthen2?_iff` and `frag?_complete` (the side conditions are
decided), and `step?_sound`, `step?_complete`, `fcStep?_sound`,
`fcStep?_complete`, `run_complete`, `fcRun_complete` (the machines agree with
the step relations).

## What it leaves out

- A derivation through a middle type the program does not write. Every middle is a bound of a member the lookup finds.
- A merge of two members of one name. `Oopsla16` has no rule for it, so a call tries each.
- Members of a union or of `⊥`. `unionCall` and `botCall` are rejected.
- A judgment whose search needs more than the fuel. LP compares two aliases of a method type whose result is the alias itself, meets its goal again under one more parameter at every level, and ends at the recursion limit.
- A lookup through a cyclic member, which is cut as the compiler's cyclic reference. P2 calls a parameter whose method lies behind a selection on the parameter itself. It is rejected at every binder depth, and `P2_not_alg` says `Alg` does not type its parameter at the method type it calls. So member premises are phrased through the lookup, and no inductive judgment of lookup comes with a completeness theorem: the cut can remove an answer that a different answer of the same key needed.
- A completeness theorem for the typer as a whole. `Alg.sound` says no more than the derivation the algorithm emits.
- Programs over a store. A surface program names no store location.
- An elaboration that erases to the program in general, since it binds every call operand with `let`.

## Building

`lake build Oopsla16Frontend`. It is not a default target, so building the
metatheory does not wait on it. Every theorem depends on `propext` and
`Quot.sound` at most. There is no `sorry`, `axiom` or `native_decide`, and no
Mathlib.
