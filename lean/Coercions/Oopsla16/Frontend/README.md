# Oopsla16 front end

A way to write, type and run programs of `Oopsla16` without assembling
derivations by hand. `Oopsla16` is the DOT calculus of the OOPSLA 2016 paper. It
has subtyping between recursive types. A program is written in the paper's
notation inside `o16%`. The front end resolves names and labels, finds the
`Oopsla16.HasType` typing derivation and runs the program on the `Oopsla16`
machine. It also translates the derivation into FCdotR, a calculus in which
every use of subtyping is a term, checks the translation and runs it. It proves
nothing new about the calculi and changes nothing in them.

```lean
def unionCallSrc : STm :=
  o16% new { c ⇒ def g(x : { def f(y : ⊤) : ⊤ } ∨ { def f(y : ⊤) : ⊤ }) : ⊤ = x.f(x) }
```

Both operands of the union have `f`. The compiler looks a member up in the join
of a union, a single type that stands for both operands, and the join of two
structural types keeps none. So the typer rejects the call, as scalac does. With
one operand in place of the union the program compiles.

A literal is `new { z ⇒ d₁ … dₙ }`, with an optional self type after `z`. A
member is `type L = T` or `def m(x : S) : U = t`. A call is `t.m(u)`, and
`(t : T)` ascribes a type. There is no `let`. `o16Ty%` and `o16Dm%` write a type and a
member. A member's label is its position in the literal, so a name must sit at
one position in every literal that has it. `labelsOfProgram Λ₀ e` builds the
label table of these positions from the entries `Λ₀` and the literals of `e`. It
fails when a name needs two positions. A name that labels no literal member,
such as a type member of a parameter's type, needs an entry in `Λ₀`.

`compile b Λ e` takes a budget `b : Budget`, a label table `Λ` and a source term
`e`. The budget is the fuel the typer may spend, by default
`defaultFuel = 2 ^ 15`. The result is the resolved term with its type and derivation. It is nothing
when resolution fails, when the typer rejects the program or when the fuel runs
out. `elaborate` gives the FCdotR term. `compileAndRun` and `compileAndRunFC`
run the source and the target machine for a number of steps.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax, the label table, a test helper and a command that lists definitions by well-founded recursion |
| `Notation` | the notation `o16Ty%`, `o16%` and `o16Dm%` |
| `Ann` | `Oopsla16` terms with a written self type and an ascription |
| `Resolve` | name and label resolution |
| `Decide` | decision procedures for the typer's side conditions |
| `Look` | the default fuel and member lookup on demand |
| `Sub` | subtyping in the compiler's case order |
| `Alg` | the rules of the algorithm, completeness up to the recursion limit, and soundness |
| `Avoid` | avoidance of a method's parameter at a call |
| `Typer` | the budget and the typer |
| `Step` | the `Oopsla16` machine as a function, and its driver |
| `StepFC` | the FCdotR machine as a function, and its driver |
| `Pipeline` | `compile`, `elaborate`, the two drivers and the pipeline theorems |
| `Pretty` | printers back to the paper's notation |
| `Examples` | the programs taken end to end, each with its verdict in the kernel |

## The typer

The typer follows the subtype checker of the Scala 3 compiler, pinned as
scala/scala3 at commit 4dae25087d: `TypeComparer` (core/TypeComparer.scala),
with member lookup as in `Types.findMember`. The whole typing draws on one fuel
tank. A goal that finds the tank short marks it, and the run ends at the
recursion limit, which is not a rejection by the rules. A run that ends with the
tank unmarked did not reach it. `Alg` states the rules of the algorithm without
fuel. The typer is complete with respect to `Alg` up to the recursion limit. It
rejects what scalac rejects: a call on a receiver at a union or at `⊥`. It
returns the `HasType` derivation, so it is sound by construction. A call tries
every method type the lookup finds. When the argument is not a variable,
avoidance approximates the result type by a type free of the parameter. The
programmer may leave out the parameter and result types of a method. A literal
with such a method needs its self type written.

## Main theorems

- `compile_safe`, `compile_not_stuck`, `compile_target_safe`: no state a source or target run reaches is stuck.
- `compile_checks`, `compile_checks_get`: the FCdotR checker accepts the translation.
- `compile_corr`, `compile_adequate`: the translation matches the program up to annotations and `let`, and reaches a final state exactly when the program reaches an answer.
- `compile_run_progress`, `compile_fcRun_progress`, `compile_drivers_agree`: each driver stops at an answer or at a state that steps, and the two terminate together.
- `compile_frag_erase`, `compile_frag_checks`: on the fragment `FCdotR.TmFrag` a simpler translation erases to the program, and the checker accepts it.
- `sub?_complete`, `var?_complete`, `sub?_reject`, `var?_reject`: a goal `Alg` derives is answered at every fuel at which the run ends with the tank unmarked. So a rejection with the tank unmarked means `Alg` derives no such goal.
- `Alg.sound`: a subtyping goal `Alg` derives has an `Oopsla16.Stp` derivation.
- `sub?_mono`, `var?_mono`, `synthTop?_mono`, `synthTop?_stable`: an answer, or a rejection with the tank unmarked, stays the same at more fuel.
- `avoidArg_weaken`: avoidance returns a result type free of the parameter unchanged.
- `resolveTm_isSome`, `labelsOfProgram_positioned`: resolution succeeds on scoped programs that fit the label table.
- `strengthen2?_iff`, `frag?_complete`: the test that a type is free of a binder has a specification, and the fragment test finds every term of the fragment.
- `step?_sound`, `step?_complete`, `fcStep?_sound`, `fcStep?_complete`: the machines agree with the step relations.
- In `Examples`: `_type` and `_checks` for each accepted program, `_rejected` for each rejected one, `P2_not_alg`, and `LP_limit` at the recursion limit.

## What it leaves out

- A transitivity step through a type that is not a bound of a member the lookup finds.
- A merge of two members of one name. `Oopsla16` has no rule for it, so a call tries each.
- A judgment whose search needs more than the fuel. The example `LP` compares two aliases of a method type whose result is the alias itself.
- A completeness theorem for the typer as a whole.
- A completeness theorem for lookup through a cyclic member, which is cut as the compiler's cyclic reference. The example `P2` calls a parameter whose method lies behind a selection on the parameter itself. The typer rejects it.
- Store locations. A surface program names none.
- A translation that erases to the program in general, since it binds every call operand with `let`.

## Building

`lake build Oopsla16Frontend`. It is not a default target, so building the
metatheory does not wait on it. Every definition is structural, so each verdict
is a `decide +kernel` theorem. Every theorem depends on `propext` and
`Quot.sound` at most. There is no `sorry`, `axiom`, `native_decide` or Mathlib.
