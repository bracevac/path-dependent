# Oopsla16 Frontend

A way to write, type and run programs of `Oopsla16` without assembling
derivations by hand. `Oopsla16` is the DOT calculus of the OOPSLA 2016 paper,
which has subtyping between recursive types. A program is written in the
paper's notation inside `o16%`. The front end resolves names and labels, finds
a typing derivation, and runs the program on the `Oopsla16` machine. Unlike the
vanilla front end, it also elaborates the derivation into a term of FCdotR,
the target calculus in which every use of subtyping is a term of the program.
It checks that term and runs it on the FCdotR machine. It proves nothing new
about the calculi and changes nothing in `..` or `../../FCdotR`.

```lean
def recArgSrc : STm :=
  o16% (new { c : { def apply(x : μ(z. { def f(y : ⊤) : z.B })) : ⊤ } ∧ ⊤ ⇒
              def apply(y) = y }).apply(
         new { z : { type A : z.B .. z.B } ∧ { type B : ⊤ .. ⊤ } ∧ { def f(y : ⊤) : z.A } ∧ ⊤ ⇒
              type A = z.B
              type B = ⊤
              def f(y) = y })
```

A literal is `new { z ⇒ d₁ … dₙ }`, with an optional self type after `z`. A
member is `type L = T` or `def m(x : S) : U = t`. A call is `t.m(u)`, and
`(t : T)` ascribes a type. There is no `let`.

`compile b Λ e` takes a `Budget`, a label table and a program. It resolves,
then types. It returns the annotated term and a `Compiled` with the
synthesized type and the `Oopsla16.HasType` derivation, or `none` when
resolution fails or the budget runs out. `elaborate` turns the derivation into
an FCdotR term. `compileAndRun` and `compileAndRunFC` run the source and the
target machine at a step budget.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax, the label table, and the test helper `expect` |
| `Notation` | the entry points `o16Ty%`, `o16%`, `o16Dm%`, and the example programs |
| `Ann` | `Oopsla16` terms with a written self type and an ascription, and their `erase` |
| `Resolve` | name and label resolution, and the label table built from a program |
| `Decide` | strengthening past two binders, and membership in the fragment of FCdotR |
| `Search` | the `Budget`, the views of a variable, and the subtyping search `sub?` |
| `Typer` | `synth?`, `check?` and the entry point `synthTop?` |
| `Step` | the `Oopsla16` machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdotR machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `compile`, `elaborate`, the two drivers and the pipeline theorems |
| `Pretty` | printers back to the paper's notation, no theorems |
| `Examples` | the programs of `Oopsla16` and a few call examples, taken end to end |

## Labels

In `Oopsla16` a member's label is its position in the literal. So a name must
sit at the same position in every literal that has it. A label table maps each
name to its position. `labelsOfProgram` builds it from the program and fails
when two literals put one name at two positions. Such a program needs other
names. A name that labels no literal member, such as a type member of a
parameter's type, is an explicit entry of the table.

## The typer

The typer is sound by construction. `synth?` returns a type together with an
`Oopsla16.HasType` derivation, so there is no soundness theorem to state. The
typer is incomplete, since subtyping in `Oopsla16` is undecidable.

The views of a variable are the types the typer derives for it. It opens
recursive types, splits intersections and widens type selections. For a call
it reads candidate method types off the receiver's type and views. It uses the
first candidate that gives the call a result type.

The typer runs on a `Budget` of three counters: rounds of the view closure,
fuel of the subtyping search, and fuel of the typer. The default is
`{ views := 4, sub := 8, typer := 12 }`. A larger budget may find a program
the default misses.

A method may carry its parameter and result types. Beyond those, the user
writes two annotations. A literal carries its self type when one of its methods
has no annotation, because the typing rule needs it and the syntax has no slot
for it. An ascription `(t : T)` states the type `t` is checked at.

## Main theorems

The pipeline theorems take a successful `compile` and apply results of
`Oopsla16` and `FCdotR` to the derivation it returned.

- `compile_safe`: no state a source run reaches is stuck.
- `compile_not_stuck`: every state a source run reaches is an answer or steps.
- `compile_checks`: the FCdotR checker accepts the elaboration.
- `compile_corr`: the elaboration matches the program up to annotations and `let` binding.
- `compile_adequate`: the program reaches an answer exactly when its elaboration reaches a final state.
- `compile_target_safe`: no state a target run reaches is stuck.
- `compile_run_progress`, `compile_fcRun_progress`: at any step budget, each driver stops at an answer or at a state that still steps.
- `compile_drivers_agree`: the source driver answers at some budget exactly when the target driver finishes at some budget.
- `compile_frag_erase`, `compile_frag_checks`: on the fragment `FCdotR.TmFrag`, where calls apply variables to variables, a simpler elaboration erases to the program and the checker accepts it. `ex0`, `ex1` and `paperLst` are in it.
- `compile_checks_get`: `compile_checks` with the compile as a decidable premise, closed by `decide +kernel`.
- `ex0_checks`, `recArg_checks`, `paperLst_checks` and the other `_checks` theorems of `Examples`: the checker accepts the elaboration of each example.

Supporting results:

- `resolveTy_isSome`, `resolveTm_isSome`, `resolveDms_isSome`: resolution succeeds on scoped programs that fit the label table. `labelsOfProgram_positioned`: a table built from a program fits it.
- `strengthen2?_iff`, `frag?_complete`: the side conditions are decided.
- `hviews_mono`, `sub?_le`, `synth?_le`: more rounds never lose a view, and more fuel never loses an answer.
- `step?_sound`, `step?_complete`, `step?_none_classify`: `step?` agrees with the `Oopsla16` step relation, and a state with no step is an answer or stuck.
- `fcStep?_sound`, `fcStep?_complete`, `fcStep?_none_classify`: the same for the FCdotR machine, with final in place of answer.
- `run_complete`, `fcRun_complete`: every reachable state is one the driver returns at some budget.

## What it leaves out

- No completeness theorem for the typer. Each example states a budget at which it is found.
- Closed programs over the empty store only. A surface program cannot name an object that already sits in a store.
- The elaboration does not erase to the program in general, since it binds every call operand with `let`.
- No inference of a self type. A literal with an unannotated method writes its self type.

## Building

`lake build Oopsla16Frontend`. It is not a default target, so building the
metatheory does not wait on it. Every definition is structural, and the build
checks it. So the kernel runs the examples with `decide +kernel`. Every
theorem depends on `propext` and `Quot.sound` at most. There is no `sorry`,
`axiom` or `native_decide`, and no Mathlib.
