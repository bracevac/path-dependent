# Oopsla16 Frontend

A way to write, type and run programs of `Oopsla16`, the DOT calculus of the
OOPSLA 2016 paper with recursive subtyping, without assembling derivations by
hand. A program is written in the paper's notation inside `o16%`. The front end
resolves names and labels, finds a typing derivation of the version, elaborates
it into FCdotR, checks the elaboration, and runs the program on the version's
machine and on the target machine. This shows the version and its translation
working end to end on concrete programs. It proves nothing new about the
calculi. It imports the version, `..`, and its target, `../../FCdotR`, and
changes nothing in them. `BASE` records that the vanilla front end,
`../../Frontend`, is its template, and names the two small functions copied
from it.

```lean
def recArgSrc : STm :=
  o16% (new { c : { def apply(x : μ(z. { def f(y : ⊤) : z.B })) : ⊤ } ∧ ⊤ ⇒
              def apply(y) = y }).apply(
         new { z : { type A : z.B .. z.B } ∧ { type B : ⊤ .. ⊤ } ∧ { def f(y : ⊤) : z.A } ∧ ⊤ ⇒
              type A = z.B
              type B = ⊤
              def f(y) = y })
```

A literal is `new {z ⇒ d₁ … dₙ}`, with its self type written after `z` when a
method has no annotation. A member is `type L = T` or `def m(x : S) : U = t`.
A call is `t.m(u)`, and `(t : T)` ascribes a type. `compile` runs the resolver
and then the typer. It returns the annotated term and a `Compiled`, which holds
the synthesized type, the `Oopsla16.HasType` derivation and, when the term is in
the fragment `FCdotR.TmFrag`, its fragment proof. `elaborate` translates the
derivation into an FCdotR term. `compileAndRun` and `compileAndRunFC` add the
source and the target machine at a step budget.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax `SType`, `STm`, `SDm`, `SDms`, the `LabelTable`, the conditions `Scoped`, `LabelsIn`, `Positioned`, the test helper `expect` and the command `#assert_no_wf` |
| `Notation` | the entry points `o16Ty%`, `o16%`, `o16Dm%` for the paper's notation, and the version's programs written in it |
| `Ann` | `ATm`, `ADm`, `ADms`, the version's terms with a written self type and an ascription, their `erase`, and `selfOf?` |
| `Resolve` | name resolution (`resolve`, `resolveIn`, `resolveTy`), the label tables `labelsOfProgram` builds, and totality |
| `Decide` | strengthening past two binders (`strengthen2?`) and membership in the fragment (`frag?`) |
| `Search` | the `Budget`, the views of a variable, and the subtyping search `sub?` |
| `Typer` | `synth?`, `check?`, `checkVar?`, `checkDms?`, the call ladder, and the entry points `synthIn?`, `checkIn?`, `synthTop?` |
| `Step` | the version's machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdotR machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `elaborate`, `compileAndRun`, `compileAndRunFC` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation (`ppTy`, `ppTm`, `ppRun`), no theorems |
| `Examples` | the version's programs, the open examples and the programs for the call ladder taken end to end |

## Labels

A member's label in the version is its position in the literal, counted from
the last member. So the resolver does not invent labels. A name resolves to the
position its table gives it, and a member list resolves only when every member
sits at its name's position. `labelsOfProgram` builds the table from the
program. It fails when the literals force one name to two positions, for
instance three literals with the members `{a, b}`, `{b, c}` and `{c, a}`. Such
a program needs other names. A name that labels no literal member, such as a
type member of a parameter's type, is an explicit entry of the table. Two
literals may give two names one position, so the printer shows the position
beside every name.

## The typer

The typer is sound by construction. `synth?` returns a pair of a type and an
`Oopsla16.HasType` derivation, so soundness is the result type, and there is no
soundness theorem to state. The typer is incomplete, since subtyping in the
version is undecidable. It runs on a `Budget` of three counters: rounds of the
view closure, fuel of the subtyping search, fuel of the typer.

A variable's views are the types derived for it without a goal. A recursive
type is opened, an intersection is split, and a selection `y.L` is widened to
the upper bound of `L` in a view of `y`. A call `t.m(u)` looks for a method
type of the receiver among candidates read off its type and its views, plus a
widening candidate `{def m(x : A) : ⊤}` at the argument's type `A`, and the
search decides each one. A candidate gives the call its result by the first of
four rungs that applies: `T_AppVar` at a variable argument, `T_App` when the
codomain does not mention the parameter, narrowing the parameter's selections
to the bounds of the argument's type, and `⊤`. Checking a variable at a goal
pushes the goal through an intersection and through the lower bound of a
selection before it packs a recursive type.

Beyond the parameter and result types a method may carry, the user writes two
annotations. A literal carries its self type when one of
its methods has no annotation, because `T_Obj` types the members under it and
the version's literal has no slot for it. An ascription `(t : T)` states the
type a program is checked at. It erases to `t`.

Every recursive definition is structural, on fuel or on syntax. The kernel
reduces the resolver, the search, the typer and both machines. So the
per-program facts of `Examples` are `decide +kernel` theorems, and the root
module ends with `#assert_no_wf Oopsla16Frontend`, which fails the build when a
definition falls back to well-founded recursion.

## Main theorems

The pipeline theorems take a successful compile,
`h : compile b Λ e = some ⟨a, c⟩`, and apply results of `Oopsla16` and
`FCdotR` to the derivation it returned. A run, a step budget or a fragment
proof in a statement picks what the theorem speaks of, and the docstring names
it as such.

- `compile_safe`: no state a source run reaches is stuck.
- `compile_not_stuck`: every state a source run reaches is an answer or steps.
- `compile_checks`: the FCdotR checker accepts the elaboration at the synthesized type.
- `compile_corr`: the elaboration corresponds to the source term, up to annotations and `let` binding.
- `compile_adequate`: the source program reaches an answer exactly when the target run from its elaboration reaches a final state.
- `compile_target_safe`: no state a target run from the elaboration reaches is stuck.
- `compile_run_progress`, `compile_fcRun_progress`: at any step budget, each driver stops at an answer or at a state that still steps.
- `compile_drivers_agree`: the source driver answers at some budget exactly when the target driver reaches a final state at some budget.
- `compile_frag_erase`, `compile_frag_checks`: on the fragment, the fragment elaboration erases to the source term and the checker accepts it. `ex0`, `ex1` and `paper_lst` are in the fragment.
- `compile_checks_get`: `compile_checks` with the successful compile as a decidable premise, so that it closes by `decide +kernel` at a concrete program.
- `ex0_checks`, `ex0Asc_checks`, `recArg_checks`, `curryCall_checks`, `ex1_checks`, `paperLst_checks`: the checker accepts the elaboration of each program of the version, with no hypothesis.
- `selfCall_checks`, `selCall_checks`, `twoCand_checks`, `unionCall_checks`, `botCall_checks`, `packSel_checks`, `packAnd_checks`: the same for seven programs that exercise the call candidates, the call ladder and the packing of a variable at a goal.
- `ex2_checks`: the checker accepts the elaboration of the open `ex2` in `y : polyId`.
- `ex0_frag_erase`, `ex1_frag_erase`, `paperLst_frag_erase` and the three matching `_frag_checks`: the fragment theorems at those programs, with no hypothesis.

Supporting results:

- `resolveTy_isSome`, `resolveTm_isSome`, `resolveDms_isSome`: resolution succeeds on scoped phrases whose labels are in the table and positioned.
- `labelsOfProgram_positioned`, `labelsOfProgram_explicit`: a table built from a program positions it and keeps the explicit entries.
- `strengthen2?_iff`, `frag?_complete`: the side conditions are decided.
- `hviews_mono`, `sub?_le`, `synth?_le`, `synth?_le_ty`: more rounds never lose a view, more fuel never loses an answer, and the synthesized type does not change with more fuel.
- `step?_sound`, `step?_complete`, `step?_eq_none_iff`, `step?_none_classify`, `step_det`: `step?` agrees with the version's step relation, a state with no step is an answer or stuck, and a step is determined by its state.
- `run_steps`, `run_complete`: the driver follows the step relation, and every reachable state is one it returns at some budget.
- `fcStep?_sound`, `fcStep?_complete`, `fcStep?_eq_none_iff`, `fcStep?_none_classify`, `fcRun_steps`, `fcRun_complete`: the same for the target machine.

## What it leaves out

- No completeness theorem for the typer. Its monotonicity is stated in its own fuel only, not in the view rounds or the search fuel of a `Budget`. Each example states the budget it is found at. `paper_lst` is found at `{ views := 3, sub := 12, typer := 13 }` and not at the default `{ views := 4, sub := 8, typer := 12 }`.
- Closed programs over the empty store only. A surface program cannot name a location, so the examples of `Oopsla16` and `FCdotR` that start from a store with locations, `TwoObjectStore`, `HonestCall`, `PackingCounterexample`, `DishonestStore`, `CurryStore` and `UncheckedBody`, are not written here.
- No `let`. The version has none, and a surface program writes the object encoding when it needs one.
- The elaboration of a program does not erase to the program in general, since it binds every call operand with `let`. `compile_corr` and `compile_adequate` relate the two, and `compile_frag_erase` gives the equation on the fragment.
- No inference of a self type for a literal with a method that has no annotation. Such a literal writes its self type.

## Building

`lake build Oopsla16Frontend`. It is not a default target, so building the
metatheory does not wait on it. Every theorem depends on `propext` and
`Quot.sound` at most. No proof is left open, no axiom is added, no proof trusts
compiled code, and there is no Mathlib.
