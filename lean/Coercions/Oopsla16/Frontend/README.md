# Oopsla16 front end

A way to write, type and run programs of `Oopsla16` without assembling
derivations by hand. `Oopsla16` is the DOT calculus of the OOPSLA 2016 paper,
with subtyping between recursive types. A program is written in the paper's
notation inside `o16%`. The front end resolves names and labels, fills the
self types the programmer left out, finds the `Oopsla16.HasType` derivation and
runs the program on the `Oopsla16` machine. It also translates the derivation
into FCdotR, a calculus in which every use of subtyping is a term, checks the
translation and runs it. It proves nothing new about the calculi and changes
nothing in them.

```lean
def fwdSrc : STm :=
  o16% new { o ⇒ def g(x : ⊤) = o.f(x)   def f(x : ⊤) = x }
```

Neither method writes a result type, and `g` calls `f` through the self. The
typer alone needs the self type of the literal and rejects the program. The
front end types `f` first, forms the self type from the two members and
compiles the program, as scalac does.

A literal is `new { z ⇒ d₁ … dₙ }`, with an optional self type after `z`. A
member is `type L = T` or `def m(x : S) : U = t`. A call is `t.m(u)`, and
`(t : T)` ascribes a type. There is no `let`. A member's label is its position
in the literal, so a name must sit at one position in every literal that has
it. `labelsOfProgram Λ₀ e` builds the label table from the entries `Λ₀` and the
literals of `e`, and fails when a name needs two positions. A name that labels
no literal member, such as a type member of a parameter's type, needs an entry
in `Λ₀`.

`compile b Λ e` takes a budget `b : Budget`, a label table `Λ` and a source term
`e`. The budget is the fuel the search may spend, `defaultFuel = 2 ^ 15` by
default. The result is the filled term with its type and derivation. It is
nothing when resolution fails, when the program is rejected or when the fuel
runs out. `compileE` returns the reason and `ppReason` prints it. `elaborate`
gives the FCdotR term. `compileAndRun` and `compileAndRunFC` run the source and
the target machine for a number of steps.

## What the programmer may leave out

The self type of a literal, the result type of a method, and the parameter type
of a method where a goal says what it is. Everything else is written. A
program the typer takes as it is is typed as it is, at the same fuel, so leaving
slots out never loses such a program. The filled term differs from the written
one in self types only.

## Where an expected type comes from

An ascription `(t : T)` gives `T` to `t`. A call argument gets the dominant
formal of the methods the lookup finds at the label, the parameter type that
the others lie below, and it gets none when the formals are not ordered. A
method body gets the method's result type. A literal takes a goal as its parent
and reads the declarations the goal makes about its members, after following
every alias. A receiver gets no goal. When the attempt at a goal fails, the
term is filled with no goal, and the typer then types it as it is.

## The compiler's errors

A method with no parameter type and no goal that declares it is rejected with
"Missing parameter type", as scalac does. Methods without result types that
call each other through the self in a cycle are rejected with "Recursive value
f needs type", the compiler's cyclic reference. A body whose candidate types
have no least one gives "The types of f have no least one". The other reasons
are a type mismatch and "Recursion limit exceeded". Only a program with an
empty slot gets the first three (`compileE_slot`). One program scalac accepts
stays rejected. The self type of a method that returns the self does not name
that method, so a second call on the result is a mismatch.

## Modules

| module | contents |
|---|---|
| `Surface`, `Notation`, `Resolve` | the named surface syntax, the notation `o16Ty%`, `o16%` and `o16Dm%`, and name and label resolution |
| `Ann` | `Oopsla16` terms with a written self type and an ascription, and the fill relation between terms |
| `Decide`, `Look` | decision procedures for side conditions, the default fuel and member lookup on demand |
| `Sub`, `Alg`, `Avoid` | subtyping in the compiler's case order, the rules of the algorithm with completeness and soundness, and avoidance at a call |
| `Typer`, `Infer` | the budget and the typer, then the fill of self types, the rounds that type methods without results, and the elaborator |
| `Step`, `StepFC` | the `Oopsla16` and FCdotR machines as functions, and their drivers |
| `Pipeline` | `compile`, `compileE`, `elaborate`, the two drivers and the pipeline theorems |
| `Pretty` | printers back to the paper's notation, and of reasons |
| `Examples` | the programs end to end, and each program with a kind of annotation erased |

## The typer

The typer follows the subtype checker of the Scala 3 compiler, pinned as
scala/scala3 at commit 4dae25087d: `TypeComparer` (core/TypeComparer.scala),
with member lookup as in `Types.findMember`. The whole typing, the fill
included, draws on one fuel tank. A goal that finds the tank short marks it,
and the run ends at the recursion limit, which is not a rejection by the rules.
`Alg` states the rules without fuel, and the typer is complete with respect to
`Alg` up to the recursion limit. It rejects what scalac rejects: a call on a
receiver at a union or at `⊥`. It returns the `HasType` derivation, so it is
sound by construction. A call tries every method type the lookup finds. The
derivation ends in `T_Obj` at every literal. Each body is filled once and
checked once more, so the fuel of nested literals grows with the square of
their depth.

## Main theorems

- `compile_safe`, `compile_not_stuck`, `compile_target_safe`: no state a source or target run reaches is stuck. `compile_checks` and `compile_checks_get`: the FCdotR checker accepts the translation.
- `compile_corr`, `compile_adequate`: the translation matches the program up to annotations and `let`, and reaches a final state exactly when the program reaches an answer.
- `compile_run_progress`, `compile_drivers_agree`: each driver stops at an answer or at a state that steps.
- `compile_conservative`, `compileE_erase`, `compileE_slot`: a program the typer alone compiles compiles to the same result, the filled term erases to the resolved program, and the slot reasons arise only where a slot is empty.
- `elabTop?_mono`, `elabTop?_stable`, `compile_rejects`: an answer, or a rejection with the tank unmarked, stays the same at more fuel.
- `elabF_eq` is the definition of the elaborator, the fill followed by the typer, unfolded. `fillF_fills`, `missingParam_iff`, `leastCand_least`, `cycleAt_onCycle`: the fill only writes self types, and it reports the errors above where they apply.
- `sub?_complete`, `var?_complete`, `sub?_reject`, `var?_reject`, `Alg.sound`: a goal `Alg` derives is answered at every fuel at which the run ends with the tank unmarked, and has an `Oopsla16.Stp` derivation.
- In `Examples`: `_type` and `_checks` for each accepted program, `_rejected` for each rejected one, `_erased` for the programs with annotations left out, `P2_not_alg`, and `LP_limit` at the recursion limit.

## What it leaves out

- A merge of two members of one name, which `Oopsla16` has no rule for, and a judgment whose search needs more than the fuel, as `LP` does.
- A completeness theorem for the typer or the fill as a whole, and for lookup through a cyclic member, which is cut as the compiler's cyclic reference. The example `P2` calls a parameter whose method lies behind a selection on the parameter itself. The typer rejects it.
- Store locations, and a translation that erases to the program in general, since it binds every call operand with `let`.

## Building

`lake build Oopsla16Frontend`. It is not a default target, so building the
metatheory does not wait on it. Every definition is structural, so each verdict
is a `decide +kernel` theorem. Every theorem depends on `propext` and
`Quot.sound` at most. There is no `sorry`, `axiom`, `native_decide` or Mathlib.
