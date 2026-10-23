# Frontend

A way to write, type and run DOT programs without building derivations by
hand. DOT is the calculus behind path-dependent types in Scala 3. A program is
written in DOT notation inside `dot%`. The front end resolves names, binds each
intermediate result with a `let` (monadic normal form, MNF), fills the types
the programmer left out, finds a typing derivation, translates it to FCdot,
and runs it. DOT-MNF is DOT in that form. FCdot is a target calculus with a
type checker. The front end proves nothing new about the calculi. It imports
`../DotMNF`, `../FCdot` and `../DotToFCdot` and changes nothing in them.

```lean
def E3src : STm :=
  dot% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}).
         λ(z : {b : ⊤}). let y : {a : ⊤} = z in y
```

E3 needs `z : x.A` on the way from `{b : ⊤}` to `{a : ⊤}`. The program does
not write that middle type. So the typer rejects E3, as scalac does. E3s
writes it as `let y : {a : ⊤} = (let u : x.A = z in u) in y` and compiles.

`compile b Λ e` resolves, elaborates and types the term `e`. The table `Λ`
maps the names of type and field members to labels. The budget `b` holds the
fuel of the search, `defaultFuel = 2 ^ 15` by default. The result is `none` if
`e` is out of scope, uses a name missing from `Λ`, is rejected, or ends at the
recursion limit, and it carries no reason. Otherwise it is the filled term with
its type and its `DotMNF.HasTy` derivation. `compileE` returns the reason of a
rejection, and `ppReason` prints it. `compileAndRun b m Λ e` also runs the
DOT-MNF machine for at most `m` steps.

## What the programmer may leave out

The domain of a lambda: `λy. y` is enough where the context says what `y` is.
The self type of an object literal: `ν(z. {a = v})` has no `μ` written on it.
The type of a field, with or without a self type. Everything else is written.
A program that writes every domain and self type is typed as it is, at the same
fuel.

## Where an expected type comes from

The elaborator checks a term against a goal and passes the goal down. The goal
of a `let` body is its written type, and the goal of `t` in `(t : U)` is `U`.
The goal of a call argument is the dominant formal of the callee, the parameter
type that the others of an intersection of functions lie below. The goal of a
field is its declaration in the self type. A lambda takes its domain from the
function part of its goal, or from `g` when its body is `g x`. An object
literal takes its self type from a `μ` goal, or else forms it from its fields.
When the attempt at a goal fails, the typer's own route runs on the term.

## The compiler's errors

A lambda with no domain and no goal with a function part is rejected with
"Missing parameter type", as scalac does. Fields without written types that
read each other in a cycle are rejected with "Recursive value a needs type",
the compiler's cyclic reference. The other reasons are a field whose candidate
types have no least one, a type mismatch, and the recursion limit. Only a
program with an empty slot gets the first three (`compileE_slot`).

## Modules

| module | contents |
|---|---|
| `Surface`, `Notation` | the named surface syntax and the entry points `dotTy%`, `dot%` and `dotDefs%` |
| `Ann` | DOT-MNF terms with the annotations the typer needs, and partial terms |
| `Resolve` | name resolution and `let` insertion, and the programs E1 to E10 |
| `Decide`, `Fuel`, `Reason` | side conditions, the fuel tank, and why a program is rejected |
| `Look`, `Sub` | the cost of a goal, member lookup, and the subtyping algorithm |
| `Alg`, `Limit` | the judgment `Alg`, completeness up to the recursion limit, and goals that reach it |
| `Avoid` | avoidance at a `let` |
| `Typer` | the typer and its entry point `synthTop?` |
| `Elab` | the elaborator that fills the empty slots of a partial term |
| `Step`, `StepFC` | the DOT-MNF and FCdot machines as functions |
| `Pipeline` | `compile`, `compileE`, `compileAndRun` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation, and of reasons |
| `Examples` | the programs end to end, each with its verdict in the kernel |
| `Scala` | the translation from the shared reader's tree to `STm`, `outcome`, the member check, the printers, `roundTrip` |
| `ScalaTests` | the tests of `Scala`, in the kernel and by `#eval expect` |
| `ScalaCmd` | the commands that read Scala files at elaboration, the front end's only file reading |

## The typer

The typer follows the subtype checker of the Scala 3 compiler. That is
`TypeComparer.recur` in `core/TypeComparer.scala` and the `firstTry` to
`fourthTry` it calls, in their case order. The pinned version is scala/scala3
at commit 4dae25087d. The search spends fuel from one tank for the whole
typing, the elaborator's included. When the tank runs short it is marked, and
the typer reports a recursion limit. That is never a rejection by the rules.
Up to the limit the subtyping algorithm, `sub?` and `var?`, is complete with
respect to `Alg`, the inductive judgment that says which subtyping goals the
algorithm should decide. The typer as a whole has no such theorem. It takes no
middle type from the context, so it rejects what scalac rejects (E1, E3, E4).
A written `let` type binds. Without one, the body's type is replaced by a type
free of the binder, as `TypeOps.avoid` does. The typer returns the derivation,
so it is sound by construction. Every definition is structural, so Lean's
kernel runs the typer in `decide +kernel`.

## Main theorems

- `compile_checks`, `compile_checks_get`: for a program that compiles, the FCdot checker accepts the translated derivation.
- `compile_erase`: the translation erases to the erasure of the fill, which has the `let`s the resolver inserted.
- `compile_safe`, `compile_not_stuck`: every state reachable from a compiled program, from the empty store, is final or can step, so none is stuck.
- `compile_run_progress`: after any number of steps, the driver is at a final state or at one that can still step.
- `sub?_complete`, `var?_complete`: if `Alg` derives a goal and the run of `sub?` or `var?` ends with the tank unmarked, the algorithm finds a derivation.
- `sub?_reject`, `var?_reject`: a rejection with the tank unmarked means `Alg` derives no such goal.
- `Alg.sound`: a subtyping goal `Alg` derives has a `DotMNF.Sub` derivation.
- `synthTop?_mono`, `elabTop?_mono`: a closed typing or elaboration keeps its answer at more fuel. `synthTop?_stable`, `elabTop?_stable`: one that ends with the tank unmarked, answer or rejection, gives the same verdict at more fuel.
- `avoidLet_strengthen`: from an unmarked tank with fuel left, a body type that does not mention the binder is returned as that type outside the binder.
- `compile_full`, `compileE_fills`, `compileE_slot`: a program with every slot written compiles as the typer's synthesis, the fill agrees with every written slot, and the first three reasons above come only from a program with an empty slot.
- `elab_complete_direct`, `compile_complete_direct`: at the sites where the elaborator runs the typer's own clause, a canonical fill the typer accepts is found from some fuel on.
- In `Examples`: `Ek_checks` for each accepted program, `Ek_rejected` for each rejected one, `Ek_erased` for each program with annotations erased, and `LP_limit`, `PF_limit`, `Doubled12_limit` for programs that end at the recursion limit.

Resolution is total on scoped programs whose member names are in the label
table (`resolveTm_isSome`). The side conditions are decided
(`defsDistinct?_iff`, `tyStrengthen?_iff`). The DOT-MNF machine agrees with its
step relation (`step?_sound`, `step?_complete`). The FCdot machine `fcStep?` is
sound at every normalisation fuel (`fcStep?_sound`) and complete at some fuel
(`fcStep?_complete`).

## What it leaves out

- A derivation through a middle type the program does not write (E1, E3, E4).
- A judgment whose search needs more than the fuel (LP, and Pierce's divergence PF).
- A domain whose goal comes from a candidate, a self type that must meet a written `μ` anywhere but at the literal, a field type that must be a meet of two candidates, and a bare use of the self that must see itself.
- Completeness over every filling. It fails at an ascription with a `μ` side (AscMu) and at a call argument the typer types only at a non-dominant formal (Mid).
- A semantic statement for `let` insertion, and the other calculi, which have a front end each in their own `Frontend/` folder.

## Scala syntax

The modules `Scala`, `ScalaTests` and `ScalaCmd` read and print programs
written as `.scala` files. They read through the shared reader
[`../ScalaSyntax`](../ScalaSyntax/README.md), which the front end imports
beside `../DotMNF`, `../FCdot` and `../DotToFCdot`. `readVanilla` reads the
characters of a file into a surface term and its label table. `outcome` parses,
checks, translates and compiles a file, and answers one of five kinds: `ok`,
`rejected`, `unknown`, `limit` or `outside`. Its last step is the member check
of plan IX, S-17. A selection `x.A` in a written type, where the type of `x`
declares no `A`, makes the file `outside`, as scalac refuses it. `toScala`
prints a surface term as a Scala program, the inverse of the reading on its
image, and `fillToScala` prints the fill of a compiled program. `roundTrip`
prints a term, reads the text back and compares the two terms after resolution.
The command `scala_example` reads one file and proves in the kernel that the
reader gives its term. `scala_corpus` does the same for every file of a corpus
and proves the kind of each outcome. The corpus, its table and the harness that
runs scalac are in [scala/README.md](../../../scala/README.md).

## Building

`lake build Frontend`. It is not a default target, so building the metatheory
does not wait on it. Every theorem depends on `propext` and `Quot.sound` at
most. There is no `sorry`, `axiom` or `native_decide`, and no Mathlib.
