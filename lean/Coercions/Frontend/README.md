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
maps the names of members to labels. The budget `b` holds the fuel of the
search, `defaultFuel = 2 ^ 15` by default. The result is `none` if the program
is rejected, and otherwise the filled term with its type and its
`DotMNF.HasTy` derivation. `compileE` returns the reason of a rejection, and
`ppReason` prints it. `compileAndRun b m Λ e` also runs the machine for `m` steps.

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

## The typer

The typer follows the subtype checker of the Scala 3 compiler, `TypeComparer`
and the `firstTry` to `fourthTry` it calls, in their case order (scala/scala3
at commit 4dae25087d). The search spends one tank of fuel for the whole typing,
the elaborator's included. A short tank is marked and the typer reports a
recursion limit. Up to the limit it is complete with respect to `Alg`. It takes
no middle type from the context. It returns the derivation, so it is sound by
construction. Every definition is structural, so Lean's kernel runs it in
`decide +kernel`.

## Main theorems

- `compile_checks`, `compile_erase`, `compile_safe`, `compile_not_stuck`: the FCdot checker accepts the translated derivation, it erases to the source term, and no reachable state is stuck.
- `sub?_complete`, `var?_complete`, `sub?_reject`, `var?_reject`, `Alg.sound`: the algorithm finds what `Alg` derives, up to the limit.
- `compile_full`, `compileE_fills`, `compileE_slot`: a program with every slot written compiles as the typer's synthesis, and the fill agrees with every written slot.
- `elabTop?_mono`, `elabTop?_stable`: an answer keeps at more fuel.
- `elab_complete_direct`, `compile_complete_direct`: at the sites where the elaborator runs the typer's own clause, a canonical fill the typer accepts is found from some fuel on.
- In `Examples`: `Ek_checks`, `Ek_rejected`, `Ek_erased`, and `LP_limit`, `PF_limit`, `Doubled12_limit`.

## What it leaves out

- A derivation through a middle type the program does not write (E1, E3, E4).
- A judgment whose search needs more than the fuel (LP, and Pierce's divergence PF).
- A domain whose goal comes from a candidate, a self type that must meet a written `μ` anywhere but at the literal, a field type that must be a meet of two candidates, and a bare use of the self that must see itself.
- Completeness over every filling. It fails at an ascription with a `μ` side (AscMu) and at a call argument the typer types only at a non-dominant formal (Mid).
- A semantic statement for `let` insertion, and the other calculi, which have a front end each in their own `Frontend/` folder.

## Building

`lake build Frontend`. It is not a default target, so building the metatheory
does not wait on it. Every theorem depends on `propext` and `Quot.sound` at
most. There is no `sorry`, `axiom` or `native_decide`, and no Mathlib.
