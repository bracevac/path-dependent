# Paths front end

A way to write, type and run `Paths` programs without building derivations by
hand. `Paths` extends DOT with the paths `x.a.b`, stable fields `{val a : T}`
and singleton types `p.type` of pDOT (OOPSLA 2019). A program is written in
pDOT's notation inside `pdot%`. The front end resolves names and binds each
intermediate result with a `let`, which gives DOT in monadic normal form
(DOT-MNF). It fills the annotations the program leaves out, finds a typing
derivation, translates it to FCdot, a target calculus with a type checker,
checks the translation and runs it. It imports `../DotMNF`, `../FCdot` and
`../DotToFCdot`, changes nothing in them, and proves nothing new about the
calculi.

```lean
def R1_src : STm :=
  pdot% λ(f : ⊤). λ(g : ⊤). λ(m : {A : f.type .. g.type}). λ(x : f.type).
        let y : g.type = x in y
```

R1 needs `x : m.A` on the way from `f.type` to `g.type`. The program does not
write that middle type. So the typer rejects R1, as the Scala 3 compiler
(scalac) does. R1s writes `let y : g.type = (let u : m.A = x in u) in y` and
compiles. The programs named here, such as R1, E1p and LPt, are in `Examples`.

`compile b Λ e` resolves `e` at the label table `Λ`, which maps member names
to labels (the examples use `pathsTable`). The budget `b` holds the fuel, by
default `defaultFuel = 2 ^ 15`. The result is `none` if `e` is rejected, and
otherwise the filled term with its type and its `Paths.DotMNF.HasTy`
derivation. `compileE` returns the reason of a rejection and `ppReason` prints
it. `compileAndRun` and `compileAndRunFC` also run the two machines.

## What the programmer may leave out

The domain of a lambda: `λy. t` is enough where the context says what `y` is.
The self type of an object literal: `ν(x. {a = v})` has no `μ` written on it.
The type of a field, as in `{a = t}`. Everything else is written. A program
that writes every domain and self type is typed as it is, at the same fuel.

## Where an expected type comes from

The elaborator checks a term against a goal and passes the goal down. The goal
of a `let` body is its written type, and the goal of `t` in `(t : U)` is `U`.
The goal of a call argument is the dominant formal of the callee, the parameter
type that the others of an intersection of functions lie below. The goal of a
field is its declaration in the self type, and a literal at a stable field
takes the `μ` of that declaration as its self type. A lambda takes its domain
from the function part of its goal, after it follows aliases through selections
and stable fields, or from `g` when its body is `g x`. An object literal takes
its self type from a `μ` goal, or else forms it from its fields. When the
attempt at a goal fails, the typer's own route runs on the term.

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
| `Surface`, `Notation` | the surface syntax with paths, the label table, and the entry points `pdotTy%`, `pdot%` and `pdotDefs%` |
| `Ann`, `Resolve` | DOT-MNF terms with annotations and partial terms, name resolution and `let` insertion |
| `Decide`, `Look` | side conditions, the cost of a goal, `defaultFuel`, and member lookup |
| `Sub` | the subtyping algorithm in the compiler's case order |
| `Alg`, `Avoid` | the judgment `Alg` with completeness up to the recursion limit, and avoidance at a `let` |
| `Typer` | the typer and its entry point `synthTop?` |
| `Elab` | the elaborator that fills the empty slots of a partial term |
| `Step`, `StepFC` | the DOT-MNF and FCdot machines as functions |
| `Pipeline`, `Pretty` | `compile`, `compileE`, the pipeline theorems, and printers of terms and reasons |
| `Examples` | the programs end to end, each with its verdict in the kernel |

## The typer

The typer follows the subtype checker of the Scala 3 compiler,
`TypeComparer.recur` in `core/TypeComparer.scala`, in its case order (scala/scala3
at commit 4dae25087d). The search spends one tank of fuel for the whole typing,
the elaborator's included. A short tank is marked and the typer reports a
recursion limit, which is never a rejection by the rules. Up to that limit it
is complete with respect to `Alg`, the judgment that says which subtyping goals
the algorithm should decide. It takes no middle type from the context, so it
rejects what scalac rejects (E1p, E3p, E4p, R1). A `let` without a type gets
the type of its body with the binder avoided, as `TypeOps.avoid` does. The
typer returns the derivation, so it is sound by construction. Each verdict is a
`decide +kernel` theorem.

## Main theorems

- `compile_checks`, `compile_checks_get`: the FCdot checker accepts the translated derivation.
- `compile_erase`, `compile_safe`, `compile_not_stuck`, `compile_run_progress`: the translation erases to the filled term, no reachable state is stuck, and the source driver stops at a final state or at one that can still step.
- `compile_consistent`, `compile_fcRun_consistent`, `compile_no_bad_literal`: every store a run reaches is typed at a context that does not prove `⊤ ≤ ⊥`, and a compiled object literal never has the type `μ(x. {A : ⊤..⊥})`.
- `sub?_complete`, `path?_complete`, `var?_complete`, `sub?_reject`, `path?_reject`, `var?_reject`: a goal `Alg` derives is found whenever the tank ends unmarked, and a rejection with the tank unmarked means `Alg` derives no such goal.
- `Alg.sound`: a subtyping goal `Alg` derives has a `Paths.DotMNF.Sub` derivation.
- `compile_full`, `compileE_fills`, `compileE_slot`: a program with every slot written compiles as the typer's synthesis, the fill agrees with every written slot, and the first three reasons come only from a program with an empty slot.
- `elabTop?_mono`, `elabTop?_stable`, `synthTop?_mono`, `synthTop?_stable`: an answer, and a rejection that ends with the tank unmarked, stay the same at more fuel.
- `elab_complete_direct`, `compile_complete_direct`: at the sites where the elaborator reads a goal and then runs the typer's own clause, a fill the typer accepts is found from some fuel on.
- In `Examples`: `Ek_checks` for each accepted program, `Ek_rejected` for each rejected one, `Ek_erased` for each program with annotations erased, `LPt_limit` and `LPd_limit` at the recursion limit, and `Fig2_not_stuck` for gDOT's Fig. 2 (ICFP 2020).

The side conditions are decided (`tyWf?_iff`, `defsDistinct?_iff`,
`tyStrengthen?_iff`) and the machines agree with the step relations
(`step?_sound`, `fcStep?_complete`).

## What it leaves out

- A derivation through a middle type the program does not write, as in E1p, E3p, E4p, R1 and B1.
- A singleton widened at a term to the declared type of its path (R2), and a relation between `p.A` and `q.A` at `p : q.type` (PQ). `Paths` has no rule for either, and scalac accepts both.
- A judgment whose search needs more than the fuel (LPt, LPd), and a lookup through a cyclic member, which is cut as the compiler reports a cyclic reference.
- The singleton of a direct-style path. `let` insertion binds the prefix of `x.a.b`, so R7 loses the path and is rejected.
- A field with a written type is no stable member, and the self inside a closure stays at the partial `μ` (SL).
- Completeness over every filling. It fails at an ascription with a `μ` side (AscMu) and at a call argument the typer types only at a non-dominant formal (Mid).
- A merge of two fields of one name, a completeness theorem for the typer as a whole, and a semantic statement for `let` insertion.

## Building

`lake build PathsFrontend`. It is not a default target, so the metatheory
build does not wait on it. Theorems depend on `propext` and `Quot.sound` at
most. There is no `sorry`, `axiom`, `native_decide` or Mathlib.
