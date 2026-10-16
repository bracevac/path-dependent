# Paths front end

A way to write, type and run `Paths` programs without building derivations by
hand. `Paths` extends DOT with the paths `x.a.b`, stable fields `{val a : T}`
and singleton types `p.type` of pDOT (OOPSLA 2019). A program is written in
pDOT's notation inside `pdot%`. The front end resolves names and binds each
intermediate result with a `let`, which gives DOT in monadic normal form
(DOT-MNF). It then finds a typing derivation, translates it to FCdot, a target
calculus with a type checker, checks the translation and runs it. It imports
`../DotMNF`, `../FCdot` and `../DotToFCdot`, changes nothing in them, and
proves nothing new about the calculi.

```lean
def R1_src : STm :=
  pdot% λ(f : ⊤). λ(g : ⊤). λ(m : {A : f.type .. g.type}). λ(x : f.type).
        let y : g.type = x in y

def R1s_src : STm :=
  pdot% λ(f : ⊤). λ(g : ⊤). λ(m : {A : f.type .. g.type}). λ(x : f.type).
        let y : g.type = (let u : m.A = x in u) in y
```

R1 needs `x : m.A` on the way from `f.type` to `g.type`. The program does not
write that middle type. So the typer rejects R1, as the Scala 3 compiler
(scalac) does. R1s writes it as an ascription and compiles. The programs named
here, such as R1, E1p and LPt, are in `Examples`.

`compile b Λ e` resolves `e` at the label table `Λ`, which maps member names
to labels (the examples use `pathsTable`). It types `e` at the fuel of the
budget `b`, by default `defaultFuel = 2 ^ 15`. The result is `none` if `e` is
out of scope, uses a name missing from `Λ`, is rejected by the typer, or ends
at the recursion limit, and it gives no reason. Otherwise it is the annotated term with its type and its
`Paths.DotMNF.HasTy` derivation. `compileAndRun` and `compileAndRunFC` also
run the DOT-MNF or the FCdot machine.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax with paths, the label table, test helpers |
| `Notation` | the entry points `pdotTy%`, `pdot%` and `pdotDefs%`, and example programs |
| `Ann` | DOT-MNF terms with the annotations the typer needs |
| `Resolve` | name resolution and `let` insertion |
| `Decide` | decision procedures for well formedness, distinct labels and strengthening |
| `Look` | the cost of a goal, `defaultFuel`, and member lookup |
| `Sub` | the subtyping algorithm in the compiler's case order |
| `Alg` | the algorithmic judgment `Alg` and completeness up to the recursion limit |
| `Avoid` | avoidance at a `let` |
| `Typer` | the typer and its entry point `synthTop?` |
| `Step` | the DOT-MNF machine as a function |
| `StepFC` | the FCdot machine as a function |
| `Pipeline` | `compile`, `compileAndRun`, `compileAndRunFC` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation |
| `Examples` | the programs end to end, each with its verdict in the kernel |

## The typer

The typer follows the subtype checker of the Scala 3 compiler,
`TypeComparer.recur` in `core/TypeComparer.scala`, in its case order. The
pinned version is scala/scala3 at commit 4dae25087d. The typer runs on one
fuel tank for the whole typing. When the tank runs short it is marked and the
typer reports a recursion limit, which is never a rejection by the rules. Up
to that limit its subtyping, path and variable goals are complete with respect
to `Alg`, the inductive judgment that says which subtyping goals the algorithm
should decide. The typer as a whole has no such theorem. It takes no middle
type from the context, so it rejects what scalac rejects (E1p, E3p, E4p, R1).
The programmer writes the domain of a lambda, the self type of an object
literal, and optionally the type of a `let`. A written `let` type binds.
Without one, the body's type is replaced by a type free of the binder, as
`TypeOps.avoid` does. The typer returns the derivation, so it is sound by
construction. Each verdict is a `decide +kernel` theorem.

## Main theorems

- `compile_checks`, `compile_checks_get`: for a program that compiles, the FCdot checker accepts the translated derivation.
- `compile_erase`: the translation erases to the erasure of the resolved term, which has the `let`s the resolver inserted.
- `compile_safe`, `compile_not_stuck`: no state reachable from the empty store by a compiled program is stuck.
- `compile_run_progress`: the source driver stops at a final state or at one that can still step.
- `compile_consistent`, `compile_fcRun_consistent`: every store the translated program reaches from the empty store is typed at a context that does not prove `⊤ ≤ ⊥`.
- `compile_no_bad_literal`: if the erasure of the resolved program is an object literal, the compiled type is not `μ(x. {A : ⊤..⊥})`.
- `sub?_complete`, `path?_complete`, `var?_complete`: if `Alg` derives a goal and the run ends with the tank unmarked, the algorithm answers it. For a path goal, the search must start from a type (`StartP`). `sub?_reject`, `path?_reject` and `var?_reject` say that a rejection with the tank unmarked means `Alg` derives no such goal. `path?_reject` also needs `StartP`.
- `Alg.sound`: a subtyping goal `Alg` derives has a `Paths.DotMNF.Sub` derivation.
- `synthTop?_mono`: a closed typing keeps its answer at more fuel. `synthTop?_stable`: a closed typing that ends with the tank unmarked, answer or rejection, gives the same verdict at more fuel.
- `avoidLet_strengthen`: from an unmarked tank with fuel left, a body type that does not mention the binder is returned as that type outside the binder.
- In `Examples`: `Ek_checks` for each accepted program, `Ek_rejected` for each rejected one, `LPt_limit` and `LPd_limit` at the recursion limit, and `Fig2_not_stuck` for gDOT's Fig. 2 (ICFP 2020).

Resolution is total on scoped programs whose member names are in the label
table (`resolveTm_isSome`). The side conditions are decided (`tyWf?_iff`,
`defsDistinct?_iff`, `tyStrengthen?_iff`). The DOT-MNF machine agrees with its
step relation (`step?_sound`, `step?_complete`). The FCdot machine `fcStep?` is
sound at every normalisation fuel (`fcStep?_sound`) and complete at some fuel
(`fcStep?_complete`).

## What it leaves out

- A derivation through a middle type the program does not write, as in E1p, E3p, E4p, R1 and B1.
- A singleton widened at a term to the declared type of its path (R2), and a relation between `p.A` and `q.A` at `p : q.type` (PQ). `Paths` has no rule for either, and scalac accepts both.
- A merge of two fields of one name. `Paths` has no rule for it, so a projection tries each field.
- A judgment whose search needs more than the fuel, as in LPt and LPd, which reach their goal again under one more binder at every level.
- A lookup through a cyclic member. It is cut, as the compiler reports a cyclic reference.
- The singleton of a direct-style path. `let` insertion binds the prefix of `x.a.b`, so R7 loses the path and is rejected.
- A completeness theorem for the typer as a whole, and a semantic statement for `let` insertion.

## Building

`lake build PathsFrontend`. It is not a default target, so the metatheory build
does not wait on it. Theorems depend on `propext` and `Quot.sound` at most.
There is no `sorry`, `axiom`, `native_decide` or Mathlib.
