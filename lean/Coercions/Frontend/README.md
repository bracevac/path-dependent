# Frontend

A way to write, type and run DOT programs without building derivations by
hand. DOT is the calculus behind path-dependent types in Scala 3. A program is
written in DOT notation inside `dot%`. The front end resolves names, binds each
intermediate result with a `let` (monadic normal form, MNF), finds a typing
derivation, translates it to FCdot, and runs it. DOT-MNF is DOT in that form.
FCdot is a target calculus with a type checker. The front end proves nothing
new about the calculi. It imports `../DotMNF`, `../FCdot` and `../DotToFCdot`
and changes nothing in them.

```lean
def E3src : STm :=
  dot% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}).
         λ(z : {b : ⊤}). let y : {a : ⊤} = z in y

def E3ssrc : STm :=
  dot% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}).
         λ(z : {b : ⊤}). let y : {a : ⊤} = (let u : x.A = z in u) in y
```

E3 needs `z : x.A` on the way from `{b : ⊤}` to `{a : ⊤}`. The program does
not write that middle type. So the typer rejects E3, as scalac does. E3s
writes it as the inner `let u : x.A = z` and compiles.

`compile b Λ e` resolves and types the term `e`. The table `Λ` maps the names
of type and field members to labels. The budget `b` holds the fuel of the
search, `defaultFuel = 2 ^ 15` by default. The result is `none` if `e` is out
of scope, uses a name missing from `Λ`, or does not type, and it carries no
reason. Otherwise it is the annotated term with its type and its
`DotMNF.HasTy` derivation. `compileAndRun b m Λ e` also runs the DOT-MNF
machine for at most `m` steps.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax, the label table, test helpers |
| `Notation` | the entry points `dotTy%`, `dot%` and `dotDefs%` |
| `Ann` | DOT-MNF terms with the annotations the typer needs |
| `Resolve` | name resolution and `let` insertion, and the programs E1 to E10 |
| `Decide` | decision procedures for distinct labels and strengthening |
| `Fuel` | the fuel tank and the search that cuts repeated goals |
| `Look` | the cost of a goal, `defaultFuel`, and member lookup |
| `Sub` | the subtyping algorithm in the compiler's case order |
| `Alg` | the algorithmic judgment `Alg` and completeness up to the recursion limit |
| `Limit` | goals that end at the recursion limit |
| `Avoid` | avoidance at a `let` |
| `Typer` | the typer and its entry point `synthTop?` |
| `Step` | the DOT-MNF machine as a function |
| `StepFC` | the FCdot machine as a function |
| `Pipeline` | `compile`, `compileAndRun` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation |
| `Examples` | the programs end to end, each with its verdict in the kernel |

## The typer

The typer follows the subtype checker of the Scala 3 compiler. That is
`TypeComparer.recur` in `core/TypeComparer.scala` and the `firstTry` to
`fourthTry` it calls, in their case order. The pinned version is scala/scala3
at commit 4dae25087d. The search spends fuel from one tank for the whole
typing. When the tank runs short it is marked, and the typer reports a
recursion limit. That is never a rejection by the rules. Up to the limit the
typer is complete with respect to `Alg`, the inductive judgment that says
which subtyping goals the algorithm should decide. It takes no middle type from
the context, so it rejects what scalac rejects (E1, E3, E4). The programmer
writes the domain of a lambda, the self type of an object literal, and
optionally the type of a `let`. A written `let` type binds. Without one, the
body's type is replaced by a type free of the binder, as `TypeOps.avoid` does.
The typer returns the derivation, so it is sound by construction. Every
definition is structural, so Lean's kernel runs the typer in `decide +kernel`.

## Main theorems

- `compile_checks`, `compile_checks_get`: the FCdot checker accepts the translated derivation.
- `compile_erase`: the translation erases to the source term.
- `compile_safe`, `compile_not_stuck`: every state reachable from a compiled program is final or can step, so none is stuck.
- `compile_run_progress`: after any number of steps, the driver is at a final state or at one that can still step.
- `sub?_complete`, `var?_complete`: if `Alg` derives a goal and the tank ends unmarked, the algorithm finds a derivation.
- `sub?_reject`, `var?_reject`: a rejection with the tank unmarked means `Alg` derives no such goal.
- `Alg.sound`: a subtyping goal `Alg` derives has a `DotMNF.Sub` derivation.
- `synthTop?_mono`, `synthTop?_stable`: a typing keeps its answer at more fuel.
- `avoidLet_strengthen`: a body type that does not mention the binder comes back unchanged.
- In `Examples`: `Ek_checks` for each accepted program, `Ek_rejected` for each rejected one, and `LP_limit`, `PF_limit`, `Doubled12_limit` for programs that end at the recursion limit.

Resolution is total on scoped programs (`resolveTm_isSome`). The side
conditions are decided (`defsDistinct?_iff`, `tyStrengthen?_iff`). The machines
agree with the step relations (`step?_sound`, `step?_complete`, `fcStep?_sound`,
`fcStep?_complete`).

## What it leaves out

- A derivation through a middle type the program does not write, as in E1, E3 and E4.
- A merge of two fields of one name. DOT-MNF has no rule for it, so a projection tries each field.
- A judgment whose search needs more than the fuel, as in LP and Pierce's divergence PF.
- A lookup through a cyclic member. It is cut, as the compiler reports a cyclic reference.
- A completeness theorem for the typer as a whole. E10, `λ(f : ⊤). λ(g : ⊤). f (g f)`, is rejected because `f : ⊤` is not a function.
- A semantic statement for `let` insertion. A program means the term the resolver returns.
- The other calculi. `Captures`, `CapturesCC`, `Classifiers`, `Paths` and `Oopsla16` each have a front end in their own `Frontend/` folder.

## Building

`lake build Frontend`. It is not a default target, so building the metatheory
does not wait on it. Every theorem depends on `propext` and `Quot.sound` at
most. There is no `sorry`, `axiom` or `native_decide`, and no Mathlib.
