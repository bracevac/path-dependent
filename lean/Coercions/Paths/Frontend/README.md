# Paths front end

A way to write, type and run programs of the `Paths` development without
assembling derivations by hand. A program is written in pDOT's notation inside
`pdot%`, with paths `x.a.b`, stable fields `{val a : T}` and singleton types
`p.type`. The front end resolves names and inserts `let`s to reach monadic
normal form, finds a typing derivation, translates it to FCdot, checks the
translation and runs it on either machine. This shows the development working
end to end on concrete programs, gDOT's Fig. 2 among them. It proves nothing
new about the calculi. It imports `../DotMNF`, `../FCdot` and `../DotToFCdot`
and changes nothing in them.

```lean
def E9_src : STm :=
  pdot% let q = ν(q : {B : {b : ⊤}..{b : ⊤}}. {type B = {b : ⊤}}) in
        let x = ν(x : {a : q.type}. {a = q}) in
        let y = x.a in
        λ(z : y.B). let w = z in w
```

The field `a` is declared at the singleton `q.type`, so `y` is bound at
`q.type` and `y.B` selects the member `B` of `q` through that alias.

`compile` runs the resolver and then the typer. It returns the annotated term
and a `Compiled`, which holds the synthesized type and the
`Paths.DotMNF.HasTy` derivation. `compileAndRun` adds the source machine at a
step budget. `compileAndRunFC` translates the derivation and adds the target
machine at a normalization fuel and a step budget.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax `SPath`, `SType`, `STm`, `SDefs`, the `LabelTable`, the conditions `Scoped` and `LabelsIn`, the test helper `expect` and the command `#assert_no_wf` |
| `Notation` | the entry points `pdotTy%`, `pdot%`, `pdotDefs%`, and every program of the version written in them, with R1, R2 and R7 |
| `Ann` | `ATm` and `ADefs`, DOT-MNF terms with the annotations the typer needs, and their `erase` |
| `Resolve` | name resolution and `let` insertion (`resolve`, `resolveIn`, `atomize`), totality, and the comparison of every program with the version's term |
| `Decide` | decision procedures for well-formed types (`tyWf?`), distinct labels (`defsDistinct?`), strengthening (`tyStrengthen?`) and the self-free premise of `Sub.mu` (`selfFree?`) |
| `Table` | the `Budget` and the path table: the views of every path the context reaches, with their `PathTy` derivations |
| `Search` | the subtyping search `sub?`, the path check `checkPath?` and the views of a variable |
| `Typer` | `synth?`, `check?`, `checkVar?`, `checkDefs?`, the entry points `synthTop?` and `synthIn?`, and the budget of every program |
| `Step` | the DOT-MNF machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdot machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `compileAndRun`, `compileAndRunFC` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation (`ppTy`, `ppTm`, `ppSTm`, `ppRun`), no theorems |
| `Examples` | every program taken end to end and compared with the version's derivations, and the runs of both machines |

## The typer

The typer is sound by construction. `synth?` returns a `Synth`, whose second
field is the `Paths.DotMNF.HasTy` derivation. So soundness is the result
type, and there is no soundness theorem to state. The typer is incomplete,
since DOT subtyping is undecidable. It runs on a `Budget` of five counters:
the rounds of the path table, the rounds of a variable's views, the depth of
the subtyping search, the typer's own fuel, and the new rows a round of the
table may add.

The path table is what pDOT adds. It starts with one row per variable of the
context and grows in rounds by the rules of `PathTy`. A stable field
`{val a : T}` of `p` gives the row `p.a` at `T`. A self type at a path is
opened. A singleton `q.type` at `p` copies the views of `q`. The table's
declarations `{A : S..T}`, keyed by their path, are the middles the subtyping
search tries. A projection reads its field off a view of the receiver's row
(`HasTy.projP`). A singleton goal at a variable is a path typing, asked of
`checkPath?`.

The user writes three annotations. A lambda carries its domain type, as in
the calculus. An object literal carries its self type, because
`Paths.DotMNF.Value.obj` has no slot for it and the typing rule needs it. A
`let` may carry its result type when `⊤` would lose too much. Without one, the
result type of a `let` is the body's type strengthened past the binder, else
`⊤`. A `let` checked against a known type checks its body against that type,
so the body keeps the view of its binder that the synthesized type may lose.
Fig. 2 needs this for its constructor `newTypeRef`.

Every function of the front end is structural, on a fuel or on the syntax, so
the kernel reduces resolution, the table, the search, the typer and both
machines. Per program facts are `decide +kernel` theorems. The root module
ends with `#assert_no_wf PathsFrontend`, which fails the build if any
definition falls back to well-founded recursion.

## Main theorems

The pipeline theorems take a successful `compile` and apply results of the
`Paths` development to the derivation it returned. Each holds for every
program. The other premises name what a theorem speaks of: a run, a step
budget and a fuel, or the equation that the program is an object literal.

- `compile_checks`: the FCdot checker accepts the translated derivation.
- `compile_checks_get`: the same for a program only known to compile, so a concrete program needs one decided fact.
- `compile_erase`: the translation erases to the source term.
- `compile_safe`: every state the source machine reaches is final or can step.
- `compile_not_stuck`: no state the source machine reaches is stuck.
- `compile_run_progress`: at any step budget, `run` stops at a final state or at one where `step?` still has a step.
- `compile_consistent`: every store the translated program reaches on the target machine is typed, and its context proves no `⊤ ≤ ⊥`.
- `compile_fcRun_consistent`: the same at the state `fcRun` returns, at any fuel and step budget.
- `compile_no_bad_literal`: a program that compiles to an object literal does not have gDOT's bad bounds type `μ(x. {A : ⊤..⊥})`.
- `E1_checks` to `R2_checks`: the checker accepts the translation of each example program, with no hypothesis.
- `P3e_no_bad_literal`: `compile_no_bad_literal` at pDOT's bad bounds example P3e, which compiles to an object literal.
- `Fig2_not_stuck`: no state the source machine reaches from gDOT's Fig. 2 is stuck.

Supporting results:

- `resolvePath_isSome`, `resolveTy_isSome`, `resolveTm_isSome`, `resolveDefs_isSome`: resolution succeeds on scoped programs whose labels are in the table.
- `atomize_var`: `let` insertion inserts nothing at a variable.
- `tyWf?_iff`, `defsDistinct?_iff`, `tyStrengthen?_iff`: the side conditions are decided.
- `table_mono`, `views_mono`: more rounds of the table or of the views, with the other counters kept, lose no view.
- `sub?_le`, `synth?_le`: more fuel loses no answer of the search or of the typer.
- `step?_sound`, `step?_complete`, `step?_none_classify`: `step?` agrees with the DOT-MNF step relation, and a state with no step is final or stuck.
- `fcStep?_sound`, `fcStep?_le`, `fcStep?_complete`: `fcStep?` agrees with the FCdot step relation, at every fuel and up to a fuel.
- `fcFinal?_iff`, `fcStep?_none_iff`, `fcStep?_none_classify`: a target state with no step at any fuel has no step of the relation, and is final or stuck.

## The examples

Every program of `Paths/DotMNF/Examples.lean` that the notation can write is
an example: E1 to E8, their variants E1p to E8p one stable field away, X1 to
X4, E9, E11, P3e, gDOT's Fig. 2 and pDOT's Fig. 1. All twenty-five compile.
Twenty-four compile at the type of the version's derivation. X3, E6 and X4
are typed by the version under a context, so they are written closed with a
lambda and compile at the version's type under one `∀`. Fig. 1 compiles
at the self type of `pcore`, where the version derives `⊤`, and it also
checks against `⊤`. For each program the resolved term is compared with the
version's term, the synthesized type with the version's type, and the
checker's verdict on the translation is run. Derivations are not compared,
since the typer often reaches the same judgment by another route. Six
programs reduce, and their runs on both machines are pinned at the step
counts they need.

## The restrictions of the version

The version states its restrictions on aliases in `../README.md`. No rule
replaces a path by its alias, and a variable of singleton type is not used at
a non-singleton type of its alias. The typer has no clause that replaces a
path by its alias either. That does not make it reject every program that
seems to need one. `Sub.selLower` and `Sub.selUpper` relate two singletons
through a type member whose bounds are those singletons, and the typer finds
that chain. R1 passes `x : f.type` where `g.type` is expected, under
`m : {A : f.type..g.type}`. R2 passes `x : f.type` where the function type of
`f` is expected, under `p : {A : f.type..∀(z : ⊤) ⊤}`. Both compile, and the
checker accepts both. So the front end makes no promise to reject a program
because it touches an alias.

`let` insertion at a path loses the singleton. In R7, `h x.a.b` with
`h : ∀(k : x.a.B) ⊤` becomes `let z = (let y = x.a in y.b) in h z`. The
version binds a `let` at a singleton only when the field is declared at one,
and `a` is declared at a self type. So `y` is not bound at `x.a.type`, `y.b`
has the type `y.B`, and the inner `let` falls to `⊤`, since `y.B` mentions its
binder. `⊤` is not below `x.a.B`. R7 resolves and does not compile, though
pDOT types it.

## What it leaves out

- No completeness theorem for the typer. Besides the budget, it does not find
  a subtyping whose middle is not a selection at a path of the table, a path
  the table does not reach within its rounds, an alias whose chain is longer
  than the rounds, a goal that only the replacement of a path by its alias
  would reach, which no rule of the version gives, or `Sub.mu` when the body
  of the goal is not a declaration type. It never invents a `μ`, and the
  result of a `let` without annotation is the strengthening or `⊤`. It poses
  no `PathTy.recI` or `PathTy.andI` goal at a path, so a path typing that
  needs one of the two is not found.
- Only the typer's own fuel is known to be monotone for the whole compile.
  For the other counters a budget is reported as one at which a program
  compiles, not as a bound below which it fails.
- No semantic statement for `let` insertion. The meaning of a surface program
  is the term the resolver returns.
- No printer for the target machine's state or for the object a path names
  in a final store. Facts about the target side come from the checker's
  verdict and the pipeline theorems.
- The printer's output is not claimed to parse back through `pdot%`.

## Building

`lake build PathsFrontend`. It is not a default target, so building the
metatheory does not wait on it. Every theorem depends on `propext` and
`Quot.sound` at most. No definition is well founded, and there is no Mathlib.
