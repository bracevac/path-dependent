# Paths front end

A way to write, type and run programs of the `Paths` development without
assembling derivations by hand. `Paths` extends DOT with the paths and
singleton types of pDOT (OOPSLA 2019). A program is written in pDOT's notation
inside `pdot%`. The front end resolves names and inserts `let`s so that every
intermediate result is named, which is the monadic normal form of the source
calculus DOT-MNF. It then finds a typing derivation, translates it to the
target calculus FCdot, checks the translation and runs it on either machine.
This shows the development working end to end on concrete programs, among
them gDOT's Fig. 2 (ICFP 2020). It proves nothing new about the calculi and
changes nothing in `../DotMNF`, `../FCdot` and `../DotToFCdot`, which it
imports.

What it adds to the vanilla front end in `../../Frontend` is paths. The notation has paths
`x.a.b`, stable fields `{val a : T}` and singleton types `p.type`, and the
typer finds the path typings that use them.

```lean
def E9_src : STm :=
  pdot% let q = ν(q : {B : {b : ⊤}..{b : ⊤}}. {type B = {b : ⊤}}) in
        let x = ν(x : {a : q.type}. {a = q}) in
        let y = x.a in
        λ(z : y.B). let w = z in w
```

The field `a` is declared at the singleton `q.type`. So `y` has the type
`q.type`, and `y.B` selects the member `B` of `q`.

`compile b Λ e` takes a `Budget`, a `LabelTable` of the labels in scope (the
examples use `pathsTable`) and the surface term. It runs the resolver and then
the typer. It returns the annotated term and a `Compiled`, which holds the
synthesized type and the `Paths.DotMNF.HasTy` derivation. `compileAndRun` adds
the source machine for DOT-MNF terms. `compileAndRunFC` translates the
derivation and adds the target machine for FCdot terms.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax with paths, the `LabelTable`, the test helper `expect` and the command `#assert_no_wf` |
| `Notation` | the entry points `pdotTy%`, `pdot%`, `pdotDefs%`, and the example programs written in them |
| `Ann` | `ATm` and `ADefs`, DOT-MNF terms with the annotations the typer needs, and their `erase` |
| `Resolve` | name resolution and let insertion (`resolve`, `atomize`) and their totality |
| `Decide` | decision procedures for the side conditions of the typing rules |
| `Table` | the `Budget` and the path table, the types of every path the context reaches |
| `Search` | the subtyping search `sub?` and the path check `checkPath?` |
| `Typer` | `synth?`, `check?` and the entry point `synthTop?` |
| `Step` | the DOT-MNF machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdot machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `compileAndRun`, `compileAndRunFC` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation, no theorems |
| `Examples` | the programs taken end to end and compared with the hand-written derivations |

## The typer

The typer is sound by construction. `synth?` returns a `Synth`, whose second
field is the `Paths.DotMNF.HasTy` derivation. So soundness is the result type,
and there is no soundness theorem to state. The typer is incomplete, since DOT
subtyping is undecidable. It runs on a `Budget` of fuel counters. Raising a
counter is not known to keep a program compiling, except the typer's own fuel.

For paths, the typer builds a table. It starts with the variables of the
context and grows by the path typing rules. A stable field `{val a : T}` of
`p` gives `p.a` the type `T`. A singleton `q.type` at `p` gives `p` the types
of `q`. The type members the table finds are what the subtyping search tries.

The user writes three annotations. A lambda carries its domain type. An object
literal carries its self type, because the typing rule needs it. A `let` may
carry its result type when `⊤` would lose too much. Without one, the result
type of a `let` is the body's type strengthened past the binder, else `⊤`.

No definition uses well-founded recursion, so the kernel evaluates the typer
and both machines. The facts about each program are `decide +kernel` theorems.

## Main theorems

The pipeline theorems take a successful `compile` and apply the `Paths`
results to the derivation it returned.

- `compile_checks`: the FCdot checker accepts the translated derivation.
- `compile_erase`: the translation erases to the source term.
- `compile_safe`: every state the source machine reaches is final or can step.
- `compile_not_stuck`: no state the source machine reaches is stuck.
- `compile_run_progress`: at any step budget, `run` stops at a final state or at one where `step?` still has a step.
- `compile_consistent`: every store the translated program reaches on the target machine is typed at a context in which `⊤ ≤ ⊥` is not provable.
- `compile_fcRun_consistent`: the same at the state `fcRun` returns.
- `compile_no_bad_literal`: a program that compiles to an object literal does not have the bad bounds type `μ(x. {A : ⊤..⊥})`, which would prove `⊤ ≤ ⊥`.
- `E1_checks` to `R2_checks`: one for each example program, the checker accepts its translation.
- `Fig2_not_stuck`: no state the source machine reaches from gDOT's Fig. 2 is stuck.

Supporting results:

- `resolveTy_isSome`, `resolveTm_isSome`: resolution succeeds on programs whose names are bound and whose labels are in the table.
- `tyWf?_iff`, `defsDistinct?_iff`, `tyStrengthen?_iff`: the side conditions are decided.
- `sub?_le`, `synth?_le`: more fuel loses no answer.
- `step?_sound`, `step?_complete`: `step?` agrees with the DOT-MNF step relation.
- `fcStep?_sound`, `fcStep?_complete`: every answer of `fcStep?` is a step of the FCdot step relation, and every such step is found at some fuel.

## The examples

The examples are the programs of `Paths/DotMNF/Examples.lean` that the
notation can write, gDOT's Fig. 2 and pDOT's Fig. 1 among them, and the alias
cases R1 and R2. Each one compiles, and the checker accepts its translation.
Decided facts fix the synthesized type of each and, for most, the resolved
term. They are compared with the hand-written derivation where there is one.
Six of them reduce, and both machines run them to a final state.

## What it leaves out

- No completeness theorem for the typer. It never invents a `μ`, and it only finds paths the table reaches.
- No rule of `Paths` replaces a path by its alias, so the typer has no such step. Aliases that go through a type member with singleton bounds still work, as R1 and R2 show.
- Let insertion at a path loses the singleton. R7, `h x.a.b`, resolves but does not compile, though pDOT types it.
- No semantic statement for let insertion. The meaning of a surface program is the term the resolver returns.

## Building

`lake build PathsFrontend`. It is not a default target, so building the
metatheory does not wait on it. Every theorem depends on `propext` and
`Quot.sound` at most, and there is no Mathlib.
