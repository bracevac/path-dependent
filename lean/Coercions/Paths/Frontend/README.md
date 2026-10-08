# Paths front end

A way to write, type and run programs of the `Paths` development without
assembling derivations by hand. `Paths` extends DOT with the paths `x.a.b`,
stable fields `{val a : T}` and singleton types `p.type` of pDOT (OOPSLA
2019). A program is written in pDOT's notation inside `pdot%`. The front end
resolves names and inserts `let`s to reach monadic normal form, finds a typing
derivation, translates it to FCdot, checks the translation and runs it on
either machine. gDOT's Fig. 2 (ICFP 2020) is among the programs. It proves
nothing new about the calculi and changes nothing in `../DotMNF`, `../FCdot`
and `../DotToFCdot`, which it imports.

```lean
def R1_src : STm :=
  pdot% λ(f : ⊤). λ(g : ⊤). λ(m : {A : f.type .. g.type}). λ(x : f.type).
        let y : g.type = x in y

def R1s_src : STm :=
  pdot% λ(f : ⊤). λ(g : ⊤). λ(m : {A : f.type .. g.type}). λ(x : f.type).
        let y : g.type = (let u : m.A = x in u) in y
```

R1 needs `x : m.A` on the way from `f.type` to `g.type`. The program does not
write that middle type, so the typer rejects R1, as scalac does. R1s writes it
as an ascription and compiles.

`compile b Λ e` resolves at the label table `Λ` (the examples use
`pathsTable`) and types at the fuel of `b : Budget`, by default
`defaultFuel = 2 ^ 15`. It returns the annotated term with the type and the
`Paths.DotMNF.HasTy` derivation. `compileAndRun` adds the source machine at a
step budget, and `compileAndRunFC` the target machine.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax with paths, the `LabelTable`, the test helper `expect` and the command `#assert_no_wf` |
| `Notation` | the entry points `pdotTy%`, `pdot%`, `pdotDefs%`, and the example programs written in them |
| `Ann` | `ATm` and `ADefs`, DOT-MNF terms with the annotations the typer needs, and their `erase` |
| `Resolve` | name resolution and let insertion (`resolve`, `atomize`) and their totality |
| `Decide` | decision procedures for the side conditions (`tyWf?`, `defsDistinct?`, `tyStrengthen?`, `selfFree?`) |
| `Look` | `cost`, `defaultFuel`, member lookup on demand (`lookP`, `startP`, `declsP`, `lookV`) on the tank of `../../Frontend/Fuel.lean`, and the walker of the abstract view |
| `Sub` | the algorithm in the compiler's case order, with three goals (`sub?`, `path?`, `var?`) |
| `Alg` | the algorithmic judgment `Alg`, completeness up to the recursion limit, and `Alg.sound` |
| `Avoid` | avoidance at a `let` (`up`, `down`, `avoidLet`) |
| `Typer` | `Budget`, the candidate lists, `synthF`, `checkF` and the entry point `synthTop?` |
| `Step` | the DOT-MNF machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdot machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `compileAndRun`, `compileAndRunFC` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation, no theorems |
| `Examples` | the programs taken end to end, each with its verdict in the kernel |

## The typer

The typer follows the subtype checker of the Scala 3 compiler,
`TypeComparer`, in its case order, and takes no middle type from the context.
It runs on one fuel tank for the whole typing and reports a recursion limit
when the tank runs short, which is never a rejection by the rules. It is
complete up to that limit with respect to its algorithmic judgment `Alg`. It
rejects E1p, E3p, E4p and R1 as scalac does, and E1ps and R1s, which write
the middle type, compile. It rejects R2 and PQ, which scalac accepts, because
the version has no rule that widens a singleton at a term and none that
relates `p.A` to `q.A` at `p : q.type`.

The version has three judgments where the compiler has one, so the algorithm
has three goals, `sub`, `path` and `var`, and only `path` widens a singleton.
Lookup reads a member of `q` at `p : q.type` keeping the path `p`.

The typer returns the `Paths.DotMNF.HasTy` derivation, so it is sound by
construction. Synthesis returns a list of candidates, each a type with its
derivation. An application tries every function type the lookup finds, and a
projection returns every field. A written `let` annotation binds. Without one,
the body's type is approximated by a type free of the binder, as the
compiler's `avoid` does. The user writes three annotations: the domain of a
lambda, the self type of an object literal, and optionally the type of a
`let`. Every definition is structural, so the kernel evaluates the typer, and
each program's verdict is a `decide +kernel` theorem.

## Main theorems

- `compile_checks`, `compile_checks_get`: the FCdot checker accepts the translated derivation.
- `compile_erase`: the translation erases to the source term.
- `compile_safe`, `compile_not_stuck`: every reachable state is final or can step, and none is stuck.
- `compile_run_progress`: at any step budget, `run` stops at a final state or at one where `step?` still has a step.
- `compile_consistent`, `compile_fcRun_consistent`: every store the translated program reaches is typed at a context in which `⊤ ≤ ⊥` is not provable.
- `compile_no_bad_literal`: a compiled object literal never has the type `μ(x. {A : ⊤..⊥})`.
- `sub?_complete`, `path?_complete`, `var?_complete`: a goal `Alg` derives is answered at every fuel at which the run ends with the tank unmarked.
- `sub?_reject`, `path?_reject`, `var?_reject`: a rejection with the tank unmarked means `Alg` derives no such goal.
- `Alg.sound`: a subtyping goal `Alg` derives has a `Paths.DotMNF.Sub` derivation. It is a corollary of `Alg.answer`.
- `sub?_mono`, `path?_mono`, `var?_mono`, `synthTop?_mono`, `synthTop?_stable`: an answer, or a rejection with the tank unmarked, stays the same at more fuel.
- `avoidLet_strengthen`: where the body's type strengthens past the binder, avoidance returns that type.
- In `Examples`: `Ek_type` and `Ek_checks` for each accepted program, `Ek_rejected` for each rejected one with `Ek_not_alg` where it fails at one core goal, `LPt_limit`, `LPd_limit`, `LP_sub_limit` and `LPd_sub_limit` at the recursion limit, and `Fig2_not_stuck`.

Supporting results: `resolveTy_isSome`, `resolveTm_isSome` and
`resolveDefs_isSome` (resolution is total on scoped programs), `tyWf?_iff`,
`defsDistinct?_iff` and `tyStrengthen?_iff` (the side conditions are decided),
and `step?_sound`, `step?_complete`, `fcStep?_sound`, `fcStep?_complete` (the
machines agree with the step relations).

## What it leaves out

- A derivation through a middle type the program does not write, as in E1, E3, E4, their path twins E1p, E3p, E4p, R1 and B1.
- A singleton widened at a term to the declared type of the path it names, as R2 needs, and a relation between `p.A` and `q.A` at `p : q.type`, as PQ needs. The version has no rule for either. R2s writes the middle and compiles.
- A merge of two fields of one name. The version has no rule for it, so a projection tries each field.
- A judgment whose search needs more than the fuel. LPt and LPd meet their goal again under one more binder at every level and end at the recursion limit. Scalac rejects LPt.
- A lookup through a cyclic member, which is cut as the compiler's cyclic reference. So member premises are phrased through the lookup, and no inductive judgment of lookup comes with a completeness theorem: the cut can remove an answer that a different answer of the same key needed.
- The singleton of a direct-style path. Let insertion binds the prefix of `x.a.b`, so R7 loses the path and does not compile, though pDOT types it.
- A completeness theorem for the typer as a whole, and a semantic statement for let insertion.

## Building

`lake build PathsFrontend`. It is not a default target, so building the
metatheory does not wait on it. Every theorem depends on `propext` and
`Quot.sound` at most. There is no `sorry`, `axiom` or `native_decide`, and no
Mathlib.
