# Frontend

A way to write, type and run DOT programs without assembling derivations by
hand. A program is written in the paper's notation inside `dot%`. The front end
resolves names and inserts `let`s to reach monadic normal form, finds a typing
derivation, translates it to FCdot, and runs it. It proves nothing new about
the calculi. It imports `../DotMNF`, `../FCdot`, `../DotToFCdot` and
`../Runtime.lean` and changes nothing in them.

```lean
def E3src : STm :=
  dot% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}).
         λ(z : {b : ⊤}). let y : {a : ⊤} = z in y

def E3ssrc : STm :=
  dot% λ(x : {A : ⊥ .. {a : ⊤}} ∧ {A : {b : ⊤} .. ⊤}).
         λ(z : {b : ⊤}). let y : {a : ⊤} = (let u : x.A = z in u) in y
```

E3 needs `z : x.A` on the way from `{b : ⊤}` to `{a : ⊤}`. The program does
not write that middle type, so the typer rejects E3, as scalac does. E3s
writes it as an ascription and compiles.

`compile b Λ e` resolves and types at the fuel of `b : Budget`, by default
`defaultFuel = 2 ^ 15`. It returns the annotated term with the type and the
`DotMNF.HasTy` derivation. `compileAndRun` adds the machine at a step budget.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax, the `LabelTable`, the test helper `expect` and the command `#assert_no_wf` |
| `Notation` | the entry points `dotTy%`, `dot%`, `dotDefs%`, with `{type A = T}` for a type member definition |
| `Ann` | `ATm` and `ADefs`, DOT-MNF terms with the annotations the typer needs, and their `erase` |
| `Resolve` | name resolution and let insertion (`resolve`, `atomize`), totality, and the programs E1 to E10 |
| `Decide` | decision procedures for distinct labels (`defsDistinct?`) and strengthening (`tyStrengthen?`) |
| `Fuel` | the tank, the run with its cut of repeated goals, and the frame and cut lemmas |
| `Look` | `cost`, `defaultFuel`, and member lookup on demand (`look`, `decls`) |
| `Sub` | the subtyping algorithm in the compiler's case order (`sub?`, `var?`) |
| `Alg` | the algorithmic judgment `Alg`, completeness up to the recursion limit, and `Alg.sound` |
| `Limit` | goals that end at the recursion limit |
| `Avoid` | avoidance at a `let` (`up`, `down`, `avoidLet`) |
| `Typer` | `Budget`, the candidate lists, `synthF`, `checkF` and the entry point `synthTop?` |
| `Step` | the DOT-MNF machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdot machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `compileAndRun` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation (`ppTy`, `ppTm`, `ppRun`), no theorems |
| `Examples` | the programs taken end to end, each with its verdict in the kernel |

## The typer

The typer follows the subtype checker of the Scala 3 compiler,
`TypeComparer`, in its case order, and takes no middle type from the context.
It runs on one fuel tank for the whole typing and reports a recursion limit
when the tank runs short, which is never a rejection by the rules. It is
complete up to that limit with respect to its algorithmic judgment `Alg`. It
rejects what scalac rejects (E1, E3, E4), and E1s and E3s, which write the
middle type, compile.

The typer returns the `DotMNF.HasTy` derivation, so it is sound by
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
- `sub?_complete`, `var?_complete`: a goal `Alg` derives is answered at every fuel at which the run ends with the tank unmarked.
- `sub?_reject`, `var?_reject`: a rejection with the tank unmarked means `Alg` derives no such goal.
- `Alg.sound`: a subtyping goal `Alg` derives has a `DotMNF.Sub` derivation. It is a corollary of `Alg.answer`.
- `sub?_mono`, `var?_mono`, `synthTop?_mono`, `synthTop?_stable`: an answer, or a rejection with the tank unmarked, stays the same at more fuel.
- `avoidLet_strengthen`: where the body's type strengthens past the binder, avoidance returns that type.
- `run_frame`, `run_index`, `cut_complete`: the run of `Fuel` gives the same answer with more fuel, and its cut loses no success.
- In `Examples`: `Ek_type` and `Ek_checks` for each accepted program, `Ek_rejected` for each rejected one with `Ek_not_alg` where it fails at one core goal, and `LP_limit`, `PF_limit`, `Doubled12_limit` at the recursion limit.

Supporting results: `resolveTy_isSome`, `resolveTm_isSome` and
`resolveDefs_isSome` (resolution is total on scoped programs),
`defsDistinct?_iff` and `tyStrengthen?_iff` (the side conditions are decided),
and `step?_sound`, `step?_complete`, `fcStep?_sound`, `fcStep?_complete` (the
machines agree with the step relations).

## What it leaves out

- A derivation through a middle type the program does not write, as in E1, E3 and E4.
- A merge of two fields of one name. DOT-MNF has no rule for it, so a projection tries each field.
- A judgment whose search needs more than the fuel. LP, Pierce's divergence PF and a doubled alias chain end at the recursion limit.
- A lookup through a cyclic member, which is cut as the compiler's cyclic reference. So member premises are phrased through the lookup, and no inductive judgment of lookup comes with a completeness theorem: the cut can remove an answer that a different answer of the same key needed.
- A completeness theorem for the typer as a whole. E10, `λ(f : ⊤). λ(g : ⊤). f (g f)`, is rejected because `f` is not a function.
- A semantic statement for let insertion. The meaning of a surface program is the term the resolver returns.
- The other calculi. Each version has a front end of its own in its `Frontend/` folder: `Captures`, `CapturesCC`, `Classifiers`, `Paths` and `Oopsla16`.

## Building

`lake build Frontend`. It is not a default target, so building the metatheory
does not wait on it. Every theorem depends on `propext` and `Quot.sound` at
most. There is no `sorry`, `axiom` or `native_decide`, and no Mathlib.
