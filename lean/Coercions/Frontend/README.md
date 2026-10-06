# Frontend

A way to write, type and run DOT programs without assembling derivations by
hand. A program is written in the paper's notation inside `dot%`. The front end
resolves names and inserts `let`s to reach monadic normal form, finds a typing
derivation, translates it to FCdot, and runs it. This shows the vanilla
development working end to end on concrete programs. It proves nothing new
about the calculi. It imports `../DotMNF`, `../FCdot`, `../DotToFCdot` and
`../Runtime.lean` and changes nothing in them.

```lean
def E2src : STm :=
  dot% let x = ν(s : {A : ∀(y : s.A) s.A .. ∀(y : s.A) s.A} ∧ {a : ∀(y : s.A) s.A}.
                  {type A = ∀(y : s.A) s.A} ∧ {a = λ(y : s.A). y})
       in let f = x.a in f f
```

`compile` runs the resolver and then the typer. It returns the annotated term
and a `Compiled`, which holds the synthesized type and the `DotMNF.HasTy`
derivation. `compileAndRun` adds the machine at a step budget.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax `SType`, `STm`, `SDefs`, the `LabelTable`, the conditions `Scoped` and `LabelsIn`, and the test helper `expect` |
| `Notation` | the entry points `dotTy%`, `dot%`, `dotDefs%` for the paper's notation, with `{type A = T}` for a type member definition |
| `Ann` | `ATm` and `ADefs`, DOT-MNF terms with the annotations the typer needs, and their `erase` |
| `Resolve` | name resolution and let insertion (`resolve`, `resolveTm`, `atomize`), totality, and the surface programs E1 to E10 |
| `Decide` | decision procedures for distinct labels (`defsDistinct?`) and strengthening (`tyStrengthen?`) |
| `Search` | the `Budget`, the views of a variable, the declaration table, and the subtyping search `sub?` |
| `Typer` | `synth?`, `check?`, `checkVar?`, `checkDefs?` and the entry point `synthTop?` |
| `Step` | the DOT-MNF machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdot machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `compileAndRun` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation (`ppTy`, `ppTm`, `ppRun`), no theorems |
| `Examples` | twelve programs taken end to end and compared with the hand-written vanilla derivations |

## The typer

The typer is sound by construction. `synth?` returns a `Synth`, whose second
field is the `DotMNF.HasTy` derivation. So soundness is the result type, and
there is no soundness theorem to state. The typer is incomplete, since DOT
subtyping is undecidable. It runs on a `Budget` of four fuel counters, and the
search for the middle type of a transitivity step only tries declarations the
context already has. It never invents a `μ`. For a `let`, the result type is
the annotation if there is one, else the body's type strengthened past the
binder, else `⊤`.

The user writes three annotations. A lambda carries its domain type, as in the
calculus. An object literal carries its self type, because `DotMNF.Value.obj`
has no slot for it and the typing rule needs it. A `let` may carry its result
type when `⊤` would lose too much.

## Main theorems

The pipeline theorems take a successful `compile` and apply results of the
vanilla development to the derivation it returned.

- `compile_checks`: the FCdot checker accepts the translated derivation.
- `compile_erase`: the translation erases to the source term.
- `compile_safe`: every reachable state is final or can step.
- `compile_not_stuck`: no reachable state is stuck.
- `compile_run_progress`: at any step budget, `run` stops at a final state or at one where `step?` still has a step.
- `E1_checks` to `E11_checks`: `compile_checks` for each example program.

Supporting results:

- `resolveTy_isSome`, `resolveTm_isSome`, `resolveDefs_isSome`: resolution succeeds on scoped programs whose labels are in the table.
- `atomize_var`: let insertion inserts nothing at a variable.
- `defsDistinct?_iff`, `tyStrengthen?_iff`: the side conditions are decided.
- `views_mono`, `decls_mono`, `sub?_le`, `synth?_le`: more fuel never loses an answer.
- `step?_sound`, `step?_complete`, `step?_none_classify`: `step?` agrees with the DOT-MNF step relation, and a state with no step is final or stuck.
- `fcStep?_sound`, `fcStep?_le`, `fcStep?_complete`: `fcStep?` agrees with the FCdot step relation, at every fuel and up to a fuel.

## What it leaves out

- No completeness theorem for the typer. E10, `λ(f : ⊤). λ(g : ⊤). f (g f)`, is rejected because `f` is not a function. Its variant `E10t` at `∀(x : ⊤) ⊤` is accepted.
- No semantic statement for let insertion. The meaning of a surface program is the term the resolver returns.
- The typer and the search are well-founded definitions, so the kernel does not reduce them. Their tests run compiled code through `expect`. Resolution, the decision procedures and the DOT-MNF machine are structural, and their tests are `by decide` or `rfl`.
- Only the vanilla calculus. The extensions have no front end.

## Building

`lake build Frontend`. It is not a default target, so building the metatheory
does not wait on it. Every theorem depends on `propext` and `Quot.sound` at
most. There is no `sorry`, `axiom` or `native_decide`, and no Mathlib.
