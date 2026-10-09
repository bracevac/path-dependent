# Captures front end

A way to write, type and run programs of the `Captures` version without
assembling derivations by hand. `Captures` is DOT with capture checking. A type
`S ^ C` says that a value of shape `S` may use the capabilities in the capture
set `C`. A box `□ T` hides the captures of `T` until an unboxing `C ⊸ x` uses
them. A program is written in the paper's notation inside `cap%`. The front end
resolves names and inserts the `let`s that name every intermediate result,
which gives DOT-MNF, the source calculus. Unlike the vanilla front end in
`../../Frontend`, it also inserts the boxes and unboxings the program leaves
out. It finds a typing derivation with its use set, the capabilities the term
may use, translates it to FCdot, the target calculus, checks the translation
and runs the program. It proves nothing new about the calculi and changes
nothing in the version.

```lean
def C7scalaSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}). λ(u : ⊤).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in e u
```

This is a container of two capabilities, written as in Scala, with no box.
The typer boxes `f1` and `f2` where the fields ask for a box. It unboxes `e`
before the call. The type it finds charges `{k1}` to the innermost function only.

A program runs over a platform, which binds one capability for each one the
program may use. The examples use `k1` and `k2`. `compile b Λ π e` resolves the
program `e` with the label table `Λ` over the platform `π`. It types the result
within the fuel of `b : Budget`, by default `defaultFuel = 2 ^ 15`. It returns
the resolved term and a `Compiled`: the elaborated term, its use set, its type
and the `DotMNF.HasTy` derivation. `compileAndRun` adds the machine.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax, the label table, the test helper `expect` and the command `#assert_no_wf` |
| `Notation` | the entry points `capCap%`, `capTy%`, `cap%` and `capDefs%` |
| `Ann` | DOT-MNF terms with the annotations the typer needs, and their erasure |
| `Resolve` | name resolution, let insertion and platforms |
| `Decide` | decision procedures for the side conditions |
| `Search` | the first view of a variable, its declared type at the least use set |
| `Look` | `cost`, `defaultFuel` and member lookup on demand |
| `Sub` | subtyping and subcapturing in the compiler's case order |
| `Alg` | the algorithmic judgment `Alg`, completeness up to the recursion limit, and soundness |
| `Avoid` | avoidance at a `let` |
| `Adapt` | box inference at a variable |
| `Typer` | `Budget`, the typer and the entry points `synthTop?` and `synthIn?` |
| `Step` | the DOT-MNF machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdot machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `compileAndRun` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation |
| `Examples` | the programs taken end to end, each with its verdict in the kernel |

## The typer

The typer follows the subtype checker of the Scala 3 compiler, pinned as
scala/scala3 at commit 4dae25087d: `TypeComparer` (core/TypeComparer.scala)
for types and `CaptureSet.subCaptures` (cc/CaptureSet.scala) for capture sets.
`Alg` is its algorithmic judgment, one rule for each alternative of the
compiler's case order. The typer spends one fuel tank over the whole typing.
The tank is marked when it runs dry, and the typer then reports a recursion
limit, which is not a rejection by the rules. Up to that limit it is complete
with respect to `Alg`. It rejects E1, E3, E4, B1, A1 and the converse of
P1cc, programs in `Examples` that scalac rejects too. Writing the middle type,
as in E1s and E3s, compiles. The typer returns the `HasTy` derivation, so it is
sound by construction, and it finds the least use set the rules allow. An unannotated `let` is typed by avoidance, which replaces the type of
the body by one free of the binder, as in `TypeOps.avoid` (core/TypeOps.scala).
A written `let` type binds. Missing boxes and unboxings are inserted as in
`CaptureChecker.adaptBoxed` (cc/CheckCaptures.scala). The programmer writes the
domain of a lambda and the self type of an object literal. A `let` type, an
object's capture set, a box, an unboxing and an ascription are optional.

## Main theorems

- `compile_checks`, `compile_uses_checks`, `compile_checks_get`: the FCdot checker accepts the translated derivation and the use set evidence. `compile_erase`, `compile_faithful`: the translation erases to the compiled term, which has the skeleton of the resolved one.
- `compile_safe`, `compile_not_stuck`, `compile_run_progress`: every reachable state is final or can step, and `run` never stops at a stuck state.
- `compile_capture_prediction`: along any run, the matched FCdot state uses no more than the translated use set, up to a renaming.
- `compile_effect_safety`, `compile_effect_safety_get`: a run never reads a variable rooted at a platform capability outside the use set. `S1_never_reads_fs` and `C2_never_reads_k1` in `Examples` are the instances for S1 and C2 at `k1`.
- `shape?_complete`, `subcap?_complete`, `sub?_complete`, `var?_complete`: a goal `Alg` derives is answered at every fuel at which the run ends with the tank unmarked. The `_reject` versions say that a rejection with the tank unmarked means `Alg` derives no such goal. `Alg.sound_shape` and `Alg.sound_cap`: a goal `Alg` derives has a `SubShape` or `Subcap` derivation.
- `shape?_mono`, `var?_mono`, `synthTop?_mono`, `synthTop?_stable`: an answer stays the same at more fuel, and so does a rejection that ends with the tank unmarked.
- `avoidLet_strengthen`: where the body's type strengthens past the binder, avoidance returns that type.
- `objFix_progress`: each further pass of the object fixpoint adds a capture the set does not cover, or changes the definitions.
- In `Examples`, for a program `X`: `X_type` and `X_checks` for each accepted one, `X_rejected` for each rejected one with `X_not_alg` where it fails at one core goal, and `LPlet_limit`, `LPasc_limit`, `LPw2_limit` and `Doubled12k2_limit` at the recursion limit.
- `resolveTm_isSome`, `tyWf?_iff`, `defsDistinct?_iff`, `tyStrengthen?_iff`, `step?_sound`, `fcStep?_sound`: resolution is total on scoped programs, the side conditions are decided, and the machines agree with the step relations.

## What it leaves out

- A derivation through a middle type the program does not write, as in E1, E3, E4 and B1.
- A merge of two members of one name. The `Captures` calculus has no rule for it, so the typer tries each.
- A judgment whose search needs more than the fuel. The programs LP, LPw2 and a doubled alias chain of twelve links in `Examples` end at the recursion limit.
- A completeness theorem for lookup through a cyclic member, which the lookup cuts as the compiler reports a cyclic reference.
- A completeness theorem for the typer as a whole. E10, `λ(f : ⊤). λ(g : ⊤). f (g f)`, is rejected because `f` is not a function.
- A semantic statement for let insertion or box inference, and a safety theorem at an open context such as C5's.
- `any` in the outer set of a parameter type, and reach capabilities. The resolver rejects them. Scopes, levels and fresh capabilities are in `CapturesCC`.

## Building

`lake build CapturesFrontend`. It is not a default target, so building the
metatheory does not wait on it. Every definition is structural, and
`#assert_no_wf` fails the build otherwise. Every theorem depends on `propext`
and `Quot.sound` at most. There is no `sorry`, `axiom`, `native_decide` or Mathlib.
