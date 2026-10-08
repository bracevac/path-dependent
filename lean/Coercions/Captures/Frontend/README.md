# Captures front end

A way to write, type and run programs of the `Captures` version without
assembling derivations by hand. `Captures` is DOT with capture checking. A type
`S ^ C` says that a value of shape `S` may use the capabilities in the capture
set `C`. A program is written in the paper's notation inside `cap%`. It may also
use capture members `{C^ : c₁..c₂}`, boxes `□ T` and unboxings `C ⊸ x`. The front end resolves names and inserts `let`s to reach
monadic normal form, where every intermediate result is named. It finds a
typing derivation with its use set, the capabilities the term may use. It
translates the derivation to FCdot, the target calculus with explicit evidence,
and runs the program. Unlike the vanilla front end in `../../Frontend`, it also
inserts the boxes and unboxings a program leaves out. It proves nothing new
about the calculi. It imports `../DotMNF`, `../FCdot`, `../DotToFCdot` and
`../Runtime.lean` and changes none of them.

```lean
def C7scalaSrc : STm :=
  cap% λ(f1 : (∀(u : ⊤) ⊤) ^ {k1}). λ(f2 : (∀(u : ⊤) ⊤) ^ {k2}). λ(u : ⊤).
        let o = ν(z : {e1 : □((∀(u : ⊤) ⊤) ^ {k1})} ∧ {e2 : □((∀(u : ⊤) ⊤) ^ {k2})}.
                   {e1 = f1} ∧ {e2 = f2})
        in let e = o.e1 in e u
```

This is a container of two capabilities, written as in Scala, with no box.
The typer boxes `f1` and `f2` where the fields ask for a box and unboxes `e`
before the call. The type it finds charges `{k1}` to the innermost function only.

A program runs over a platform: one capture binder per capability it may use.
The platform `πc` names two, `k1` and `k2`. `compile` runs the resolver and then
the typer over the platform. It returns the resolved term and a `Compiled`,
which holds the elaborated term, its use set, its type and the `DotMNF.HasTy`
derivation. `compileAndRun` adds the machine at a step budget.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax, the label table, the test helper `expect` and the command `#assert_no_wf` |
| `Notation` | the entry points `capCap%`, `capTy%`, `cap%`, `capDefs%` for the paper's notation |
| `Ann` | DOT-MNF terms with the annotations the typer needs, their erasure and their skeleton |
| `Resolve` | name resolution, let insertion, and platforms |
| `Decide` | decision procedures for the typing side conditions |
| `Search` | the `Budget` and the search for subtyping and subcapturing |
| `Adapt` | box inference at a variable |
| `Typer` | `synth?`, `check?` and the entry points `synthTop?` and `synthIn?` |
| `Step` | the DOT-MNF machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdot machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `compileAndRun` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation, no theorems |
| `Examples` | 23 programs taken end to end and compared with the hand written derivations |

## The typer

The typer is sound by construction. Every result carries the `DotMNF.HasTy`
derivation of the term it typed. So soundness is the result type, and there
is no soundness theorem to state. The typer is incomplete, since DOT
subtyping is undecidable and subcapturing goes through it. It runs on a
`Budget` of fuel counters. The middle type of a transitivity step is always
one the context declares, so the typer never invents a `μ`. A program fails
to compile when it needs a middle type the context lacks or the budget runs out.

The typer looks for the smallest use sets. A variable declared at the empty set
is used at `{}`, any other variable at `{x}`. Without its ascription, S1 types
at `{}` where the version's derivation says `{k1}`, and C2 at `{k2}` where it
says `{k1, k2}`.

Box inference is part of the typer. Where a variable does not fit its goal,
or a function or a receiver is a box, the typer inserts `□ x` or `C ⊸ x`.
So the elaborated term can differ from the written one. `compile` accepts
it only if the two have the same skeleton. The skeleton forgets
annotations, capture sets, boxes, unboxings and ascriptions, and it inlines a
`let` of a variable.

The user writes a few annotations. A lambda carries its domain type. An
object literal carries its self type. A `let` may carry its result type,
and an ascription `(t : T)` may name the type of a bound term. A capturing type
written as a type member bound is boxed by the resolver, as Scala boxes a type
argument.

## Main theorems

The pipeline theorems take a successful `compile` and apply results of the
`Captures` version to the derivation it returned.

- `compile_checks`: the FCdot checker accepts the translated derivation.
- `compile_uses_checks`: the FCdot checker accepts the use set evidence the translation emits.
- `compile_erase`: the translation erases to the compiled term.
- `compile_faithful`: the elaborated term has the skeleton of the resolved term.
- `compile_safe`: every state reachable from the platform's initial store is final or can step.
- `compile_not_stuck`: no reachable state is stuck.
- `compile_run_progress`: at any step budget, `run` stops at a final state or at one where `step?` still has a step.
- `compile_capture_prediction`: along any run, the matched FCdot state uses no more than the translated use set the typer found, up to a renaming.
- `compile_effect_safety`: in the matched FCdot state, a run never reads a variable rooted at a platform capability (one that holds it) outside that use set.
- `compile_checks_get`, `compile_effect_safety_get`: the same two for a program whose compile succeeds by a decided test.
- `E1_checks` to `S2_checks`, `C5_checks`: the checker accepts the translation of each example the typer accepts, with no hypothesis.
- `S1_never_reads_fs`: a run of the version's `S1tm` never reads a variable rooted at `k1`, the file system. The use set the typer finds for S1 is `{}`.
- `C2_never_reads_k1`: a run of the version's `C2tm` never reads a variable rooted at `k1`. The use set the typer finds for C2 is `{k2}`.

Supporting results:

- `resolveT_isSome`, `resolveTm_isSome`, `resolveDefs_isSome`: resolution succeeds on scoped programs whose labels are in the table and whose `any` and capturing types sit where the version allows.
- `tyWf?_iff`, `defsDistinct?_iff`, `tyStrengthen?_iff`: the side conditions are decided.
- `views_mono`, `decls_mono`, `sub?_le`, `subcap?_le`, `synth?_le`: more fuel never loses an answer.
- `step?_sound`, `step?_complete`, `step?_none_classify`: `step?` agrees with the DOT-MNF step relation, and a state with no step is final or stuck. `fcStep?_sound`, `fcStep?_complete` and `fcStep?_none_classify` say the same of `fcStep?` and FCdot.

## What it leaves out

- No completeness theorem for the typer. E10, `λ(f : ⊤). λ(g : ⊤). f (g f)`, is rejected because `f` is not a function. Its variant `E10t` at `∀(x : ⊤) ⊤` is accepted.
- No semantic statement for let insertion or box inference. The skeleton equation is what relates the written and the elaborated term.
- No safety theorem at an open context. C5 is typed and checked at the version's open context only.
- `any` in the outer set of a parameter type, and reach capabilities. The resolver rejects them.
- Scopes, levels and fresh capabilities. They are the `CapturesCC` version.

## Building

`lake build CapturesFrontend`. It is not a default target, so building the
metatheory does not wait on it. Every definition is structural, and
`#assert_no_wf` fails the build otherwise. Every theorem depends on `propext`
and `Quot.sound` at most. There is no `sorry`, `axiom`, `native_decide` or Mathlib.
