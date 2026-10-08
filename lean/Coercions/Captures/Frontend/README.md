# Captures front end

A way to write, type and run programs of the `Captures` version without
assembling derivations by hand. `Captures` is DOT with capture checking. A type
`S ^ C` says that a value of shape `S` may use the capabilities in the capture
set `C`. A program is written in the paper's notation inside `cap%`, with
capture members `{C^ : c₁..c₂}`, boxes `□ T` and unboxings `C ⊸ x`. The front
end resolves names and inserts `let`s, finds a typing derivation with its use
set, the capabilities the term may use, translates it to FCdot, checks the
translation and runs the program. Unlike the vanilla front end in
`../../Frontend`, it inserts the boxes and unboxings a program leaves out. It
proves nothing new about the calculi and changes nothing in the version.

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

A program runs over a platform, a capture binder per capability it may use, as
`πc` with `k1` and `k2`. `compile b Λ π e` resolves over `π` and types at the
fuel of `b : Budget`, by default `defaultFuel = 2 ^ 15`. It returns the
resolved term and a `Compiled`: the elaborated term, its use set, its type and
the `DotMNF.HasTy` derivation. `compileAndRun` adds the machine.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax, the label table, the test helper `expect` and the command `#assert_no_wf` |
| `Notation` | the entry points `capCap%`, `capTy%`, `cap%`, `capDefs%` for the paper's notation |
| `Ann` | DOT-MNF terms with the annotations the typer needs, their erasure and their skeleton |
| `Resolve` | name resolution, let insertion, platforms, and their totality |
| `Decide` | decision procedures for the side conditions (`tyWf?`, `defsDistinct?`, `tyStrengthen?`) |
| `Search` | the first view of a variable (`View`, `pureVar`, `varView`) |
| `Look` | `cost`, `defaultFuel`, and member lookup on demand (`look`, `decls`, `capDecls`), on the tank of `../../Frontend/Fuel.lean` |
| `Sub` | the algorithm in the compiler's case order, with three goals (`shape?`, `subcap?`, `sub?`, `var?`) |
| `Alg` | the algorithmic judgment `Alg`, completeness up to the recursion limit, and its soundness |
| `Avoid` | avoidance at a `let` (`up`, `down`, `capUp`, `capDown`, `avoidLet`, `avoidUses`) |
| `Adapt` | the result types of the typer and box inference at a variable (`adaptVarF`) |
| `Typer` | `Budget`, the candidate lists, `inferF`, the object fixpoint `objFixF` and the entry points `synthTop?` and `synthIn?` |
| `Step` | the DOT-MNF machine as a function, `step?`, with the driver `run` |
| `StepFC` | the FCdot machine as a function, `fcStep?`, with the driver `fcRun` |
| `Pipeline` | `Compiled`, `compile`, `compileAndRun` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation, no theorems |
| `Examples` | the programs taken end to end, each with its verdict in the kernel |

## The typer

The typer follows the subtype checker of the Scala 3 compiler,
`TypeComparer`, in its case order, and the compiler's subcapturing,
`subCaptures` and `subsumes`, and takes no middle type from the context.
It runs on one fuel tank for the whole typing and reports a recursion limit
when the tank runs short, which is never a rejection by the rules. It is
complete up to that limit with respect to its algorithmic judgment `Alg`.
The capture set of an object literal with no written set is a least
fixpoint, grown by the atoms its definitions use that the set does not
account for, as the compiler solves a class's use set. It rejects E1, E3,
E4, B1, A1 and the converse of P1cc as scalac does, and E1s and E3s, which
write the middle type, compile.

The algorithm has three goals: `shape` on shapes, `cap` on capture sets, and
`var`, which keeps a variable while it widens its shape. `Sub.lean` lists
where the version's rules force a route other than the compiler's. The typer
returns the `DotMNF.HasTy` derivation, so it is sound by construction. It
finds the least use set the rules allow. Synthesis returns a list of
candidates. An application tries every function type the lookup finds, and a
projection returns every field. A written `let` annotation binds. Without one,
the body's type and use set are approximated by ones free of the binder, as
the compiler's `avoid` does. Where a variable does not fit its goal, or a
function or a receiver is a box, the typer inserts `□ x` or `C ⊸ x`, as the
compiler's `adaptBoxed` does, and `compile` checks that the skeleton is the
written one. The passes of the object fixpoint are bounded by `objBound`, a
size of the program not proved to suffice, and a pass that reaches it marks
the tank.

## Main theorems

- `compile_checks`, `compile_uses_checks`, `compile_checks_get`: the FCdot checker accepts the translated derivation and the use set evidence.
- `compile_erase`, `compile_faithful`: the translation erases to the compiled term, which has the skeleton of the resolved one.
- `compile_safe`, `compile_not_stuck`, `compile_run_progress`: every reachable state is final or can step, none is stuck, and `run` stops at a final state or at one that still steps.
- `compile_capture_prediction`: along any run, the matched FCdot state uses no more than the translated use set, up to a renaming.
- `compile_effect_safety`, `compile_effect_safety_get`: a run never reads a variable rooted at a platform capability outside that use set.
- `shape?_complete`, `subcap?_complete`, `sub?_complete`, `var?_complete`: a goal `Alg` derives is answered at every fuel at which the run ends with the tank unmarked.
- `shape?_reject`, `subcap?_reject`, `sub?_reject`, `var?_reject`: a rejection with the tank unmarked means `Alg` derives no such goal.
- `Alg.sound_shape`, `Alg.sound_cap`: a goal `Alg` derives has a `SubShape` or `Subcap` derivation. Both are corollaries of `Alg.answer`.
- `shape?_mono`, `subcap?_mono`, `sub?_mono`, `var?_mono`, `synthTop?_mono`, `synthTop?_stable`: an answer, or a rejection with the tank unmarked, stays the same at more fuel.
- `avoidLet_strengthen`: where the body's type strengthens past the binder, avoidance returns that type.
- `objFix_progress`: a pass of the object fixpoint that goes on adds an atom the set does not account for, or other definitions.
- In `Examples`: `Ek_type` and `Ek_checks` for each accepted program, `Ek_rejected` for each rejected one with `Ek_not_alg` where it fails at one core goal, `LPlet_limit`, `LPasc_limit`, `LPw2_limit` and `Doubled12k2_limit` at the recursion limit, and `S1_never_reads_fs` and `C2_never_reads_k1`, which say that a run of S1 or of C2 never reads a variable rooted at `k1`.

Supporting results: resolution is total (`resolveTm_isSome`), the side
conditions are decided (`tyWf?_iff`, `defsDistinct?_iff`, `tyStrengthen?_iff`),
and the machines agree with the step relations (`step?_sound`, `fcStep?_sound`).

## What it leaves out

- A derivation through a middle type the program does not write, as in E1, E3, E4 and B1.
- A merge of two members of one name. The version has no rule for it, so the typer tries each.
- A judgment whose search needs more than the fuel. LP, ascribed or through a written `let` type, LPw2 and the doubled alias chain of twelve links at `{k2}` end at the recursion limit. Scalac rejects LP at its cyclic members and stops on LPw2 at its own recursion limit.
- A lookup through a cyclic member, which is cut as the compiler's cyclic reference. So member premises are phrased through the lookup, and no inductive judgment of lookup comes with a completeness theorem: the cut can remove an answer that a different answer of the same key needed.
- A completeness theorem for the typer as a whole. E10, `λ(f : ⊤). λ(g : ⊤). f (g f)`, is rejected because `f` is not a function.
- A semantic statement for let insertion or box inference, and a safety theorem at an open context such as C5's.
- `any` in the outer set of a parameter type, and reach capabilities. The resolver rejects them. Scopes, levels and fresh capabilities are the `CapturesCC` version.

## Building

`lake build CapturesFrontend`. It is not a default target, so building the
metatheory does not wait on it. Every definition is structural, and
`#assert_no_wf` fails the build otherwise. Every theorem depends on `propext`
and `Quot.sound` at most. There is no `sorry`, `axiom`, `native_decide` or Mathlib.
