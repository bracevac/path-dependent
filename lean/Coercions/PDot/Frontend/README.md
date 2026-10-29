# pDOT front end

A way to write, type and run pDOT programs without building derivations by
hand. A program is written in the paper's notation under `pdt%`. The front end
resolves names, fills the annotations the program leaves out, and searches for
a derivation of `PDot.Source.HasTy`. It checks the translation of that
derivation in FCp and runs it on the source machine or the FCp machine. Paths
stay paths: `h x.a.b` applies `h` to the path `x.a.b`, and no `let` is
inserted. The front end imports the `PDot` library, changes nothing in it, and
proves nothing new about the calculus.

```lean
def E9l_src : STm := pdt% λ(x : μ(z. {a : z.type} ∧ {b : ⊤})). let r : x.b.type = x.a.b in r
```

E9l compiles at `∀(x : μ(z. {a : z.type} ∧ {b : ⊤})) x.b.type`, by
`ty_path_elim`. The paths front end rejects it. The programs named here, such
as E9l, R7 and E7w, are in `Examples`. E1 to E8 and E13 are the programs of
`PDot/Source`, which `Sources` writes in the notation.

`compile b Λ e` resolves `e` at the label table `Λ`, which maps member names to
labels. The budget `b` holds the fuel, by default `defaultFuel = 2 ^ 15`, the
mode, `.dot` by default, and the module paths the Scala mode keeps. The result
is `none` if `e` is out of scope, uses a name missing from `Λ`, has a field of
a shape pDOT lacks, is rejected, or ends at the recursion limit. Otherwise it is the filled term with its type and
the annotated derivation `AHasTy`, whose erasure `Compiled.deriv` is the pDOT
derivation. `compileE` returns the reason of a rejection and `ppReasonWith`
prints it. `compileAndRun` runs the source machine and `compileAndRunFC` the
FCp machine. The Scala mode is for the Scala reader. At a `let` without a
written type it widens a singleton to the first view that is no singleton, as
scalac does at a `val`, and keeps the singleton of a module path.

`ScalaRead/` is the reader of the pDOT Scala subset, stage XS1a of plan XI. It
reads a `.scala` file into a tree of its own on the lexer of `ScalaSyntax`,
checks scopes and the kind table of paths, and prints a tree back as text. It
builds as the library `PDotScalaRead` until a later stage maps its tree into
`pdt%`'s surface syntax. Its root `ScalaRead.lean` describes its modules.

The library is `PDotFrontend`, built by `lake build PDotFrontend`. It is not a
default target, so the metatheory build does not wait on it. Every definition
is structural or fuelled, and the root ends with `#assert_no_wf PDotFrontend`.
Theorems depend on `propext` and `Quot.sound` at most. There is no `sorry`,
`axiom`, `native_decide`, `partial`, `unsafe`, `implemented_by`, `aesop` or
Mathlib.

## What the programmer may leave out

Three slots. The domain of a lambda: `λx. t` is enough where a goal has a
function part, or where the body is `g x` with `g` known. The self type of a
literal: `ν(x) {d₁, …, dₙ}` has its self type formed from its definitions, in
definition order. The declared type of a lambda field: `a = λ(u : ⊤). u` takes
the least of its candidate types, found in rounds. A path field and a nested
literal need no annotation, since `ty_def_path` and `ty_def_new` fix their
declarations. A path field may carry its singleton, as in
`m : c.types.type = c.types`, which is checked and dropped. A goal comes from a
written `let` type, an ascription, the domain of a callee, a field's written
declaration, a lambda body, or the body of a checked `let`. A program that
writes every slot is typed as written (`compile_full`).

A program with an empty slot can be rejected with "Missing parameter type",
"Recursive value a needs type", or "The types of a have no least one". Only a
program with an empty slot gets these three (`compileE_slot`).

## What the typer leaves out

A pDOT-typable program that the typer does not type has no derivation that
keeps to the typer's alternatives. The ways out, with a program where one is
known:

- L1. `subtyp_trans` through a middle type that is no bound read off a view, no
  operand of `∧`, no replacement step and no view. Program: under
  `x : {A : ⊤..⊥}`, `(y: Any) => (y: Nothing)` without the middle `x.A`
  written. scalac rejects it too.
- L2. `ty_rcd_intro`, `ty_rec_intro` or `ty_and_intro` used to build a view
  rather than to meet a goal of that shape.
- L3. `ty_sub` of a term that is not a path, to a type other than its check
  goal.
- L4. A `let` without a type at a type other than the first or widened
  candidate, or a body type the avoidance rules do not reach. Program:
  `λ(q : ⊤). λ(p : q.type). let y = p in (y : q.type)`.
- L5. Replacement at a place the replacement search does not walk.
- L6. Lambda fields without types that read each other in a cycle, which is
  scalac's cyclic reference.
- L7. A member of `⊥`: `λ(x : ⊥). x.a`.
- L8. A derivation past the fuel, or one that repeats a goal along a branch.
- L9. Two nested literals that select each other's members, each with a field
  type to infer, wait for each other and are rejected with a cyclic reference.
  scalac completes members one at a time and accepts them. Program: `Cross_src`
  of `Pipeline.lean`.

Not a gap: the reflexive singleton `p : p.type` has no pDOT derivation
(`PDot/Source/Examples.lean:525`), and the typer rejects N4 at it. In the Scala
mode the typer is stricter than pDOT on purpose, in its widening and in the
`let` of an unstable prefix.

## The theorems

Each takes a compile `h : compile b Λ e = some ⟨a, c⟩`, `compile_checks_get`
only `(compile b Λ e).isSome = true`, and restates a theorem of the `PDot`
library at the compiled program.

- `compile_checks`, `compile_checks_get`: the FCp checker accepts the translation of the derivation at the translated type.
- `compile_erase`: the translation erases to the erasure of the fill.
- `compile_safe`: in every configuration that the fill reaches from the empty store, the term is a normal form or the configuration steps, and a path in focus has a safe lookup (`PDot.safety`).
- `compile_reachable`: the erasure of every such configuration is the erasure of an FCp state typed at the translated type, and every typing of that state's store proves no `⊤ ≤ ⊥` (`PDot.reachable_typed`).
- `compile_lockstep`: the FCp machine runs the translation to a state with that erasure (`PDot.reachable_run`).
- `compile_run_progress`, `compileAndRun_progress`: the source driver stops at a normal form or at a configuration that steps.
- `compileAndRunFC_reaches`, `compileAndRunFC_typed`, `compileAndRunFC_consistent`: the FCp driver's state is reached by steps of the machine, typed, and over a store that proves no `⊤ ≤ ⊥`.

The front end's own theorems.

- `resolveTm_isSome`: resolution succeeds on a program that is scoped, has its member names in the table, and has fields of the allowed shapes. `resolve_noInsert`: with every operand a path, resolution inserts no `let`.
- `compile_full`: a program with every slot written compiles as `compileLanded` types its resolution.
- `compileE_fills`: a fill agrees with every slot the program writes. `compileE_slot`: a reason that names a slot comes only from a program with an empty slot.
- `elabTop?_stable`: an elaboration that ends with the tank unmarked gives the same verdict at more fuel. `elabTop?_mono`: an accepted program stays accepted at more fuel.
- In `Pipeline`: `Ek_checks` for E1 to E8 and E13 with every slot written, `Ek_fill` with the slots a goal or the definitions give erased, `N1_rejected` to `N3_rejected` and `N4_reason`.
- In `Examples`: `X_checks` for the paths programs R2, PQ, R7, E7w and E9l, and for E10 and E11 as programs. `Ek_run` for E5, E7 and E8, the run of `PDot/Translation/Pages.lean` in 4, 2 and 9 steps, `Ek_fc_end`, the FCp machine at a final state with the erasure of the page's end, in 9, 7 and 24 steps, and `Ek_same`, the two runs at one erasure.

## Modules

| module | contents |
|---|---|
| `Surface`, `Notation` | the surface tree, the label table, the side conditions `Scoped`, `LabelsIn`, `FieldsOk` and `PathOperands`, and the entry points `pdtTy%`, `pdt%` and `pdtDefs%` |
| `Ann`, `Resolve` | annotated terms `ATm`, partial terms `PTm`, and name resolution with its totality |
| `Sources` | E1 to E8, E13 and N1 to N3 in the notation, each resolved to its hand term, and the contexts of E9 to E11 |
| `Decide`, `Look` | the decided side conditions, `defaultFuel`, and the views V1 to V7 of a path |
| `Sub` | path goals G1 to G6 and subtyping S1 to S9, with replacement |
| `Judgment`, `Avoid` | the annotated judgment `AHasTy` with its erasure, and avoidance at a `let` |
| `Typer`, `Elab` | the typer with its modes, and the elaborator that fills the three slots |
| `Pipeline` | `compileE`, `compile`, `checkAt`, `compileLanded`, the two drivers, the theorems, and the checks of E1 to E8, E13 and N1 to N4 |
| `Pretty` | printers of surface, partial, annotated and source terms, types, reasons and runs |
| `Examples` | the paths programs compiled, E10 and E11 as programs, and the runs of E5, E7 and E8 on both machines |
