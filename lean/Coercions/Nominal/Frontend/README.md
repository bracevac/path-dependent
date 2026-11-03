# pDOT-C front end

A way to write, type and run pDOT-C programs, pDOT with classes, without
building derivations by hand. A program is written in the paper's notation
under `pdc%`. The front end
resolves names, fills the annotations the program leaves out, and searches for
a derivation of `Nominal.Source.HasTy`. It checks the translation of that
derivation in FCn and runs it on the source machine or the FCn machine. Paths
stay paths: `h x.a.b` applies `h` to the path `x.a.b`, and no `let` is
inserted. The front end imports the `Nominal` library and changes nothing in it. Its
own theorems about the calculus are plan XII's nominality theorems, about the
derivations its search builds.

```lean
def E9l_src : STm := pdc% λ(x : μ(z. {a : z.type} ∧ {b : ⊤})). let r : x.b.type = x.a.b in r
```

E9l compiles at `∀(x : μ(z. {a : z.type} ∧ {b : ⊤})) x.b.type`, by
`ty_path_elim`. The paths front end rejects it. The programs named here, such
as E9l, R7 and E7w, are in `Examples`. E1 to E8 and E13 are the programs of
`Nominal/Source`, which `Sources` writes in the notation.

`compile b Λ e` resolves `e` at the label table `Λ`, which maps member names to
labels. The budget `b` holds the fuel, by default `defaultFuel = 2 ^ 15`, the
mode, `.dot` by default, and the module paths the Scala mode keeps. The result
is `none` if `e` is out of scope, uses a name missing from `Λ`, has a field of
a shape pDOT lacks, is rejected, or ends at the recursion limit. Otherwise it is the filled term with its type and
the annotated derivation `AHasTy`, whose erasure `Compiled.deriv` is the pDOT-C
derivation. `compileE` returns the reason of a rejection and `ppReasonWith`
prints it. `compileAndRun` runs the source machine and `compileAndRunFC` the
FCn machine. The Scala mode is for the Scala reader. At a `let` without a
written type it widens a singleton to the first view that is no singleton, as
scalac does at a `val`, and keeps the singleton of a module path.

`ScalaRead/` is the reader of the Scala subset with classes and traits, stage
XS1a of plan XI and N5 of plan XII. It
reads a `.scala` file into a tree of its own on the lexer of `ScalaSyntax`,
checks scopes and the kind table of paths, and prints a tree back as text. It
builds as the library `NominalScalaRead`, and its root `ScalaRead.lean` describes
its modules. The section "The Scala front end" says how its tree reaches the
typer.

The library is `NominalFrontend`, built by `lake build NominalFrontend`. It is not a
default target, so the metatheory build does not wait on it. Every definition
is structural or fuelled, and the root ends with `#assert_no_wf NominalFrontend`.
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

## Classes

Plan XII adds two forms. A definition `class C = T` declares the class `C` with the body `T`,
at `{C : ⊥..T}`, and its label joins the class labels of the run. A literal
`ν(x) as p.C {d₁, …, dₙ}` is an instance of `p.C`. It resolves to a `let` tagged `inst p C`
around the literal and an ascription to `p.C`, and the typer seals the instance at `p.C`
through the class reading of `p`. The elaborator reads every slot of a tagged literal off
its text, so its lambdas need written domains and its lambda fields written types. A field
whose lambda returns a tagged literal needs its declared type, as in
`mk : ∀(u : ⊤) s.C = λ(u : ⊤). ν(i) as s.C {a = u}`, since the candidate types of its
lambda have no least one. Resolution refuses a tag whose label is the label of no class
definition of the program. The running example of plan XII, a trait `T` and a class `C`
that extends it, is `Run_src` in `Examples`. It compiles at the body of `T`, checks in FCn,
runs on both machines to one erasure, and NOM-B holds at it. A structural literal at `σ.C`
is rejected, and so is an instance that lacks a field of its class body.

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
(`Nominal/Source/Examples.lean:529`), and the typer rejects N4 at it. In the Scala
mode the typer is stricter than pDOT on purpose, in its widening and in the
`let` of an unstable prefix.

## The theorems

Each takes a compile `h : compile b Λ e = some ⟨a, c⟩`, `compile_checks_get`
only `(compile b Λ e).isSome = true`, and restates a theorem of the `Nominal`
library at the compiled program.

- `compile_checks`, `compile_checks_get`: the FCn checker accepts the translation of the derivation at the translated type.
- `compile_erase`: the translation erases to the erasure of the fill.
- `compile_safe`: in every configuration that the fill reaches from the empty store, the term is a normal form or the configuration steps, and a path in focus has a safe lookup (`Nominal.safety`).
- `compile_reachable`: the erasure of every such configuration is the erasure of an FCn state typed at the translated type, and every typing of that state's store proves no `⊤ ≤ ⊥` (`Nominal.reachable_typed`).
- `compile_lockstep`: the FCn machine runs the translation to a state with that erasure (`Nominal.reachable_run`).
- `compile_run_progress`, `compileAndRun_progress`: the source driver stops at a normal form or at a configuration that steps.
- `compileAndRunFC_reaches`, `compileAndRunFC_typed`, `compileAndRunFC_consistent`: the FCn driver's state is reached by steps of the machine, typed, and over a store that proves no `⊤ ≤ ⊥`.

The front end's own theorems.

- `resolveTm_isSome`: resolution succeeds on a program that is scoped, has its member names in the table, and has fields of the allowed shapes. `resolve_noInsert`: with every operand a path, resolution inserts no `let`.
- `compile_full`: a program with every slot written compiles as `compileLanded` types its resolution.
- `compileE_fills`: a fill agrees with every slot the program writes. `compileE_slot`: a reason that names a slot comes only from a program with an empty slot.
- `elabTop?_stable`: an elaboration that ends with the tank unmarked gives the same verdict at more fuel. `elabTop?_mono`: an accepted program stays accepted at more fuel.
- In `Pipeline`: `Ek_checks` for E1 to E8 and E13 with every slot written, `Ek_fill` with the slots a goal or the definitions give erased, `N1_rejected` to `N3_rejected` and `N4_reason`.
- In `Examples`: `X_checks` for the paths programs R2, PQ, R7, E7w and E9l, and for E10 and E11 as programs. `Ek_run` for E5, E7 and E8, the run of `Nominal/Translation/Pages.lean` in 4, 2 and 9 steps, `Ek_fc_end`, the FCn machine at a final state with the erasure of the page's end, in 9, 7 and 24 steps, and `Ek_same`, the two runs at one erasure.

The nominality theorems of plan XII, in `Pipeline`. Here `C` is a class label of
the run, the label of a class definition.

- `sub?_nominal` (NOM-A): an answer of the search to `S <: p.C`, in any context, factors. `S` goes up through operands of `∧`, upper bounds read off views and alias replacements, and reaches `⊥` or `q.C` with `q` an alias of `p` (`Factor`).
- `path?_nominal`: an answer to `q : p.C` comes from a view of `q` that factors through `p.C`, or `q` is a tagged instance of a class below `C` (`SealAt`). `path?_structural`: a path whose views are all structural and that is no tagged variable has no answer at `p.C`.
- `compile_nominal_resolved` and `compile_nominal` (NOM-B): every step into a class type of a compiled derivation carries its certificate. `compile_seal_sites`: every seal of a compiled derivation is the last step of a path answer at a tagged variable.
- In `Examples`: `Run_src`, the running example of plan XII, compiles at the body of `T`, checks in FCn, and runs on both machines to one erasure.

## The Scala front end

A pDOT-C program can also be a `.scala` file. The reader of `ScalaRead/` parses
it and refuses a file outside the subset with a rule and a position. `Scala`
maps the reader's tree to the surface syntax of `pdc%`, one case per construct
of plan XI. The members of the wrapper object become the stem `σ`, a literal
that holds them. Every template gets the hidden field `ℓself`, declared at the
template's singleton (D-7). A term that names an object or `this` reads as its
`ℓself` field, so it has the object's singleton type, which pDOT gives no path
on its own (N4). The shortest unstable prefix of a term path is bound by a
`let` first (D-10). An application that is a lambda body or a block result is
bound by a `let` that widens, as scalac widens there (D-13). `readNominal` gives
the term, the label table and the module paths of a file.

`outcome` reads a file, compiles its term in the Scala mode with the file's
module paths, and runs the member check R-M on the result. It answers `ok` with
the compiled program, `rejected` with a reason, `limit`, or `outside` with the
refusal and its position. It never answers `unknown`. `outcome_ok` says that an
`ok` outcome is the compilation of the term `readNominal` gives, `outcome_checks`
that its derivation checks in FCn, and `outcome_safe` that its term is safe by
`Nominal.safety`. `toScala` prints a term as Scala, or says why it has no Scala
form. `fillToScala` prints a compiled program with every slot written, and
`roundTrip` prints a term and reads it back. `ScalaCmd` holds the commands
`nominal_scala_example` and `nominal_scala_corpus`. These modules build as the
library `NominalScala`, by `lake build NominalScala`.

Plan XII N6 maps classes and traits. A class or trait of the wrapper or of an
object becomes, in that template's literal, a class definition
`class K = Body(K)`, the module functions `f$K` and the `val` witnesses `a$K`
typed under the receiver `this : z.K`, the override witnesses whose obligations
do not hold by their form (with `ovc` for the pairwise consistency of a type
member inherited from two classes), and, for a concrete class, the constructor
`new$K`, whose body is the tagged literal `ν(i) as z.K {…}`. The literal holds
the members of the linearization in order: hidden fields `ℓx$D` of plain
parameters, `val` parameters at the arguments the parents pass, type members at
the first alias or the meet of the upper bounds, path `val`s, and forwarders
that call the implementer's module function at `i`. `new p.K(ē)` is
`let ·n = ⟦p⟧.new$K ē in ·n`. `ScalaClasses` holds Martres' implementer `mimpl`
(thesis p.74), the class of an effective member, the order of an instance's
members, the superclass of a class, and the checks, which `outcome` runs before
the typer and answers `rejected` with scalac's text: the shape of the parents
and the arity of `new` (E171, E104), OV-Need at a concrete member (E164),
OV-Nothing (E037), OV-Accidental (thesis p.75, E164, with scalac's two texts),
OV-Abstract and OV-New (E042). `ofScala_tags` says that the mapping writes a tag
only on a constructor's instance literal, and `scala_seal_sites` that an `ok`
outcome seals only at tagged variables, with the class order of each seal in the
certificate `Nom`. The printers give a class definition and a tagged literal the
gap `gapClass`.

The corpus is `scala/nominal/`, 115 files, which `scala/README.md` describes.
The module `Coercions.ScalaCorpus.Nominal` judges each file in the kernel from
its bytes when `lake build ScalaCorpusNominal` builds it. The harness
`scripts/scala/Agree.lean` compiles each file with scalac 3.8.4 and writes
`scala/nominal/TABLE.md`, and CI fails when that table changes.

The claim is plan IX's: outside `disagree/`, every corpus file that this front
end accepts, scalac 3.8.4 accepts. It is tested on these 115 files and not
proved. It holds for the pinned compiler only, and it compares verdicts, not
types. 50 files are agree-accept, 36 agree-reject and 26 outside. The
3 files of `disagree/` are the exceptions, each with its cause, and each is
ours-stricter. AndCall needs a rule from an intersection of method types to a
method of the intersection (And-Fun), FunStructParam a subtyping from a `μ` to
a record (Bind1), and ThisTypeOverride a subtyping that widens a singleton.
No file is ours-looser. N holds: each file that scalac
rejects fails exactly on its `// error` lines. A check of `ScalaClasses`
rejects 9 of the `neg` files with scalac's message, shortened for
OV-Abstract, and the typer the other 27. Every file of the corpus declares a
class or a trait, so no pos file has a fill. Of the 89 files the reader
takes, 87 round trips stop at the gap `gapClass`, and the harness admits them
by F-C. The round trips of AbstractNew and NewTrait do not resolve, since `new`
of a trait or an abstract class names a constructor that no class has, and F-C
admits them too, since a check rejects both files first. So R checks no printer
on this corpus. The same front end reads the 78 files of `scala/pdot/` at
their kinds there, except `outside/Tree.scala`, which it compiles.

## Modules

| module | contents |
|---|---|
| `Surface`, `Notation` | the surface tree, the label table, the side conditions `Scoped`, `LabelsIn`, `FieldsOk` and `PathOperands`, and the entry points `pdcTy%`, `pdc%` and `pdcDefs%`, with the class forms `class C = T` and `ν(x) as p.C {ds}` |
| `Ann`, `Resolve` | annotated terms `ATm`, partial terms `PTm`, and name resolution with its totality |
| `Sources` | E1 to E8, E13 and N1 to N3 in the notation, each resolved to its hand term, and the contexts of E9 to E11 |
| `Decide`, `Look` | the decided side conditions, `defaultFuel`, the views V1 to V7 of a path, and the certificates `NomSub`, `SealAt` and `NomPath` |
| `Sub` | path goals G1 to G6 and G7', the seal at a tagged instance, and subtyping S1 to S9, with replacement |
| `Judgment`, `Avoid` | the annotated judgment `AHasTy` with its erasure and the certificates `NomAt` and `SealsAt`, and avoidance at a `let` |
| `Typer`, `Elab` | the typer with its modes, and the elaborator that fills the three slots |
| `Pipeline` | `compileE`, `compile`, `checkAt`, `compileLanded`, the two drivers, the theorems, the nominality theorems NOM-A and NOM-B, and the checks of E1 to E8, E13 and N1 to N4 |
| `Pretty` | printers of surface, partial, annotated and source terms, types, reasons and runs |
| `Examples` | the paths programs compiled, E10 and E11 as programs, the runs of E5, E7 and E8 on both machines, and the running example `Run_src` of plan XII |
| `ScalaClasses` | the implementer `mimpl`, the effective member, the members of an instance, the superclass, and the checks of the classes and of `new` |
| `Scala` | the mapping from the reader's tree to `STm` with classes and traits, `readNominal`, `outcome` with the checks of `ScalaClasses`, the member check R-M and its three theorems, `ofScala_tags`, `scala_seal_sites`, the printers `toScala` and `fillToScala`, and `roundTrip` |
| `ScalaTests` | checks of the mapping, the outcomes, the member check, the printers and the round trips, by `#eval expect` |
| `ScalaCmd` | the commands `nominal_scala_example` and `nominal_scala_corpus` |
