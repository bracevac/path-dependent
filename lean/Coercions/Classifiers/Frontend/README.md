# Classifiers front end

A way to write, type and run programs of `Classifiers`, capture checking the
way Scala 3 does it with classifiers, without assembling derivations by hand. A
capability may be declared at a classifier such as `Control`, and a capture set
filtered by a kind, as in `{ctl, io}.only[Control]`. A program is written in the
paper's notation inside `clsProg%`. Its header declares classifiers, the
platform of capabilities the program is given, and optionally a use set and a
kind. The front end resolves names, inserts `let`s, finds a typing derivation
with its use set, translates it to FCdot and runs the program. It proves
nothing new and changes nothing in the version.

```lean
def CE1src : SProg :=
  clsProg% classifiers IO, ThreadLocal, Control extends ThreadLocal
    platform [ctl : Control, io : IO]
    uses {ctl, io}.only[Control]
    kind only[Control]
    let b = ((λ(u : ⊤ ^ {}). u) : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}.only[Control]) in
    let f = ((λ(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io}).
                ν(z : {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}. {body = λ(u : ⊤ ^ {}). u})) :
              (∀(body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {ctl, io})
                μ(z. {body : (∀(u : ⊤ ^ {}) ⊤ ^ {}) ^ {z}}) ^ {body.only[Control]}) ^ {}) in
    let r = f b in
    r
```

This is `Try.apply`. `f` returns its body filtered to `Control`, so a run never
reads `io` (`CE1_reads_only_control`).

`compile b Λ p` resolves the program and types it at the fuel of `b : Budget`,
by default `defaultFuel = 2 ^ 15`. Its `Verdict` is `ok` with the elaborated
term, its use set, its type and the `DotMNF.HasTy` derivation, `rejected` with
a `Reason` and its proof, or `unknown`, which covers the recursion limit.
`compileKinded` adds a kinding of the use set, `compileFiltered` the proof that
it is filtered, and `compileAndRun` the machine.

## Modules

| module | contents |
|---|---|
| `Surface` | the named syntax, with kinds, filters and the program header, and the `LabelTable` |
| `Notation` | the entry points `clsTy%`, `cls%`, `clsProg%` and the others, and the example programs |
| `Ann` | DOT-MNF terms with the annotations the typer needs, their erasure and their skeleton |
| `Resolve` | name resolution, classifier tables, platforms and let insertion |
| `Decide` | decision procedures for the side conditions |
| `Search` | the first view of a variable (`varView`) and the certificate lemma `escape_rejected_at` |
| `Look` | `cost`, `defaultFuel`, and member lookup on demand (`look`, `members`, `typs`, `caps`, `capks`), on the tank of `../../Frontend/Fuel.lean` |
| `Sub` | the algorithm in the compiler's case order, its five goals and their entry points (`shp?`, `cap?`, `kind?`, `esub?`, `var?`, `sub?`) |
| `Alg` | the algorithmic judgment `Alg`, completeness up to the recursion limit, and `Alg.sound` |
| `Kind` | the kinding goal checked at the version's examples |
| `Avoid` | avoidance at a `let` and at an unpacking (`up`, `down`, `capUp`, `capDown`, `avoidLet`, `avoidUses`, `avoidEx`) |
| `Adapt` | the result types of the typer and box adaptation at a variable (`adaptVarF`) |
| `Typer` | `Budget`, `Verdict`, `Reason`, `inferF`, the object fixpoint `objFixF` and the entry points `synthTop?` and `synthIn?` |
| `Step`, `StepFC` | the DOT-MNF machine `step?` and the FCdot machine `fcStep?`, with the drivers `run` and `fcRun` |
| `Pipeline` | `compile` and its variants, the log `levelSteps` and the pipeline theorems |
| `Pretty` | printers back to the paper's notation, no theorems |
| `Examples` | the programs taken end to end, each with its verdict in the kernel |

## The typer

The typer follows the Scala 3 compiler's subtype checker, `TypeComparer`, in
its case order, its subcapturing, `subCaptures` and `subsumes`, and its levels,
`acceptsLevelOf`, and takes no middle type from the context. Kinds are searched
by the same algorithm, as a goal beside subtyping and subcapturing, following
the compiler's `transClassifiers` and `isKnownClassifiedAs`. It runs on one
fuel tank for the whole typing and reports a recursion limit when the tank runs
short, which is never a rejection by the rules. It is complete up to that limit
with respect to its algorithmic judgment `Alg`. It rejects E1, E3, E4, B1, A1,
and CE4 at a member bounded by an unrelated classifier, as scalac does, and E1s
and E3s, which write the middle type, compile.

The algorithm has five goals: `shp` on shapes, `cap` on capture sets, `kind` on
a set and a kind, `esub` on answers, and `var`, which keeps a variable while it
widens it. `Sub.lean` lists where the version's rules force a route other than
the compiler's. The typer returns the `DotMNF.HasTy` derivation, and each
kinding its `DotMNF.CapKind`, so it is sound by construction. It finds the least
use set the rules allow. Synthesis returns candidates: an application tries
every function type the lookup finds, and a projection returns every field. A
`let` without a written type approximates the body's type and use set by ones
free of the binder, as the compiler's `avoid` does, and keeps each restriction.
At a variable checked against a goal, the typer boxes or unboxes by the box
status of the two types, as the compiler's `adaptBoxed` does. The capture set
of an object literal is a least fixpoint, grown by the atoms its definitions
use that the set does not account for. Its passes are bounded by `objBound`, a
size of the program not proved to suffice, and a pass that reaches it marks
the tank.

A written type and a declared use set bind. When the typer cannot meet one, it
looks for a reason with a proof: a misplaced `any` or `fresh`, a level escape,
or an existential answer at the top.

## Main theorems

- `compile_checks`, `compile_uses_checks`, `compile_checks_get`, `compile_erase`, `compile_faithful`: the FCdot checker accepts the translation, which erases to the compiled term, whose skeleton is the resolved one.
- `compile_safe`, `compile_not_stuck`, `compile_run_progress`: every reachable state is final or can step.
- `compile_capture_prediction`, `compile_effect_safety`: a run uses no more than the use set, and never reads a capability outside a use set with no filter.
- `compile_lvl_safety`, `compile_rejected_goal`: no member-free subcapturing of the derivation leaves a scope, and an escape names a goal no such subcapturing proves.
- `compile_kind_checks`, `compile_classified_effect_safety`, `compile_filtered_effect_safety`: after `compileKinded` or `compileFiltered` at `φ`, the kinding checks and a run reads only capabilities whose classifier `φ` admits.
- `shp?_complete`, `cap?_complete`, `kind?_complete`, `esub?_complete`, `sub?_complete`, `var?_complete`: a goal `Alg` derives is answered at every fuel at which the run ends with the tank unmarked.
- `shp?_reject`, `cap?_reject`, `kind?_reject`, `esub?_reject`, `sub?_reject`, `var?_reject`: a rejection with the tank unmarked means `Alg` derives no such goal.
- `Alg.sound`, with `Alg.sound_shp`, `Alg.sound_cap`, `Alg.sound_kind`, `Alg.sound_esub`, `Alg.sound_var`: a goal `Alg` derives has a derivation of the version.
- `shp?_mono`, `cap?_mono`, `kind?_mono`, `esub?_mono`, `sub?_mono`, `var?_mono`, `kind?_stable`, `synthTop?_mono`, `synthTop?_stable`: an answer, or a rejection with the tank unmarked, stays the same at more fuel.
- `avoidLet_strengthen`, `avoidUses_strengthen`, `avoidEx_strengthen`: where the body's type or use set strengthens past the binder, avoidance returns it.
- `objFix_progress`: a pass of the object fixpoint that goes on adds an atom the set does not account for, or other definitions.
- In `Examples`: `Ek_type`, `Ek_compiles` and `Ek_checks` for each accepted program, `Ek_verdict` and `Ek_rejected` for each rejected one with `Ek_not_alg` where it fails at one core goal, `LP_limit`, `PF_limit` and `LQ2_limit` at the recursion limit, and `CE1_reads_only_control`, `CE2_no_thread_local`, `CE3_reads_only_control` for the classified runs.

## What it leaves out

- A derivation through a middle type the program does not write, as in E1, E3, E4 and B1.
- A merge of two members of one name. The version has no rule for it, so the typer tries each, at a cost the tank bounds.
- A judgment whose search needs more than the fuel. LP, Pierce's divergence PF and LQ2 end at the recursion limit.
- A lookup through a cyclic member, cut as the compiler's cyclic reference. So member premises are phrased through the lookup, with no completeness theorem for it.
- A completeness theorem for the typer as a whole. A rejection with a reason is about the goal the typer reached.
- A semantic statement for let insertion or box inference, and a safety theorem at an open context.
- `fresh` under a filter and in a lambda domain. A kind built as an `only` minus an exclusion prints in a form the notation does not parse.

## Building

`lake build ClassifiersFrontend`, which is not a default target.
`#assert_no_wf` checks that every definition is structural. Every theorem depends
on `propext` and `Quot.sound` at most, with no `sorry`, `axiom`, `native_decide`
or Mathlib.
