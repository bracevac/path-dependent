# Classifiers front end

A way to write, type and run programs of `Classifiers`, a calculus of capture
checking with classifiers, without assembling derivations by hand. A
classifier labels a capability with the effect it grants, and classifiers form
a tree, as in `Control extends ThreadLocal`. A kind is a set of classifiers.
`{ctl, io}.only[Control]` keeps the capabilities classified `Control` or below.

A program is written inside `clsProg%`. Its header declares the classifiers,
the platform (the capabilities it is given), and optionally a use set (the
capabilities it may use) and a kind that this set must satisfy. The front end
resolves names, adds `let`s, finds a typing derivation, translates it to
FCdot, a DOT variant with coercions and a checker, and runs the program.

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

This is `Try.apply`. `f` filters its body to `Control`, so a run never reads
`io` (`CE1_reads_only_control`).

`compile b Λ p` types the program `p` at the fuel of `b : Budget`, by default
`defaultFuel = 2 ^ 15`, with label table `Λ`. The `Verdict` is `ok` with the
elaborated term, its use set, its type and the `DotMNF.HasTy` derivation (DOT in
monadic normal form), `rejected` with a `Reason` and its proof, or `unknown`,
which covers the recursion limit. A `Reason` is an `any` or `fresh` atom where
the calculus reads none, a level escape (a capability leaving its scope) or an
existential answer at the top. `compileKinded`, `compileFiltered` and
`compileAndRun` add a kinding, a filter proof and a run.

## Modules

| module | contents |
|---|---|
| `Surface` | the named syntax with kinds, filters and the program header |
| `Notation` | the notation `clsProg%`, `cls%`, `clsTy%` and the example programs |
| `Ann` | DOT-MNF terms with the annotations the typer needs |
| `Resolve` | name resolution, classifiers, platforms and let insertion |
| `Decide` | decision procedures for the side conditions |
| `Search` | the first type of a variable and the proof behind a level escape |
| `Look` | member lookup on demand and the default fuel |
| `Sub` | subtyping, subcapturing and kinding in the compiler's case order |
| `Alg` | the algorithmic judgment, completeness and soundness |
| `Kind` | the kinding goal checked at the examples of the calculus |
| `Avoid` | avoidance at a `let` and at an unpacking |
| `Adapt` | box adaptation at a variable |
| `Typer` | the typer and its entry points `synthTop?` and `synthIn?` |
| `Step` | the DOT-MNF machine and its driver `run` |
| `StepFC` | the FCdot machine and its driver `fcRun` |
| `Pipeline` | `compile`, its variants and the pipeline theorems |
| `Pretty` | printers back to the notation |
| `Examples` | the programs taken end to end, each with its verdict in the kernel |

## The typer

The typer follows the subtype checker of the Scala 3 compiler, pinned as
scala/scala3 at commit 4dae25087d: the case order of `TypeComparer`
(core/TypeComparer.scala), `CaptureSet.subCaptures`, and `transClassifiers` and
`isKnownClassifiedAs` (cc/Capability.scala) for kinds. A `let` avoids its binder
as `TypeOps.avoid` does, replacing a type that mentions the bound variable. The
typer computes the least use set the rules allow, and a declared use set binds.

The whole typing runs on one fuel tank, a counter of work. When the tank runs
short, the typer reports a recursion limit, never a rejection. `Alg` states its
algorithm as rules without fuel. Up to that limit its goals are complete with
respect to `Alg`. As scalac does, it rejects E1, E3 and E4 of `Examples`, which
need a middle type (an intermediate type of a subtyping chain) that the program
omits. What the programmer writes binds. E1s and E3s write it and compile.

## Main theorems

- `compile_checks`, `compile_uses_checks`, `compile_checks_get`: the FCdot checker accepts the translated derivation and its use set. `compile_erase`, `compile_faithful`: the translation erases to the compiled term, which is the written one up to what the typer adds.
- `compile_safe`, `compile_not_stuck`, `compile_run_progress`: a run of a compiled program never gets stuck. `compile_capture_prediction`, `compile_effect_safety`: a run uses no more than the use set, and never reads a capability outside a use set with no filter.
- `compile_lvl_safety`, `compile_rejected_goal`: a subcapturing of the derivation that reads no capture member keeps capabilities in their scopes, and a rejection for a level escape proves that no such subcapturing reaches its goal.
- `compile_kind_checks`, `compile_classified_effect_safety`, `compile_filtered_effect_safety`: after `compileKinded` or `compileFiltered` at a kind `φ`, the FCdot checker accepts the kinding, and a run reads only capabilities whose classifier `φ` admits.
- `shp?_complete`, `cap?_complete`, `kind?_complete`, `esub?_complete`, `sub?_complete`, `var?_complete`: a goal `Alg` derives is answered when the tank did not run short.
- `shp?_reject`, `cap?_reject`, `kind?_reject`, `esub?_reject`, `sub?_reject`, `var?_reject`: a rejection when the tank did not run short means `Alg` derives no such goal. `Alg.sound`: a goal `Alg` derives has a derivation of the calculus.
- `sub?_mono`, `kind?_stable`, `synthTop?_mono`, `synthTop?_stable`: an answer, or a rejection when the tank did not run short, stays the same at more fuel.
- In `Examples`: a type, a compile and a checker verdict for each accepted program, a rejection at every budget for each rejected one, and the recursion limit for `LP_limit`, `PF_limit` and `LQ2_limit`.

## What it leaves out

- A derivation through a middle type the program does not write, and a merge of two members of one name. The calculus has no rule for the merge, so the typer tries each member.
- A judgment whose search needs more than the fuel, such as Pierce's divergence of F<:.
- A lookup through a cyclic member, cut as the compiler cuts a cyclic reference.
- A completeness theorem for the typer as a whole, and a safety theorem at a context other than the platform's.
- `fresh` under a filter and in a lambda domain, and a kind built from `only` and `except` together, which may print as `name \ {names}`, a form the notation does not parse.

## Building

`lake build ClassifiersFrontend`, which is not a default target.
`#assert_no_wf` checks that every definition is structural. Every theorem
depends on `propext` and `Quot.sound` at most, with no `sorry`, `axiom`,
`native_decide` or Mathlib.
