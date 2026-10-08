# Classifiers front end

A way to write, type and run programs of `Classifiers` without assembling
derivations by hand. `Classifiers` is capture checking the way Scala 3 does it,
with classifiers. A capability may be declared at a classifier such as `Control`.
A capture set, the set of capabilities a type may hold, may be filtered by a
kind, as in `{ctl, io}.only[Control]`. A program is written in the paper's
notation inside `clsProg%`. Its header declares classifiers, the platform (the
capabilities the program is given, each at a classifier), and optionally a use
set, the capabilities the program may use, and a kind. The front end resolves
names, inserts `let`s to reach monadic normal form (DOT-MNF), finds a typing
derivation, translates it to FCdot, the target calculus, and runs it. It proves
nothing new and imports `../Cls`, `../DotMNF`, `../FCdot` and `../DotToFCdot`
without changing them.

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

This is `Try.apply`. A type `S ^ C` is `S` holding the capture set `C`. `f`
takes a body that may use `ctl` and `io` and returns an object holding the body,
filtered to `Control`. So a run never reads `io` (`CE1_reads_only_control`).

`compile` takes a search `Budget`, a table of field labels and a program. Its verdict is
`ok` with the elaborated term, its use set, its type and its `DotMNF.HasTy`
derivation, `rejected` with a reason and its proof, or `unknown`. `compileKinded`
adds a kinding of the use set, `compileFiltered` the proof that it is filtered,
and `compileAndRun` the machine at a step budget.

Beyond the vanilla front end in `../../Frontend`, this one computes the use set.
It inserts the boxes and unboxings a program leaves out, as the `Captures` front
end does. It orders scopes by level and rejects a capability that escapes its
scope, as the `CapturesCC` front end does. A program may write `any` for the
root of its scope and `fresh` for a new capability. It also kinds the use set,
to show which classifiers a run may read.

## Modules

| module | contents |
|---|---|
| `Surface` | the named syntax, with kinds, filters and the program header |
| `Notation` | the entry points `clsTy%`, `cls%`, `clsProg%` and the others, and the example programs |
| `Ann` | DOT-MNF terms with the annotations the typer needs, their erasure and their skeleton, the term without annotations, capture sets and boxes |
| `Resolve` | name resolution, classifier tables, platforms and let insertion |
| `Decide` | decision procedures for the side conditions |
| `Kind` | the kinding search `kind?` |
| `Search` | the `Budget` and the searches for subcapturing and subtyping |
| `Adapt` | box inference at a variable |
| `Typer` | the typer `synth?` and `check?`, and the rejections with their certificates |
| `Step`, `StepFC` | the DOT-MNF machine `step?` and the FCdot machine `fcStep?`, with the drivers `run` and `fcRun` |
| `Pipeline` | `compile` and its variants, and the pipeline theorems |
| `Pretty` | printers back to the paper's notation, no theorems |
| `Examples` | the capture programs and the classifier programs, the rejections and the effect theorems |

## The typer

The typer is sound by construction. Every result carries its `DotMNF.HasTy`
derivation, and every kinding its `DotMNF.CapKind` derivation. So there is no
soundness theorem to state. The typer is incomplete, since DOT subtyping is
undecidable. It runs on a `Budget` of fuel counters. More fuel for the typer or
the kinding search never loses a success.

It finds the least use set the rules allow. A declared use set is binding, and
`compile` searches for a subcapturing from the found set to it. The kinding
search reads classifiers off the platform, filter kinds off the set and member
bounds off declarations. A rejection is `levelEscape`, a capability that escapes
its scope, `anyNotOk` or `freshNotOk`, a type that uses `any` or `fresh` where
they have no reading, or `existentialAtTop`, an answer outside every scope that
must be a plain type.

The programmer writes the header, the domain type of each lambda and the self
type of each object literal. A `let` may carry its result type, and an
ascription `(t : T)` names the type of a bound term.

## Main theorems

The pipeline theorems take a successful `compile` over the platform.

- `compile_checks`, `compile_uses_checks`: the FCdot type checker accepts the translated derivation and the evidence for the use set.
- `compile_erase`, `compile_faithful`: the translation erases to the compiled term, which has the skeleton of the written one.
- `compile_safe`, `compile_not_stuck`: every reachable state is final or can step.
- `compile_capture_prediction`: a run uses no more than the use set.
- `compile_effect_safety`: a run never reads a variable rooted at a capability the use set does not contain, when the use set has no filter. A filter must be excluded, since `{ctl}.only[Control]` does not contain `ctl` and still reaches it.
- `compile_lvl_safety`: in each subcapturing of the derivation that goes through no capture member (a capture set declared in an object type), a scope root that confines the upper set confines the lower set. A root confines a set when no capability of the set lives in a scope strictly inside it.
- `compile_rejected_goal`: a program rejected for an escape names a goal that no such subcapturing proves.
- `compile_kind_checks`: after `compileKinded`, the FCdot checker accepts the translated kinding.
- `compile_classified_effect_safety`, `compile_filtered_effect_safety`: after `compileKinded` or `compileFiltered` at `φ`, a run reads only capabilities whose classifier `φ` admits.

On the examples:

- `E1_checks` to `E8_checks`, `CE1_checks` to `CE4_checks` and the others: the checker accepts each translation.
- `CE1_reads_only_control`, `CE3_reads_only_control`, `CE2_no_thread_local`: a run reads only `Control` capabilities, or no thread-local one.
- `Esc_rejected'`, `top_escape_rejected`, `W5_escape_rejected`: the certificates of three escapes.

## What it leaves out

- No completeness theorem for the typer or the kinding search.
- No semantic statement for let insertion or box inference. The skeleton relates the written and the elaborated term.
- No proof that a program the typer does not compile has no derivation. `Future.apply` with a thread-local body is not compiled. The `Classifiers` examples prove that the thread-local capability has no kinding at `except[ThreadLocal]`.
- No safety theorem at an open context.
- No `fresh` under a filter and no `fresh` in a lambda domain.
- A kind built as an `only` minus an exclusion prints in a form the notation does not parse.

## Building

`lake build ClassifiersFrontend`, which is not a default target.
`#assert_no_wf` checks that every definition is structural. Every theorem depends
on `propext` and `Quot.sound` at most, with no `sorry`, `axiom`, `native_decide`
or Mathlib.
