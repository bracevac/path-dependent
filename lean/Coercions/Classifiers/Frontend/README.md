# Classifiers front end

A way to write, type and run programs of `Classifiers`, a calculus of capture
checking with classifiers, without assembling derivations by hand. A
classifier labels a capability with the effect it grants, and classifiers form
a tree, as in `Control extends ThreadLocal`. A kind is a set of classifiers.
`{ctl, io}.only[Control]` keeps the capabilities classified `Control` or below.

A program is written inside `clsProg%`. Its header declares the classifiers,
the platform (the capabilities it is given), and optionally a use set (the
capabilities it may use) and a kind that this set must satisfy. The front end
resolves names, adds `let`s, fills the annotations the program leaves out,
finds a typing derivation, translates it to FCdot, a DOT variant with
coercions and a checker, and runs the program. A program whose capability
escapes its scope is rejected with a proof.

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

This is `Try.apply`. `f` filters its body to `Control`. `CE1_reads_only_control`
says that every root of a variable a run reads carries a classifier
`only[Control]` admits. In this program the run reads only `f`, which is
declared at the empty capture set, so the theorem holds trivially here. The
program never calls `r.body`, so the run does not exercise the filter.

`CE1bSrc` in `Examples` calls the filtered closure: `let b = λu.u` at
`{ctl, io}.only[Control]`, `let t = λu.u` at `{}`, then `let r = b t in r`.
After five steps the run reads `b` (`CE1b_reads_b`), which is declared at the two
atoms of the filtered set (`CE1b_declared`), whose base names `io`.
`CE1b_reads_only_control` says that along any run of the filtered compile of
CE1b, every root of a variable the reached state reads, in the matched FCdot
state, carries a classifier `only[Control]` admits.

`compile b Λ p` types the program `p` at the fuel of `b : Budget`, by default
`defaultFuel = 2 ^ 15`, with label table `Λ`. The `Verdict` is `ok` with the
filled body, the elaborated term, its use set, its type and the
`DotMNF.HasTy` derivation (DOT in monadic normal form), `rejected` with a
`Reason` and its proof, or `unknown`, which covers the recursion limit. A
`Reason` is an `any` or `fresh` atom where the calculus reads none, a level
escape or an existential answer at the top.
`compileE` returns the reason of every rejection and `ppReason` prints it.
`compileKinded`, `compileFiltered` and `compileAndRun` add a kinding, a filter
proof and a run.

## What the programmer may leave out

The domain of a lambda, the self shape of an object literal and the type of a
field, but not the header: `Try.apply` above compiles with `f (λu. u)` for its
last line (`CE1argSrcD`), and a program that writes every domain and self shape
is typed as it is, at the same fuel.

## Where an expected type comes from

The elaborator passes a goal down: the written type of a `let`, the type of an
ascription, the dominant formal of the callee at a call argument (the
parameter type that the others of an intersection of functions lie below),
the declaration of a field in the self shape, and the `μ` goal of a literal,
all found through aliases. A lambda takes its domain from the function part of
its goal, or from `g` when its body is `g x`. A literal with no `μ` goal forms
its self shape from its fields. If the attempt at a goal fails, the typer's own
route runs.

## The compiler's errors

A lambda with no domain and no goal is rejected with "Missing parameter type",
fields that read each other without written types with "Recursive value a needs
type", a field whose type holds a root capability the self shape cannot state
with "Value a needs a written type", and candidates with no least type with
"The types of a have no least one" (`compileE_slot`, for a program with an empty
slot). The others are a type mismatch, a level escape with its proof, and the
recursion limit. A body whose use set the kind does not admit, as `Future.apply`
with a thread-local body, has no reason of its own: the kinding search finds no
derivation and the verdict is `unknown`, printed "Type mismatch".

## Modules

| module | contents |
|---|---|
| `Surface`, `Notation`, `Ann`, `Resolve` | the surface syntax with kinds, filters and the program header, the notations `clsProg%`, `cls%` and `clsTy%`, terms with annotations and partial terms, name resolution, classifiers, platforms and `let` insertion |
| `Decide`, `Search`, `Look` | decision procedures, the first type of a variable, the proof behind a level escape, the fuel and member lookup |
| `Sub`, `Kind`, `Alg` | subtyping, subcapturing and kinding in the compiler's case order, the kinding goal at the examples of the calculus, the judgment `Alg`, its completeness and soundness |
| `Avoid`, `Adapt`, `Typer` | avoidance, box adaptation, the typer and its entry points `synthTop?` and `synthIn?` |
| `Elab`, `Step`, `StepFC` | the elaborator that fills the empty slots of a partial term, the DOT-MNF and FCdot machines as functions |
| `Pipeline` | `compileE`, `compile`, its variants, the pipeline theorems and completeness at the direct sites |
| `Pretty`, `Examples` | printers back to the notation, and the programs end to end, written and with annotations erased, each verdict checked in the kernel |

## The typer

The typer follows the subtype checker of the Scala 3 compiler, pinned as
scala/scala3 at commit 4dae25087d: the case order of `TypeComparer`
(core/TypeComparer.scala), `CaptureSet.subCaptures`, and `transClassifiers` and
`isKnownClassifiedAs` (cc/Capability.scala) for kinds. A `let` avoids its binder
as `TypeOps.avoid` does, replacing a type that mentions the bound variable. The
typer computes the least use set the rules allow, and a declared use set binds.

The whole typing runs on one fuel tank, a counter of work, the elaborator's
included. When the tank runs short, the typer reports a recursion limit, never
a rejection. `Alg` states its algorithm as rules without fuel. Up to that limit
its goals are complete with respect to `Alg`. As scalac does, it rejects E1, E3
and E4 of `Examples`, which need a middle type (an intermediate type of a
subtyping chain) that the program omits, and it chooses none. What the
programmer writes binds. E1s and E3s write it and compile.

## Main theorems

- `compile_checks`, `compile_uses_checks`, `compile_checks_get`: the FCdot checker accepts the translated derivation and its use set. `compile_erase`, `compile_faithful`: the translation erases to the compiled term, which has the skeleton of the fill.
- `compile_safe`, `compile_not_stuck`, `compile_run_progress`: a run of a compiled program never gets stuck. `compile_capture_prediction`, `compile_effect_safety`: a run uses no more than the use set, and never reads a capability outside a use set with no filter.
- `compile_lvl_safety`, `compile_rejected_goal`: a subcapturing of the derivation that reads no capture member keeps capabilities in their scopes, and a rejection for a level escape proves that no such subcapturing reaches its goal.
- `compile_kind_checks`, `compile_classified_effect_safety`, `compile_filtered_effect_safety`: after `compileKinded` or `compileFiltered` at a kind `φ`, the FCdot checker accepts the kinding, and a run reads only capabilities whose classifier `φ` admits.
- `shp?_complete`, `cap?_complete`, `kind?_complete`, `esub?_complete`, `sub?_complete`, `var?_complete` and the `_reject` versions: a goal `Alg` derives is answered when the tank did not run short, and a rejection then means `Alg` derives no such goal. `Alg.sound`: a goal `Alg` derives has a derivation of the calculus.
- `sub?_mono`, `kind?_stable`, `synthTop?_mono`, `synthTop?_stable`, `elabTop?_mono`, `elabTop?_stable`, `elabProg?_mono`, `elabProg?_stable`: an answer, or a rejection when the tank did not run short, stays the same at more fuel.
- `compile_full`, `compileE_fills`: a program with every slot written compiles as the typer's verdict on it, declared use set included, and the fill agrees with every written slot.
- `elab_complete_direct`, `compile_complete_direct`, `compile_complete_canonAt`: where the elaborator runs the typer's own clause on the fill, a canonical fill the typer accepts is found from some fuel on, and an erased program compiles as the written one.
- In `Examples`, for a program `X`: `X_compiles`, `X_checks` for each accepted one, `X_rejected` at every budget for each rejected one, `X_erased` for the erasure tables, `X_complete` where completeness applies, and `LP_limit`, `PF_limit` and `LQ2_limit` at the limit.

## What it leaves out

- A derivation through a middle type the program does not write, and a merge of two members of one name. The calculus has no rule for the merge, so the typer tries each member.
- A union of two domains, which scalac forms and the typer rejects as a mismatch.
- Completeness over every filling, which fails at a call argument the typer types only at a non-dominant formal (`Mid` in `Examples`), and for the typer as a whole.
- A judgment whose search needs more than the fuel, such as Pierce's divergence of F<:.
- A lookup through a cyclic member, cut as the compiler cuts a cyclic reference.
- A safety theorem at a context other than the platform's.
- `fresh` under a filter and in a lambda domain, and a kind built from `only` and `except` together, which may print as `name \ {names}`, a form the notation does not parse.

## Building

`lake build ClassifiersFrontend`, which is not a default target.
`#assert_no_wf` checks that no definition of the front end is well-founded. The
level-escape verdict reads the well-founded `FCdot.Ctx.caps` through its
structural twin `capsK`, so the kernel computes it too. Every theorem
depends on `propext` and `Quot.sound` at most, with no `sorry`, `axiom`,
`native_decide` or Mathlib.
