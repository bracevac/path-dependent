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
algorithm as rules without fuel. Up to that limit its shape, subtype, subcapture,
kind, answer and variable checks are complete with respect to `Alg`. The typer
as a whole has no such theorem. As scalac does, it rejects E1, E3 and E4 of `Examples`, which
need a middle type (an intermediate type of a subtyping chain) that the program
omits. What the programmer writes binds. E1s and E3s write it and compile.

## Main theorems

- `compile_checks`, `compile_uses_checks`, `compile_checks_get`: for a program that compiles, the FCdot checker accepts the translated derivation and its use set. `compile_erase`: the translation erases to the erasure of the compiled term.
- `compile_faithful`, `compile_faithful_get`: if `compile b Λ p = .ok ⟨r, c⟩`, then `resolveProg Λ p = some r`, the typer `synthIn?` at the platform's context answers on the resolved body `r.body` with a result whose term is `c.tm`, whose answer is the plain type `c.ty`, and whose use set is `c.use` or else the program declares `c.use` (`q.uses = c.use ∨ r.uses = some c.use`), and `ATm.skel c.tm = ATm.skel r.body`. `ATm.skel` forgets annotations, capture sets, boxes, unboxings, ascriptions and capture binders. It inlines a `let` of a variable and does not tell `let` from `letex`. So the elaborated term differs from the resolved body only there. `C7_faithful` in `Examples` is an instance where the two terms differ and the skeletons agree.
- `compile_safe`, `compile_not_stuck`, `compile_run_progress`: a run of a compiled program from the platform's initial store never gets stuck. `compile_safe` is `DotMNF.dot_safety_platform` and `compile_not_stuck` is `DotMNF.dot_not_stuck_platform`. `compile_capture_prediction`: along such a run, an FCdot state with the same erasure and a typed store exists. It is reached by a run of the translated derivation from the platform's target store, it is typed, and it uses no more than the use set the typer found, translated and renamed along the store extension.
- `compile_effect_safety`: let `κ` be a platform capability that the use set lacks, where the use set contains no projection (no filter). The matched FCdot state is reached from the platform's target store, is typed, and reads the variable the reached state reads, and `κ` renamed along the store extension is not a root of that variable.
- `compile_consistent`, `compile_realized`: every FCdot state that a run of the translated derivation reaches from the platform's target store has a typed store. Its context proves no closed `⊤ ≤ ⊥` at any pair of capture sets (`DotMNF.reachable_consistent`), and every block name of every store binder is defined by closed equality evidence (`DotMNF.reachable_realized`).
- `compile_lvl_safety`: for each member-free subcapturing `lo <: hi` in the log of the derivation, and each atom `ρ`, if the resolution of `hi` in the entry's context, translated to FCdot, is confined to `ρ` at every depth, so is the resolution of `lo` at every depth.
- `compile_kind_checks`: after `compileKinded` at a kind `φ`, the FCdot checker accepts the kinding. `compile_classified_effect_safety`: after `compileKinded`, every root of a variable a run reads carries a classifier `φ` admits. `compile_filtered_effect_safety`: the same after `compileFiltered`. Both are statements about the matched FCdot state of a run from the platform's initial store, which is reached by a run of the translated derivation, is typed, and reads the variable the source state reads.
- `shp?_complete`, `cap?_complete`, `kind?_complete`, `esub?_complete`, `sub?_complete`, `var?_complete`: if `Alg` derives the goal and the run ends with the tank unmarked, it is answered.
- `shp?_reject`, `cap?_reject`, `kind?_reject`, `esub?_reject`, `sub?_reject`, `var?_reject`: a rejection with the tank unmarked means `Alg` derives no such goal, or for `sub?` not both halves. `Alg.sound`: a goal `Alg` derives has a derivation of the calculus, or for a variable goal a map from typings of the variable at the first type to typings at the second.
- `sub?_mono`, `synthTop?_mono`: an answer stays the same at more fuel. `kind?_stable`, `synthTop?_stable`: a verdict that ends with the tank unmarked stays the same at more fuel.

A rejection for a level escape carries a certificate that no member-free subcapturing proves the goal the typer reached. `certify?` builds it by `escape_rejected_at`. It reads the resolution `FCdot.Ctx.caps`, which is well founded, through `capsK`, a structural twin on a budget of steps whose answers are the resolution (`capsK_sound`). A resolution that needs more than the budget of `certify?` gives no certificate. So the kernel computes the verdict. `compile_rejected_goal` in `Examples`: `compile {} Λc (onC EscSrc)` is `.rejected (.levelEscape EscGoalCtx [f] [κ_g] κ_g cert)` for a certificate `cert : ¬ ∃ d : Subcap EscGoalCtx [f] [κ_g], d.MemberFree`. `TopEsc_compile_rejected` is the same for the escape at the top, at `TopGoalCtx` and the universal root. `Esc_rejected'` and `top_escape_rejected` prove the two certificates by hand.

- In `Examples`: a type, a compile and a checker verdict for each accepted program, a rejection at every budget for each rejected one, the reason of each rejection by a level escape, and the recursion limit for `LP_limit`, `PF_limit` and `LQ2_limit`.

## What it leaves out

- A derivation through a middle type the program does not write, and a merge of two members of one name. The calculus has no rule for the merge, so the typer tries each member.
- A judgment whose search needs more than the fuel, such as Pierce's divergence of F<:.
- A lookup through a cyclic member, cut as the compiler cuts a cyclic reference.
- A completeness theorem for the typer as a whole, and a safety theorem at a context other than the platform's.
- `fresh` under a filter and in a lambda domain, and a kind built from `only` and `except` together, which may print as `name \ {names}`, a form the notation does not parse.

## Building

`lake build ClassifiersFrontend`, which is not a default target.
`#assert_no_wf` checks that no definition of the front end is well-founded. The
level-escape verdict reads the well-founded `FCdot.Ctx.caps` through its
structural twin `capsK`, so the kernel computes it too. Every theorem
depends on `propext` and `Quot.sound` at most, with no `sorry`, `axiom`,
`native_decide` or Mathlib.
