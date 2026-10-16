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
its shape, subtype, subcapture, kind, answer and variable checks are complete
with respect to `Alg`. The typer as a whole has no such theorem. As scalac
does, it rejects E1, E3 and E4 of `Examples`, which need a middle type (an
intermediate type of a subtyping chain) that the program omits, and it chooses
none. What the programmer writes binds. E1s and E3s write it and compile.

## Main theorems

- `compile_checks`, `compile_uses_checks`, `compile_checks_get`: for a program that compiles, the FCdot checker accepts the translated derivation and its use set. `compile_erase`: the translation erases to the erasure of the compiled term.
- `compile_faithful`, `compile_faithful_get`: if `compile b Λ p = .ok ⟨r, c⟩`, then `p` resolves to a header and a partial body, `r` is the header with the fill as its body, and the fill agrees with every slot the partial body writes. The elaborator's first candidate on the partial body has the fill, the term `c.tm` and the plain type `c.ty`, and its use set is `c.use` or else the program declares `c.use`. `ATm.skel c.tm = ATm.skel r.body`. `ATm.skel` forgets annotations, capture sets, boxes, unboxings, ascriptions and capture binders. It inlines a `let` of a variable and does not tell `let` from `letex`. So the elaborated term differs from the fill only there. `compile_faithful_written`: when the body writes every slot, `resolveProg Λ p = some r`, and the typer `synthIn?` at the platform's context answers on `r.body` with a result whose term is `c.tm`, whose answer is the plain type `c.ty`, and whose use set is `c.use` or else the declared one. `C7_faithful` in `Examples` is an instance where the two terms differ and the skeletons agree.
- `compile_safe`, `compile_not_stuck`, `compile_run_progress`: a run of a compiled program from the platform's initial store never gets stuck. `compile_safe` is `DotMNF.dot_safety_platform` and `compile_not_stuck` is `DotMNF.dot_not_stuck_platform`. `compile_capture_prediction`: along such a run, an FCdot state with the same erasure and a typed store exists. It is reached by a run of the translated derivation from the platform's target store, it is typed, and it uses no more than the use set the typer found, translated and renamed along the store extension.
- `compile_effect_safety`: let `κ` be a platform capability that the use set lacks, where the use set contains no projection (no filter). The matched FCdot state is reached from the platform's target store, is typed, and reads the variable the reached state reads, and `κ` renamed along the store extension is not a root of that variable.
- `compile_consistent`, `compile_realized`: every FCdot state that a run of the translated derivation reaches from the platform's target store has a typed store. Its context proves no closed `⊤ ≤ ⊥` at any pair of capture sets (`DotMNF.reachable_consistent`), and every block name of every store binder is defined by closed equality evidence (`DotMNF.reachable_realized`).
- `compile_lvl_safety`: for each member-free subcapturing `lo <: hi` in the log of the derivation, and each atom `ρ`, if the resolution of `hi` in the entry's context, translated to FCdot, is confined to `ρ` at every depth, so is the resolution of `lo` at every depth.
- `compile_kind_checks`: after `compileKinded` at a kind `φ`, the FCdot checker accepts the kinding. `compile_classified_effect_safety`: after `compileKinded`, every root of a variable a run reads carries a classifier `φ` admits. `compile_filtered_effect_safety`: the same after `compileFiltered`. Both are statements about the matched FCdot state of a run from the platform's initial store, which is reached by a run of the translated derivation, is typed, and reads the variable the source state reads.
- `shp?_complete`, `cap?_complete`, `kind?_complete`, `esub?_complete`, `sub?_complete`, `var?_complete`: if `Alg` derives the goal and the run ends with the tank unmarked, it is answered.
- `shp?_reject`, `cap?_reject`, `kind?_reject`, `esub?_reject`, `sub?_reject`, `var?_reject`: a rejection with the tank unmarked means `Alg` derives no such goal, or for `sub?` not both halves. `Alg.sound`: a goal `Alg` derives has a derivation of the calculus, or for a variable goal a map from typings of the variable at the first type to typings at the second.
- `sub?_mono`, `synthTop?_mono`, `elabTop?_mono`, `elabProg?_mono`: an answer stays the same at more fuel. `kind?_stable`, `synthTop?_stable`, `elabTop?_stable`, `elabProg?_stable`: a verdict that ends with the tank unmarked stays the same at more fuel.
- `compile_full`, `compileE_fills`: a program with every slot written compiles as the typer's verdict on it, declared use set included, and the fill agrees with every written slot.
- `elab_complete_direct`, `compile_complete_direct`, `compile_complete_canonAt`: where the elaborator runs the typer's own clause on the fill, a canonical fill the typer accepts is found from some fuel on, and an erased program compiles as the written one.

A rejection for a level escape carries a certificate that no member-free subcapturing proves the goal the typer reached. `certify?` builds it by `escape_rejected_at`. It reads the resolution `FCdot.Ctx.caps`, which is well founded, through `capsK`, a structural twin on a budget of steps whose answers are the resolution (`capsK_sound`). A resolution that needs more than the budget of `certify?` gives no certificate. So the kernel computes the verdict. `compile_rejected_goal` in `Examples`: `compile {} Λc (onC EscSrc)` is `.rejected (.levelEscape EscGoalCtx [f] [κ_g] κ_g cert)` for a certificate `cert : ¬ ∃ d : Subcap EscGoalCtx [f] [κ_g], d.MemberFree`. `TopEsc_compile_rejected` is the same for the escape at the top, at `TopGoalCtx` and the universal root. `Esc_rejected'` and `top_escape_rejected` prove the two certificates by hand.

- In `Examples`: a type, a compile and a checker verdict for each accepted program, a rejection at every budget for each rejected one, the reason of each rejection by a level escape, `X_erased` for the erasure tables, `X_complete` where completeness applies, and the recursion limit for `LP_limit`, `PF_limit` and `LQ2_limit`.

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
