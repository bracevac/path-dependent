# CapturesCC front end

This front end writes, types and runs programs of `CapturesCC`. That calculus
is capture checking as the Scala 3 compiler does it. A type `S ^ C` is a type
`S` whose values may use the capabilities in the set `C`, and scopes and levels
stop a capability from outliving its scope. A program is written in the
paper's notation inside `cc%`. The front end resolves names, inserts `let`s,
boxes `□ T` and unboxings `C ⊸ x`, and fills the annotations the program
leaves out. It finds a typing derivation together with its use set, the
capabilities the program may use. It translates the derivation to FCdot, the
target calculus with its own checker and machine, and runs the program. A
program whose capability escapes its scope is rejected, and the rejection
carries a certificate. Nothing here is new metatheory.

```lean
def EscSrc : STm :=
  cc% λ(g : ⊤).
    let cb : (∀(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any})
                (∀(u : ⊤) μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}) ^ {any}) ^ {}
      = λ(f : μ(f. {read : (∀(u : ⊤) ⊤) ^ {f}}) ^ {any}). λ(u : ⊤). f
    in cb
```

This is the `withFile` escape. The callback `cb` takes a file `f` and returns
a closure that holds it. The `any` in the result names the root of the scope
the annotation is written in, the body of `λ(g : ⊤)`, which lies outside the
scope of `f`. The typer rejects the program, and the rejection carries a
certificate that no member-free subcapturing puts `{f}` below that root. A
subcapturing is member-free when it uses no instance binder and no bound of a
selection. `Esc_compile_rejected` proves in the kernel that `compile` returns
this rejection, at the goal `{f} <: {κ_g}` in `EscGoalCtx`, with the root
`κ_g` of the body of `λ(g : ⊤)` and the certificate `Esc_rejected'`. With its
result written at `{f}`, the callback is accepted. The type of `cb` is written,
so its domains can go: `λf. λu. f` is rejected the same way.

A program runs over a platform, one capture binder per capability it may use,
such as `πc` with `k1` and `k2`. `compile b Λ π e` resolves `e` over `π` with
the label table `Λ` and types it within the fuel of `b : Budget`, by default
`defaultFuel = 2 ^ 15`. It returns a `Verdict`. `ok` holds the filled term and
a `Compiled`: the elaborated term, its use set, its type and its derivation.
`rejected` holds a reason with its proof. `unknown` says the typer found no
type and no such reason, or reached the recursion limit. `compileE` returns
the reason of every rejection and `ppReason` prints it. `compileAndRun` also
runs the program.

## What the programmer may leave out

The domain of a lambda: `λy. y` is enough where the context says what `y` is.
The self shape of an object literal: `ν(z. {a = v})` has no shape written on
it. The type of a field, the box at an argument and the unboxing at a use. A
program that writes every domain and self shape is typed as it is, at the same
fuel.

## Where an expected type comes from

The elaborator checks a term against a goal and passes the goal down. The goal
of a `let` body is its written type, the goal of `t` in `(t : U)` is `U`, and
the goal of `t` in `let x : A = t in x` is `A`. The goal of a call argument is
the dominant formal of the callee, the parameter type that the others of an
intersection of functions lie below, whole, and a box on it is stripped. The
goal of a field is its declaration in the self shape. A lambda takes its
domain from the function part of its goal, looking through a box and an alias
and dropping the capture set, or from `g` when its body is `g x`. An object
literal takes its self shape from a `μ` goal, or else forms it from its
fields. If the attempt at a goal fails, the typer's own route runs.

## The compiler's errors

A lambda with no domain and no goal with a function part is rejected with
"Missing parameter type", as scalac does. Fields without written types that
read each other in a cycle are rejected with "Recursive value a needs type",
the compiler's cyclic reference. A field whose type holds a root capability
the self shape cannot state needs a written type, as
`CheckCaptures.checkInferredResult` asks. The others are candidates with no
least type, a type mismatch, a level escape with its proof, and the recursion
limit. Only a program with an empty slot gets the first four (`compileE_slot`).

## Modules

| module | contents |
|---|---|
| `Surface`, `Notation`, `Ann`, `Resolve` | the surface syntax and `cc%`, terms with annotations and partial terms, name resolution, `let` insertion and the platforms |
| `Decide`, `Search`, `Look` | decision procedures, the first view of a variable, the certificate of an escape, the fuel and member lookup |
| `Sub`, `Alg` | subtyping and subcapturing in the compiler's case order, the judgment `Alg`, its completeness and soundness |
| `Avoid`, `Adapt`, `Typer` | avoidance, box adaptation, the typer and its verdicts |
| `Elab`, `Step`, `StepFC` | the elaborator that fills the empty slots of a partial term, the source and FCdot machines as functions |
| `Pipeline` | `compileE`, `compile`, `compileAndRun`, the pipeline theorems and completeness at the direct sites |
| `Pretty`, `Examples` | printers back to the notation, and the programs end to end, each verdict checked in the kernel |

## The typer

The typer follows the Scala 3 compiler, pinned as scala/scala3 at commit
4dae25087d: the case order of `TypeComparer.firstTry`
and its kin, `CaptureSet.subCaptures`, and the levels of
`LocalCap.acceptsLevelOf` (cc/Capability.scala). It approximates an
unannotated `let` as `TypeOps.avoid` does and inserts boxes as
`CheckCaptures.adaptBoxed` does. It runs on one fuel tank for the whole typing,
the elaborator's included. When the tank runs short, it reports a recursion
limit, which is never a rejection. Up to that limit its shape, subtype,
subcapture, answer and variable checks are complete with respect to the
algorithmic judgment `Alg`, which its search follows. The typer as a whole has
no such theorem. It rejects what scalac rejects. The examples E1, E3, E4 and B1
in `Examples` need a middle type the program does not write, and the typer
chooses none. Written with that type, E1 and E3 compile. What the programmer
writes binds. A written `any` is read at the scope it is written in, and a
`fresh` in an arrow's result is an existential.

## Main theorems

- `compile_checks`, `compile_uses_checks`: for a program that compiles, the FCdot checker accepts the translated derivation and its use set.
- `compile_erase`: the translation erases to the erasure of the compiled term.
- `compile_faithful`: for `compile b Λ π e = .ok ⟨a, c⟩`, `a` is the fill of what `resolvePTop` makes of `e`, and it agrees with every slot `e` writes. The elaborator's first candidate has `a` as its fill, and its term, use set and plain answer are those of `c`. The compiled term has the skeleton of `a` (`ATm.skel c.tm = ATm.skel a`). So the two differ only where `ATm.skel` forgets: annotations, capture sets, capture binders, boxes, unboxings and their sets, and ascriptions. It also inlines a `let` of a variable and does not tell `let` from `letex`. `compile_faithful_written`: when `e` writes every slot, `a` is the resolution of `e` (`resolveTop Λ π e = some a`), and `synthTop?` answers on `a` with the term, use set and plain answer of `c`.
- `compile_safe`, `compile_not_stuck`, `compile_run_progress`: no run from the platform's initial store reaches a stuck state, and `run` stops at a final state or at one that can still step. `compile_safe` is `dot_safety_platform`.
- `compile_capture_prediction`: along a run from the platform's initial store, there is a typed FCdot state with the same erasure and a typed store that the run of the translated derivation reaches from its initial state. Its store extends the platform's along a renaming, and it uses no more than the use set the typer found, translated to FCdot and renamed along that extension.
- `compile_effect_safety`: let `κ` be a platform capability that the use set lacks, and `x` a variable the reached state reads. There is such an FCdot state, and in it `κ` renamed along the store extension is not a root of `x`. Only FCdot contexts have roots. `C2_never_reads_k1` in `Examples` is the instance for C2 at `k1`. `ReadK2_never_reads_k1` is the instance at `k1` for `ReadK2Src`, whose run reads a variable declared at `{k2}` (`ReadK2f_set`) after six steps, while the store also holds a variable declared at `{k1}` (`ReadK2a_set`). Its use set is `{k2}` (`ReadK2_uses`).
- `compile_lvl_safety`: for each member-free subcapturing `lo <: hi` in the log of the derivation, and each atom `ρ`, if the resolution of `hi` in the entry's context, translated to FCdot, is confined to `ρ` at every depth, so is the resolution of `lo` at every depth. `compile_lvl_safety_get` states the same for the entries of `compileLog` of a program that compiles by a decided test. `Examples` applies it to two entries where `lo` as written is not confined to the root `ρ`. At entry 6 of the log of C7 (`C7entry_lvl`) the premise holds at every capture binder of the context. At the first entry of the log of `CallbackSrc` (`CallbackEntry_lvl`) the premise holds at the root of an inner scope and fails at the root of an outer one (`CallbackEntry_separates`).
- `certify?_sound`: when `certify? Γ C D = some R`, `R` is `.levelEscape Γ C D r cert` for a root `r` and a proof `cert` that no member-free subcapturing proves `C <: D` at `Γ`. `certify?_isSome`: if `(certify? Γ C D).isSome = true` there is no such subcapturing. `certify?` resolves capture sets with `capsS`, which `capsS_eq` shows equal to `FCdot.Ctx.caps` and which the kernel reduces. It speaks of the goal the typer reached, not of every derivation of the program. `Esc_certify` and `W5_certify` give its answer at two goals, and `Esc_compile_rejected` and `TopEsc_compile_rejected` give the rejection `compile` returns for two programs.
- `shape?_complete`, `subcap?_complete`, `esub?_complete`, `sub?_complete`, `var?_complete`: if `Alg` derives the goal and the run ends with the tank unmarked, it is answered. For `sub?` the goal is a shape goal and a capture goal, and both must be derived.
- `shape?_reject`, `subcap?_reject`, `esub?_reject`, `sub?_reject`, `var?_reject`: a rejection with the tank unmarked means `Alg` derives no such goal, or for `sub?` not both halves.
- `Alg.sound`: a goal `Alg` derives has a derivation in `CapturesCC`, or for a variable goal a map from typings of the variable at the first type to typings at the second.
- `synthTop?_mono`, `elabTop?_mono`: an answer stays the same at more fuel. `synthTop?_stable`, `elabTop?_stable`: a closed typing or elaboration that ends with the tank unmarked, answer or rejection, gives the same verdict at more fuel.
- `compile_full`, `compileE_fills`: a program with every slot written compiles as the typer's verdict on it, and the fill agrees with every written slot.
- `elab_complete_direct`, `compile_complete_direct`, `compile_complete_canonAt`: where the elaborator runs the typer's own clause on the fill, a canonical fill the typer accepts is found from some fuel on, and an erased program compiles as the written one.
- In `Examples`, for a program `X`: `X_type`, `X_checks`, `X_rejected`, `X_erased` for the erasure tables, `X_complete` where completeness applies, and `LP_limit` and `PF_limit` at the limit.

## What it leaves out

- A derivation through a middle type the program does not write.
- A union of two domains, which scalac forms and the typer rejects as a mismatch, and a merge of two members of one name, where the typer tries each member.
- A judgment whose search needs more than the fuel, such as Pierce's divergence of F<:.
- Completeness over every filling, which fails at a call argument the typer types only at a non-dominant formal (Mid), and for the typer as a whole.
- A semantic statement for `let` insertion or box inference.

## Building

`lake build CapturesCCFrontend`, which is not a default target. Every
definition of the front end is structural, so the kernel runs the typer. That
includes the level-escape verdicts: `certify?` resolves with `capsS`, the
structural form of the well-founded `FCdot.Ctx.caps`. Every theorem depends
on `propext` and `Quot.sound` at most. There is no `sorry`, `axiom`,
`native_decide` or Mathlib.
