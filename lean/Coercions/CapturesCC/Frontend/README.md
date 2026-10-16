# CapturesCC front end

This front end writes, types and runs programs of `CapturesCC`. That calculus
is capture checking as the Scala 3 compiler does it. A type `S ^ C` is a type
`S` whose values may use the capabilities in the set `C`, and scopes and levels
stop a capability from outliving its scope. A program is written in the
paper's notation inside `cc%`. The front end resolves names, inserts `let`s,
boxes `□ T` and unboxings `C ⊸ x`, and finds a typing derivation together
with its use set, the capabilities the program may use. It translates the
derivation to FCdot, the target calculus with its own checker and machine, and
runs the program. A program whose capability escapes its scope is rejected,
and the rejection carries a certificate. Nothing here is new metatheory.

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
selection. `Esc_rejected'` proves that statement in the kernel at the goal the
typer reached. That `compile` returns this rejection is checked by `#eval`,
since the kernel does not reduce `FCdot.Ctx.caps`. With its result written at
`{f}`, the callback is accepted.

A program runs over a platform, one capture binder per capability it may use,
such as `πc` with `k1` and `k2`. `compile b Λ π e` types `e` over `π` with the
fuel of `b : Budget` and returns a `Verdict`. The `LabelTable` `Λ` lists the
field labels. `ok` holds the elaborated term, its use set, its type and its
derivation. `rejected` holds a reason with its proof. `unknown` says that the
typer found no type and no reason, or reached the recursion limit.
`compileAndRun` also runs the program.

## Modules

| module | contents |
|---|---|
| `Surface` | the named surface syntax and the table of field labels |
| `Notation` | the notation `cc%` and its kin |
| `Ann` | terms with the annotations the typer needs |
| `Resolve` | name resolution, scope roots, `let` insertion and the platforms |
| `Decide` | decision procedures for well-formedness and labels |
| `Search` | the first view of a variable and the certificate of an escape |
| `Look` | the fuel and member lookup |
| `Sub` | subtyping and subcapturing in the compiler's case order |
| `Alg` | the algorithmic judgment `Alg`, its completeness and soundness |
| `Avoid` | avoidance at a `let` and at an unpacking |
| `Adapt` | box adaptation at a variable |
| `Typer` | the typer and its verdicts |
| `Step` | the source machine as a function |
| `StepFC` | the FCdot machine as a function |
| `Pipeline` | `compile`, `compileAndRun` and the pipeline theorems |
| `Pretty` | printers back to the notation |
| `Examples` | the programs end to end, each verdict checked in the kernel, except the reasons of level-escape rejections, which `#eval` checks |

## The typer

The typer follows the subtype checker of the Scala 3 compiler, pinned as
scala/scala3 at commit 4dae25087d: the case order of `TypeComparer.firstTry`
and its kin, `CaptureSet.subCaptures`, and the levels of
`LocalCap.acceptsLevelOf` (cc/Capability.scala). It approximates an
unannotated `let` as `TypeOps.avoid` does and inserts boxes as
`CheckCaptures.adaptBoxed` does. It runs on one fuel tank for the whole typing.
When the tank runs short, it reports a recursion limit, which is never a
rejection. Up to that limit its shape, subtype, subcapture, answer and variable checks
are complete with respect to the algorithmic judgment `Alg`, which its search
follows. The typer as a whole has no such theorem. It rejects what scalac rejects. The
examples E1, E3, E4 and B1 in `Examples` need a middle type the program does
not write, and the typer chooses none. Written with that type, E1 and E3
compile. What the programmer writes binds. A written `any` is read at the
scope it is written in, and a `fresh` in an arrow's result is an existential.

## Main theorems

- `compile_checks`, `compile_uses_checks`: for a program that compiles, the FCdot checker accepts the translated derivation and its use set.
- `compile_erase`: the translation erases to the erasure of the compiled term.
- `compile_faithful`: it names the field `Compiled.skel`, so it holds trivially. The content is the test in `compile`, which builds the record only when the compiled term has the skeleton of the resolved program. `ATm.skel` forgets annotations, capture sets, boxes, unboxings, ascriptions and capture binders. It inlines a `let` of a variable and does not tell `let` from `letex`.
- `compile_safe`, `compile_not_stuck`, `compile_run_progress`: no run from the platform's initial store reaches a stuck state, and `run` stops at a final state or at one that can still step.
- `compile_capture_prediction`: along a run from the platform's initial store, an FCdot state with the same erasure and a typed store exists. Its store extends the platform's along a renaming, and it uses no more than the use set the typer found, translated to FCdot and renamed along that extension.
- `compile_effect_safety`: let `κ` be a platform capability that the use set lacks, and `x` a variable the reached state reads. In the matched FCdot state, `κ` renamed along the store extension is not a root of `x`. Only FCdot contexts have roots. `C2_never_reads_k1` in `Examples` is the instance for C2 at `k1`.
- `compile_lvl_safety`: for each member-free subcapturing `lo <: hi` in the log of the derivation, and each atom `ρ`, if the resolution of `hi` in the entry's context, translated to FCdot, is confined to `ρ` at every depth, so is the resolution of `lo` at every depth.
- `shape?_complete`, `subcap?_complete`, `esub?_complete`, `sub?_complete`, `var?_complete`: if `Alg` derives the goal and the run ends with the tank unmarked, it is answered. For `sub?` the goal is a shape goal and a capture goal, and both must be derived.
- `shape?_reject`, `subcap?_reject`, `esub?_reject`, `sub?_reject`, `var?_reject`: a rejection with the tank unmarked means `Alg` derives no such goal, or for `sub?` not both halves.
- `Alg.sound`: a goal `Alg` derives has a derivation in `CapturesCC`, or for a variable goal a map from typings of the variable at the first type to typings at the second.
- `synthTop?_mono`: an answer stays the same at more fuel. `synthTop?_stable`: a closed typing that ends with the tank unmarked, answer or rejection, gives the same verdict at more fuel.

`compile_rejected_goal` is not a result. Its conclusion is the certificate that the hypothesis `compile b Λ π e = .rejected (.levelEscape Γ C D ρ cert)` already carries, so it holds trivially. The content is in `Reason.levelEscape` and in `certify?`, which builds the certificate by `escape_rejected_at`, and `Esc_rejected'` checks one such certificate in the kernel. The hypothesis holds at `EscSrc` by `#eval` only, since the kernel does not reduce `FCdot.Ctx.caps`.

## What it leaves out

- A derivation through a middle type the program does not write.
- A merge of two members of one name, where the typer tries each member.
- A judgment whose search needs more than the fuel, such as Pierce's divergence of F<:.
- A lookup through a cyclic member, which is cut as the compiler cuts it.
- A completeness theorem for the typer as a whole.
- A semantic statement for `let` insertion or box inference, or for `fresh` in a lambda domain, which the resolver rejects.

## Building

`lake build CapturesCCFrontend`, which is not a default target. Every
definition of the front end is structural, so the kernel runs the typer, except
for the level-escape verdicts, which read the well-founded `FCdot.Ctx.caps` and
are computed by compiled code. Every theorem depends
on `propext` and `Quot.sound` at most. There is no `sorry`, `axiom`,
`native_decide` or Mathlib.
