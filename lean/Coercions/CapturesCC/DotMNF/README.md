# DotMNF, capture checking the compiler's way

The source calculus.  It is DOT in monadic normal form (`../../DotMNF/`) with Scala 3 capture
checking.  A type is a shape with a capture set, `S ^ C`, a capture parameter is a capture member
`{C : c₁..c₂}` of an object, a capturing type enters a type member through a box `□ T`, and a
term's typing records the set of capabilities it uses.  A lambda body and an object body open a
scope root, as in the target, and the rule `Subcap.level` is the compiler's level check.  `any` and
`fresh` are notations that no typing rule mentions: a program is read by `Tm.expand` and
`Ty.expandFresh` before it is typed.

| module | contents |
|---|---|
| `Syntax` | paths, capture atoms (with the notations `any` and `fresh`), capture sets, shapes, types `S ^ C`, answers `ETy`, terms with `unbox` and `letex`, values with `box`, definitions with capture members, substitutions, and the readings `Ty.expand`, `Tm.expand`, `Ty.expandFresh` with their checks `Ty.AnyOk`, `Ty.FreshOk` |
| `Typing` | contexts (`consSelf`, `consC`, `consRoot`, `consInst`), the reading `Ctx.reading`, levels (`Ctx.lvl`, `Ctx.lvlLeB`), scope contexts (`Ctx.scope`, `Ctx.body`, `Ctx.objBody`), and the judgments `Subcap`, `SubShape`, `Sub`, `ESub`, `HasTy`, `DefsTy` |
| `Machine` | stores with data-free capture slots, continuations with an unpacking frame, steps including `unbox`, `letex`, `unpack` and `allocE`, and the platform prefix `Platform` |
| `Erasure` | erasure to the runtime, `erase_step`, `erase_reflect`, `Tm.inspects_erase` |
| `Examples` | the vanilla examples E1 to E8 at pure types, and the capture examples listed below |

## New notation

| | |
|---|---|
| `S ^ C` | a shape with a capture set |
| `∃ᶜ[C₀] T` | an existential answer, a capture binder bounded by `C₀` |

The judgments are written as functions.  `Subcap Γ C D` is subcapturing, `Sub Γ T T'` is
subtyping, `ESub Γ E E'` is inclusion between answers, and `HasTy U Γ t E` types `t` at the answer
`E` with use set `U`.  `HasTyP U Γ t T` is `HasTy` at a plain type.

## How `any` and `fresh` are read

`any` stands for the root of the scope that encloses its position.

- At the top of a program, `any` reads as the platform capabilities.  The source has no universal
  root.  With one, a program could name it in its use set and `dot_effect_safety` would say
  nothing about that program.  This last point is an argument, not a checked fact.
- In the outer capture set of an arrow's domain, `any` is the arrow's own capture binder.  This
  makes the arrow a capture-parameter arrow, and a call instantiates it at the argument.
- In an arrow's result, a field, or the upper bound of a capture member, `any` reads as the root
  enclosing the type.  So a field that captures the object itself writes `{self}`.
- `any` is refused in a type-member bound, in the lower bound of a capture member, under a box,
  and deeper inside a domain.  `Ty.AnyOk` decides this.

`fresh` is allowed only in the top capture set of an arrow's result.  `Ty.expandFresh` turns it
into an existential bounded by the callee's own capture set and its parameter.  `ESub.pack` packs
a value at such a type, and `HasTy.letex` unpacks it under a new rigid capture binder.

`Ctx.reading` names the set a position reads `any` as: the innermost root of the context, or the
platform set when there is none.

## Main theorems

The source has no metatheory of its own beyond erasure.  Its safety, capture prediction and level
safety are proved in `../DotToFCdot/` through the translation.

- `erase_step`, `erase_reflect`: a source step erases to a runtime step, and back.
- `Tm.inspects_erase`, `State.inspects_erase`: erasure keeps the capability a term reads.

Statements of the base that changed form:

- `HasTy` is indexed by an answer.  A base statement about `HasTy U Γ t T` reads `HasTyP U Γ t T`.
- `Shape.all` binds a capture binder for its domain, and a lambda body sits under a body root.
- `S1_typed` has the platform set as its use set, where the base had `{fs}`, because the result
  `any` of a top-level `withFile` reads as the platform set.

## Examples

- `W1_inner_absorbs_outer`, `W1_outer_not_inner`: nested lambdas, where the level rule lets an
  inner root absorb the outer one and not the reverse.  The second theorem refutes the premise of
  the level rule only.
- `W2_typed`, `W2_call`, `W2_deep_rejected`: a parameter `any` as a capture binder, instantiated at
  the argument, and refused deeper in the domain.
- `W5_no_level`, `W5_level_own`: the `withFile` callback's parameter is not at the level of the
  outer scope, only at its own body root.
- `W6_fires`: under the other binder order, one level derivation puts the parameter below the
  body root.
- `S1_typed`, `S2_typed`: `withFile` with an explicit capture parameter, and an iterator class
  with a capture member, each typed at its expanded type.
- `S1_readings`: the compiler's reading of the result `any` differs from the arrow's own set.
- `Z1_typed`, `Z1_caller`: `freshCell` with a `fresh` result, and a caller that unpacks it.
- `Z2_typed`, `Z3_typed`: `makeLogger`, packed at its parameter, and an iterator with a `fresh` result.
- `S3_typed`, `C2_typed`, `C7_typed`: a boxed type in a type member, explicit capture
  polymorphism through a capture member, and a pure container of boxed capabilities.
