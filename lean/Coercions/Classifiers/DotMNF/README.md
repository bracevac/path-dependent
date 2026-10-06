# DotMNF with classifiers

This is the source calculus, DOT in monadic normal form with Scala 3 capture checking read the
compiler's way, and now with classifiers.  The capture layer gives a type a capture set, `S ^ C`, and
types a term at a use set, the capabilities it may use.  It adds capture members `{C : c₁..c₂}`,
boxes, scope roots at every lambda body and object body, a level order, and the notations `any` and
`fresh`, which are expanded before a program is typed.  The classifier layer, new in this tree, lets
a capture atom be filtered by a kind, lets a capture member be declared at a kind, lets a platform
capability declare a classifier, and adds a kinding judgment `CapKind`.  The capture layer is
described in `../../CapturesCC/DotMNF/README.md`.

## What classifiers add

- `CapAtom.proj a φ` filters the atom `a` by the kind `φ`.  `CapAtom.base` is the atom under its
  filters and `CapAtom.kindOf` the intersection of the kinds they carry.  Filters may nest.
- `Shape.capk A φ` is a capture member whose set is only known to be kinded at `φ`, such as
  `{C : only[Control]}`.  There is no definition form for it.  A literal writes a set-bounded member,
  `{C = c}`, and reaches the kind bound by subtyping, through `SubShape.capkI`.
- `Ctx.consCls` binds a rigid capability with a classifier, and `Platform.consCls` is its platform
  twin.  A `consC` binder declares no classifier, and an unwritten classifier means unknown.  So a
  plain platform capability is kinded only at a kind that admits every classifier, and the examples
  declare their capabilities with `consCls`.
- `CapKind Γ C φ` says that every capability `C` stands for has a classifier `φ` admits.  It has ten
  rules, which mirror the target's `KindCo`.  It is `Type` valued and lives in the same mutual block
  as `Subcap`, `SubShape`, `Sub`, `ESub`, `HasTy` and `DefsTy`, because one rule has a typing premise
  and because the translation maps it to target evidence.
- Subcapturing gains `Subcap.unproj`, `Subcap.proj` and `Subcap.projMono`, and subtyping gains
  `SubShape.capkI` and `SubShape.capk`.
- A filtered `any` is legal.  Expansion pushes the reading of `any` under the filter, so a
  parameter's `any` filtered by `except[ThreadLocal]` reads as the arrow's own capture binder with
  the same filter.  A filtered `fresh` in a result is refused by `ETy.codFreshOk`, because the
  reading of `fresh` looks for the bare atom and would let the filtered one slip through.

## Modules

| module | contents |
|---|---|
| `Syntax` | paths, capture atoms with `proj`, capture sets with `CaptureSet.proj`, shapes with `cap` and `capk`, types `S ^ C`, answers `ETy` with `∃ᶜ[C] T`, terms with `unbox` and `letex`, values with boxes, definitions, the expansion of `any` (`Ty.expand`, `Tm.expand`) and of `fresh` (`Ty.expandFresh`) with their tests `Shape.AnyOk` and `Ty.FreshOk`, substitution |
| `Typing` | contexts with `consC`, `consRoot`, `consInst` and `consCls`, levels `Ctx.lvl` and `Ctx.lvlLeB`, the classifier reader `Ctx.ClsOf`, and the mutual block `Subcap`, `SubShape`, `Sub`, `ESub`, `HasTy`, `DefsTy`, `CapKind`, with the member-free predicates `Subcap.MemberFree` and `CapKind.MemberFree` |
| `Machine` | stores with a data-free capture slot, continuations, `Step` with the `unbox`, `letex`, `unpack` and `allocE` steps, `State.inspects`, platforms with `Platform.consCls` and `Platform.classOf` |
| `Erasure` | erasure into the runtime, `erase_step`, `erase_reflect`, `State.inspects_erase` |
| `Examples` | the examples of the base, then the classifier examples `E1`, `E2` and `E3` |

## Main theorems

- `erase_step`: every source step erases to one runtime step.
- `erase_reflect`: every runtime step out of an erased state comes from a source step.

The source's type safety, capture prediction and classified theorems are proved through the
translation, in `../DotToFCdot`.

Base statements that changed form:

- `CaptureSet.expand_cons_of_ne`, `CaptureSet.noAny_cons_of_ne` assume `a.base ≠ .any` where they assumed `a ≠ .any`, since a filtered `any` expands like `any`.
- `ETy.codFreshOk` gains a conjunct that refuses a filtered `fresh`, true on every unfiltered set.
- `Subcap.MemberFree` moved here from `../DotToFCdot/Evidence.lean`, because it is now mutual with `CapKind.MemberFree`.

## Examples

`E1` is `Try.apply`.  Its one field holds the body closure filtered to `only[Control]`, over a
platform with one `Control` and one `IO` capability (`E1Plat`).  `E2` is `Future.apply`.  Its
parameter, the body closure, is filtered to `except[ThreadLocal]`, over a platform of a
`ThreadLocal`, a `Control` and an `IO` capability (`E2PlatIO`).  `Control` is a subclass of
`ThreadLocal` here, so the filter excludes both, and the `IO` capability gives a legal body
something to capture.  `E3` is a capture-polymorphic client whose capture member is bounded by
`only[Control]` instead of an explicit set.  `E3_stable_clsOf` and the declarations after it show
that a third `Control` capability added to the platform leaves the example standing, which a set
bound could not state without being rewritten.  The run-time facts of the three examples are stated
on the target side, in `../FCdot/Examples.lean`.

Four `example`s at the end of `Syntax.lean` check the treatment of filtered notations: a filtered
`any` in a type-member bound is refused, and would otherwise expand to the empty set, while a
filtered `fresh` in a result is refused and a bare one is accepted.

Every theorem depends on `propext` and `Quot.sound` at most.
