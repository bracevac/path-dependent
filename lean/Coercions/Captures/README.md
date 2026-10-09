# Captures

Scala 3 capture checking, modelled the DOT way.  A type carries a capture set, written `S ^ C`,
which bounds the capabilities a value of that type can reach.  A capture parameter is a capture
member of an object, `{C : c₁..c₂}`, just as DOT models a type parameter as a type member.  This
development adds capture sets to the source DOT-MNF and to the target FCdot, translates one into
the other, and shows the target's capture discipline.  For a source program over a platform prefix,
whenever a source run reaches a state that reads a variable `x`, the target machine runs from the
translation of the program to a typed state with the same erasure, and that state does not root
`x` at a platform capability that the declared use set omits.

The tree is a copy of the vanilla development (`../DotMNF`, `../FCdot`, `../DotToFCdot`,
`../Runtime.lean`) at the commit recorded in `BASE`.  It keeps the theorems of that base,
restated with capture sets.  Two are weaker or narrower: `FCdot.closed_le_shapes` gains a disjunct,
and the body of a recursive type is restricted (below).  Everything lives in namespace `Captures`.

## What is proved

- `FCdot.preservation'`, `FCdot.progress`: FCdot with captures is type safe.
- `FCdot.capture_prediction`: along any run from a typed state, the roots of a state's use set stay
  within the roots of the first state's use set, up to the store extension.
- `FCdot.effect_safety`: from a typed state whose use set has no root `κ`, a run never reaches a
  state that reads a variable rooted at the image of `κ` in a typing of the end store.  It says something at a rigid capture binder.  A stored
  box has the empty annotation, so reading a box is not flagged.
- `FCdot.effect_safety_unbox`: from a typed state whose use set has no root `κ`, a run never reaches
  a state that unboxes a stored box `□ b` with `b` rooted at the image of `κ` in a typing of the end
  store.  This charges the unboxing.
- `FCdot.returned_capture_bound`: over a typed store, the annotation of a returned value and the
  root of a returned atom are bounded by the capture set of the answer's type.
- `DotMNF.HasTy.translate_typed`, `DotMNF.HasTy.translate_uses`: for well-formed contexts
  (`Ctx.Wf`), the translation preserves types and use sets.
- `DotMNF.HasTy.translate_erase`: a translated program erases to the source program.
- `DotMNF.dot_safety`: a source program well-typed in the empty context never gets stuck.  A program
  that uses a platform capability is not in the empty context.
- `DotMNF.dot_safety_platform`: a source program typed over a platform prefix never gets stuck from
  the platform's initial store.  `compile_safe` in `Frontend/Pipeline.lean` is this theorem at a
  compiled program.
- `DotMNF.dot_effect_safety`: let a program be typed over a platform prefix, with a declared use set
  that omits `κ`, and let a source run reach a state that reads `x`.  Then the target machine runs
  from the translation of the program to a typed state with the same erasure.  Its store extends
  the translated platform store, and `x` is not rooted at the image of `κ` in that store.
  `DotMNF.dot_capture_prediction` names the same target state and bounds its use set.
- `DotMNF.Ty.noAny_expand`: expanding a type at a set with no `any` leaves no `any`.
- `DotMNF.Ty.expandWith_of_anyOk`: for a type that is `AnyOk`, no `any` is read as `{}`.  The
  expansion does not change when the positions `expand` reads as `{}` are given any other set.

## What it leaves out

- `any` in the outer set of a parameter type, which quantifies over the argument's captures.  A
  program writes an explicit capture member instead, because the implicit form would allocate an
  object at every call and break erasure to the source term.
- Reach capabilities: `any` in a type-member bound, under a box, or in the lower bound of a capture
  member.  The front end rejects these positions before typing (`Frontend/Resolve.lean`).  `HasTy`
  does not mention `AnyOk`, and the translation drops `any`.  `Ty.expandWith_of_anyOk` says what
  the check secures about expansion, and no theorem about typing or runs depends on it.
- Scopes, levels and fresh capabilities, the Scala 3 compiler's model, which is `../CapturesCC/`.
- The body of a recursive type `μ(x. S)` must be a declaration.  The vanilla development lifted this
  restriction after the copy was taken.

## The parts

**`FCdot/`** is the target.  Inclusion evidence splits into a shape part, as in the vanilla calculus,
and a capture part that proves inclusion of capture sets.  Both erase.  Every term has a use set, the
capabilities it may read, and the evidence that bounds it is explicit.  The module `Prediction` proves
the capture theorems beside preservation.  The examples check a capability closure, reject a variant
that hides a capability, and run the accepted one.

**`DotMNF/`** is the source.  It adds capture sets, capture members, boxes `□ T`, the unboxing term
`C ⊸ x`, and a use set on every typing judgement.  A program is typed under a prefix of rigid capture
variables, the platform capabilities such as a file system.  `any` is a notation: `Ty.expand` reads
each occurrence by its position before typing, and no typing rule mentions it.

**`DotToFCdot/`** is the translation.  A capture member becomes two inclusions on a capture name.  A
second function on derivations, `HasTy.translateUses`, carries the source's use-set evidence into the
target.  The source's safety, consistency and capture prediction are all borrowed from the target
through it.

**`Runtime.lean`** is the untyped runtime both calculi erase into.  It has a data-free store slot for
a capture binder and an inert box of its own.  Both calculi erase a box to it, so a box never shares
an erasure with an object literal, and the simulation needs no side condition.

## Building

`lake build Captures` builds the tree, and `Captures` is a default target.  Every theorem depends on
`propext` and `Quot.sound` at most.  The tree contains no `sorry`, `axiom` or `native_decide`.
