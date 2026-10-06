# Captures

Scala 3 capture checking, modelled the DOT way.  A type carries a capture set, written `S ^ C`,
which bounds the capabilities a value of that type can reach.  A capture parameter is a capture
member of an object, `{C : c₁..c₂}`, just as DOT models a type parameter as a type member.  This
development adds capture sets to the source DOT-MNF and to the target FCdot, translates one into
the other, and shows that the target's capture discipline holds for source programs: a program
reads only the capabilities its declared use set names.

The tree is a copy of the vanilla development (`../DotMNF`, `../FCdot`, `../DotToFCdot`,
`../Runtime.lean`) at the commit recorded in `BASE`.  It keeps every theorem of that base,
restated with capture sets, and weakens none of them.  Everything lives in namespace `Captures`.

## What is proved

- `FCdot.preservation'`, `FCdot.progress`: FCdot with captures is type safe.
- `FCdot.capture_prediction`: along any run, the capabilities a state's use set reaches only shrink.
- `FCdot.effect_safety`: a run whose use set does not reach a capability never reads it.
- `FCdot.returned_capture_bound`: a final answer captures no more than its type says.
- `DotMNF.HasTy.translate_typed`, `DotMNF.HasTy.translate_uses`: the translation preserves types and use sets.
- `DotMNF.HasTy.translate_erase`: a translated program erases to the source program.
- `DotMNF.dot_safety`: a well-typed source program never gets stuck.
- `DotMNF.dot_effect_safety`: a source program whose declared use set omits a platform capability never reads it.
- `DotMNF.Ty.noAny_expand`: reading `any` by its position leaves no `any` behind.

## What it leaves out

- `any` in the outer set of a parameter type, which quantifies over the argument's captures.  A
  program writes an explicit capture member instead, because the implicit form would allocate an
  object at every call and break erasure to the source term.
- Reach capabilities: `any` in a type-member bound, under a box, or in the lower bound of a capture
  member.  `AnyOk` rejects these positions before typing, so nothing is translated wrongly.
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
