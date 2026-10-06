# CapturesCC: capture checking the compiler's way

Scala 3's capture checker tracks in a type `T^{c}` which capabilities a value may retain.  The
compiler reads the universal capability `any` by scope.  Every method body and every class has a
local root of its own, a capability may only be absorbed by a root whose scope encloses it, a
parameter `any` is a capture parameter, and a result `fresh` is a new capability for each call.
This development models that reading on top of DOT and FCdot.  The classic escape
`withFile[() => File^]("test.txt")(f => () => f)` is then rejected by the compiler's own level
check, and every subcapturing step is an explicit proof term that erases to nothing.

The tree is a copy of `../Captures/`, which models capture checking the DOT way, at the commit
named in `BASE`.  It keeps every theorem of that base.

## What is proved

- `level_inversion`: capture evidence that reads no capture bound never lets a capability of an
  inner scope pass for one of an outer scope.  It needs no store.
- `source_lvl_safety`: the same for source subcapturing, through the translation.
- `no_ex_le_ty`: an existential answer is never included in a plain type, so a `fresh` result
  cannot be forgotten into an outer `any`.
- `two_calls_incomparable`: two calls of a function with a `fresh` result open capabilities that
  no evidence in the caller relates.
- `capture_prediction`, `effect_safety`, and `dot_capture_prediction`, `dot_effect_safety` on the
  source: the capabilities a program may use only shrink, and an unnamed one is never read.
- `preservation'`, `progress`: type safety of the target.
- `dot_safety`, `HasTy.translate_typed`, `HasTy.translate_erase`: type safety of the source, by
  a typed translation that erases to the source program.

## What it leaves out

- Tunneling: `any` under a box or in a type-member bound is refused.
- `fresh` with an outer bound.
- The `Unscoped` and shared-capability classifiers that the compiler's level check consults.
- Separation checking and its hidden sets.
- The narrowing that folds a call's result back into the caller's capabilities, which is type
  inference.

It also departs from the compiler in five places.  A call sends the callee's body root to the
universal root `⊤ᶜ`, which is sound because a store binds no scope.  A parameter `any` is
instantiated at the argument itself, not at a fresh capability.  The source has no universal
root, so a top-level `any` reads as the platform capabilities.  An `any` in a class member reads
as the root enclosing the object type, not as the class root.  The level rule needs a root on its
right, so it never puts a capability below an arrow's capture binder.

## The parts

**`FCdot/`** is the target.  Types are shapes with capture sets, `S ^ C`, capture sets have their
own inclusion and equality evidence, and a telescope can hold capture members.  A lambda body and
an object body open a scope root, and the `level` rule is the compiler's `acceptsLevelOf`.  An
answer may be an existential `∃ᶜ[C] T`, unpacked by `letex`.

**`DotMNF/`** is the source, DOT in monadic normal form with capture sets, boxes, capture members
and use sets.  `any` and `fresh` are notations, read before typing by the scope that encloses
them.  The source has the target's scopes and levels, and a level rule of its own.

**`DotToFCdot/`** translates source derivations into target terms and evidence.  The translation
is homomorphic on types.  Source safety, consistency, capture prediction and level safety are all
transported from the target.

**`Runtime.lean`** is the untyped runtime both calculi erase into.  Capture binders are store
slots without data, and `letex` has runtime steps of its own.

## Building

`lake build CapturesCC` builds the library, which is a default target.  Every theorem depends on
`propext` and `Quot.sound` at most.  The tree contains no `sorry`, `axiom` or `native_decide`.
