# CapturesCC: capture checking the compiler's way

Scala 3's capture checker tracks in a type `T^{c}` which capabilities a value may retain.  The
compiler reads the universal capability `any` by scope.  Every method body and every class has a
local root of its own, a capability may only be absorbed by a root whose scope encloses it, a
parameter `any` is a capture parameter, and a result `fresh` is a new capability for each call.
This development models that reading on top of DOT and FCdot.  For the classic escape
`withFile[() => File^]("test.txt")(f => () => f)`, the level premise fails for the callback's
parameter (`X4_no_level`).  No capture evidence puts the parameter below the universal root in the
target (`X4_no_escape`), and no source subcapturing derivation puts it below the platform
capability (`W5_no_escape`).  These are statements about one subcapturing question.  The claim that the whole
program is rejected belongs to `Frontend/`.  Every subcapturing step is an explicit proof term
that erases to nothing.

The tree is a copy of `../Captures/`, which models capture checking the DOT way, at the commit
named in `BASE`.  It keeps every theorem of that base.

## What is proved

- `level_inversion`: for capture evidence that reads no capture bound, if the resolution of the
  upper set is confined to an atom `r` at every depth, so is the resolution of the lower set.  So a
  capability of an inner scope does not pass for one of an outer scope.  It needs no store.
- `level_inversion_plain`: the same for all capture evidence, in a context whose term binders are
  opaque at shapes with no member to read and whose capture binders are not instances.
- `root_inversion`: member-free capture evidence includes resolved roots, in every context.  It is
  `cap_canon` for member-free evidence, with no store.
- `source_lvl_safety`: the same for source subcapturing, through the translation.  It needs a
  well-formed context.
- `no_ex_le_ty`: no evidence includes an existential answer in a plain answer.  A `fresh` result
  is an existential answer.
- `two_calls_incomparable`: for `freshCell` called twice at a caller with no scope root, no
  capture evidence puts either opened binder below the other, and none puts either cell below the
  other.  `two_calls_incomparable_rooted` says the same for member-free evidence at a caller that
  is a lambda body.
- `capture_prediction`, `effect_safety`: along a run from a typed state the roots of the use set
  only shrink.  `effect_safety` also asks for a typed store: a capability that is not a root of the
  initial use set is not the root of the variable a later state reads, up to the renaming of the
  store extension.
- `dot_capture_prediction`, `dot_effect_safety`: the same through the translation, for a closed
  source program at a plain answer over a platform prefix.  The conclusions are about a typed
  target state that the run of the translated program reaches from its initial state and whose
  erasure is the source state's, since the source machine has no use sets.
- `preservation'`, `progress`: type safety of the target, for a typed state.
- `dot_safety`, `dot_safety_platform`: a closed source program at a plain answer never gets
  stuck, over the empty context and over a platform prefix.
  `HasTy.translate_typed` and `HasTy.translate_erase`: a source derivation over a well-formed
  context translates to a typed target term, and that term erases to the source program.

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
