# Paths

The path project of plan V (`plan-5-extensions.md` §4, `plan-5g-paths-stages.md`), namespace
`Paths`.  It started as a copy of the vanilla line at the commit in `BASE`, and it extends it with
paths `x.a.b`, stable fields and singleton types in the source, path-keyed blocks with a forwarding
forest in the target, and a translation that keeps the safety corollary.  Stages P0, P1 and P2 have
landed.  `Runtime.lean` is the shared untyped runtime, copied unchanged.

**`DotMNF/`** is the source, at P0 with P2's restrictions.  Paths live in types, terms stay in
monadic normal form, and path typing is a judgment of its own with pDOT's singleton rules.  T10
carries `Defs.Distinct d` (decision 21), and X2 refutes the stable member and not the path judgment
(decision 22).  P2 restricts four rules that have no target image: the `let` at a singleton is
derived (decision 23), a field that holds a variable or a lambda is plain (decision 27), term typing
keeps the base's variable rules with the bridge at a singleton (decision 28), and replacement is
removed (decision 29).

**`FCdot/`** is the target, at P1.  A block name is a path, a stable field extends the block
forest, and an alias is a forwarding node.  A singleton is introduced at a path and at an atom
(decision 23).  A path is typed at the precise type of a node of the forest, which repairs T1
(decision 24).  The block builder reads the last field at each label (decision 25).  A field is
stable when its body is an object literal under table-only casts (decision 26).  The checker is
complete, and preservation, progress and canonical forms keep the base's statements.

**`DotToFCdot/`** is the translation, at P2, with `dot_safety` and the consistency corollaries.
`Ty.translate` reads the type only, and the block of a literal reads its definitions (decision 30).
Every translation function is structural, so the kernel evaluates translations (decision 31).  The
`let` at a singleton translates to the opaque `let` (decision 32).  `Sel-<:`, `<:-Sel` and `projP`
read a member at the path image (decision 33).  The examples Z1 to Z9 check images in the kernel,
and `Paths` joins the default targets in the stage's last commit (decision 34).

Every theorem is inside `[propext, Quot.sound]`, with no `sorry`, `axiom` or `native_decide`.
