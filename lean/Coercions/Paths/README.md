# Paths

The path project of plan V (`plan-5-extensions.md` §4, `plan-5g-paths-stages.md`), namespace
`Paths`.  It started as a copy of the vanilla line at the commit in `BASE`, and it extends it with
paths `x.a.b`, stable fields and singleton types in the source, path-keyed blocks with a forwarding
forest in the target, and a translation that keeps the safety corollary.  Stages P0 to P3 have
landed.  `Runtime.lean` is the shared untyped runtime, copied unchanged.

**`DotMNF/`** is the source, at P0 with P2's restrictions and P3's examples.  Paths live in types,
terms stay in monadic normal form, and path typing is a judgment of its own with pDOT's singleton
rules.  T10 carries `Defs.Distinct d` (decision 21), and X2 refutes the stable member and not the
path judgment (decision 22).  P2 restricts four rules that have no target image: the `let` at a
singleton is derived (decision 23), a field that holds a variable or a lambda is plain
(decision 27), term typing keeps the base's variable rules with the bridge at a singleton
(decision 28), and replacement is removed (decision 29).  P3 adds source pages after X4: E1p to
E8p hop the receiver of each base example one field deeper, E9 to E11, P2e and P3e exercise a
forwarding definition, a stable field, a cyclic pair and a computation field with bad declared
bounds, and the gDOT Fig. 2 source (with a pDOT twin, P1e) declares two literals, `types` and
`symbols`, that name each other through the enclosing self.

**`FCdot/`** is the target, at P1, with P3's pages checking translated terms.  A block name is a
path, a stable field extends the block forest, and an alias is a forwarding node.  A singleton is
introduced at a path and at an atom (decision 23).  A path is typed at the precise type of a node
of the forest, which repairs T1 (decision 24).  The block builder reads the last field at each
label (decision 25).  A field is stable when its body is an object literal under table-only casts
(decision 26).  The checker is complete, and preservation, progress and canonical forms keep the
base's statements.

**`DotToFCdot/`** is the translation, at P2, with `dot_safety`, the consistency corollaries, and
P3's two acceptance tests.  `Ty.translate` reads the type only, and the block of a literal reads
its definitions (decision 30).  Every translation function is structural, so the kernel evaluates
translations (decision 31).  The `let` at a singleton translates to the opaque `let` (decision 32).
`Sel-<:`, `<:-Sel` and `projP` read a member at the path image (decision 33).  The examples Z1 to
Z9 check images in the kernel, and `Paths` joins the default targets at P2's landing (decision 34).
`Pages` moves the P3 examples of `DotMNF/Examples.lean` onto the target, one sub-namespace per
example.  `Acceptance` holds the two tests P3 asks for.  Test A checks gDOT Fig. 2 as written, with
the `Option` encoding, and takes the abstract view of a nested literal at the selection and at the
variable, never at the value, since no `SelfFree` clause reaches between two types that mention the
outer self (decision 36).  Test B is `acceptance_gdot3`, gDOT's Sec. 3 counterexample refuted for
every literal, proved by translating the derivation, allocating the peeled-off literal, and reading
`Store.Typed.no_top_le_bot` at the store binder, since the source has no invertible typing to case
on directly (decision 35).  The extent of test B is two facts.  `acceptance_gdot3_any` says no closed literal has the type
with bad bounds.  `diverging_at_bad_bounds` is a closed term that does have it, and its run loops at
its third step (`div_reach`, `div_loop`), so it never allocates a literal at that type.  That is why
the test speaks of literals.

**What P3 leaves out**, beyond the calculi: union types, gDOT's later in any form, `Bind-1` and
`Bind-2`, a member whose declared bound is a proper self-mentioning supertype of its definition,
pDOT's precise and invertible typing, a `let` over a field not declared at a singleton, a `val`
field initialised by a variable or a lambda, a stable field whose cast eliminates outside `pi`, a
singleton-typed variable used where its alias's type is not a singleton, and `Sub.repl` between an
abstract member's two aliased selections.  Every restriction, with what it loses and where it is
recorded, is `notes-paths-p3/paths-report.md`.  That report also reads the gDOT rule table of
Sec. 4.1 to 4.4 as it now stands after decision 44: `P-Sngl-Refl` names `PathCo.sngl`/`Atom.sngl`,
`D-Path` names the term typing of a variable body, and `D-Path-Sngl` names the derived `trmSngl` at
a plain field.  It carries the merged table of every statement whose form changed from P0 to P3,
decisions 1 to 44, and the axioms of every theorem the four READMEs name.  `notes-paths-p3/p3-report.md`
is the stage's own report.

Every theorem is inside `[propext, Quot.sound]`, with no `sorry`, `axiom` or `native_decide`.
