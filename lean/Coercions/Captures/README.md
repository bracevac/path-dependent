# Captures

Captures, the DOT way: the first capture project of plan V (`plan-5-extensions.md` §2, `plan-5a-captures-note.md`),
namespace `Captures`.  The tree started as a copy of the vanilla line `lean/Coercions/{DotMNF,FCdot,DotToFCdot,Runtime.lean}`
at the commit in `BASE` and grows a capture sort beside the type sort.  Every vanilla statement is kept, restated in
the new representation, never weakened.

Stage A0 of `plan-5c-captures-stages.md` is complete.  What the vanilla line called a type is now a shape, a type is
a shape with a capture set beside it, binders and stores gain a capture kind, and the box former is added.  Capture
sets are carried everywhere and read nowhere: the only rules that look at one are the pairing of a shape inclusion
with a capture inclusion and the decided syntactic inclusion.  Every value and every translated type is pure.

## The representation

```
Shape ::= ⊥ | x ∙ ℓ | Π(T) T' | μ Tel | □ T          the vanilla Ty, plus the box
Ty    ::= S ^ C                                      a shape with a capture set
CapAtom  ::= x | κ | x ∙ ℓ                           CaptureSet s := List (CapAtom s)
Kind  ::= var | cap                                  signatures s,x and s,c
CapBound ::= root | ∗ | ⊑ C | = C
```

Inclusion splits accordingly: `ShapeCo` is the vanilla `LeCo` at the shape sort,
`CapCo` is new (`refl`, `trans`, `elem`, `union`), and `LeCo ::= capt ShapeCo CapCo`
is a type inclusion.  Atoms gain `box a` and `unbox a f`; contexts and both stores
gain a data-free capture slot `consC`.

**`FCdot/`** is the target, FCdot^cc at stage A0: the shape family of inclusion evidence is the vanilla one, the capture
family has four rules, and a type inclusion pairs the two.  Its README lists the modules, what A0 changed in each,
the notation, and the theorems.

**`DotMNF/`** is the source, unchanged in this stage.  The capturing source calculus is stage A3.

**`DotToFCdot/`** is the translation, routed through the pure pairing `capt _ (refl _)`: a translated type is the shape
translation with the empty capture set.  Its README lists what changed and the theorems.

**`Runtime.lean`** is the shared untyped runtime with a data-free capture slot in its store.

Identifiers the plan spells with a `ᶜ` suffix carry the ASCII suffix `C` here (`Ctx.consC`, `Store.consC`,
`Subst.liftC`), since `ᶜ` is not a legal identifier character; notation tokens such as `⊢ᶜ` are unaffected.

## What is not here yet

Capture propositions and capture witnesses in telescopes, and the capture conjunct of
`atom_canon` (A1).  Use sets, the annotations on `let`, `λ` and `ν`, and capture
prediction (A2).  The capturing source calculus `DOT-MNF^cc` and its translation
(A3).  Until then `Ctx.roots` has no `x ∙ ℓ` clause, `unbox` charges against the empty
set, and every value type in the tree is `^ []`.
