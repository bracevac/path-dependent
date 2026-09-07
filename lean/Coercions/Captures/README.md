# Captures

Captures, the DOT way: the first capture project of plan V (`plan-5-extensions.md` §2, `plan-5a-captures-note.md`),
namespace `Captures`.  The tree started as a copy of the vanilla line `lean/Coercions/{DotMNF,FCdot,DotToFCdot,Runtime.lean}`
at the commit in `BASE` and grows a capture sort beside the type sort.  Every vanilla statement is kept, restated in
the new representation, never weakened.

Stages A0 and A1 of `plan-5c-captures-stages.md` are complete.  A0 made the representation: what the vanilla line
called a type is now a shape, a type is a shape with a capture set beside it, binders and stores gained a capture
kind with its four capture bounds, and the box former joined the shapes.  Capture sets were carried everywhere and
read nowhere.  A1 makes them mean something.  Telescopes now carry capture propositions, an inclusion `C₁ ⊑ᶜ C₂`
and an equality `C₁ ≐ᶜ C₂`, both under the self like every proposition, so an object type can say what its members
capture; an object literal records a capture witness per label beside its type witness, and its precise telescope
lists the type definitions, then the capture definitions, then the field presences.  Capture evidence can now read a
variable (`capvar`, "an atom is captured by its own type"), a telescope entry at an atom (`member` in the capture
sort), and a block's capture definition (`defC`), with an equality family beside the inclusion family and template
morphisms that route a capture proposition through a chain of steps.  Resolution follows a capture witness through
`x ∙ ℓ` with fuel, a cycle resolving to the empty set as the least solution, and the canonical-forms theorem gains
its capture items: `cap_canon` moved into the mutual induction, and `atom_canon` gained item 7, that over a typed
store the root of a typed atom is below the capture set of the atom's type.

A1 also carries out the **box revision** (`plan-5c-captures-stages.md` §A1, "Design correction, second version").
A0 made boxing and unboxing *atom* wrappers, so that they would erase to nothing, and read an atom's capture set
through a function that emptied it at a box.  That is unsound: a type witness may mention the self inside a capture
set, and then a `member` at a boxed-and-unboxed atom instantiates the self to the empty set while resolution at the
root instantiates it to the variable, so the two readings of a variable in a capture set disagree and `eq_canon`
fails on a typed store.  The fix removes boxed atoms: `box` is a value, stored like any literal with no witnesses
and no fields, `unbox` is a term whose machine step reads the chain of casts of its atom as the application steps
do, and `recap` is the one new atom wrapper, which changes a capture set without touching the root.  Every atom's
capability is therefore the capability of its root; substitution into a capture set is the root renaming again, and
the capture rules and the view of an atom instantiate at the same thing.  A box erases to a one-field runtime object
and an unbox to that field's projection, so erasure equality and both simulations keep their statements and the
runtime is unchanged.

**`FCdot/`** is the target, FCdot^cc.  Its README lists the modules, what each of A0 and A1 changed in them, the
notation, and the theorems, including item 7, `cap_canon`, and `closed_box_inversion`, the box analogue of
`closed_pi_inversion` that progress and the backward simulation need at an unboxing.

**`DotMNF/`** is the source, still the vanilla DOT-MNF: it has no capture members, no boxes and no use sets.  The
capturing source calculus `DOT-MNF^cc` is stage A3.

**`DotToFCdot/`** is the translation, routed through the pure pairing `capt _ (refl _)`: a translated type is the
shape translation with the empty capture set.  Since the source has no capture members, a translated literal's
capture witnesses are empty and the capture block of its precise telescope is empty; the index computations over
that telescope are nevertheless stated with the capture block in them, so that A3 has only to change what
`Ty.capWitnesses` returns.  Its README lists what each stage changed and the theorems, all with their A0
statements.

**`Runtime.lean`** is the shared untyped runtime with a data-free capture slot in its store, unchanged by A1.

Identifiers the plan spells with a `ᶜ` suffix carry the ASCII suffix `C` here (`Ctx.consC`, `Store.consC`,
`Subst.liftC`, `Ctx.lookupDefC`, `Proposition.leC`, `CapEq.defC`, `SideC`, `HoleC`), since `ᶜ` is not a legal
identifier character; notation tokens such as `⊑ᶜ`, `≐ᶜ` and `⊢ᶜ` are unaffected.

## What is not here yet

Use sets: the total structural `uses`, the annotations on `let`, `λ` and `ν` with their avoidance and closing
evidence, the state typing with a use set, and capture prediction (A2).  Until they arrive, `unbox` charges its
capture set against the empty set rather than against a use set, and every value type in the tree is `^ []`.  The
capturing source calculus and its translation, capturing types, capture members, `any`, boxes and use sets on the
source side, with the five-template packing of an existential result, are A3.
