# Captures

Captures, the DOT way: the first capture project of plan V (`plan-5-extensions.md` §2, `plan-5a-captures-note.md`),
namespace `Captures`.  The tree started as a copy of the vanilla line `lean/Coercions/{DotMNF,FCdot,DotToFCdot,Runtime.lean}`
at the commit in `BASE` and grows a capture sort beside the type sort.  Every vanilla statement is kept, restated in
the new representation, never weakened.

Stages A0, A1 and A2 of `plan-5c-captures-stages.md` are complete.  A0 made the representation: what the vanilla
line called a type is now a shape, a type is a shape with a capture set beside it, binders and stores gained a
capture kind with its four capture bounds, and the box former joined the shapes.  Capture sets were carried
everywhere and read nowhere.  A1 gave them a place to be read: telescopes carry capture propositions, an inclusion
`C₁ ⊑ᶜ C₂` and an equality `C₁ ≐ᶜ C₂`, both under the self like every proposition, so an object type can say what
its members capture; an object literal records a capture witness per label beside its type witness; capture
evidence can read a variable, a telescope entry at an atom, or a block's capture definition; resolution follows a
capture witness through `x ∙ ℓ` with fuel, a cycle resolving to the empty set as the least solution; and the
canonical-forms theorem gained its capture items.  A1 also carried out the box revision: boxing is a value and
unboxing a term, so every atom's capability is the capability of its root.

A2 makes the capture sets do their job.  A value now carries the capture set its introduction rule assigns to it, so
a stored value's binder has a real capture set and the roots of a variable are no longer empty; a term has a use
set, computed by a total structural function `uses` and paired with explicit evidence wherever a use set is
discharged against a declared set.  A let declares the use set of its body and carries the avoidance evidence that
puts the body's use set below it, a lambda and a literal carry their assigned set and the closing evidence that
puts each body's use set below that set together with the binder, and an unboxing charges its boxed set against a
declared use set instead of against nothing.  The prediction theorem of the stage is proven beside preservation and
never folded into it: along any run from a typed state the roots of the use set only shrink (`step_uses` and
`capture_prediction`), every step that reads a root reads one covered by the use set (`inspects_covered`), a run
whose initial use set has no root in a platform capability never reads a root that has one (`effect_safety`), and a
finished program's answer captures no more than its type says (`returned_capture_bound`).  A2 adds no sort, no
evidence family, and no form, entry or slot: use sets are not in types.

**`FCdot/`** is the target, FCdot^cc.  Its README lists the modules, what each of A0, A1 and A2 changed in them, the
notation, and the theorems: the canonical-forms theorem with `cap_canon` and item 7, `closed_box_inversion`, the
five theorems of the new module `Prediction.lean`, and the capture examples C1 and C6, which check a capability
closure, compute its use sets in the kernel, reject the variant that hides a capability, and instantiate the
prediction on a run.

**`DotMNF/`** is the source, still the vanilla DOT-MNF: no capturing types, no capture members, no boxes, no use
sets.  It is unchanged by all three stages so far.  The capturing source calculus `DOT-MNF^cc` is stage A3.

**`DotToFCdot/`** is the translation, routed through the pure pairing `capt _ (refl _)`: a translated type is the
shape translation with the empty capture set.  A2 reaches it twice.  A field's result now carries the capture name
of its label, so the declared telescope of a source field gained the capture entry `{self∙ℓ} ⊑ᶜ {}` beside its
presence and its bound, a translated literal declares one empty capture witness per field label, and a translated
projection is cast back to the pure type by that entry read at the receiver.  And every binder of a translated
context is pure, so the use set of a translated term holds term variables of pure type only: a translated let
declares the empty use set with `pureEvidence` as its avoidance evidence, and a translated lambda and literal carry
the empty assigned set with the closing evidence built from the same.  Every theorem of the translation keeps its
statement.

**`Runtime.lean`** is the shared untyped runtime with a data-free capture slot in its store.  A2 gave it the
inspected root of a runtime term, `Runtime.Tm.inspects`, and changed nothing else.

Identifiers the plan spells with a `ᶜ` suffix carry the ASCII suffix `C` here (`Ctx.consC`, `Store.consC`,
`Subst.liftC`, `Ctx.lookupDefC`, `Proposition.leC`, `CapEq.defC`, `SideC`, `HoleC`), since `ᶜ` is not a legal
identifier character; notation tokens such as `⊑ᶜ`, `≐ᶜ` and `⊢ᶜ` are unaffected.

## What is not here yet

The capturing source calculus and its translation: capturing types, capture members, `any` as the top of
subcapturing, boxes and use sets on the source side, `(sub)` on answers, the level-free reading of a result `any` as
the concrete set of binders in scope, the five-template packing of an existential result, and the box clauses of the
translation.  That is stage A3.
