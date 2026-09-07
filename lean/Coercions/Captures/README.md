# Captures

Captures, the DOT way: the first capture project of plan V (`plan-5-extensions.md` §2, `plan-5a-captures-note.md`),
namespace `Captures`.  The tree started as a copy of the vanilla line `lean/Coercions/{DotMNF,FCdot,DotToFCdot,Runtime.lean}`
at the commit in `BASE` and grows a capture sort beside the type sort.  Every vanilla statement is kept, restated in
the new representation, never weakened.

Stages A0, A1, A2 and A3a of `plan-5c-captures-stages.md` are complete.  A0 made the representation: what the vanilla
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

A3a is the capturing source and its translation.  `DOT-MNF^cc` is DOT-MNF after the split stage A0 made on the
target, with capture members at type labels, the box former, the unboxing term `C ⊸ x`, a rigid platform capture
binder, and a use set as the first index of term typing.  `any` is not in it, so every capture set of the stage is a
list of concrete atoms, and `any` by position is stage A3b.  The translation reads the source's own use-set
evidence: beside `HasTy.translate` there is `HasTy.translateUses`, typed at `uses ⟦h⟧ ⊑ ⟦U⟧`, and it supplies the
annotation and the evidence of every translated lambda, literal, let and unboxing, so the A2 stand-ins that assumed
a pure source are gone.  Two corollaries carry the target's prediction across the simulation, both over a platform
prefix: `dot_capture_prediction` bounds the matched target state's use set by the translation of the source's
declared set along the run, and `dot_effect_safety` says that a source program whose declared use set does not name
a platform capability never reads a root with that capability.  The stage also revised the runtime, and the reason
is a collision.  The A1 erasure sent a box to a one-field object at a reserved label, and once the source has boxes
too, a source literal with a field at that label and a source box have the same erasure, so the simulation, which
relates the two calculi by erasure alone, cannot tell them apart.  The runtime therefore has an inert box of its
own, both calculi erase a box to it, and `dot_safety` and `dot_not_stuck` are the vanilla statements on the whole
source with no side condition.

**`FCdot/`** is the target, FCdot^cc.  Its README lists the modules, what each of A0, A1 and A2 changed in them, the
notation, and the theorems: the canonical-forms theorem with `cap_canon` and item 7, `closed_box_inversion`, the
five theorems of the new module `Prediction.lean`, and the capture examples C1 and C6, which check a capability
closure, compute its use sets in the kernel, reject the variant that hides a capability, and instantiate the
prediction on a run.  A3a reached it twice.  The erasure of a box and of an unboxing goes to the runtime's own box
and unboxing, and the target twins of the three source examples of the stage, S3, C2 and C7, are checked there by
the structural checker in the kernel.

**`DotMNF/`** is the source, `DOT-MNF^cc` since A3a.  A shape is the vanilla type former, a type is a shape with a
capture set, and the new shapes are the capture member `{C : c₁..c₂}` and the box `□ T`.  A value is pure and the
capture set of its type is the use set of its body without the binder, `Var` refines a binder's capture set to
`{x}`, and `sc-var` reads the declared set back off the context.  Type-member bounds are shapes, so a capturing
type enters a type member through a box, which is what the example S3 is about.  The machine allocates a box like
any value and has one new step, which reads a box out of the store and continues at its content.

**`DotToFCdot/`** is the translation.  A source type is a shape with a capture set and so is a target type, so the
translation splits the same way, and a field's declared capture set now reaches its telescope entry instead of the
empty set A2 put there.  A capture member becomes the two inclusions of a capture name, a translated literal
declares one capture witness per field and per capture member, and a translated projection is cast to the field's
declared set by the capture entry read at the receiver.  Use sets are the other half: the source carries its own,
so the translation of a derivation carries the evidence for it, and no translated binder needs to be pure any more.
Every theorem of the translation keeps its statement, and the source's safety, consistency and prediction are all
borrowed from the target through it.

**`Runtime.lean`** is the shared untyped runtime with a data-free capture slot in its store.  A2 gave it the
inspected root of a runtime term, `Runtime.Tm.inspects`.  A3a gave it an inert box: `Tm.box x` is a value,
`Tm.unbox x` a term, and the one new step reads the box the store holds at `x` and continues at its content.
Both calculi erase their boxes to it, so a box and an object literal never share an erasure.

Identifiers the plan spells with a `ᶜ` suffix carry the ASCII suffix `C` here (`Ctx.consC`, `Store.consC`,
`Subst.liftC`, `Ctx.lookupDefC`, `Proposition.leC`, `CapEq.defC`, `SideC`, `HoleC`), since `ᶜ` is not a legal
identifier character; notation tokens such as `⊑ᶜ`, `≐ᶜ` and `⊢ᶜ` are unaffected.

## What is not here yet

`any` as the top of subcapturing, read by position: the level-free reading of a result `any` as the concrete set of
binders in scope, the five-template packing of an existential result, and `(sub)` on answers.  That is stage A3b.
