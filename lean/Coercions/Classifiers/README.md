# Classifiers

Classifiers on the compiler's way: the third capture project of plan V (`plan-5-extensions.md` §5,
`plan-5f-classifiers-stages.md`), namespace `Classifiers`.  The tree started as a verbatim copy of
`lean/Coercions/CapturesCC/` at the commit in `BASE`, the end of captures the compiler's way, and it
grows the classifier tree and kinds as data, classified platform binders, projected captures, kinding
on telescopes with its evidence family, and classified prediction.  Stages K0, K1 and K2 have landed.
K0 and K1 are the target only, and K2 is the classified source, the translation that carries the
classifier across, and the two headline theorems.  The stage after them, K3, will add the closing
examples.

Stage K0 adds the classifier data and reads it in one place.  A classifier is a tree, a kind is a
list of subtrees with exclusions, and both are closed data that mention no de Bruijn index, so
renaming, weakening and substitution act on the atom a projection carries and never on its kind.  A
classifier lives on a capture bound and nowhere else, because resolution lands in capture binders and
in the universal root.  A capture atom may be projected by a kind, and that filter is the last thing
that happens: it is consumed inside `Ctx.expandAtom`, the second and final stage of `Ctx.roots`, so
nothing re-opens what a filter admitted.  Expansion therefore produces projection-free atoms, which
is why `Ctx.roots`, `Ctx.Root` and `CapLe` keep their bodies, their statements and their proofs.  The
decisions of the stage are those four sentences: the filter is consumed in expansion and not in
resolution, `star` reads as the root classifier `⊤`, a projection is never a scope root and is at the
level of what it projects, and a classified capability is rigid, so it sits in the platform prefix and
no step of the machine allocates one.

`Cls` is the classifier data, below the whole development and importing nothing of it.  `Core.lean`
has the classifier tree, the subclass order as a `Bool` function with its reflexivity, transitivity,
antisymmetry and trichotomy, and disjointness.  `Kind.lean` has subtrees with exclusions, kinds as
lists of them, union, membership, emptiness and intersection, all executable, with the bridge lemmas
that the development consumes: every kind contains `⊤` at the root kind, membership distributes over
union, and an intersection admits exactly what both sides admit.  `Ops.lean` has kind subtraction,
subkinding and kind disjointness as the decision procedures Capless(K) proves lawful, the one
direction of subtraction the development needs, the fact that a subkind contains what its subkind
contains, and the example classifiers `Control`, `ThreadLocal` and `IO` with the kind formers `only`
and `except`, each fact closed in the kernel by `decide`.  Only the sound direction of subtraction is
proved.  The converse needs the whole of Capless(K)'s subtraction file, which does not port without
Mathlib, and the module records that where the fallback is taken.

Stage K1 adds the kinding judgment and keeps it a checking judgment.  A telescope may carry the
proposition `C :ᶜ φ`, written `C ⊑ᵏ φ`, which says that every capability `C` reaches carries a
classifier `φ` admits, and closed evidence for it is the family `KindCo` with nine rules.  Every rule
concludes about a general capture atom and reads it through its base and the kind it carries, which
is the root kind when it carries none, so the family covers exactly what Capless(K)'s covers rather
than only projected atoms.  Two of Capless(K)'s four label rules are one rule with an implicational
premise, whose vacuous branch is the absurd rule.  Subcapturing gains three rules, one that drops a
projection, one that adds a projection to a kinded set, and the congruence, and object coercions gain
a template for a target kinding proposition.  The canonical form of the stage is that closed kinding
evidence for `C ⊑ᵏ φ` says exactly `Ctx.KindLe C φ`, the proposition K0 proved the algebra of, and it
runs in the same mutual induction as the canonical forms of capture evidence and of atoms, whose
statements do not move.  The kinding checker decides its judgment in both directions, because the
premises of the rules are the very `Bool` functions of the kind algebra; what only the sound
direction of subtraction is needed for is the step from the checker's evidence to the semantic
reading, and the stage records where.  There is no kind-bounded capture binder: a kind bound on a
capture member is a proposition, because the binder encoding is empty inside a scope.

`FCdot` is the target calculus, and it is where both stages do their work.  A capture bound gains the
flavour `cls c`, which is `star` with a classifier written on it, and a capture atom gains the
projection `a ↾ φ`.  Resolution gains two clauses, one that maps a projection through the resolution
of its base and one that stops at a classified binder, and expansion gains the clause that consumes
the filter.  The semantic side is `Ctx.KindLe`, which says every root of a capture set carries a
classifier the kind admits, and the four theorems of the stage are about it: the roots of a projected
set are the roots of the set filtered by the kind, a projected set is kinded by construction, kinding
is antitone along subcapturing and monotone along subkinding, and kinding travels along a store
extension.  `FCdot/README.md` has the module table, the notation and the statements.

Stage K2 classifies the source, carries the classifier across the translation, and states the two
theorems the whole development is for.  Classified prediction says that a program whose use set is
kinded at a kind keeps a use set kinded at that kind along every run.  Classified effect safety says
that such a program never reads a capability whose classifier lies outside the kind.  Neither needs a
new induction: the first is capture prediction with the kinding carried to the new context by the
store-extension lemma and pulled back along the predicted inclusion, and the second is the first
composed with the fact that the root a state reads is covered by its use set.  Read aloud this is
Capless(K)'s capture prediction refined by the classifier.  Where the reference bounds a set of
runtime labels by a projected set, this bounds the classifier of every root by a kind.  The source
side of the stage is a projected capture atom, a capture member declared at a kind, a seventh context
binder that declares a classifier, and the source's own capture-kinding judgment with ten rules.  The
target side is two additive evidence rules, one that composes subcapturing into kinding and one
morphism template that produces a kinding entry from a capture hole.

Five decisions shape K2.  Effect safety at the source takes the semantic hypothesis, that the
platform capability is not a root of the declared use set, because the syntactic membership form is
false over a projecting source, and a new platform lemma derives the semantic form from the syntactic
one on every projection-free program, so the delivered theorem reads the old way on every program the
copied source could write.  There is no definition form for a kind-bounded capture member: a
literal's capture witnesses are read off its declaration shape, a kind bound carries no set, and a
literal declared at one would be untypable, so a literal writes the set-bounded member it always did
and reaches the kind bound by subtyping.  The two target rules land in this source stage rather than
in a patch of their own, and the second of them is not the rule the expansion note first wrote: that
one carried a chain out of the target set and no hole, and no such chain exists where the source rule
needs it, which was machine checked before the replacement was written.  The source's kinding
judgment is `Type` valued, because it premises typing and because its translation is a function into
the target's evidence, so two derivations of the same judgment are two terms and the source has no
kinding checker of its own, only the target's read through the translation.  And a projected `any` is
legal while a projected `fresh` is not, because `any` is read by an expansion that pushes the reading
under a projection and `fresh` by a syntactic membership test at the top of a result set.  The cost
of the legal side is the one place two copied lemmas change their premise, from an atom that is not
`any` to an atom whose base is not `any`, which is the same premise on every projection-free atom.

`DotMNF` is the source calculus.  It was unchanged in K0 and in K1, and K2 is where it gains the
projected atom, the kind bound, the classified binder and the kinding judgment.  `DotToFCdot` is the
translation.  It was unchanged in K0 and in K1 beyond two lemmas that say the source writes no
projection, and the mechanical clause K1 added for the new proposition to its telescope predicates
and its identity morphism.  K2 gives it the atom clause, the shape clause, the context clause, the
five evidence clauses and the translation of the source's kinding derivations, and it is where the
source's four prediction theorems are stated.  `Runtime.lean` is shared with the other trees and is
untouched.
