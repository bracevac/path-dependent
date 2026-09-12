# Classifiers

Classifiers on the compiler's way: the third capture project of plan V (`plan-5-extensions.md` §5,
`plan-5f-classifiers-stages.md`), namespace `Classifiers`.  The tree started as a verbatim copy of
`lean/Coercions/CapturesCC/` at the commit in `BASE`, the end of captures the compiler's way, and it
grows the classifier tree and kinds as data, classified platform binders, projected captures, kinding
on telescopes with its evidence family, and classified prediction.  Stages K0 and K1 have landed,
and both are the target only.  The stages after them, K2 and K3, will add the classified source and
translation, classified prediction, and the closing examples.

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

`DotMNF` is the source calculus and it is unchanged in K0 and in K1: the source writes no classifier,
and the classified source is K2's subject.  `DotToFCdot` is the translation, and no rule, judgment or
translation clause of it changed either.  Two of its lemmas gained the clause or the premise that
says the source writes no projection, which is what makes its platform prefix behave as it did, and
K1 added the mechanical clause for the new proposition to its telescope predicates and to its
identity morphism.  `Runtime.lean` is shared with the other trees and is untouched.
