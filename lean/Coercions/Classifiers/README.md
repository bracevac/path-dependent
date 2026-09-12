# Classifiers

Classifiers on the compiler's way: the third capture project of plan V (`plan-5-extensions.md` §5,
`plan-5f-classifiers-stages.md`), namespace `Classifiers`.  The tree started as a verbatim copy of
`lean/Coercions/CapturesCC/` at the commit in `BASE`, the end of captures the compiler's way, and it
grows the classifier tree and kinds as data, classified platform binders, projected captures, kinding
on telescopes with its evidence family, and classified prediction.  Stages K0, K1, K2 and K3 have
landed.  K0 and K1 are the target only.  K2 is the classified source, the translation that carries
the classifier across, and the two headline theorems.  K3 is the three mandatory examples of
`plan-5-extensions.md` §5, each staged as a real program and decided against the theorems of K2, and
this report.

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
no step of the machine allocates one.  Two more decisions sit beside them.  A bare root is kinded
only at a kind that admits every classifier, because no proper kind contains `⊤` on its own and an
`except[_]` kind contains `⊤` all the same, so a reader who expects `cap.except[ThreadLocal]` to be
kinded at `except[ThreadLocal]` gets that through the projected atom and not through the bare root.
And a projected atom is a constructor of `CapAtom` rather than a normalised pair, so nesting a
projection inside a projection is legal and reachable, because renaming and substitution are
structural and would otherwise have to normalise on the way through, which would make `rename_id`
false.

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
premises of the rules are the very `Bool` functions of the kind algebra.  Only the sound direction
of subtraction is needed, for the step from the checker's evidence to the semantic reading, and the
stage records where.  There is no kind-bounded capture binder: a kind bound on a
capture member is a proposition, because the binder encoding is empty inside a scope.  Dropping a
projection, `Subcap.unproj`, is a primitive rule and not a derived one, because a capture set is a
plain list here and not a kind-aware subset relation the way Capless(K)'s is.  And subcapturing at a
projection is stated on a set, `Subcap.projMono`, with the atom form at a projected variable derived
from it, which is the reverse of how Capless(K) states the two, and the one congruence rule gives the
projected form of every existing rule, `Subcap.capvar` included.

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
seventh binder is a new constructor of the source's context rather than a payload on the existing
`consC`, and every other context former grows one clause for it, so that every source example
written before K2, and `Platform.ctx`, `Platform.store` and `Platform.targetStore` with them, stay
textually unchanged.  The target side is two additive evidence rules, one that composes subcapturing
into kinding and one morphism template that produces a kinding entry from a capture hole.  An
unwritten classifier means unknown, which is the revised reading of the ninth decision of the
development, so a rigid binder that declares no classifier is kinded only at a kind that admits every
classifier, and the platform examples write their capabilities at `consCls` binders for exactly that
reason.

Five decisions shape K2.  Effect safety at the source takes the semantic hypothesis (decision 16),
that the platform capability is not a root of the declared use set, because the syntactic membership
form is false over a projecting source, and a new platform lemma derives the semantic form from the
syntactic one on every projection-free program, so the delivered theorem reads the old way on every
program the copied source could write.  There is no definition form for a kind-bounded capture member
(decision 17): a literal's capture witnesses are read off its declaration shape, a kind bound carries
no set, and a literal declared at one would be untypable, so a literal writes the set-bounded member
it always did and reaches the kind bound by subtyping.  The two target rules land in this source stage
rather than in a patch of their own (decision 18), and the second of them is not the rule the
expansion note first wrote: that one carried a chain out of the target set and no hole, and no such
chain exists where the source rule needs it, which was machine checked before the replacement was
written.  The source's kinding judgment is `Type` valued (decision 19), because it premises typing
and because its translation is a function into the target's evidence, so two derivations of the same
judgment are two terms and the source has no kinding checker of its own, only the target's read
through the translation.  And a projected `any` is legal while a projected `fresh` is not (decision
20), because `any` is read by an expansion that pushes the reading under a projection and `fresh` by
a syntactic membership test at the top of a result set.  The cost of the legal side is the one place
two copied lemmas change their premise, from an atom that is not `any` to an atom whose base is not
`any`, which is the same premise on every projection-free atom.

No statement of the tree at the base commit lost a conclusion or gained a hypothesis beyond what is
recorded here, across all three target stages.  In K0, `Platform.root_iff` gains the premise that
every atom of the set is its own base, `Ctx.expandAtom_of_not_root` and `Ctx.expand_eq_self` gain the
same premise pointwise and set-wise, and all three are false without it at a witness where an atom's
own kind admits nothing while the atom is still a member of the set, so on the copied representation,
where every atom is its own base, each reads as the statement it always was.  `CapAtom.cons_cases`
and `CapAtom.consC_cases` gain one more disjunct that is additive and uninhabited on the copy.
`CapBound` gains the constructor `cls`, additively, and `CapBound.opaque` gains the clause that a
classified bound is opaque, which is what `star` already said.  `CapAtom` gains the constructor
`proj`, additively, and a bare atom is `a ↾ ⊤` up to roots.  `Ctx.lvlAtom`, `Ctx.capsAtom`,
`Ctx.capsBound` and `Ctx.expandAtom` each gain one clause, and every old clause of each keeps its
statement and its proof word for word, the wildcard branch of `Ctx.expandAtom` in particular being
the old body.  `Ctx.caps_opaque` reads `a.base` where it read `a`, `base` being the identity on the
copy.  `Ctx.mem_expandAtom_self` gains a conclusion about `a.base` under an admission premise that is
vacuous on an unprojected atom.  `Ctx.subset_expand`, `Ctx.caps_subset_roots` and
`Ctx.Root.of_mem_caps` are restated with a base and an admission, because a projected atom of
`Ctx.caps` that its own kind excludes is no longer a root, and on a projection-free set the three read
as they did.  `Ctx.roots_eq_caps_of_rootFree` restates its conclusion as the admitted sublist mapped
by `base` and its hypothesis through `base`, for the same reason.  `lvl_canon`, `lvl_safety` and
`rigid_target` move their conclusion from `Ctx.caps` to `Ctx.roots`, which is the stronger statement
on a projection-free set and is interderivable with the old one there.  `Store.Typed.confined` reads
its hypothesis through `base`, which the proof does not even use.  `Rename.InjectiveOnAtoms.comp_succ`
keeps its statement and trades a case split for an induction, because `CapAtom` is recursive now.  And
`Ctx.roots`, `Ctx.Root`, `CapLe`, `RootsEq`, `Ctx.expand`, `Ctx.caps`, the weakening lemmas
`Ctx.caps_weaken`, `Ctx.caps_weakenC`, `Ctx.capsBound_weakenC`, `Ctx.capsAtom_var`,
`Ctx.capsAtom_cvar`, `Ctx.expand_weakenC` and `CapLe.weakenC`, and every theorem that reads only
`CapLe` and `Ctx.Root`, `cap_canon`, `atom_canon`, `preservation'`, `progress`, `not_stuck`,
`Store.Ext.roots`, `Store.Ext.capLe` and the five Prediction theorems among them, change nothing at
all, because expansion consumes every projection and produces projection-free atoms before any of
them is reached.

In K1, `Ctx.Ren`, `Ctx.RenR`, `Subst.Typed` and `Ctx.Refines` gain the fields that fix a capture
binder's classifier and its bound under a renaming or a substitution, found by a counterexample where
a renaming carried a `Control` binder to an `IO` one and satisfied the old relation, and every
instance the tree builds proves the new fields, so no lemma loses an instance.  `Entry.kindC` carries
a `SideC` chain beside its index, as `Entry.leC` already does, because the kinding entry of a template
needs the side its hole is reached through.  `KindCo.kcvar` takes a `CapAtom` where it took a bound
capture variable, its premise collapsing the two bound flavours into one reading, which is exactly
what the two premises it replaces named.  `Proposition` gains one constructor, additively, leaving
`leC` and `eqC` untouched, and `CapCo` and `CapCo.HasType` gain three constructors and three rules,
additively, leaving `capvar`, `member`, `level` and `eqToLe` untouched.  `Entry`, `PropForm`,
`Morphism`, `EntriesTyped`, `EntryTyped`, `ViewTyped` and `identityEntries` each gain one constructor
or one case, additively, and the new entry carries no `Cls.Kind`, which is the data-freeness that
matters.  `cap_canon` keeps its statement, gains three cases, and joins a mutual recursion with
`kind_canon`, on the same evidence-size measure the block already used.  `CapCo.MemberFree`,
`checkCap`, `checkCap_iff` and the renaming and substitution blocks each gain one case per new rule,
additively.  And `preservation'`, `progress`, `not_stuck`, `erase_step`, `erase_reflect'` and
`closed_le_shapes` change nothing, because the new evidence carries no term and erases to nothing.

In K2, `dot_effect_safety`'s hypothesis moves from a syntactic membership to the semantic statement
that the platform capability is not a root of the translated use set, the one row that is not purely
additive and the subject of decision 16 above.  `CaptureSet.expand_cons_of_ne` and
`CaptureSet.noAny_cons_of_ne` read an atom's base is not `any` where they read the atom is not `any`,
because a projected `any` satisfies the old premise and expands like `any` all the same, and on a
projection-free atom the two premises coincide.  `CaptureSet.base_of_mem_translate` gains the premise
that the source set is projection free, which every set the copied source could build satisfies.
`ETy.codFreshOk`'s plain-answer clause gains a conjunct that is vacuously true on every
projection-free set, which is the refusal half of decision 20.  `CaptureSet.noAny` and
`CaptureSet.noFresh` become folds of an atom-level helper, and `CaptureSet.expand` and
`CaptureSet.substFresh` become the append of one, each agreeing with the old clause on every old
constructor, so every existing `@[simp]` lemma stays `rfl`.  `CapAtom` and `Shape` gain one
constructor each, `proj` and `capk`, and the source's `Ctx` gains a seventh constructor, `consCls`,
all three additively.  `Ctx.lvlLeB` gains one clause that reads through a projection on the source
side, since the target already reads through one on both.  `Subcap`, `SubShape` and `CapKind` gain
three, two and ten rules respectively, `Subcap` and `SubShape` additively and `CapKind` new outright,
leaving `refl`, `trans`, `elem`, `union`, `var`, `inst`, `level`, `selLower` and `selUpper` untouched.
`KindCo` and `Morphism`, with `Entry`, `EntriesTyped` and `EntryTyped`, gain one constructor or case
each, `kle` and `kindCle`, additively, the second carrying two `SideC` chains and a hole and no kind
exactly as `Entry.leC` does.  `Platform` gains the constructor `consCls`, additively, and every
function on it gains the matching clause.  `EntriesTyped.At_kindC`'s conclusion becomes a disjunction
whose left disjunct is the old conclusion word for word and whose right one names the new entry,
uninhabited on every derivation the old tree could build.  `Subcap.MemberFree` relocates from
`DotToFCdot/Evidence.lean` to `DotMNF/Typing.lean`, keeping its seven constructors and gaining one per
new rule, because `Subcap.proj` premises a `CapKind` and `CapKind.kle` premises a `Subcap`, so the two
member-free families are mutual.  `KindCo.MemberFree` gains one clause, additively.  The source's
`Ctx.lookup`, `Ctx.instSet?`, `Ctx.root?`, `Ctx.lvl`, `Ctx.rootB`, `Ctx.varAtom`, `Ctx.translate` and
`Ctx.Wf`, and the seven clause lemmas of `TypesLemmas`, each gain one clause for `consCls`, which is
the `consC` clause with the classifier carried, and a classifier mentions no de Bruijn index.
`Shape.rename`, `subst`, `expand`, `noAny`, `anyOk`, `noFresh`, `substFresh`, `labels`, `declOf?`,
`capOf?`, `fldOf?`, `Decl`, `isDecl`, `erase`, `isObj`, `translate`, `tel`, `telSelf` and
`fieldLabels` each gain one clause for `capk`, additively, and none of them reads a capture set there,
because `capk` carries none.  `Entry.through`, `Entry.at`, `entries`, `identityEntries`,
`synthMorCore`, `checkMor` and `mor_canon` each gain the one case for `kindCle`, additively.
`CaptureSet.top_not_mem_translate` changes nothing, because a translated atom is never the universal
root.  `Shape.witnesses` and `Shape.capWitnesses` change nothing, because their wildcard covers `capk`
and no literal is ever declared at it.  `Defs`, `Defs.Distinct`, `Defs.labels`, `Defs.erase` and
`DefsTy` change nothing, which is decision 17.  `Platform.root_iff` changes nothing, because K0
already gave it the base premise a projecting source needs.  And
`capture_prediction`, `effect_safety`, `inspects_covered`, `preservation'`, `progress`, `not_stuck`,
`erase_step`, `kind_canon`, `cap_canon`, `atom_canon`, `checkKindCo_iff`, `checkTm_iff`,
`HasTy.translate_erase`, `dot_safety`, `dot_not_stuck` and `dot_capture_prediction` change nothing,
because the new evidence is inert at run time and the run is the copied run.

K3 adds nothing to the calculi.  It is the three mandatory examples of `plan-5-extensions.md` §5,
each a real program over a platform built from `Platform.consCls`, each staged as a page of decided
facts against the theorems K0 to K2 proved, and this report.  E1 is `Try.apply` of
`exceptions.tex:60-66`, a body closure filtered to `only[Control]` before it is stored in an object
field, over the platform `κ_ctl ⊑ᶜ cls Control, κ_io ⊑ᶜ cls IO`, closed by `classified_effect_safety`
and, at the source, by `dot_classified_effect_safety'`.  E2 is `Future.apply` of
`exceptions.tex:74-92`, a body closure filtered to `except[ThreadLocal]`, over a platform that adds a
third, unclassified-by-the-filter `IO` capability so that a legal body has something to capture, with
two total refutations that no derivation of any shape kinds a `ThreadLocal` capability at
`except[ThreadLocal]`, closed the same way as E1.  E3 is stage A3a's capture-polymorphism example C2
retyped at the kind bound `{C : only[Control]}` in place of the set bound `{}..{κ₁,κ₂}`, closed by
`dot_classified_prediction` and `dot_classified_prediction'`, with a stability fact, decided twice
over two platforms, that a third `Control` capability added to the platform leaves every fact of the
example standing, which a set bound would have had to be rewritten to state at all.  Every verdict of
the three is decided in the kernel, closed by `simp` over the equation lemmas, or an instance of a
named theorem, and none is a `decide` on `Ctx.caps` or `Ctx.roots`, which are well-founded recursions.
Both source and target definitions live where K0 to K2 left them, E1 and E2's source pages and E3's
source page in `DotMNF/Examples.lean`, and everything that reads the translation in
`FCdot/Examples.lean`, because that is the module that imports `DotToFCdot`.

Six things K3 does not add, and the reason each is left out.  No boundary, no handler and no handler
coverage, so no counterpart of the reference project's boundary or handler-safety corollaries, because
classifiers carry no control effect at all, which is the same declared restriction K2 already stood
on.  No oracle and no non-deterministic classifier assignment, because a classifier is fixed at the
binder that declares it and nowhere else.  No `s-merge`.  No kind-bounded capture binder, hence no
counterpart of Capless(K)'s `Bound.kind`, which is decision 4 above and would be a sixth capture-bound
flavour and a stage of its own if the user wants it.  No completeness of the kinding checker, which is
decision 6.  And no scoped-capability or reach-capability extension, the latter excluded for the whole
line by `plan-5-extensions.md` §9.

`DotMNF` is the source calculus.  It was unchanged in K0 and in K1, and K2 is where it gains the
projected atom, the kind bound, the classified binder and the kinding judgment.  K3 adds no new form
to it, only the three examples, each a platform, a source program typed against it, and the source
half of its kinding and prediction facts, appended to `Examples.lean` after C2 in the order E1, E2,
E3.

`DotToFCdot` is the translation.  It was unchanged in K0 and in K1 beyond two lemmas that say the
source writes no projection, and the mechanical clause K1 added for the new proposition to its
telescope predicates and its identity morphism.  K2 gives it the atom clause, the shape clause, the
context clause, the five evidence clauses and the translation of the source's kinding derivations, and
it is where the source's four prediction theorems, T8, T8', T9 and T9', are stated.  K3 touches none
of it: the three examples instantiate those four theorems and read `Platform.ctx` at the platform each
one declares, and both are already exactly what K2 left behind.

`FCdot` carries K3's other half, the
target twin of each source page and the checker verdicts the source facts are decided through, in
`Examples.lean` after the target's own C2.  `Runtime.lean` is shared with the other trees and is
untouched.
