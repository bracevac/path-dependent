# Classifiers

Scala 3 capture checking can sort capabilities into classifiers, such as `Control` for exceptions
and break labels or `ThreadLocal` for capabilities tied to one thread.  A capture set can be filtered
by a kind, as in `cap.only[Control]`, to say what a closure may hold.  The body of `Try.apply` may use
control capabilities only, and the body of `Future.apply` may capture no thread-local one.  This tree
adds the classifiers of System Capless(K) to capture checking the compiler's way.  It proves that along a
run from a typed state whose use set is kinded at `φ`, every root of a variable a step reads has a
classifier `φ` admits.  Kinding is an explicit proof term that erases to nothing.

The tree is a copy of `../CapturesCC/` at the commit in `BASE`, under the namespace `Classifiers`, and
keeps every theorem of that base.  The directory READMEs name the few statements that changed form.
Three kept theorems, `lvl_canon`, `lvl_safety` and `no_inner_escape`, hold trivially over a typed store,
as `FCdot/README.md` explains.

## What is proved

- `classified_prediction`: if the use set of a typed state (the capabilities it may use) is kinded at `φ`, the use set of every state it reaches is kinded at `φ` too, in every context that types its store.
- `classified_effect_safety`: along such a run, with the stores typed, every root of a variable a step reads has a classifier that `φ` admits.
- `kind_canon`: over a typed store, closed kinding evidence for `C ⊑ᵏ φ` is true, so every capability `C` stands for has a classifier `φ` admits.
- `checkKindCo_iff_hasType`: the checker decides the kinding judgment.
- `Ctx.roots_proj`: the roots of a capture set filtered by a kind are the roots of the set that the kind admits.
- `CapKind.translate_typed`: a kinding derivation of the source over a well-formed context (`Ctx.Wf`, which every platform context is) translates to typed kinding evidence of the target.
- `dot_classified_prediction`, `dot_classified_effect_safety`: the two run-time theorems for source programs. Their primed forms take a source kinding derivation as the hypothesis.

## What it leaves out

- Control effects. A classifier is a label and nothing more. There are no boundaries and no handlers.
- Classifiers chosen at run time. A classifier is fixed where its capability is declared, and a run never allocates a classified capability.
- Kind-bounded capture binders. A capture member may be declared at a kind, `{C : only[Control]}`, but that is a proposition in an object type, not a new binder.
- Completeness. Only the sound direction of kind subtraction is proved, so subkinding is a sound test that is not known to be complete. The converse would need a port of the subtraction proof of Capless(K), which relies on Mathlib and `aesop`. The kinding rules do not kind a rigid capability that declares no classifier at a kind that excludes some classifier, even where the semantics would allow it.  Lean checks this for the example `K6x` only, where the rules `kcls` and `kproj` reject it.  No theorem excludes the other rules. Capless(K)'s `s-merge`, which matters only for completeness, is absent.
- A filtered `fresh`. The source refuses a filter on a result `fresh`, while a filtered `any` is legal.
- Reach capabilities and scoped capabilities.

## Layout

`Cls/` (root `Cls.lean`) is the classifier data, shared by both calculi.  A classifier is a path in an
infinite tree, so exclusion stays sound under separate compilation.  A kind is a list of subtrees with
exclusions.  Every operation is a `Bool` function, so `by decide` settles a concrete fact.

| module | contents |
|---|---|
| `Core` | the classifier tree `Classifier`, the subclass order `leB` with reflexivity, transitivity and antisymmetry, disjointness, `subclass_or_disjoint` (which holds by the definition of `disjointB` as neither direction of `leB`) |
| `Kind` | `Subtree`, `Kind`, `Kind.top`, union, membership `Contains`, emptiness, intersection, and the facts the calculi use about them |
| `Ops` | subtraction, subkinding `Subkind` and kind disjointness, the sound direction `Kind.contains_subtract_of`, `Kind.Admits`, `Kind.AdmitsStep`, and the example classifiers `Control`, `ThreadLocal`, `IO` with the kind formers `only` and `except` |

`FCdot/` is the target calculus.  A rigid capability may declare a classifier, a capture atom may be
filtered, written `a ↾ φ`, and a telescope may carry the kinding proposition `C ⊑ᵏ φ` with evidence
`KindCo`.  The filter applies at the end of capture resolution, so subcapturing keeps its definition.
The two run-time theorems are here.

`DotMNF/` is the source calculus.  It gains the filtered atom, a capture member declared at a kind, a
binder that declares a classifier, and the kinding judgment `CapKind`.  Its examples are `Try.apply`,
`Future.apply`, and a client whose capture parameter is bounded by `only[Control]`.

`DotToFCdot/` is the translation.  It maps kinding derivations to kinding evidence and states the
source's classified theorems.  `Runtime.lean` is the untyped runtime both calculi erase to, and
`All.lean` imports everything.

## Building

`lake build Classifiers` builds the tree, and it is a default target.  Every theorem depends on
`propext` and `Quot.sound` at most.  There is no `sorry`, no `axiom` and no `native_decide`.
