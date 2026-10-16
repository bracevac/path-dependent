# FCdot with classifiers

This is the target calculus.  It is vanilla FCdot, where every use of subtyping, type equality and
field presence is a proof term that erases to nothing, extended in three layers.  Captures give a
type a capture set, `S ^ C`, give a term a use set, and add boxes.  The compiler's way makes every
lambda body and object body a scope with a root of its own, orders capabilities by level, adds the
universal root `⊤ᶜ`, and gives a result `fresh` an existential answer.  Classifiers, new in this
tree, let a rigid capability declare a classifier, let a capture atom be filtered by a kind, and add
a kinding proposition with its own evidence.  The first two layers are described in
`../../CapturesCC/FCdot/README.md`, and this README dwells on the third.

## How classifiers fit

- A classifier rides on a capture bound.  `CapBound.cls c` is a rigid capability with classifier
  `c`, and `star` is the same with the root classifier.
- `a ↾ φ` filters the atom `a` by the kind `φ`.  Resolution (`Ctx.caps`) carries the filter along,
  and expansion (`Ctx.expandAtom`, the last step of `Ctx.roots`) applies it.  Expansion yields
  unfiltered atoms, so `Ctx.roots`, `Ctx.Root` and `CapLe` keep their definitions.
- Classifiers and kinds are closed data.  They mention no variable, so renaming and substitution
  never touch them.
- The meaning of kinding is `Ctx.KindLe Γ C φ`: every root of `C` has a classifier that `φ` contains.
- Kinding evidence `KindCo` has ten rules.  A rule about one atom reads it through its base
  (`CapAtom.base`) and the kind it carries (`CapAtom.kindOf`), so one rule covers filtered and plain
  atoms alike.  Subcapturing gains three rules: drop a filter, add a filter to a kinded set, and
  filter both sides.
- A classified capability is opaque, and the machine allocates only non-opaque capture binders.  So
  classified capabilities sit in the platform prefix, and every capability a run allocates has the
  root classifier.
- An unwritten classifier means unknown.  A `star` binder is kinded only at a kind that admits every
  classifier.

## Modules

| module | contents |
|---|---|
| `Debruijn` | signatures with term and capture binders, bound variables, renamings |
| `Syntax` | shapes, types `S ^ C`, capture atoms with `⊤ᶜ` and `a ↾ φ`, capture sets with `CaptureSet.proj`, propositions with `C ⊑ᵏ φ`, answers `ETy`, the evidence families with `KindCo`, terms, values, renaming and substitution |
| `Context` | capture bounds with `cls`, contexts, levels as positions on the spine, the scope contexts `Ctx.scope`, `Ctx.body`, `Ctx.objBody`, `Ctx.scopeInst`, the readers `Ctx.classOf`, `Ctx.admitsB`, `Ctx.ClsOf`, `Ctx.SetOf` |
| `Typing` | every judgment, including kinding `Γ ⊢ᵏ g : C ⊑ᵏ φ` and the member-free predicates |
| `Store` | stores and store typing |
| `Normalizer` | head normal forms of closed evidence, views of atoms, the fuel-indexed normalizer, the kinding entries `Entry.kindC` and `Entry.kindCle` |
| `Machine` | continuations, states, the step relation, use sets `State.uses`, store extension `Store.Ext` with `Store.Ext.kindLe` |
| `Erasure` | erasure into the runtime |
| `RenameLemmas`, `TypingRename`, `Transparency`, `TypingSubst` | renaming and substitution, and their action on typing |
| `Preservation` | inversion lemmas and `preservation` |
| `ErasureMetatheory` | forward simulation `erase_step`, backward simulation `erase_reflect` |
| `Checker`, `CheckerCompleteness` | the checkers, `checkTm_iff`, and the kinding checker `checkKindCo` with `checkKindCo_iff_hasType` |
| `Resolution` | type resolution, capture resolution `Ctx.caps`, expansion, `Ctx.roots`, `CapLe`, `Ctx.KindLe` and its algebra |
| `LevelInversion` | `level_inversion`: member-free capture evidence never lowers a level |
| `Levels` | the order lemmas of levels and their weakening |
| `FormTyping`, `FormAlgebra` | typed normal forms, their composition and application, `kindCle_semantic` |
| `CanonicalForms` | canonical forms of all evidence, `cap_canon`, `kind_canon`, `atom_canon`, `mor_canon`, `preservation'` |
| `Progress` | `progress`, `not_stuck` |
| `Consistency` | shapes of closed inclusions, no closed `⊤ ≤ ⊥`, `lvl_canon`, `lvl_safety` and `no_inner_escape`, which hold trivially over a typed store |
| `Prediction` | `capture_prediction`, `effect_safety`, `classified_prediction`, `classified_effect_safety` |
| `Examples` | examples decided in the kernel, from the vanilla ones to the classifier examples |

## New notation

All notation is `scoped` in namespace `FCdot`.  Rows marked (k) are the classifier layer.

| | |
|---|---|
| `S ^ C`, `□ T` | a shape with a capture set, the box shape |
| `⊤ᶜ` | the universal root, the local root of the whole program |
| `a ↾ φ` (k) | the capture atom `a` filtered by the kind `φ` |
| `C ⊑ᶜ D`, `C ≐ᶜ D` | capture propositions in a telescope |
| `C ⊑ᵏ φ` (k) | kinding proposition: every capability `C` stands for has a classifier `φ` admits |
| `∃ᶜ[C] T` | an answer under one capture binder bounded by `C` |
| `Γ ⊢ˢ e : S ≤ T` | inclusion evidence between shapes |
| `Γ ⊢ᶜ f : C ⊑ D`, `Γ ⊢ᶜ φ : C ≡ D` | inclusion and equality evidence between capture sets |
| `Γ ⊢ᵏ g : C ⊑ᵏ φ` (k) | kinding evidence |
| `Γ ⊢ᵉ g : E ≤ E'`, `Γ ⊢ₚ p : E`, `Γ ⊢ t :ᵉ E`, `Γ ⊢ᵥᵉ v : E` | answers: inclusion, packed atoms, terms, values |
| `Γ ⊢ᶠ[A] F` | fields of a literal whose assigned capture set is `A` |
| `σ ⊢ e ⇓ˢ[n] F` | head form of a shape coercion |

## Main theorems

The classifier layer:

- `kind_canon`: over a typed store, closed kinding evidence for `C ⊑ᵏ φ` gives `Ctx.KindLe Γ C φ`.
- `classified_prediction`: a run from a typed state whose use set is kinded at `φ` (`Γ.KindLe`) keeps its use set kinded at `φ`, in every context that types the new store.
- `classified_effect_safety`: on such a run, with the stores typed, every root of a variable a step reads has a classifier `φ` admits.
- `checkKindCo_iff_hasType`: the kinding checker accepts exactly the derivable judgments.
- `Ctx.roots_proj`, `Ctx.Root_proj`: the roots of a filtered set are the roots of the set that the kind admits.
- `Ctx.kindLe_proj`: a filtered set is kinded at its own filter.
- `Ctx.KindLe.mono`, `Ctx.KindLe.sub`: kinding is antitone along subcapturing and monotone along subkinding.
- `Store.Ext.kindLe`: a kinding over a typed store survives an extension to a typed store.

Kept from the base with their statements: `checkTm_iff`, `cap_canon`, `atom_canon`, `preservation'`,
`progress`, `not_stuck`, `erase_step`, `erase_reflect'`, `capture_prediction`, `effect_safety`,
`level_inversion`.

Three more theorems of the base are kept and hold trivially over a typed store, which is the only
context they are stated over: `lvl_canon`, `lvl_safety` and `no_inner_escape`.  A typed store has no
scope root (`Store.Typed.rootFree`), so its only root is `⊤ᶜ` and every atom is at the outermost level.  The conclusions of `lvl_canon`
and `lvl_safety` then hold for every set.  The premise `¬ Γ.LvlLe (.cvar κ) r` of `no_inner_escape`
never holds.  `level_inversion` carries the content, for member-free evidence and without a store.  For source programs
`source_lvl_safety` (in `../DotToFCdot/`) does the same, and `W5_no_escape` in `Examples` instantiates it.

Base statements that changed form:

- `rigid_target` concludes about `Γ.roots` where it concluded about `Γ.caps`, which is stronger on unfiltered sets.  `lvl_canon` and `lvl_safety` changed the same way, and they hold trivially, as above.
- `Ctx.expandAtom_of_not_root`, `Ctx.expand_eq_self` assume the atoms are unfiltered (`a.base = a`), which every atom of the base is.
- `Ctx.caps_subset_roots`, `Ctx.Root.of_mem_caps`, `Ctx.roots_eq_caps_of_rootFree` read an atom through its base and its kind, and say what they said on unfiltered sets.

## Examples

`Examples` keeps every example of the base and adds two groups.  The `K1x_*` to `K6x_*` theorems
are small facts about resolution and kinding.  `K6x` marks the edge of the rules: a rigid capability
with no declared classifier is kinded at `except ThreadLocal` by the semantics (`K6x_kindLe`), while
the two rules that read a rigid binder, `kcls` and `kproj`, reject it (`K6x_kcls_reject`,
`K6x_kproj_reject`).  No theorem excludes the other rules.  The classifier examples `E1` (`Try.apply`, its body filtered to
`only[Control]`), `E2` (`Future.apply`, its body filtered to `except[ThreadLocal]`) and `E3` (a client
whose capture parameter is bounded by `only[Control]`) are the target half of the source programs.
`E1_effect_safety`, `E2_effect_safety` and `E3_prediction` apply the source theorems to them.  In
the runs of E1 and E2 the one variable that is read holds the closure of `Try.apply` or
`Future.apply`, whose capture set is empty.  By inspection of the terms, which no theorem states, that
variable has no root, so the conclusions of `E1_effect_safety` and `E2_effect_safety` hold there for
want of a root.  Those two examples show that the premises of the source theorems, a typed program and its
kinding evidence, are met.  They do not exercise the filter.  `E2_tl_not_capKind` shows that no source derivation kinds the
`ThreadLocal` capability of E2's platform (`E2tl`) at `except[ThreadLocal]`.

Every theorem depends on `propext` and `Quot.sound` at most.
