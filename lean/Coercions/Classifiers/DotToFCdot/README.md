# DotToFCdot with classifiers

The translation of the source `../DotMNF` into the target `../FCdot`, in namespace `DotMNF`.
Derivations are `Type` valued, so the translation is a function on derivations, and typedness and
erasure equality are theorems about that function.  The source's type safety, capture prediction
and classified theorems are carried over from the target's.  New relative to the vanilla
translation are the capture layer, described in `../../CapturesCC/DotToFCdot/README.md`, and the
classifier layer: a filtered atom becomes a filtered atom, a kind-bounded member becomes a kinding
proposition, and a source kinding derivation becomes target kinding evidence.

## Modules

| module | contents |
|---|---|
| `Types` | the atom map `CapAtom.translate?`, `CaptureSet.translate` with `CaptureSet.translate_proj`, `Shape.translate`, `Ty.translate`, `ETy.translate`, shapes as telescopes `Shape.tel` and `Shape.telSelf`, `CaptureSet.NoProj`, `Ctx.translate` |
| `TypesSubst` | the type translation commutes with substitution |
| `TypesLemmas` | renaming and instantiation commute with the translation |
| `Evidence` | the translation of subcapturing, subtyping, answer inclusion and kinding (`CapKind.translate`), atoms of variable typings, `litCo`, `Ctx.varAtom` |
| `EvidenceTyped` | typedness of all evidence the translation produces, the context well-formedness `Ctx.Wf`, `source_lvl_safety` |
| `Terms` | `HasTy.translate`, and `HasTy.translateUses`, which reads the source's use sets as target capture evidence |
| `TermsTyped` | `HasTy.translate_typed`, `HasTy.translate_uses` |
| `Erasure` | `HasTy.translate_erase`, `coherence` |
| `Safety` | the simulation invariant `Simulated`, `dot_safety`, `dot_not_stuck` |
| `Consistency` | `reachable_consistent`, `reachable_realized` for runs of translated programs |
| `Prediction` | platforms on both sides (`Platform.ctx`, `Platform.targetStore`, `Platform.classOf_translate`, `Platform.admits_iff`), and the capture and classified theorems for source programs |

## The classifier clauses

```text
a ↾ φ        ↦  ⟦a⟧ ↾ φ                     a filter stays a filter
any, fresh   ↦  (dropped)                   the target has no atom for them
{C : φ}      ↦  μ [ {self∙C} ⊑ᵏ φ ]          one kinding proposition
consCls Γ c  ↦  consC ⟦Γ⟧ (cls c)            a classified capture bound
CapKind      ↦  KindCo                       rule by rule
```

A kinding rule at a dropped atom translates to `KindCo.nil`, which is the right answer, since the
translated set is empty.  `SubShape.capkI`, which retypes a set-bounded member at a kind bound,
translates to the morphism `Morphism.kindCle`: it reads the member's upper bound and appends the
closed kinding of that bound.

Typedness holds for well-formed contexts, `Ctx.Wf`.  A platform context is well formed
(`Platform.ctx_wf`), so the theorems over a platform have no side condition.

## Main theorems

The `translate_typed` and `translate_uses` theorems assume `Ctx.Wf` of the source context.

- `CapKind.translate_typed`: a source kinding derivation translates to typed target kinding evidence.
- `Subcap.translate_typed`, `Sub.translate_typed`, `ESub.translate_typed`: the same for subcapturing, subtyping and answer inclusion.
- `HasTy.translate_typed`: a typed source term translates to a typed target term.
- `HasTy.translate_uses`: the translated term's use set is below the translated declared use set.
- `HasTy.translate_erase`, `coherence`: the translation erases to the source term, whatever the derivation.
- `dot_safety`, `dot_not_stuck`: a closed typed source program never gets stuck.
- `reachable_consistent`, `reachable_realized`: every store a translated closed program reaches is typed, proves no `⊤ ≤ ⊥`, and defines every block name.
- `source_lvl_safety`: member-free source subcapturing never lowers a level.
- `dot_capture_prediction`, `dot_effect_safety`: capture prediction and effect safety for source programs over a platform.
- `dot_classified_prediction`: if the declared use set of a source program typed over a platform is kinded at `φ`, the use set of the target state matched to every reached source state is kinded at `φ`.
- `dot_classified_effect_safety`: along a run of such a program from the platform's initial state, every root of a variable the matched target state reads has a classifier `φ` admits.
- `dot_classified_prediction'`, `dot_classified_effect_safety'`: the same, with a source derivation `CapKind P.ctx U φ` as the hypothesis.

Base statements that changed form:

- `dot_effect_safety` assumes that the platform capability is not a root of the translated use set, where it assumed it is not a member. With a filter the membership form is false. `Platform.not_root_of_not_mem` recovers the old form on unfiltered programs.
- `CaptureSet.base_of_mem_translate` assumes `C.NoProj`, which every unfiltered set satisfies.

The examples of this directory live in `../FCdot/Examples.lean`, which imports it.  There,
`E1_effect_safety` and `E2_effect_safety` instantiate `dot_classified_effect_safety'`, and
`E3_prediction` and `E3_prediction'` instantiate the two prediction theorems.  In E1 and E2 the
variable that is read holds a closure with the empty capture set, so the conclusion of the two
effect safety instances holds there for want of a root, as `../FCdot/README.md` says.

Every theorem depends on `propext` and `Quot.sound` at most.
