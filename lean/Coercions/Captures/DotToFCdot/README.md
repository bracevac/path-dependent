# DotToFCdot with captures

The translation of DOT-MNF with captures into FCdot with captures, namespace `DotMNF`.  Derivations
are `Type`-valued, so the translation is a function on derivations, and typedness and erasure
equality are theorems about that function.  New relative to the vanilla translation: capture sets
translate atom by atom, a capture member becomes two inclusions on a capture name, and the source's
use-set evidence is translated too.  The source's safety, consistency and capture prediction are
all borrowed from the target through the translation.

## Modules

| module | contents |
|---|---|
| `Types` | `CapAtom.translate?`, `CaptureSet.translate`, `Shape.translate`, `Ty.translate`, `Ctx.translate`. `Shape.tel` and `Shape.telSelf` give a shape as a telescope over a self. `Shape.witnesses` and `Shape.capWitnesses` give the witnesses of a translated literal. `Shape.isObj` |
| `TypesLemmas` | renaming and instantiation commute with the translation |
| `Evidence` | `Subcap.translate`, `SubShape.translate`, `Sub.translate`, `HasTy.translateAtom`. `litCo`, the cast from a literal's precise type to its declared type. `identityMorphism`, `intoAtom`, `Ctx.varAtom` |
| `EvidenceTyped` | typedness of the evidence translation, and the well-formedness `Ctx.Wf` of contexts |
| `Terms` | `HasTy.translate`, `HasTy.translateUses` (the source's use-set evidence, read in the target), `DefsTy.translateFields` |
| `TermsTyped` | `HasTy.translate_typed`, `HasTy.translate_uses`, `DefsTy.translateFields_typed` |
| `Erasure` | `HasTy.translate_erase`, `coherence` |
| `Safety` | the simulation invariant `Simulated`, `dot_safety`, `dot_not_stuck` |
| `Consistency` | `reachable_consistent`, `reachable_realized` for runs of translated programs |
| `Prediction` | the platform prefix on both sides (`Platform.ctx`, `Platform.targetStore`), the matched run `Platform.simulatedRun`, `dot_capture_prediction`, `dot_effect_safety` |

## The translation

```text
S ^ C        ↦  ⟦S⟧ ^ ⟦C⟧             atom by atom, {x.C} ↦ {x∙C}, any dropped
□ T          ↦  □ ⟦T⟧
{a : S ^ C}  ↦  μ [ ∋ a , self∙a ⊑ ⟦S⟧↑ , {self∙a} ⊑ᶜ ⟦C⟧↑ ]
{C : c₁..c₂} ↦  μ [ ⟦c₁⟧↑ ⊑ᶜ {self∙C} , {self∙C} ⊑ᶜ ⟦c₂⟧↑ ]
```

The other shapes translate as in the vanilla translation.  A field's telescope gains a capture
entry beside its presence and its bound.  A box shape is not an object shape, so in an intersection
it contributes a self-bound.

Subcapturing goes to the target's capture sort.  `sc-var` becomes `capvar` at the translated atom,
and `sc-sel-lower` and `sc-sel-upper` become `member` at the lower or upper entry of the capture
member.  `Cap` becomes an object coercion of two capture templates, `Boxed` becomes `boxed`, and
`Capt` pairs the two halves.

A projection is cast to the field's declared shape and to its declared capture set.  A box and an
unboxing become the target's box and unboxing.  A literal records one capture witness per field and
per capture member, and each field is cast to its block name and to its capture name.

Use sets are the other half.  `HasTy.translateUses` is a second function on derivations, typed at
`uses ⟦h⟧ ⊑ ⟦U⟧`.  It supplies the closing evidence of a translated lambda and of each field of a
literal, the avoidance evidence of a translated let, and the premise of a translated unboxing.

`any` has no target atom.  `CapAtom.translate?` returns `none` on it, and `CaptureSet.translate`
drops it.  No typing rule reads `any`, and the front end expands it before typing.  A hand-built
derivation may still contain `any`, and no theorem covers what the translation does with it.

## Side conditions

Typedness holds for well-formed contexts, `Ctx.Wf`: a literal's self binder carries a declaration
shape with exact type members and distinct labels, which is what `{}-I` produces.  `dot_safety`
starts from the empty context and the prediction corollaries from a platform prefix.  Both are well
formed, so neither theorem has a side condition.  Same-block aliases are allowed, since FCdot's
alias-tolerant resolution follows them and resolves a cyclic alias to `⊤`.

## Main theorems

- `Subcap.translate_typed`, `SubShape.translate_typed`, `Sub.translate_typed`: evidence translates
  to typed evidence between the translated endpoints.
- `HasTy.translateAtom_typed`, `HasTy.translateAtom_root`: a variable typing becomes an atom of the
  translated type rooted at that variable.
- `HasTy.translate_typed`: over a well-formed context (`Ctx.Wf`), a typing derivation becomes a typed
  FCdot term.
- `HasTy.translate_uses`: over a well-formed context, the translated term's use set is below the
  translated declared use set.
- `HasTy.translate_erase`, `coherence`: a translated term erases to its source term, so two
  derivations of one term translate to terms with the same erasure.
- `dot_safety`, `dot_not_stuck`: a source program well-typed in the empty context never gets stuck.
  A program that uses a platform capability is not in the empty context.  `compile_safe` in
  `Frontend/Pipeline.lean` covers the compiled ones.
- `reachable_consistent`, `reachable_realized`: for a source program well-typed in the empty
  context, every store the target machine reaches from its translation is typed, has no closed
  `⊤ ≤ ⊥`, and defines every block name.
- `dot_capture_prediction`: along a source run over a platform prefix, some target state with the
  same erasure has a typed store extending the translated platform store, and its use set is
  below the translated declared use set, renamed along the extension.  The conclusion does not
  name the target run and does not require the term of that state to be typed.
- `dot_effect_safety`: let the declared use set omit a platform capability `κ`, and let a source
  run reach a state that reads `x`.  Then some target state with the same erasure and a typed
  store, extending the translated platform store, does not root `x` at the image of `κ` in that
  store.  The conclusion does not name the target run.

Two things changed form.  Every theorem about `HasTy U Γ t T` quantifies over the use set `U`.
`CapAtom.translate?` is partial, because the target has no atom for `any`.

Axioms: `propext` and `Quot.sound` at most.  No `sorry`, `axiom` or `native_decide`.
