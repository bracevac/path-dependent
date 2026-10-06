# DotToFCdot, capture checking the compiler's way

The translation of the capturing source into the capturing target, namespace `DotMNF`.  As in the
vanilla line (`../../DotToFCdot/`), derivations are `Type`-valued, so the translation is a function
on derivations.  New here: capture sets translate atom by atom, a use set is carried by the
derivation and translated into the capture evidence the target's binders ask for, and the source's
scope roots, instance binders and `letex` map to the target's.  Source safety, capture prediction,
effect safety and level safety are all borrowed from the target.

| module | contents |
|---|---|
| `Types` | `CaptureSet.translate`, `Shape.translate`, `Ty.translate`, `ETy.translate`, the telescopes `Shape.tel` and `Shape.telSelf`, the shape test `Shape.isObj`, literal witnesses, `Ctx.translate` |
| `TypesLemmas` | renaming commutes with the translation, and `Ctx.translate` commutes with roots and levels (`Ctx.translate_lvl`, `Ctx.translate_root?`) |
| `TypesSubst` | the type translation commutes with substitution (`Ty.translate_subst`), which the application case needs |
| `Evidence` | `Subcap.translate`, `SubShape.translate`, `Sub.translate`, `ESub.translate`, `HasTy.translateAtom`, `litCo`, the source predicate `Subcap.MemberFree` |
| `EvidenceTyped` | typedness of the evidence translation, the well-formedness `Ctx.Wf`, and `source_lvl_safety` |
| `Terms` | `HasTy.translate` and `HasTy.translateUses`, the use-set evidence read in the target |
| `TermsTyped` | `HasTy.translate_typed`, `HasTy.translate_uses`, `DefsTy.translateFields_typed` |
| `Erasure` | `HasTy.translate_erase`, `coherence` |
| `Safety` | the simulation invariant `Simulated`, `dot_safety`, `dot_not_stuck` |
| `Consistency` | `reachable_consistent`, `reachable_realized` for runs of translated programs |
| `Prediction` | the platform prefix on both sides, the matched run `Platform.simulatedRun`, `dot_capture_prediction`, `dot_effect_safety` |

## The translation

```text
S ^ C          ↦  ⟦S⟧ ^ ⟦C⟧            atom by atom, x.C ↦ x∙C, any and fresh dropped
∃ᶜ[C₀] T       ↦  ∃ᶜ[⟦C₀⟧] ⟦T⟧
⊤              ↦  μ []
⊥, □ T, p.A    ↦  ⊥, □ ⟦T⟧, x ∙ A
∀(x : T) E     ↦  Π(⟦T⟧) ⟦E⟧            both sides bind the same capture binder
{A : S..T}     ↦  μ [ ⟦S⟧↑ ⊑ self∙A , self∙A ⊑ ⟦T⟧↑ ]
{a : S ^ C}    ↦  μ [ ∋ a , self∙a ⊑ ⟦S⟧↑ , {self∙a} ⊑ᶜ ⟦C⟧↑ ]
{C : c₁..c₂}   ↦  μ [ ⟦c₁⟧↑ ⊑ᶜ {self∙C} , {self∙C} ⊑ᶜ ⟦c₂⟧↑ ]
S ∧ T, μ(x. S) ↦  μ (tel S ++ tel T), μ (telSelf S)
```

An operand of an intersection that is not an object shape becomes the single self-bound `⊑ ⟦B⟧`.
`any` and `fresh` are dropped, which is sound because no source rule gives them meaning and an
expanded program holds neither.  The source has no universal root, so no translated set mentions
`⊤ᶜ` (`CaptureSet.top_not_mem_translate`).

Evidence follows the source rule by rule.  `Subcap.level` becomes `level`, `Subcap.inst` becomes
an `instC` equality, `Subcap.var` becomes `capvar`, and `selLower`, `selUpper` become `member`.
`ESub.pack` becomes the target's `pack`, and a source `letex` becomes a target `letex`.  A lambda,
a literal, a `let` and an unboxing carry the translated use set and the evidence
`HasTy.translateUses` builds for it.

Typedness needs a well-formed context, `Ctx.Wf`: a literal's self binder carries a declaration
shape with exact type members and distinct labels, as the literal rule `HasTy.obj` produces.  The
initial context of `dot_safety` is empty and that of the prediction theorems is a platform prefix.
Both are well formed, so neither theorem has a side condition.

## Main theorems

- `Subcap.translate_typed`, `Sub.translate_typed`, `ESub.translate_typed`: evidence translates to
  typed evidence.
- `HasTy.translate_typed`, `HasTy.translate_uses`: a term translates to a typed term whose use set
  is below the translated source use set.
- `HasTy.translate_erase`, `coherence`: the translation erases to the source term, whatever
  derivation it starts from.
- `dot_safety`, `dot_not_stuck`: a closed well-typed source program never gets stuck.
- `reachable_consistent`, `reachable_realized`: every store a translated program reaches is typed
  and consistent.
- `dot_capture_prediction`: along a run of a program over the platform prefix, the matched target
  state's use set stays below the program's declared use set.
- `dot_effect_safety`: a program whose use set does not name a platform capability never reads it.
- `source_lvl_safety`: source subcapturing that reads no capture bound never lowers a level.  It
  is `level_inversion` applied to a translated derivation.

`Subcap.MemberFree` excludes `inst`, `selLower` and `selUpper`, exactly the source rules whose
translation uses `eqToLe` or `member`.  So `Subcap.translate_memberFree` is a walk over the rules.

Statements of the base that changed form:

- `HasTy.translate`, `HasTy.translate_typed` and `coherence` are stated at an answer.  At a plain
  answer they are the base statements.
- `Platform.root_iff` asks that the set does not mention `⊤ᶜ`, which every translated set
  satisfies.

The examples of the translation live in `../FCdot/Examples.lean`.  `W2_translated` and
`W2_erase` show that a parameter `any` stays one arrow and one lambda in the target, so a call
needs no extra application.  `W5_no_escape` is `source_lvl_safety` at the `withFile` callback.
