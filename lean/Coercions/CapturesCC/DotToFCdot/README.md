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
| `TypesSubst` | the type translation commutes with agreeing substitutions (`Ty.translate_subst`), which the application case needs |
| `Evidence` | `Subcap.translate`, `SubShape.translate`, `Sub.translate`, `ESub.translate`, `HasTy.translateAtom`, `litCo`, the source predicate `Subcap.MemberFree` |
| `EvidenceTyped` | typedness of the evidence translation, the well-formedness `Ctx.Wf`, `source_lvl_safety`, and `Subcap.memberFree_of_plain` |
| `Terms` | `HasTy.translate` and `HasTy.translateUses`, the use-set evidence read in the target |
| `TermsTyped` | `HasTy.translate_typed`, `HasTy.translate_uses`, `DefsTy.translateFields_typed` |
| `Erasure` | `HasTy.translate_erase`, `coherence` |
| `Safety` | the simulation invariant `Simulated`, `dot_safety`, `dot_not_stuck` |
| `Consistency` | `reachable_consistent`, `reachable_realized` for runs of translated programs |
| `Prediction` | the platform prefix on both sides, the matched run `Platform.simulatedRun`, `dot_capture_prediction`, `dot_effect_safety`, `dot_safety_platform` |

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

- `Subcap.translate_typed`, `Sub.translate_typed`, `ESub.translate_typed`: over a well-formed
  context, evidence translates to typed evidence.
- `HasTy.translate_typed`, `HasTy.translate_uses`: over a well-formed context, a term translates to
  a typed term whose use set is below the translated source use set.
- `HasTy.translate_erase`, `coherence`: the translation erases to the source term, whatever
  derivation it starts from.
- `dot_safety`, `dot_not_stuck`: a closed well-typed source program at a plain answer never gets
  stuck.  A closed program at an existential answer is not covered.
- `dot_safety_platform`: the same for a program at a plain answer over a platform prefix, run
  from the platform's initial store.
- `reachable_consistent`, `reachable_realized`: for a closed program at a plain answer, every
  store its translation reaches is typed and consistent.
- `dot_capture_prediction`: along a run of a program at a plain answer over the platform prefix,
  there is a typed target state that the run of the translated program reaches from its initial
  state, with the source state's erasure.  Its store extends the platform's along a renaming, and
  its use set stays below the translation of the program's declared use set, renamed.
- `dot_effect_safety`: for a program at a plain answer whose use set does not name a platform
  capability, at a source state that reads a variable, there is such a target state, and in it the
  capability, renamed, is not a root of that variable.
- `source_lvl_safety`: over a well-formed context, for source subcapturing that reads no capture
  bound, if the resolution of the translated upper set is confined to `r` at every depth, so is the
  resolution of the translated lower set.  It is `level_inversion` applied to a translated
  derivation.

`Subcap.MemberFree` excludes `inst`, `selLower` and `selUpper`, exactly the source rules whose
translation uses `eqToLe` or `member`.  So `Subcap.translate_memberFree` is a walk over the rules.
`Subcap.memberFree_of_plain`: in a context with no instance binder whose variables are declared at
shapes with no member declaration, every subcapturing is member free.

Statements of the base that changed form:

- `HasTy.translate`, `HasTy.translate_typed` and `coherence` are stated at an answer.  At a plain
  answer they are the base statements.  The machine theorems above are stated at a plain answer
  only.
- `Platform.root_iff` asks that the set does not mention `⊤ᶜ`, which every translated set
  satisfies.

The examples of the translation live in `../FCdot/Examples.lean`.  `W2_translated` types the
translation of the `W2` term at the translated type, and `W2_erase` equates its erasure with the
source term.  The translated type is one arrow (`Shape.translate_all`).  `W5_no_escape` says that
no subcapturing derivation at the `withFile` callback puts its parameter below the platform
capability, by `Subcap.memberFree_of_plain` and `source_lvl_safety`.
