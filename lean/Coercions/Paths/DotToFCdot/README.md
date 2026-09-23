# DotToFCdot, at stage P3 of paths

The translation of DOT-MNF with paths (`../DotMNF`) into FCdot with path-keyed blocks (`../FCdot`),
namespace `Paths.DotMNF`, stage P2 of `plan-5g-paths-stages.md`.  The translation is a function on
`Type`-valued derivations, and DOT-MNF's type safety is transported from FCdot's.  Every translation
function is structural (decision 31), so `decide +kernel` unfolds a translation and checks its image.

## Main theorems

```
Sub.translate_typed         : Γ.Wf → Γ.translate ⊢ d.translate : S.translate ≤ T.translate
PathTy.translatePath_typed  : Γ.Wf → Γ.translate ⊢ᵖ d.translatePath : T.translate ∧
                                d.translatePath.path = p.translate
HasTy.translateAtom_typed   : Γ.Wf → Γ.translate ⊢ₐ h.translateAtom : T.translate
HasTy.translate_typed       : Γ.Wf → Γ.translate ⊢ h.translate : T.translate
DefsTy.blocks_translate     : Defs.Distinct d →
                                T.blocks d = (Value.obj T.witnesses (h.translateFields .here Tself e)).blockSelf
let_sngl_typed_letPath      : Γ' ⊢ t : snglOf q → Γ'.cons (.opaque (snglOf q)) ⊢ u : U↑ → Γ' ⊢ let t u : U
HasTy.translate_erase       : ⌊h.translate⌋ = ⌊t⌋
coherence                   : ⌊d₁.translate⌋ = ⌊d₂.translate⌋
dot_safety                  : HasTy .nil t T → ⟨∅, ∅, t⟩ ⟶* st → st.Final ∨ ∃ st', st ⟶ st'
reachable_consistent        : HasTy .nil t T → ⟨∅, ∅, d.translate⟩ ⟶* st →
                                ∃ Γ, ⊢ st.σ : Γ ∧ ¬ ∃ e, Γ ⊢ e : ⊤ ≤ ⊥
acceptance_gdot3            : ¬ Nonempty (HasTy .nil (.val (.obj (.typ A S))) (.mu (.typ A .top .bot)))
acceptance_gdot3_any        : ¬ Nonempty (HasTy .nil (.val (.obj d)) (.mu (.typ A .top .bot)))
acceptance_fig2             : FCdot.checkTm FCdot.Ctx.nil Examples.Fig2_prog_ty.translate Ty.top.translate = true
```

Beside them: `SelfFree.translate_typed`, `SubDecl.translate_typed`, `HasTy.translateAtom_root`,
`litCo_typed`, `Ctx.varAtom_typed`, `DefsTy.translateFields_typed`, `dot_not_stuck`,
`reachable_realized`.  `HasTy.translate_typed`, `HasTy.translate_erase`, `coherence`, `dot_safety`,
`dot_not_stuck`, `reachable_consistent` and `reachable_realized` keep vanilla's statements.
`diverging_at_bad_bounds`, `div_reach` and `div_loop` are the extent of `acceptance_gdot3_any`
beyond the sketch's own statement: a closed term at the bad type exists and never allocates one.
`acceptance_fig1` and its three companions are P1e's twins of `acceptance_fig2`.

## Modules

| module | contents |
|---|---|
| `Types` | `Path.translate`, `Ty.translate`, `Ty.tel`, `Ty.telSelfAt`, `Ty.isObj`, `Ty.witnesses`, `Ty.fieldLabels`, `Ty.valLabels`, `Ty.literalTy`.  The block builder `Defs.childrenOver`, `Tm.childOf`, `Value.childOf`, `Ty.blocks`.  `Ctx.translate` |
| `TypesLemmas` | renaming, substitution and path substitution commute with the translation |
| `Evidence` | `identityMorphism` at any signature, `intoPath`, `aliasOf`, `litMorphism` and `litCo`, `Ty.typIdx`, `Ty.fldIdx`, `Ty.vfldIdx`.  `SelfFree.translate`, `SubDecl.translate`, `Sub.translate`, `PathTy.translatePath`, `HasTy.translateAtomAt` |
| `EvidenceTyped` | the typing of `Evidence`.  `Ty.EqSpec`, `Ty.HasSpec`, `Ty.ValSpec`, `litMorphism_tableOnly`, `Ctx.Wf` |
| `Terms` | `HasTy.translate`, `DefsTy.translateFields` |
| `Blocks` | `DefsTy.blocks_translate` from its three parts, `translateFields_labels`, `_valLabels`, `_children` |
| `TermsTyped` | `HasTy.translate_typed`, `DefsTy.translateFields_typed`, `let_sngl_typed_letPath` |
| `Erasure` | `HasTy.translate_erase`, `DefsTy.translateFields_erase`, `coherence` |
| `Safety` | `Simulated`, `dot_safety`, `dot_not_stuck` |
| `Consistency` | `reachable_consistent`, `reachable_realized` |
| `Examples` | Z1 to Z9, facts about images decided in the kernel, and the erasure equations of Z1, Z2, Z3, Z7 |
| `Pages` | P3's `E1p` to `E8p`, `E9`, `E10`, `E11`, `P2e`, `P3e` moved onto the target, one sub-namespace per example, each checking `../DotMNF/Examples.lean`'s source pages |
| `Acceptance` | P3's two acceptance tests: gDOT Fig. 2 with the `Option` encoding (`acceptance_fig2`) and its pDOT twin P1e (`acceptance_fig1`), and gDOT's Sec. 3 counterexample refuted for every literal (`acceptance_gdot3`, `acceptance_gdot3_any`), with the diverging closed term that never allocates one |

## The translation of types

```text
⊤              ↦  μ []
⊥              ↦  ⊥
p.A            ↦  p ∙ A                   (A in the block of the path p)
∀(x : S) T     ↦  Π(⟦S⟧) ⟦T⟧
{A : S..T}     ↦  μ [ ⟦S⟧↑ ⊑ self∙A , self∙A ⊑ ⟦T⟧↑ ]
{a : T}        ↦  μ [ ∋ a , self∙a ⊑ ⟦T⟧↑ ]
{val a : T}    ↦  μ [ ∋ a , ∋ᵛ a , self∙a ⊑ ⟦T⟧↑ ]
p.type         ↦  μ [ ≈ p↑ ]
S ∧ T          ↦  μ (tel S ++ tel T)
μ(x. T)        ↦  μ (telSelf T)
```

`Ty.translate` reads the type only (decision 30).  A binder of `cons` is opaque.  The self binder of
`consSelf d T` is transparent at `T.literalTy` with the block `T.blocks d`.

## The block of a literal

`Ty.blocks T d` is the witnesses, the field labels, the stable labels, and one child per field that
gives one.  It reads the definitions, since a field that holds a variable `y` gets the child
`.fwd (.var y)` whatever it is declared at.  A `trmObj` field gives the inner literal's block at
`p.a`, and a `trm` field gives no other child.  `DefsTy.blocks_translate` equates it with the block
the store builds from the translated fields.  Its premise `Defs.Distinct d` is there because
`Fields.valLabels` drops a label a later field repeats and `Ty.valLabels` does not.

## Decision 26's cast

A `trm` field is cast by `eqToLe (symm (member (var self) (refl Tself) e))`, where `e` is the field's
`≐` entry in the literal's precise telescope.  It reads the equation `def self a` reads, so the field
has the same type and erasure, but it eliminates, so the target does not call the body stable.  A
`trmObj` field is the inner literal cast by `litCo` and `eqToLe (symm (def self a))`, both
table-only, so it is stable.  Stability in the target is `trmObj` in the source.  With `def` at a
`trm` literal body the two block builders disagree (`Z1.FPuniform_disagrees`).

## The four source restrictions

P2 restricts four rules of P0 that have no image here (`../DotMNF/README.md`, P2.0).

- **R1, decision 23.**  `letSngl` is a derived `let` over a field declared at `{a : q.type}`.  Loses a
  `let` over any other field with the binder at the singleton of the field's path.
- **R2, decision 27.**  `trmSngl` and `trmLam` are derived at a plain field, and only `trmObj`
  declares `{val a : _}`.  Loses `{val a = y}` at `{val a : y.type}`, `{val f = λ…}` at
  `{val f : ∀…}`, and every path typing at `x.a` and below for such a field.
- **R3, decision 28.**  The base's variable rules are term rules, the bridge is `HasTy.sngl` at a
  singleton, and `projP` projects from a path typing.  Loses a singleton-typed variable used as a
  term at a type of its alias that is not a singleton (`Z9.no_le_out_of_sngl`).
- **R4, decision 29.**  `Sub.repl` and `Sub.replSym` are removed.  Loses `p.type <: q.type` and
  `p.A <: q.A` at an abstract member (`Z9.alias_template_fixed`).  At an exact member it stays
  (`Z7.E3_checks`).

## Axioms

`propext` and `Quot.sound` everywhere.  No `sorry`, `axiom`, `partial`, `unsafe` or `native_decide`.
