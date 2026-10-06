# DotToFCdot with paths

The translation of DOT-MNF with paths (`../DotMNF`) into FCdot with path-keyed blocks
(`../FCdot`), in namespace `Paths.DotMNF`. As in the base, derivations are `Type`-valued, the
translation is a function on derivations, and DOT-MNF's type safety is transported from FCdot's.
New here: path typings translate to path evidence, a literal's binder gets the block forest its
definitions describe, and two acceptance tests from gDOT run on the result. Every translation
function is structurally recursive, so `decide +kernel` unfolds a translation and checks its image.

## Modules

| module | contents |
|---|---|
| `Types` | `Path.translate`, `Ty.translate`, `Ty.tel`, `Ty.telSelfAt`, `Ty.literalTy`, the block of a literal `Ty.blocks`, `Ctx.translate` |
| `TypesLemmas` | renaming and path substitution commute with the translation |
| `Evidence` | `Sub.translate`, `PathTy.translatePath`, `HasTy.translateAtom`, the literal coercion `litCo`, the alias reader `aliasOf` |
| `Terms` | `HasTy.translate`, `DefsTy.translateFields` |
| `Blocks` | `DefsTy.blocks_translate`: the source's block of a literal is the block the target builds |
| `EvidenceTyped` | typedness of `Evidence`, the context condition `Ctx.Wf` |
| `TermsTyped` | `HasTy.translate_typed`, `DefsTy.translateFields_typed`, `let_sngl_typed_letPath` |
| `Erasure` | `HasTy.translate_erase`, `coherence` |
| `Safety` | the simulation invariant `Simulated`, `dot_safety`, `dot_not_stuck` |
| `Consistency` | `reachable_consistent`, `reachable_realized` |
| `Examples` | Z1 to Z9: facts about translated derivations, decided in the kernel |
| `Pages` | the target side of the path examples of `../DotMNF/Examples.lean`, one namespace each |
| `Acceptance` | the two gDOT acceptance tests and the pDOT twin of the first |

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

`Ty.translate` reads the type only. The block of a literal's binder, `Ty.blocks T d`, also reads
the definitions: a field that holds a variable `y` gets a forwarding child to `y`, whatever its
declared type. A `trmObj` field gets the inner literal's block as a child.

## Stable fields

A plain field (`trm`) is cast to its block name by `EqCo.member` at the literal's self. That
evidence eliminates, so the target does not call the field stable. A stable field (`trmObj`) is
the inner literal cast by `litCo` and `EqCo.def`, which are table-only, so the target lists it.
Stability in the target is exactly `trmObj` in the source. `DefsTy.blocks_translate` checks that
the two block builders agree, under `Defs.Distinct d`.

## Main theorems

- `Sub.translate_typed`: a subtyping derivation becomes inclusion evidence between the images.
- `PathTy.translatePath_typed`: a path typing becomes path evidence at the translated path.
- `HasTy.translateAtom_typed`: a variable typing becomes an atom of the translated type.
- `HasTy.translate_typed`: a term typing becomes a typed FCdot term.
- `DefsTy.blocks_translate`: a literal's source block equals the block of its translation.
- `HasTy.translate_erase`, `coherence`: the image erases to the source term, so two derivations
  of one term behave the same.
- `dot_safety`, `dot_not_stuck`: a closed well-typed DOT-MNF program never gets stuck.
- `reachable_consistent`, `reachable_realized`: reachable stores are typed, have no closed
  `⊤ ≤ ⊥`, and define every block name.
- `acceptance_fig2`: the FCdot checker accepts the translation of gDOT's Fig. 2.
- `acceptance_gdot3`, `acceptance_gdot3_any`: no closed literal has type `μ(x. {A : ⊤..⊥})`.

Each of these that the base also proves keeps the base's statement.

## The gDOT acceptance tests

`acceptance_fig2` runs the checker on the translation of `Fig2_prog`, a fragment of the Dotty
compiler from gDOT's Fig. 2. Two nested literals, `types` and `symbols`, name each other through
the enclosing module. `acceptance_fig1` and its companions check the pDOT variant `Fig1_prog`.

`acceptance_gdot3_any` refutes gDOT's Sec. 3 counterexample for every closed literal. The source
has no inversion lemmas, so the proof translates the derivation, allocates the literal in a typed
store, and applies `Store.Typed.no_top_le_bot`. The claim is about literals, not terms:
`diverging_at_bad_bounds` is a closed term at the bad type, but its run reaches a state that
steps to itself (`div_reach`, `div_loop`), so it never allocates a literal at that type.

## Examples

Z1 to Z9 are kernel-decided facts about translated derivations. Z9 shows why the source leaves out
replacement and non-singleton uses of a singleton variable: no template reads an inclusion out of
a singleton (`no_le_out_of_sngl`) or rewrites an alias (`alias_template_fixed`). `Pages` checks
the translations of E1p to E8p, E9, E10, E11, P2e and P3e.
