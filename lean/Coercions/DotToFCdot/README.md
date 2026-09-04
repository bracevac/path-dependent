# DotToFCdot

The translation of DOT-MNF into FCdot (Plan III §8, milestones M3 to M5),
namespace `DotMNF`.  Derivations are `Type`-valued, so the translation is a
function on derivations; typedness and erasure equality are theorems about
that function, and DOT-MNF's type safety is transported from FCdot's.

## Modules

| module | contents |
|---|---|
| `Types` | `Ty.translate`, `Ty.tel`/`Ty.telSelf` (declaration-shaped types as telescopes over a self block), `Ty.witnesses`, `Ty.fieldLabels`, `Ty.literalTy`, `Ctx.translate` |
| `TypesLemmas` | renaming and instantiation commute with the translation; `Ty.translate_decl`; `Ty.tel_substVar` (opening a body at the root) |
| `Evidence` | `Sub.translate`, `HasTy.translateAtom`, `litCo` (the cast from a literal's precise type to its declaration type), `identityMorphism`, `Ctx.varAtom` |
| `EvidenceTyped` | `Sub.translate_typed`, `HasTy.translateAtom_typed`, `HasTy.translateAtom_root`, `litCo_typed`, `Ctx.varAtom_typed`; the well-formedness `Ctx.Wf` of contexts |
| `Terms` | `HasTy.translate`, `DefsTy.translateFields` |
| `TermsTyped` | `HasTy.translate_typed`, `DefsTy.translateFields_typed` |
| `Erasure` | `HasTy.translate_erase` (`⌊h.translate⌋ = ⌊t⌋`), `coherence` |
| `Safety` | the simulation invariant `Simulated`, `dot_safety`, `dot_not_stuck` |
| `Consistency` | `reachable_consistent`, `reachable_realized` for runs of translated programs |

## The translation

```text
⊤            ↦  μ []                    (the empty object type)
⊥            ↦  ⊥
p.A          ↦  x ∙ A
∀(x : S) T   ↦  Π(⟦S⟧) ⟦T⟧
{A : S..T}   ↦  μ [ ⟦S⟧↑ ⊑ self∙A , self∙A ⊑ ⟦T⟧↑ ]
{a : T}      ↦  μ [ ∋ a , self∙a ⊑ ⟦T⟧↑ ]
S ∧ T        ↦  μ (tel S ++ tel T)
μ(x. T)      ↦  μ (telSelf T)         (the body's self is the object's self)
```

Subtyping: `Top/Bot/Refl/Trans` to the corresponding evidence; `And₁`,
`And₂` to object coercions with identity templates on one half; `And` to
`pair`; `Fld`, `Typ` to object coercions whose templates route the source
proposition through the translated bound; `Sel-<:`, `<:-Sel` to `member` at
the atom on the exact proposition of the declaration; `All` to `pi`.

Variable typings: `Var` is the variable, cast by `litCo` when the binder is a
literal's self; `Rec-I`/`Rec-E` unfold at the root and refold at the other
telescope; `And-I` is `both`; `Sub` is a cast.  Terms follow the syntax; a
projection carries its presence evidence and is cast to the declared field
type; an object literal becomes a literal with the witnesses of its
declaration type, each field cast to its block name by the literal's own
definition equality, the whole cast by `litCo`.

## Side conditions

Typedness holds for well-formed contexts, `Ctx.Wf`: a literal's self binder
(`Ctx.consSelf`) carries a declaration type of literal shape (exact type
members) with distinct labels, which is what `{}-I` produces.  The initial
context is empty, so `dot_safety` has no side condition.

DOT-MNF's `{}-I` requires the declaration type to be guarded (`Ty.Guarded`):
no member's witness is a bare selection on the object's own self, including
the declared type of a field.  A field typed `x.A` inside its own literal
would make `x∙a` an alias of `x∙A`, which FCdot's resolution forbids; the
derivation can always type the field at the definition of `A` instead.

Fields of an intersection are translated with the right conjunct outermost,
matching DOT-MNF's shadowing and its erasure.

## Main theorems

```
Sub.translate_typed      : Γ.Wf → Γ.translate ⊢ d.translate : S.translate ≤ T.translate
HasTy.translateAtom_typed: Γ.Wf → Γ.translate ⊢ₐ h.translateAtom : T.translate
HasTy.translateAtom_root : h.translateAtom.root = x
HasTy.translate_typed    : Γ.Wf → Γ.translate ⊢ h.translate : T.translate
HasTy.translate_erase    : ⌊h.translate⌋ = ⌊t⌋
coherence                : ⌊d₁.translate⌋ = ⌊d₂.translate⌋
dot_safety               : HasTy .nil t T → ⟨∅, ∅, t⟩ ⟶* st → st.Final ∨ ∃ st', st ⟶ st'
reachable_consistent     : HasTy .nil t T → ⟨∅, ∅, d.translate⟩ ⟶* st →
                             ∃ Γ, ⊢ st.σ : Γ ∧ ¬ ∃ e, Γ ⊢ e : ⊤ ≤ ⊥
reachable_realized       : … ∧ ∀ x ℓ, ∃ W, Γ.lookupDef x ℓ = some W ∧ Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W
```

Axioms: `propext` and `Quot.sound` for typedness and erasure;
`Classical.choice` additionally in `dot_safety` and the reachability
corollaries, inherited from FCdot's `progress` and `erase_reflect'`.  No
`sorry`, `axiom`, `partial`, or `native_decide`.
