# DotToFCdot

The translation of DOT-MNF into FCdot (Plan III §8, milestones M3 to M5),
namespace `DotMNF`.  Derivations are `Type`-valued, so the translation is a
function on derivations; typedness and erasure equality are theorems about
that function, and DOT-MNF's type safety is transported from FCdot's.

## Modules

| module | contents |
|---|---|
| `Types` | `Ty.translate`, `Ty.tel`/`Ty.telSelf` (a type as a telescope over a self block: declaration shapes proposition by proposition, everything else as one self-bound), the shape test `Ty.isObj` and `Ty.translate_isObj`/`Ty.tel_of_not_isObj`, `Ty.witnesses`, `Ty.fieldLabels`, `Ty.literalTy`, `Ctx.translate` |
| `TypesLemmas` | renaming and instantiation commute with the translation; `Ty.isDecl_rename`, `Ty.isObj_rename`; `Ty.translate_decl`; `Ty.tel_substVar` (opening a body at the root) |
| `Evidence` | `Sub.translate`, `HasTy.translateAtom`, `litCo` (the cast from a literal's precise type to its declaration type), `identityMorphism`, `into`/`intoAtom` (an operand put into its own telescope), `Ctx.varAtom` |
| `EvidenceTyped` | `Sub.translate_typed`, `HasTy.translateAtom_typed`, `HasTy.translateAtom_root`, `litCo_typed`, `Ctx.varAtom_typed`, `Ty.tel_closedBnds` (every self-bound the translation produces is closed); the well-formedness `Ctx.Wf` of contexts |
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

tel B        =  [ ⊑ ⟦B⟧↑ ]            B a selection, a function type, ⊥,
                                      or a μ whose body is not a declaration
```

Intersections are unrestricted: an operand that is not an object shape
contributes the single *self-bound* proposition `⊑ ⟦B⟧` of FCdot (plan §13
item 9).  `Ty.isObj` is the shape test that decides between the two: it
holds exactly when `⟦T⟧ = μ (tel T)`, and fails exactly when `tel T` is the
one-bound telescope above.  The bodies of `μ` stay restricted to `Ty.Decl`,
because a bound never mentions the self.

Subtyping: `Top/Bot/Refl/Trans` to the corresponding evidence; `And₁`,
`And₂` to object coercions with identity templates on one half when the
operand is an object shape (a self-bound of the source is copied by
`Morphism.bnd` over `LeCo.bound`), and to the bound cast `LeCo.bound` itself
when it is not; `And` to `pair`, each component first put into its
telescope by `into` (the identity on an object shape, `LeCo.intoBnd`
otherwise); `Fld`, `Typ` to object coercions whose templates route the
source proposition through the translated bound; `Sel-<:`, `<:-Sel` to
`member` at the atom on the exact proposition of the declaration; `All` to
`pi`.

Variable typings: `Var` is the variable, cast by `litCo` when the binder is a
literal's self; `Rec-I`/`Rec-E` unfold at the root and refold at the other
telescope; `And-I` is `both` on the two operands put into their telescopes
by `intoAtom` (a cast, so the root is unchanged); `Sub` is a cast.  Terms
follow the syntax; a projection carries its presence evidence and is cast
to the declared field type; an object literal becomes a literal with the witnesses of its
declaration type, each field cast to its block name by the literal's own
definition equality, the whole cast by `litCo`.

## Side conditions

Typedness holds for well-formed contexts, `Ctx.Wf`: a literal's self binder
(`Ctx.consSelf`) carries a declaration type of literal shape (exact type
members) with distinct labels, which is what `{}-I` produces.  The initial
context is empty, so `dot_safety` has no side condition.

The self-alias restriction is gone: `{}-I` no longer restricts which members'
witnesses may be a bare selection on the object's own self.  FCdot's
alias-tolerant resolution (`FCdot.Ctx.resolve`) follows same-block aliases —
a field typed `x.A` inside its own literal makes `x∙a` an alias of `x∙A`,
which now resolves like any other alias — and a cyclic alias resolves to `⊤`.

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

Axioms: `propext` and `Quot.sound` everywhere.  No
`sorry`, `axiom`, `partial`, or `native_decide`.
