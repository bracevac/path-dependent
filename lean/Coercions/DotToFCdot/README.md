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
| `Evidence` | `Sub.translate`, `HasTy.translateAtom`, `litCo` (the cast from a literal's precise type to its declaration type), `identityMorphism`, `into`/`intoAtom` (an operand put into its own telescope), `recIAtom`/`recEAtom` (arbitrary recursive bodies), `Ctx.varAtom` |
| `EvidenceTyped` | `Sub.translate_typed`, `HasTy.translateAtom_typed`, `HasTy.translateAtom_root`, `litCo_typed`, `Ctx.varAtom_typed`, `Ty.tel_closedBnds` (bounds in `tel` are weakened under its fresh self); the well-formedness `Ctx.Wf` of contexts |
| `Terms` | `HasTy.translate`, `DefsTy.translateFields` |
| `TermsTyped` | `HasTy.translate_typed`, `DefsTy.translateFields_typed` |
| `Erasure` | `HasTy.translate_erase` (`⌊h.translate⌋ = ⌊t⌋`), `coherence` |
| `Safety` | the simulation invariant `Simulated`, `dot_safety`, `dot_not_stuck` |
| `Consistency` | `reachable_consistent`, `reachable_realized` for runs of translated programs |
| `Examples` | translated typedness and erasure regressions for E9 to E12 |
| `WadlerFest` | composed translation, typedness, erasure, and safety for the annotated WadlerFest store machine |
| `RetainedSafety` | safety for every retained-let reduction order, using the operational correspondence with the annotated machine |
| `SortedSafety` | typed translation, exact erasure, and retained-let safety for the public WadlerFest syntax with distinct type and term labels |

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
one-bound telescope above. Neither test restricts the source language.
In particular, recursive bodies may be functions, selections, arbitrary
intersections, or nested recursive types.

The distinction between `tel` and `telSelf` matters here. A bound in `tel B`
is weakened under a fresh self binder. A bound in `telSelf T` can mention
the recursive self. To translate recursive elimination at a variable `x`,
`recEAtom` opens the recursive telescope at `x`, refolds it as `tel (T[x/z])`,
and extracts its bound when the result is not an object shape. Recursive
introduction reverses this construction: `recIAtom` puts the operand into
its telescope before changing the self binder. `Ty.tel_substVar` proves
that the two opened telescopes agree. Both adapters preserve the root and
erase to the original operand. This extension uses the existing target
typing rules and safety proof.

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
literal's self; `Rec-I`/`Rec-E` use the adapters above; `And-I` is `both` on
the two operands put into their telescopes
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
