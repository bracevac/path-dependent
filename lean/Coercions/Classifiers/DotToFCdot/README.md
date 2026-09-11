# DotToFCdot, at stage B3 of captures the compiler's way (Classifiers copy, unchanged)

The translation of DOT-MNF^cc into FCdot^cc (Plan III §8, milestones M3 to
M5), namespace `DotMNF`.  Derivations are `Type`-valued, so the translation
is a function on derivations; typedness and erasure equality are theorems
about that function, and DOT-MNF's type safety, consistency and capture
prediction are all transported from FCdot's.

## Modules

| module | contents |
|---|---|
| `Types` | `CapAtom.translate?` and `CaptureSet.translate` (atom by atom, the source's `sel x C` becoming the target's name `x∙C`, `any` and `fresh` dropped), `Shape.translate`, `Ty.translate` (`⟦S ^ C⟧ = ⟦S⟧ ^ ⟦C⟧`) and `ETy.translate`, `Shape.tel`/`Shape.telSelf` (a shape as a telescope over a self block: declaration shapes proposition by proposition, everything else as one self-bound), the shape test `Shape.isObj` and `Shape.translate_isObj`/`Shape.tel_of_not_isObj`, `Shape.witnesses`, `Shape.capWitnesses`, `Shape.fieldLabels`, `Shape.literalShape`, `Shape.literalTy`, `Ctx.translate` |
| `TypesSubst` | the type translation commutes with substitution, and the two agreements `Subst.singleC` and `Subst.arg` that the `app` case of `HasTy.translate_typed` consumes |
| `TypesLemmas` | renaming and instantiation commute with the translation; `Shape.isDecl_rename`, `Shape.isObj_rename`; `Shape.translate_decl`; `Shape.tel_substVar` (opening a body at the root) |
| `Evidence` | `Subcap.translate`, `SubShape.translate`, `Sub.translate`, `ESub.translate`, `HasTy.translateAtom`, `litCo` (the cast from a literal's precise type to its declaration type), `identityMorphism`, `into`/`intoAtom` (an operand put into its own telescope), `Ctx.varAtom` |
| `EvidenceTyped` | `Subcap.translate_typed`, `SubShape.translate_typed`, `Sub.translate_typed`, `ESub.translate_typed`, `HasTy.translateAtom_typed`, `HasTy.translateAtom_root`, `litCo_typed`, `litCo_atC_typed`, `Ctx.varAtom_typed`, `Shape.tel_closedBnds` (every self-bound the translation produces is closed); the well-formedness `Ctx.Wf` of contexts |
| `Terms` | `HasTy.translate`, `HasTy.translateUses` (the source's own use-set evidence, read in the target), `DefsTy.translateFields`, `fieldBody` |
| `TermsTyped` | `HasTy.translate_typed`, `HasTy.translate_uses`, `HasTy.translate_uses_atom`, `DefsTy.translateFields_typed` |
| `Erasure` | `HasTy.translate_erase` (`⌊h.translate⌋ = ⌊t⌋`), `coherence` |
| `Safety` | the simulation invariant `Simulated`, `dot_safety`, `dot_not_stuck` |
| `Consistency` | `reachable_consistent`, `reachable_realized` for runs of translated programs |
| `Prediction` | the platform prefix on both sides (`Platform.ctx`, `Platform.targetStore`, `Platform.store_erase`, `Platform.root_iff`), the matched run `Platform.simulatedRun`, and the two corollaries `dot_capture_prediction` and `dot_effect_safety` |

## The translation

```text
S ^ C        ↦  ⟦S⟧ ^ ⟦C⟧              capture sets atom by atom, sel x C ↦ x∙C, any dropped
⊤            ↦  μ []                    (the empty object type)
⊥            ↦  ⊥
p.A          ↦  x ∙ A
∀(x : T) T'  ↦  Π(⟦T⟧) ⟦T'⟧
□ T          ↦  □ ⟦T⟧
{A : S..T}   ↦  μ [ ⟦S⟧↑ ⊑ self∙A , self∙A ⊑ ⟦T⟧↑ ]
{a : S ^ C}  ↦  μ [ ∋ a , self∙a ⊑ ⟦S⟧↑ , {self∙a} ⊑ᶜ ⟦C⟧↑ ]
{C : c₁..c₂} ↦  μ [ ⟦c₁⟧↑ ⊑ᶜ {self∙C} , {self∙C} ⊑ᶜ ⟦c₂⟧↑ ]
S ∧ T        ↦  μ (tel S ++ tel T)
μ(x. S)      ↦  μ (telSelf S)         (the body's self is the object's self)

tel B        =  [ ⊑ ⟦B⟧↑ ]            B a selection, a function shape, a box, ⊥,
                                      or a μ whose body is not a declaration
```

Intersections are unrestricted: an operand that is not an object shape
contributes the single *self-bound* proposition `⊑ ⟦B⟧` of FCdot (plan §13
item 9).  `Shape.isObj` is the shape test that decides between the two: it
holds exactly when `⟦S⟧ = μ (tel S)`, and fails exactly when `tel S` is the
one-bound telescope above.  The bodies of `μ` stay restricted to
`Shape.Decl`, because a bound never mentions the self.

Subcapturing: `refl`, `trans`, `elem` and `union` to their namesakes in the
target's capture sort; `sc-var` to `capvar` at the translated atom;
`sc-sel-lower` and `sc-sel-upper` to `member` in the capture sort, at the
lower or the upper entry of the capture member's telescope.

Subtyping: `Top/Bot/Refl/Trans` to the corresponding evidence; `And₁`,
`And₂` to object coercions with identity templates on one half when the
operand is an object shape (a self-bound of the source is copied by
`Morphism.bnd` over `LeCo.bound`), and to the bound cast `LeCo.bound` itself
when it is not; `And` to `pair`, each component first put into its
telescope by `into` (the identity on an object shape, `LeCo.intoBnd`
otherwise); `Fld`, `Typ` to object coercions whose templates route the
source proposition through the translated bound, the field's capture entry
routed by the capture half of its premise; `Cap` to an object coercion of two
capture templates, each with the closed side of its subcapturing premise;
`Boxed` to `boxed`; `Sel-<:`, `<:-Sel` to `member` at the atom on the exact
proposition of the declaration; `All` to `pi`; `Capt` to `capt` of the two
halves.

Variable typings: `Var` is the variable, recaptured at its own root and cast
by `litCo` when the binder is a literal's self; `Rec-I`/`Rec-E` unfold at the
root and refold at the other telescope; `And-I` is `both` on the two operands
put into their telescopes by `intoAtom` (a cast, so the root is unchanged);
`Sub` is a cast.  Terms follow the syntax; a projection carries its presence
evidence and is cast to the declared field type and to the declared capture
set; a box becomes a target box and an unboxing a target unboxing, carrying
the declared use set and the translated subcapturing premise; an object
literal becomes a literal with the witnesses and the capture witnesses of its
declaration shape, each field cast to its block name and to its capture name
by the literal's own definitions, the whole cast by `litCo`.

Use sets are the other half of the term translation.  The source carries a
use set of its own, so a second function on derivations, `HasTy.translateUses`,
produces the capture evidence the target's binders ask for: a translated
lambda declares `⟦U⟧` and takes the body's evidence as its closing evidence,
a translated literal declares `⟦U⟧` and each field takes its body's evidence,
a translated let declares `⟦U⟧` and takes the body's evidence as its
avoidance evidence, and a translated unboxing declares `⟦U⟧` and takes the
translated subcapturing premise.

## Side conditions

Typedness holds for well-formed contexts, `Ctx.Wf`: a literal's self binder
(`Ctx.consSelf`) carries a declaration shape of literal shape (exact type
members) with distinct labels, which is what `{}-I` produces.  The initial
context of `dot_safety` is empty and the initial context of the two
prediction corollaries is a platform prefix, and both are well formed, so
neither theorem has a side condition.

The self-alias restriction is gone: `{}-I` no longer restricts which members'
witnesses may be a bare selection on the object's own self.  FCdot's
alias-tolerant resolution (`FCdot.Ctx.resolve`) follows same-block aliases , 
a field typed `x.A` inside its own literal makes `x∙a` an alias of `x∙A`,
which now resolves like any other alias, and a cyclic alias resolves to `⊤`.

Fields of an intersection are translated with the right conjunct outermost,
matching DOT-MNF's shadowing and its erasure.

## Main theorems

```
Subcap.translate_typed   : Γ.Wf → Γ.translate ⊢ᶜ f.translate : ⟦C⟧ ⊑ ⟦C'⟧
Sub.translate_typed      : Γ.Wf → Γ.translate ⊢ d.translate : T.translate ≤ T'.translate
HasTy.translateAtom_typed: Γ.Wf → Γ.translate ⊢ₐ h.translateAtom : T.translate
HasTy.translateAtom_root : h.translateAtom.root = x
HasTy.translate_typed    : Γ.Wf → Γ.translate ⊢ h.translate : T.translate
HasTy.translate_uses     : Γ.Wf → Γ.translate ⊢ᶜ h.translateUses : h.translate.uses ⊑ ⟦U⟧
HasTy.translate_erase    : ⌊h.translate⌋ = ⌊t⌋
coherence                : ⌊d₁.translate⌋ = ⌊d₂.translate⌋
dot_safety               : HasTy U .nil t T → ⟨∅, ∅, t⟩ ⟶* st → st.Final ∨ ∃ st', st ⟶ st'
dot_not_stuck            : HasTy U .nil t T → ⟨∅, ∅, t⟩ ⟶* st → ¬ st.Stuck
reachable_consistent     : HasTy U .nil t T → ⟨∅, ∅, d.translate⟩ ⟶* st →
                             ∃ Γ, ⊢ st.σ : Γ ∧ ¬ ∃ e C C', Γ ⊢ e : ⊤ ^ C ≤ ⊥ ^ C'
reachable_realized       : … ∧ ∀ x ℓ, ∃ W, Γ.lookupDef x ℓ = some W ∧ Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W
dot_capture_prediction   : HasTy U P.ctx t T → ⟨P.store, ∅, t⟩ ⟶* st →
                             ∃ stt Γ' ρ, ⌊stt⌋ = ⌊st⌋ ∧ ⊢ stt.σ : Γ' ∧
                               Store.Ext P.targetStore stt.σ ρ ∧
                               CapLe Γ' stt.uses (⟦U⟧.rename ρ)
dot_effect_safety        : HasTy U P.ctx t T → ¬ (cvar κ ∈ ⟦U⟧) → ⟨P.store, ∅, t⟩ ⟶* st →
                             st.inspects = some x →
                             ∃ stt Γ' ρ, … ∧ ¬ Γ'.Root (cvar (ρ.var κ)) [var x]
```

Axioms: `propext` and `Quot.sound` everywhere.  No
`sorry`, `axiom`, `partial`, or `native_decide`.

## Stage A0

| module | what A0 changed |
|---|---|
| `Types` | `Ty.translateShape` (the vanilla `Ty.translate` at the shape sort) and `Ty.translate T = T.translateShape ^ []`; `Ty.tel`/`Ty.telSelf` on shapes; `FCdot.ShapeCo.pure` |
| `TypesLemmas` | `Ty.translateShape_rename` and `Ty.translate_rename` above it; the rest unchanged |
| `Evidence` | `Sub.translateShape` (the vanilla `Sub.translate` at `ShapeCo`) and `Sub.translate d = d.translateShape.pure`; `litCo` and `into` on shapes |
| `EvidenceTyped` | the shape equations `Ty.translateShape_*` beside the type equations `Ty.translate_*`; `Sub.translateShape_typed` and `Sub.translate_typed` above it; `litCo_pure_typed` |
| `Terms`, `TermsTyped`, `Erasure`, `Safety` | every cast through `capt _ (refl _)`; statements unchanged |
| `Consistency` | `reachable_consistent` quantifies the two capture sets of `⊤ ≤ ⊥` |

## Stage A1

The source is still `DOT-MNF` without captures (the capturing source is stage A3), so
A1 changes the translation only where the *target* changed: a literal now carries a
capture-witness list, and its precise telescope has a capture block between the type
block and the presences.  A translated literal declares no capture members, so its
capture witnesses are empty and the block is empty, but every index computation over
the precise telescope is stated with the capture block in it, so that A3 has only to
change what `Ty.capWitnesses` returns.

| module | what A1 changed |
|---|---|
| `Types` | `Ty.capWitnesses`, the capture witnesses of a translated literal, empty, so every label's capture witness reads as `[]` (`CapWitnesses.get` of an unlisted label); `FCdot.CapWitnesses.length`; `Ty.literalTy` and `Ctx.translate` at `Telescope.ofLiteral W Wᶜ ls` and `Binding.transparent T W Wᶜ ls` |
| `TypesLemmas` | `Ty.capWitnesses_rename` (renaming a capture-witness list of a translated literal is the identity), used by `Ty.literalTy_rename`; every other statement unchanged |
| `Evidence` | `litCo` builds the object coercion out of `ofLiteral T.witnesses T.capWitnesses T.fieldLabels`, with the presence counter offset by `T.witnesses.length + T.capWitnesses.length`; `FCdot.Morphism.append` and `identityMorphism` gain their capture clauses (a capture proposition is copied by the identity template `leC m [] (leC j) []`, a capture equality by `eqC m j false`); `FCdot.Telescope.NoBnd` and `ClosedBnds` cover the two new propositions |
| `EvidenceTyped` | `FCdot.CapWitnesses.eqEntriesOf_length`/`eqEntries_length` (the capture block is as long as the capture-witness list, so the presences start at `|W| + |Wᶜ|`) and `CapWitnesses.At.eqEntriesOf`/`At.eqEntries` (the capture block is appended after the type block, so type-equality positions keep their index); `eqSpec_of` is stated for an arbitrary capture block; `identityMorphism_typed`, `Morphism.HasType.append`, `NoBnd.append`/`rename`/`closedBnds` and `ClosedBnds.append` gain their capture cases; `litCo_typed_of_shape` reads the presence offset off the two length lemmas |
| `Terms`, `TermsTyped` | a translated literal is `Value.obj T.witnesses T.capWitnesses (…)`, typed at `μ (ofLiteral T.witnesses T.capWitnesses F.labels)`; statements unchanged |
| `Erasure`, `Safety`, `Consistency` | unchanged; a literal's capture witnesses are not erased data and the translation builds no box, so erasure equality and both simulations are A0's |

### Notation

The translation adds no notation of its own; it uses FCdot's, including A1's `⊑ᶜ`,
`≐ᶜ` and `⊢ᶜ`.  As elsewhere, an identifier the plan spells with a `ᶜ` suffix carries
the ASCII suffix `C` (`Ctx.lookupDefC`, `CapWitnesses`, `SideC`, `HoleC`).

### Main theorems, restated

Every statement is A0's, and A0's is the vanilla statement restated at the shape/type
split.  Nothing gained a hypothesis, and no conclusion was dropped.

```
DotMNF.Sub.translate_typed       : Γ.Wf → Γ.translate ⊢ d.translate : S.translate ≤ T.translate
DotMNF.Sub.translateShape_typed  : Γ.Wf → Γ.translate ⊢ˢ d.translateShape :
                                     S.translateShape ≤ T.translateShape
DotMNF.HasTy.translateAtom_typed : Γ.Wf → Γ.translate ⊢ₐ h.translateAtom : T.translate
DotMNF.HasTy.translateAtom_root  : h.translateAtom.root = x
DotMNF.HasTy.translate_typed     : Γ.Wf → Γ.translate ⊢ h.translate : T.translate
DotMNF.HasTy.translate_erase     : ⌊h.translate⌋ = ⌊t⌋
DotMNF.coherence                 : ⌊d₁.translate⌋ = ⌊d₂.translate⌋
DotMNF.dot_safety                : HasTy .nil t T → ⟨∅, ∅, t⟩ ⟶* st → st.Final ∨ ∃ st', st ⟶ st'
DotMNF.dot_not_stuck             : HasTy .nil t T → ⟨∅, ∅, t⟩ ⟶* st → ¬ st.Stuck
DotMNF.reachable_consistent      : HasTy .nil t T → ⟨∅, ∅, d.translate⟩ ⟶* st →
                                     ∃ Γ, ⊢ st.σ : Γ ∧ ¬ ∃ e C C', Γ ⊢ e : ⊤ ^ C ≤ ⊥ ^ C'
DotMNF.reachable_realized        : … ∧ ∀ x ℓ, ∃ W, Γ.lookupDef x ℓ = some W ∧
                                     Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W
```

These rest on the target's A1 theorems, which keep their statements as well: item 7 of
the canonical-forms theorem (a typed atom's root is below the capture set of its type),
`FCdot.cap_canon` over a typed store, and `FCdot.closed_box_inversion`, the box
analogue of `closed_pi_inversion` that the box revision needed.  The translation builds
no box and no `recap`, so it meets none of them directly; it inherits them through
`FCdot.progress`, `preservation'` and `erase_reflect'`.

Axioms (`#print axioms`): `propext` and `Quot.sound` everywhere.  No `sorry`, `axiom`,
`partial`, `unsafe`, or `native_decide`, and no Mathlib.

## Stage A2

The source is still `DOT-MNF` without captures, so A2 changes the translation only
where the *target* changed.  Two things reach it.

A field's result type carries a capture name: `proj` now concludes
`(x ∙ l) ^ {x∙l}`, not `(x ∙ l) ^ {}`.  At an opaque binder that name can only be read
through a declared entry, so the declared telescope of a source field `{a : T}` gains
the capture entry `{self∙a} ⊑ᶜ {}` beside its presence and its bound, and the
translated projection is cast by `capt (the bound at index 1) (member at index 2)`.
A translated literal now declares one empty capture witness per field label, so its
precise telescope has a real capture block, and `litCo` maps each precise entry
`{self∙a} ≐ᶜ {}` to the declared inclusion by a `leC` template with identity side
chains through `HoleAtC`.  Every index computation over the two telescopes moved with
it: the declared telescope of a field has three positions, the capture block of the
precise telescope starts at `|W|` and the presences at `|W| + |Wc|`, and `litMorphism`
carries a third counter that runs over the capture entries in the same order as the
presences.

Use sets are the other half.  Every binder of a translated context has a pure type
(`Ctx.translate_pure`), and the use set of a translated term holds term variables only
(`HasTy.translate_uses_allVar`), so `pureEvidence` puts it below the empty set.  A
translated let therefore declares `U' := []` with `f := pureEvidence (uses ⟦u⟧)`, and a
translated lambda and a translated literal carry `A := []` with the closing evidence
`closingEvidence [] t`, the composition of `pureEvidence` with the syntactic inclusion
`[] ⊑ A↑ ∪ {self}`.  No translated term unboxes.

| module | what A2 changed |
|---|---|
| `Types` | `Ty.tel` and `Ty.telSelf` at a field carry the capture entry `{self∙a} ⊑ᶜ {}` after the presence and the bound; `Ty.capWitnesses` is one empty capture witness per field label, built by the new `FCdot.CapWitnesses.ofLabels` (with `ofLabels_length`, `ofLabels_rename`, `ofLabels_get`), so `Ty.capWitnesses_length` is now `T.fieldLabels.length` and `Ty.capWitnesses_get` is `[]` at every label |
| `TypesLemmas` | `Ty.capWitnesses_rename` moved here, since it goes through `Ty.fieldLabels_rename`; the field cases of `Ty.translateShape_rename`, `Ty.tel_rename` and `Ty.telSelf_rename` also rename the capture entry |
| `Evidence` | the morphism of `Fld` gains the identity capture template `leC m [] (leC 2) []`; `litMorphism` takes three counters and emits `leC m [] (eqC c) []` at a field; `litCo` starts the capture counter at `T.witnesses.length` |
| `EvidenceTyped` | `Ty.tel_fld` and `Ty.telSelf_fld` are three-entry telescopes, with the position lemmas `Telescope.At.zero_three`, `one_three`, `two_three`; `CapWitnesses.At.ofLabels` and `CapWitnesses.ofLabels_At` locate a capture entry inside the precise telescope; the new specification `Ty.CapSpec` with `capSpec_of` beside `Ty.HasSpec`/`hasSpec_of`; `litMorphism_typed` and `litCo_typed_of_shape` take the capture offset; `CaptureSet.substVar_name_here` and `substVar_nil` |
| `Terms` | `pureEvidence`, `closingEvidence`, `fieldBody` and the predicate `FCdot.CaptureSet.AllVar`; a translated projection is cast by the capture member as well as the bound; a translated let carries `[]` and `pureEvidence`; a translated lambda and a translated literal carry `[]` and `closingEvidence`; a translated field carries `closingEvidence` and its body is cast into the capture name of its label |
| `TermsTyped` | `Ctx.translate_pure`, `pureEvidence_typed`, `closingEvidence_typed`, `HasTy.translate_uses_allVar`; `Fields.HasType.append` and `DefsTy.translateFields_typed` at the indexed judgement `Γ ⊢ᶠ[[]] F`; the projection case reads three positions instead of two |
| `Erasure`, `Safety`, `Consistency` | unchanged statements; the erasure of a field names the closing evidence and unfolds `fieldBody`, and every annotation and every piece of evidence erases to nothing |

### Notation

A2 adds no notation of its own.  It uses the target's `Γ ⊢ᶠ[A] F`, the field judgement
indexed by the literal's assigned capture set.

### Main theorems, restated

Every statement is A1's, which is A0's, which is the vanilla statement restated at the
shape and type split.  Nothing gained a hypothesis, and no conclusion was dropped.

```
DotMNF.Sub.translate_typed       : Γ.Wf → Γ.translate ⊢ d.translate : S.translate ≤ T.translate
DotMNF.Sub.translateShape_typed  : Γ.Wf → Γ.translate ⊢ˢ d.translateShape :
                                     S.translateShape ≤ T.translateShape
DotMNF.HasTy.translateAtom_typed : Γ.Wf → Γ.translate ⊢ₐ h.translateAtom : T.translate
DotMNF.HasTy.translateAtom_root  : h.translateAtom.root = x
DotMNF.HasTy.translate_typed     : Γ.Wf → Γ.translate ⊢ h.translate : T.translate
DotMNF.DefsTy.translateFields_typed : … → Γ.translate ⊢ᶠ[[]] h.translateFields
DotMNF.HasTy.translate_erase     : ⌊h.translate⌋ = ⌊t⌋
DotMNF.coherence                 : ⌊d₁.translate⌋ = ⌊d₂.translate⌋
DotMNF.dot_safety                : HasTy .nil t T → ⟨∅, ∅, t⟩ ⟶* st → st.Final ∨ ∃ st', st ⟶ st'
DotMNF.dot_not_stuck             : HasTy .nil t T → ⟨∅, ∅, t⟩ ⟶* st → ¬ st.Stuck
DotMNF.reachable_consistent      : HasTy .nil t T → ⟨∅, ∅, d.translate⟩ ⟶* st →
                                     ∃ Γ, ⊢ st.σ : Γ ∧ ¬ ∃ e C C', Γ ⊢ e : ⊤ ^ C ≤ ⊥ ^ C'
DotMNF.reachable_realized        : … ∧ ∀ x ℓ, ∃ W, Γ.lookupDef x ℓ = some W ∧
                                     Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W
```

Only `DefsTy.translateFields_typed` changed shape, by carrying the index the target's
field judgement now has; the index is the assigned set the value rule supplies, which
for a translated literal is empty, so the sentence is the same one.

New lemmas of the stage, all about the translation and none of them a restatement:

```
DotMNF.Ctx.translate_pure          : (Γ.translate.lookupTy y).captureSet = []
DotMNF.pureEvidence_typed          : (∀ y, (Γ.lookupTy y).captureSet = []) → C.AllVar →
                                       Γ ⊢ᶜ pureEvidence C : C ⊑ []
DotMNF.closingEvidence_typed       : … → t.uses.AllVar →
                                       Γ ⊢ᶜ closingEvidence A t : t.uses ⊑ (A↑ ∪ [var .here])
DotMNF.HasTy.translate_uses_allVar : (h.translate.uses).AllVar
```

Axioms (`#print axioms`): `propext` and `Quot.sound` everywhere.  No `sorry`, `axiom`,
`partial`, `unsafe`, or `native_decide`, and no Mathlib.

## Stage A3a

The source is now `DOT-MNF^cc`, so A3a reaches the translation everywhere.  Three things arrive
together.

A source type is a shape with a capture set, and so is a target type, so the translation splits the
same way: `Shape.translate` is the vanilla recursion at the shape sort, `CaptureSet.translate` maps
atoms pointwise, and `⟦S ^ C⟧ = ⟦S⟧ ^ ⟦C⟧`.  The declared capture set of a field now reaches its
telescope entry, in place of the empty set A2 put there, and a capture member becomes the two
inclusions of its capture name.  A translated literal therefore has real capture witnesses, one per
field and one per capture member, and every index computation over the precise and the declared
telescopes counts them.

Use sets are the second.  The source carries its own use set, so the translation of a derivation
carries the evidence for it: `HasTy.translateUses` is a function on derivations typed at
`uses ⟦h⟧ ⊑ ⟦U⟧`, and it supplies the closing evidence of a translated lambda and of every field of a
translated literal, the avoidance evidence of a translated let, and the subcapturing premise of a
translated unboxing.  A translated binder is no longer pure, so the A2 stand-ins `pureEvidence`,
`closingEvidence` and `HasTy.translate_uses_allVar` are gone, and so is `Ctx.translate_pure`.

The third is the prediction.  `Prediction.lean` is new.  It fixes the platform prefix on both sides,
matches a source run by a target run that ends at the same erasure and is not a cast redex, reads the
inspected root through the erasure, and instantiates the target's `capture_prediction` and
`effect_safety` there.

| module | what A3a changed |
|---|---|
| `Types` | `CapAtom.translate`, `CaptureSet.translate` and their lemmas; `Shape.translate` at the shape sort with the new clauses `cap` and `box`, `Ty.translate` above it; `Shape.tel`/`Shape.telSelf` carry `⟦C⟧` at a field and the two inclusions at a capture member; `Shape.capWitnesses` returns the declared set of each field and the definition of each capture member, so `CapWitnesses.ofLabels` of A2 is gone; `Ctx.translate` at `consC`, a rigid capture binder at `∗`, and at `consSelf`, whose precise type carries the assigned set `⟦U⟧` |
| `TypesLemmas` | the renaming lemmas at the two sorts and at capture sets; `Shape.capWitnesses_rename` is a real recursion now, not the identity |
| `Evidence` | `Subcap.translate`, the evidence of the source's own subcapturing judgement; `SubShape.translate` with the clauses `cap` and `box`; `Sub.translate` pairing the two halves; `litCo` maps the precise capture slot of a field and of a capture member to its declared inclusion; `litMorphism` counts the capture entries |
| `EvidenceTyped` | `Subcap.translate_typed` joins the mutual block, `SubShape.translate_typed` and `Sub.translate_typed` above it; `Ctx.Wf` gains `consC`; the specifications of a literal gain `Shape.CapDefSpec` beside `Shape.DefSpec` |
| `Terms` | `HasTy.translate` with the `box` and `unbox` clauses and with `⟦U⟧` at every binder; the new `HasTy.translateUses`; `fieldBody` casts a field body to its capture name as well as to its block name; `pureEvidence` and `closingEvidence` are gone |
| `TermsTyped` | `HasTy.translate_uses` and `HasTy.translate_uses_atom` in the mutual block with `HasTy.translate_typed`; `DefsTy.translateFields_typed` at the annotation `⟦U⟧` and with the capture specification of the literal; `Ctx.translate_pure` and `HasTy.translate_uses_allVar` are gone |
| `Erasure` | the `box` and `unbox` clauses of `HasTy.translate_erase`, both closing on `HasTy.translateAtom_root` alone, since the two calculi erase a box to the runtime's box and an unboxing to the runtime's unboxing |
| `Safety` | `simulated_init` reads the source judgement at its use set; `final_reflect` gains the `unbox` case; `dot_safety` and `dot_not_stuck` are the stage A2 statements, on the whole source |
| `Consistency` | unchanged |
| `Prediction` | new: `Platform.ctx`, `Platform.targetStore`, `Platform.ctx_wf`, `Platform.targetStore_typed`, `Platform.store_erase`, `Platform.capsAtom`/`caps`/`root_iff`, `FCdot.Value.erase_inspects`, `FCdot.Tm.inspects_reflect`, `FCdot.State.inspects_reflect`, `Platform.initial_typed`, `simulatedRun_aux`, `Platform.simulatedRun`, `dot_capture_prediction`, `dot_effect_safety` |

### Main theorems, restated

Every statement is A2's, which is A1's, which is A0's, which is the vanilla statement restated at the
shape and type split.  Nothing gained a hypothesis, and no conclusion was dropped.  What changed form
is the source judgement itself, which now carries the use set it is indexed by: a theorem that read
`HasTy Γ t T` reads `HasTy U Γ t T` and quantifies over `U`, so it applies to every derivation the
A3a source admits.

```
DotMNF.Sub.translate_typed       : Γ.Wf → Γ.translate ⊢ d.translate : ⟦T⟧ ≤ ⟦T'⟧
DotMNF.SubShape.translate_typed  : Γ.Wf → Γ.translate ⊢ˢ d.translate : ⟦S⟧ ≤ ⟦S'⟧
DotMNF.HasTy.translateAtom_typed : Γ.Wf → Γ.translate ⊢ₐ h.translateAtom : ⟦T⟧
DotMNF.HasTy.translateAtom_root  : h.translateAtom.root = x
DotMNF.HasTy.translate_typed     : Γ.Wf → Γ.translate ⊢ h.translate : ⟦T⟧
DotMNF.DefsTy.translateFields_typed : … → Γ.translate ⊢ᶠ[⟦U⟧] h.translateFields
DotMNF.HasTy.translate_erase     : ⌊h.translate⌋ = ⌊t⌋
DotMNF.coherence                 : ⌊d₁.translate⌋ = ⌊d₂.translate⌋
DotMNF.dot_safety                : HasTy U .nil t T → ⟨∅, ∅, t⟩ ⟶* st → st.Final ∨ ∃ st', st ⟶ st'
DotMNF.dot_not_stuck             : HasTy U .nil t T → ⟨∅, ∅, t⟩ ⟶* st → ¬ st.Stuck
DotMNF.reachable_consistent      : HasTy U .nil t T → ⟨∅, ∅, d.translate⟩ ⟶* st →
                                     ∃ Γ, ⊢ st.σ : Γ ∧ ¬ ∃ e C C', Γ ⊢ e : ⊤ ^ C ≤ ⊥ ^ C'
DotMNF.reachable_realized        : … ∧ ∀ x ℓ, ∃ W, Γ.lookupDef x ℓ = some W ∧
                                     Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W
```

`DefsTy.translateFields_typed` carries the annotation the target's field judgement is indexed by,
which for a translated literal is the translation of the set the source assigned it.  A2 wrote `[]`
there because a translated literal was pure.  The sentence is the same one.

### New in this stage

```
DotMNF.Subcap.translate_typed    : Γ.Wf → Γ.translate ⊢ᶜ f.translate : ⟦C⟧ ⊑ ⟦C'⟧
DotMNF.HasTy.translate_uses      : Γ.Wf → Γ.translate ⊢ᶜ h.translateUses : h.translate.uses ⊑ ⟦U⟧
DotMNF.HasTy.translate_uses_atom : h.translateAtom-headed terms use exactly `{x}`
DotMNF.dot_capture_prediction    : along a run of a program typed over a platform prefix, the matched
                                     target state's use set stays below `⟦U⟧` transported along the
                                     store extension
DotMNF.dot_effect_safety         : a program whose declared use set does not name the platform
                                     capability `κ` never reads a root with root `κ`
```

The two corollaries are the source's half of the target's prediction theorems.  All their content is
the target's `FCdot.capture_prediction` and `FCdot.effect_safety`; what is new is the transport along
the simulation, which needs `inspects` to be preserved by erasure on both sides and a target state
that is not a cast redex, so that the root the source reads is the root the matched target state
reads.

Axioms (`#print axioms`): `propext` and `Quot.sound` everywhere.  No `sorry`, `axiom`,
`partial`, `unsafe`, or `native_decide`, and no Mathlib.

## Stage A3b

`any` is a source notation with no target atom, and the translation says so.  `CapAtom.translate` is
now `CapAtom.translate?`, a function into `Option (FCdot.CapAtom s)`, with the three A3a clauses
unchanged under `some` and `none` at `any`, and `CaptureSet.translate` is the `filterMap` of it, so an
unexpanded `any` is read by the target as nothing.  That is sound because the source gives `any` no
power: no rule of the source mentions it, and the reading a program intends is the one `Ty.expand`
puts in place before the program is typed.  Nothing else of the translation changed, and no theorem of
it changed its statement.

| module | what A3b changed |
|---|---|
| `Types` | `CapAtom.translate?` in place of `CapAtom.translate`, `none` at `any`; `CaptureSet.translate` as a `filterMap`; the four clause lemmas `translate_cons_var`, `translate_cons_cvar`, `translate_cons_sel`, `translate_cons_any`; `translate_cons` at an atom that has a target atom; the new `CaptureSet.translate_substVar`; `Subset.translate` and `translate_rename` reproved for `filterMap`, both with their A3a statements |
| `EvidenceTyped` | four `simpa` argument lists name `CapAtom.translate?`.  No statement changed |
| `TypesLemmas`, `Evidence`, `Terms`, `TermsTyped`, `Erasure`, `Safety`, `Consistency`, `Prediction` | nothing |

### Statements

```
DotMNF.CapAtom.translate?        : CapAtom s → Option (FCdot.CapAtom s)
DotMNF.CapAtom.translate_rename  : (a.rename ρ).translate? = (a.translate?).map (·.rename ρ)
DotMNF.CaptureSet.translate_cons : a.translate? = some b → ⟦a :: C⟧ = b :: ⟦C⟧
DotMNF.CaptureSet.translate_cons_any : ⟦any :: C⟧ = ⟦C⟧
DotMNF.CaptureSet.translate_substVar : ⟦C.substVar y⟧ = ⟦C⟧.substVar y
```

`CapAtom.translate?` and `translate_rename` are the two statements of A3a that changed form.  A total
function from the A3b atoms into the target's atoms cannot exist, since the target has no atom for
`any`; on the three A3a atoms the two functions agree, `some` for `some`, and `translate_cons` is the
A3a equation at every atom A3a had.  `translate_nil`, `translate_append`, `translate_union`,
`translate_rename`, `translate_weaken` and `Subset.translate` keep their statements word for word, and
so does every theorem of `Evidence`, `Terms`, `Erasure`, `Safety`, `Consistency` and `Prediction`.

### The examples

The two source examples of the stage, S1 and S2, are translated and erased by the general theorems in
`../FCdot/Examples.lean`, and the packing of S2 is read off this translation there: `C5_capWitnesses`
and `C5_witnesses` compute `Shape.capWitnesses` and `Shape.witnesses` of the callee's declaration
shape, and `C5_litMorphism` computes the morphism of its `litCo`, whose capture block turns the one
capture equality of the precise telescope into the two inclusions the declared type asks for, the
lower one through a flipped hole.

## Stage B0

B0 changed one lemma here and nothing else.  The stage adds the universal root `⊤ᶜ`, levels and
the level rule to the target only.  The platform prefix stays a chain of `.star` binders, so
`Ctx.translate`, `Platform.ctx`, `Platform.targetStore` and every example context are untouched,
no example gains a slot, and no de Bruijn index shifts.  `Platform.targetStore_typed` passes
`rfl` for the new `b.isRoot = false` premise of `Store.Typed.consC`, and `Platform.capsAtom`
gains the leaf case for `⊤ᶜ`.

The lemma is `Platform.root_iff`, and it gains the premise `⊤ᶜ ∉ C`.

```
DotMNF.Platform.root_iff : ⊤ᶜ ∉ C → (P.ctx.translate.Root a C ↔ a ∈ C)
```

Under the redefined `Ctx.roots` the equivalence is false as soon as `C` mentions the universal
root: a platform context is root-free, so every platform binder is at the outermost level and
`.star` is opaque, so every platform binder lies in the expansion of `⊤ᶜ`.  That is the design
and not a defect, and the premise says what the A3a statement already assumed without writing
it down.  The statement ranged over sets the source wrote, `CaptureSet.translate` drops `any`
and never produces `⊤ᶜ` (`CaptureSet.top_not_mem_translate`, new in this stage), and on such a
set expansion is the identity, so the two readings coincide wherever the lemma is used.

The sole caller is `dot_effect_safety`, which applies it at the translation of a source use set
and discharges the premise by computation.  `dot_effect_safety` keeps its own statement, and so
does every other theorem of this directory: `dot_safety`, `dot_not_stuck`, `dot_capture_prediction`,
`translate_typed`, `translate_erase` and the coherence and consistency theorems are unchanged
word for word.  `Platform.rootFree`, "a platform context binds capabilities only", is the one
other new lemma.

## Stage B1

B1 gives both calculi the same arrow.  The source binds the parameter's `any` as one capture
binder for the whole domain and opens a body root at every lambda and every literal, and so
does the target.  So the translation stays homomorphic on types and erasure equality is free:
`Shape.translate`'s `all` clause is textually unchanged, `.pi T1.translate T2.translate`, and
`HasTy.translate` at `lam` and at `app` did not have to be rewritten at all.

The one new thing the translation needs is that the type translation commutes with
substitution, not only with renaming.  A source substitution and a target substitution agree
when they agree on term variables through `Subst.rootVar` and on capture binders through the
atom translation.  `Subst.singleC` at a variable and `Subst.arg` both agree, and that is what
`HasTy.translate_typed` needs at `app`.

| module | what B1 changed |
|---|---|
| `Types` | `Ctx.translate` gains one clause, `\| .consRoot Γ => .consC Γ.translate .root`, and keeps `\| .consC Γ => .consC Γ.translate .star`.  `Shape.translate` at `all` is textually unchanged.  `Shape.translate_all_eq` reads its operands at `Dom s` and `Cod s` |
| `TypesSubst` | the new file: the substitution twin of `Shape.translate_rename`.  The type translation commutes with a source substitution and a target substitution that agree, and the two agreements `Subst.singleC` and `Subst.arg` that the `app` case consumes |
| `TypesLemmas`, `Evidence`, `EvidenceTyped`, `TermsTyped` | proof lines and the auxiliary lemmas they need.  Every statement is unchanged |
| `Terms` | untouched |
| `Erasure`, `Safety`, `Consistency`, `Prediction` | untouched |

### Statements restated

Nothing was weakened and nothing gained a hypothesis.

```
DotMNF.Shape.translate at all  : textually unchanged, .pi T1.translate T2.translate
                                   both sides bind κ in the same position now
DotMNF.Shape.translate_all_eq  : the same equation at the arrow's new arities
DotMNF.Ctx.translate           : one clause added at consRoot, the source's scope root
                                   translating to the target's
DotMNF.Subcap.translate_typed, .SubShape.translate_typed, .Sub.translate_typed : unchanged
DotMNF.HasTy.translateAtom_typed, .translateAtom_root : unchanged
DotMNF.HasTy.translate_typed, .translate_uses, .translate_uses_atom : unchanged
DotMNF.HasTy.translate_erase, .coherence : unchanged
DotMNF.dot_safety, .dot_not_stuck : unchanged
DotMNF.reachable_consistent, .reachable_realized : unchanged
DotMNF.dot_capture_prediction, .dot_effect_safety : unchanged
DotMNF.Platform.ctx, .store, .targetStore, .capsAtom, .root_iff : unchanged, including
                                   B0's own premise ⊤ᶜ ∉ C
```

The platform prefix is still a chain of `.star` binders, so `Platform.ctx` and
`Platform.targetStore` are textually what they were, no example gains a slot and no de Bruijn
index shifts.  A store context still binds no root, which is what `Subst.Typed.enter` consumes
on the target side at every entering step of a translated run.

### New in this stage

```
DotToFCdot/TypesSubst.lean : the type translation commutes with substitution
```

### The examples

The examples of this directory are the source's, read through the translation, and every one of
them keeps its name and its conclusion.  On the target side `S1_translated`, `S1_erase`,
`S2_translated`, `S2_erase`, `C2_translated`, `C2_erase`, `C7_translated`, `C7_erase`,
`S3_translated` and `S3_erase` are unchanged, and the two new target-side acceptance tests of
B1, `S2_level` and `C5a_level`, are written directly in `FCdot/Examples.lean` because they are
about a scope root and the source has no way to name one yet.

## Stage B2

B2 keeps the translation homomorphic.  Both calculi gain the same answer sort, the same
declared bound, the same instance binding and the same `letex`, so the translation of an answer
is defined clause by clause and every older statement keeps its form with `.ty` written round
its plain type.  The three new pieces are `ETy.translate`, `ESub.translate` and the `consInst`
clause of `Ctx.translate`.

A source `fresh` is dropped as `any` is.  `CapAtom.translate?` returns `none` on it, which is
sound because the source gives `fresh` no power and is vacuous on expanded programs, since
`expandFresh` leaves no `fresh` behind.

Two clause lists grew.  `Shape.translate`, `Shape.tel` and `Shape.telSelf` split their `all`
clause into a `.ty` case, which is the old clause letter for letter, and an `.ex` case, which
is the homomorphism.  `Subcap.translate` gains `inst`, which becomes
`.eqToLe (.symm (.instC ...))` in the target, and that is the one use of finding F-1 in the
translation.  `HasTy.translate` gains a source `letex`, which becomes the target's `letex` with
the declared set, the bound evidence and the body's own use-set evidence, and a source
subsumption at an answer, which becomes `Tm.castE`.

| module | what B2 changed |
|---|---|
| `Types` | `ETy.translate` with its two `@[simp]` equations.  `CapAtom.translate?` gains `\| .fresh => none` with `CaptureSet.translate_cons_fresh`.  `Shape.translate`, `Shape.tel` and `Shape.telSelf` split their `all` clause.  `Ctx.translate` gains `\| .consInst Γ C => .consC Γ.translate (.inst C.translate)`, and `Ctx.varAtom` the matching clause |
| `TypesLemmas` | `ETy.translate_rename` and `ETy.rename_inj`.  `FCdot.CapBound.instSet?_weaken'`, `Ctx.translate_lookupCapInst`, `Ctx.translate_instSet?`, `Ctx.InstOf.translate` and `Ctx.translate_scopeInst`, the four facts the `inst` and `pack` clauses consume.  Every older statement gains the second `all` case and keeps its form |
| `TypesSubst` | `ETy.translate_subst`, the answer twin of `Ty.translate_subst` |
| `Evidence` | `ESub.translate`: `.ty` to `.plain`, `pack` to the target's `pack`, `exist` to `cong`.  `Subcap.translate` gains `inst` |
| `EvidenceTyped` | `ESub.translate_typed`, `ETy.translate_weaken`, `Ctx.Wf.consInst`, `Ctx.Wf.scopeInst`, `Ctx.lookup_consInst_there`, `Ctx.varAtom_consInst_there`.  `Ctx.Wf` gains a `consInst` constructor |
| `Terms`, `TermsTyped` | `HasTy.translate` and `HasTy.translateUses` at the answer sort, with the `letex` and `sub` clauses.  `HasTy.translate_typed`, `.translate_uses` and `.translate_erase` at the answer sort |
| `Erasure` | the `letex` and `sub` cases.  `coherence` keeps its statement |
| `Safety`, `Prediction` | the two call sites of `FCdot.erase_reflect'` pass the continuation half they already hold.  `FCdot.Tm.inspects_reflect` gains a second exclusion, and its one caller supplies it from `State.CastRedex`.  `Safety` imports `FCdot.ErasureMetatheory`, where `erase_reflect'` now lives |
| `Consistency` | untouched beyond the answer sort on the program's type |

### Statements restated

Nothing was weakened, and one statement gained a hypothesis, which is the finding below.

```
DotMNF.ETy.translate            : new, the answer twin of Ty.translate
DotMNF.Shape.translate at all   : two cases, and the .ty case is the old clause letter for
                                    letter
DotMNF.Shape.tel, .telSelf      : the same, two cases
DotMNF.Shape.translate_all_eq, .translate_isObj, .tel_of_not_isObj, .telSelf_of_not_isObj,
  .tel_closedBnds, .translate_rename, .tel_rename, .telSelf_rename, .tel_weaken_eq,
  .tel_substVar, .translate_subst, .tel_subst, .telSelf_subst : statements unchanged, each
                                    with the second all case
DotMNF.CapAtom.translate?       : one clause, fresh dropped as any is
DotMNF.Ctx.translate, .Ctx.varAtom, .Ctx.Wf : one clause each at consInst, additive
DotMNF.Subcap.translate         : one clause, inst to .eqToLe (.symm (.instC ...))
DotMNF.HasTy.translateAtom, .translateAtom_root, .translateAtom_typed, .translate_uses_atom :
                                    take a derivation at .ty T
                                    a variable typing has a plain answer, so the set of
                                    derivations quantified over is the one they quantified over
DotMNF.HasTy.translate, .translateUses, .translate_typed, .translate_uses, .translate_erase,
DotMNF.coherence                : at the answer sort
                                    on a source derivation whose type is plain, E = .ty T and
                                    the conclusion is the old one
DotMNF.Platform.initial_typed, .simulated_init, .translate_initial_typed,
DotMNF.dot_safety, .dot_not_stuck, .reachable_consistent, .reachable_realized,
DotMNF.dot_capture_prediction, .dot_effect_safety : take a derivation at .ty T
                                    a top-level program has a plain answer, because
                                    Cont.Typed.nil accepts .ty T, which is the target's own
                                    shape
DotMNF.Simulated.step, .simulatedRun_aux : pass the continuation half to erase_reflect'
                                    both sites already hold it, two lines above, from the
                                    State.Typed they destructure.  Neither statement changes
FCdot.Tm.inspects_reflect       : gains the hypothesis ∀ t₀ g, t ≠ .castE t₀ g
                                    see the finding below
FCdot.State.inspects_reflect, DotMNF.dot_effect_safety, FCdot.effect_safety : unchanged
DotMNF.Platform.ctx, .store, .targetStore, .capsAtom, .root_iff : unchanged, including B0's
                                    own premise ⊤ᶜ ∉ C
```

**The finding.**  `FCdot.Tm.inspects_reflect` is false without a second exclusion, and the
counterexample is one line: `⌊.castE t g⌋ = ⌊t⌋`, so an answer cast whose body is an
application erases to a term that reads a root, while `(Tm.castE t g).inspects` is `none`.  The
old hypothesis excluded exactly the one former with that property, and B2 adds a second.  No
caller gains an obligation: the only caller is `FCdot.State.inspects_reflect`, whose hypothesis
is `¬ st.CastRedex`, and `State.CastRedex` already has the `.castE` disjunct.  This is the
exact analogue of the `State.CastRedex` row, one lemma further in.

### New in this stage

```
DotMNF.ETy.translate, .ETy.translate_ty, .ETy.translate_ex
DotMNF.ETy.translate_rename, .ETy.rename_inj, .ETy.translate_subst, .ETy.translate_weaken
DotMNF.Ctx.translate_lookupCapInst, .Ctx.translate_instSet?, .Ctx.InstOf.translate,
DotMNF.Ctx.translate_scopeInst
DotMNF.ESub.translate, .ESub.translate_typed
DotMNF.Ctx.Wf.consInst, .Ctx.Wf.scopeInst, .Ctx.lookup_consInst_there,
DotMNF.Ctx.varAtom_consInst_there
FCdot.CapBound.instSet?_weaken'
```

`ESub.translate_typed` is the clause list of the stage in one theorem: `.ty` becomes
`ELeCo.plain`, `pack` becomes `ELeCo.pack` at the translated witness and the translated
residual, and `exist` becomes `ELeCo.cong`.  The residual of a source `pack` is read at
`Ctx.scopeInst C` on both sides, and `Ctx.translate_scopeInst` is the one equation that lets
the target's rule accept it.

### The examples

The examples of this directory are the source's, read through the translation, and every one of
them keeps its name and its conclusion.  Three are new, and they are the three source `fresh`
examples of B2.11, translated and typed at the translated type.

```
FCdot.Examples.Z1_translated       : the callee of freshCell
FCdot.Examples.Z1_caller_translated : a source letex, translated
FCdot.Examples.Z2_translated       : makeLogger, packed at the parameter
FCdot.Examples.Z3_translated       : C5b's callee
FCdot.Examples.Z1_erase, .Z1_caller_erase, .Z2_erase, .Z3_erase : the translation runs the
                                     source program
```

They live in `FCdot/Examples.lean`, beside the older `S1_translated`, `S2_translated`,
`C2_translated`, `C7_translated` and `S3_translated`, which are unchanged.  Each is
`HasTy.translate_typed` at the source derivation and `HasTy.translate_erase` at the same
derivation, and neither is decided by the checker.

## Stage B3

B3 keeps the translation homomorphic once more.  The source gains one subcapturing rule and one
predicate, and the translation gains one clause for the rule, one case for its typedness, the five
spine commutations that clause consumes, and T17.  Nothing else moves.  The type translation is
untouched, byte for byte: `CapAtom.translate?`, `CaptureSet.translate`, `Ctx.translate`,
`CaptureSet.top_not_mem_translate` and `Platform.root_iff` have no new clause and no new premise,
which is decision 23 in the diff.  The source names no universal root, so no source capture set
translates to one, and `dot_effect_safety` keeps the premise it had.

The clause itself is B3.6.  A source `Subcap.level` becomes the target's `CapCo.level`, and the
translation matches on the atom: the three real atoms become the target's own, and the two notations,
`any` and `fresh`, translate to the empty set, so their case is given evidence rather than an
absurdity and the clause stays a plain match with no dependent elimination.  The clause is a leaf of
`Subcap.translate`, so it adds no obligation to the block and the termination measure is still plain
`sizeOf`.

T-B3.2 is what makes the clause typed: `Ctx.translate` commutes with `Ctx.root?`, with `Ctx.lvl`
and with `Ctx.rootB`, so `Ctx.IsRoot` and `Ctx.LvlLe` transport to the target.  The `LvlLe`
commutation is a five-way case on the atom whose two notation cases are closed by decision 30: a
notation is below no root on the source side.

T17 is the theorem of the stage and it is one line.  `source_lvl_safety` says that member-free source
subcapturing never lowers a level, through the translation.  It needs `Subcap.MemberFree`, the
source's own member-free predicate, its translation into the target's, and `Ctx.varAtom_memberFree`,
which says that the evidence the translation builds at a variable is member-free.  Two rename lemmas
for the target's `MemberFree` families live in `FCdot/LevelInversion.lean`, the one target file
besides `Examples` that B3 touches, which is decision 33.

| module | what B3 changed |
|---|---|
| `Types` | nothing.  Not one line |
| `TypesLemmas` | T-B3.2: `Ctx.translate_root?`, `Ctx.translate_lvl`, `Ctx.translate_rootB`, `Ctx.IsRoot.translate` and `Ctx.LvlLe.translate`, after `Shape.translate_underRoot`.  One import line, `FCdot.Levels` |
| `TypesSubst` | nothing |
| `Evidence` | `Subcap.MemberFree`, the six member-free source rules.  `Ctx.varAtom_memberFree`.  `Subcap.translate_memberFree`.  One clause, `level`, in `Subcap.translate`.  One import line, `FCdot.LevelInversion` |
| `EvidenceTyped` | one case, `level`, in `Subcap.translate_typed`.  `source_lvl_safety`, which is T17 |
| `Terms`, `TermsTyped`, `Erasure` | nothing.  `HasTy.translate` gains no clause, so `coherence`, `translate_uses` and `translate_erase` keep their proofs |
| `Safety`, `Consistency`, `Prediction` | nothing |

### Statements restated

Nothing was weakened and no statement gained a hypothesis.

```
DotMNF.Subcap.translate         : one clause, level, a leaf inside the existing
                                    termination_by _ _ _ d => sizeOf d and its decreasing_by
                                    block.  Additive, and the measure is still plain sizeOf
DotMNF.Subcap.translate_typed   : statement kept, one case.  The case is cases on the atom and
                                    then the two T-B3.2 transports for the three real atoms,
                                    and .elem at the empty subset for the two notations, since
                                    a notation translates to the empty set
DotMNF.CapAtom.translate?, .CaptureSet.translate, .Ctx.translate,
DotMNF.CaptureSet.top_not_mem_translate, .Platform.root_iff, .dot_effect_safety
                                : textually unchanged, which is decision 23 in the diff
DotMNF.HasTy.translate, .translateAtom, .Shape.translate, .ETy.translate, .ESub.translate
                                : untouched
DotMNF.Sub.translate_typed, .HasTy.translate_typed, .translate_uses, .translate_erase,
DotMNF.coherence, .dot_safety, .dot_not_stuck, .reachable_consistent, .reachable_realized,
DotMNF.dot_capture_prediction   : form and proof kept, which is T18
```

### New in this stage

```
DotMNF.Ctx.translate_root?, .Ctx.translate_lvl, .Ctx.translate_rootB          T-B3.2
DotMNF.Ctx.IsRoot.translate, .Ctx.LvlLe.translate                             T-B3.2
DotMNF.Subcap.MemberFree                                                      T-B3.4 step 3
DotMNF.Ctx.varAtom_memberFree                                                 T-B3.4 step 2
DotMNF.Subcap.translate_memberFree                                            T-B3.4 step 4
DotMNF.source_lvl_safety                                                      T17
FCdot.CapCo.MemberFree.rename, FCdot.Atom.MemberFree.rename                   T-B3.4 step 1
FCdot.CapCo.MemberFree.weaken, FCdot.Atom.MemberFree.weaken
```

`Subcap.MemberFree` excludes `inst`, `selLower` and `selUpper`, and those three are exactly the
source rules whose translation is `eqToLe` or `member`, which are exactly the two target rules
`FCdot.CapCo.MemberFree` excludes.  So `Subcap.translate_memberFree` is a case-for-case walk of
`Subcap.translate` and needs no termination argument of its own: it is structural on the
member-free proof.

### The examples

The examples of this directory are the source's, read through the translation, and every one keeps
its name and its conclusion.  Five are new.

```
FCdot.Examples.W2_translated       : a parameter any stays one arrow in the target
FCdot.Examples.W2_call_translated  : one source application, one target application
FCdot.Examples.W2_erase            : the translation runs the source program
FCdot.Examples.W3_translated       : makeLogger with the parameter written any, which reads as
                                     Z2TyF, so this is Z2_translated
FCdot.Examples.W4_translated       : freshCell read the compiler's way, which is Z1_translated
FCdot.Examples.W5_caps             : the source twin of X4_caps, at every fuel
FCdot.Examples.W5_no_escape        : T17 at r = ⊤ᶜ, on the translated body context
```

`W2_translated` is the erasure argument of the stage in one theorem.  A parameter `any` is a capture
binder on the arrow, so the callee's type stays one arrow and the translated term is one lambda.
The member encoding the DOT way would have needed puts one extra application per call into the
target term, and `W2_erase` is what that would have lost.

`W5_no_escape` is T17 instantiated where the source cannot state it itself: no member-free source
subcapturing puts the callback's parameter below the platform capability, because the parameter's
binder set resolves to the arrow binder, whose level is the body root, while the platform capability
sits at the outermost level.  The source-side half of the same example, `W5_no_level`, is in
`../DotMNF/README.md`.
