# DotToFCdot, at stage A3b of captures (CapturesCC copy, unchanged)

The translation of DOT-MNF^cc into FCdot^cc (Plan III §8, milestones M3 to
M5), namespace `DotMNF`.  Derivations are `Type`-valued, so the translation
is a function on derivations; typedness and erasure equality are theorems
about that function, and DOT-MNF's type safety, consistency and capture
prediction are all transported from FCdot's.

## Modules

| module | contents |
|---|---|
| `Types` | `CapAtom.translate?` and `CaptureSet.translate` (atom by atom, the source's `sel x C` becoming the target's name `x∙C`, `any` dropped), `Shape.translate` and `Ty.translate` (`⟦S ^ C⟧ = ⟦S⟧ ^ ⟦C⟧`), `Shape.tel`/`Shape.telSelf` (a shape as a telescope over a self block: declaration shapes proposition by proposition, everything else as one self-bound), the shape test `Shape.isObj` and `Shape.translate_isObj`/`Shape.tel_of_not_isObj`, `Shape.witnesses`, `Shape.capWitnesses`, `Shape.fieldLabels`, `Shape.literalShape`, `Shape.literalTy`, `Ctx.translate` |
| `TypesLemmas` | renaming and instantiation commute with the translation; `Shape.isDecl_rename`, `Shape.isObj_rename`; `Shape.translate_decl`; `Shape.tel_substVar` (opening a body at the root) |
| `Evidence` | `Subcap.translate`, `SubShape.translate`, `Sub.translate`, `HasTy.translateAtom`, `litCo` (the cast from a literal's precise type to its declaration type), `identityMorphism`, `into`/`intoAtom` (an operand put into its own telescope), `Ctx.varAtom` |
| `EvidenceTyped` | `Subcap.translate_typed`, `SubShape.translate_typed`, `Sub.translate_typed`, `HasTy.translateAtom_typed`, `HasTy.translateAtom_root`, `litCo_typed`, `litCo_atC_typed`, `Ctx.varAtom_typed`, `Shape.tel_closedBnds` (every self-bound the translation produces is closed); the well-formedness `Ctx.Wf` of contexts |
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
