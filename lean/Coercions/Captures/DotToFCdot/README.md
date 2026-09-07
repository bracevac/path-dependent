# DotToFCdot, at stage A2 of captures

The translation of DOT-MNF into FCdot (Plan III §8, milestones M3 to M5),
namespace `DotMNF`.  Derivations are `Type`-valued, so the translation is a
function on derivations; typedness and erasure equality are theorems about
that function, and DOT-MNF's type safety is transported from FCdot's.

## Modules

| module | contents |
|---|---|
| `Types` | `Ty.translate`, `Ty.tel`/`Ty.telSelf` (a type as a telescope over a self block: declaration shapes proposition by proposition, everything else as one self-bound), the shape test `Ty.isObj` and `Ty.translate_isObj`/`Ty.tel_of_not_isObj`, `Ty.witnesses`, `Ty.capWitnesses`, `Ty.fieldLabels`, `Ty.literalTy`, `Ctx.translate` |
| `TypesLemmas` | renaming and instantiation commute with the translation; `Ty.isDecl_rename`, `Ty.isObj_rename`; `Ty.translate_decl`; `Ty.tel_substVar` (opening a body at the root) |
| `Evidence` | `Sub.translate`, `HasTy.translateAtom`, `litCo` (the cast from a literal's precise type to its declaration type), `identityMorphism`, `into`/`intoAtom` (an operand put into its own telescope), `Ctx.varAtom` |
| `EvidenceTyped` | `Sub.translate_typed`, `HasTy.translateAtom_typed`, `HasTy.translateAtom_root`, `litCo_typed`, `Ctx.varAtom_typed`, `Ty.tel_closedBnds` (every self-bound the translation produces is closed); the well-formedness `Ctx.Wf` of contexts |
| `Terms` | `HasTy.translate`, `DefsTy.translateFields`, `pureEvidence`, `closingEvidence`, `fieldBody`, `FCdot.CaptureSet.AllVar` |
| `TermsTyped` | `HasTy.translate_typed`, `DefsTy.translateFields_typed`, `Ctx.translate_pure`, `pureEvidence_typed`, `closingEvidence_typed`, `HasTy.translate_uses_allVar` |
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
{a : T}      ↦  μ [ ∋ a , self∙a ⊑ ⟦T⟧↑ , {self∙a} ⊑ᶜ {} ]
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
to the declared field type, and to the empty capture set by the field's
capture entry; an object literal becomes a literal with the witnesses of its
declaration type, each field cast to its block name by the literal's own
definition equality, the whole cast by `litCo`.  Every translated binder is
pure, so a translated let declares the empty use set and a translated lambda
and literal the empty assigned set.

## Side conditions

Typedness holds for well-formed contexts, `Ctx.Wf`: a literal's self binder
(`Ctx.consSelf`) carries a declaration type of literal shape (exact type
members) with distinct labels, which is what `{}-I` produces.  The initial
context is empty, so `dot_safety` has no side condition.

The self-alias restriction is gone: `{}-I` no longer restricts which members'
witnesses may be a bare selection on the object's own self.  FCdot's
alias-tolerant resolution (`FCdot.Ctx.resolve`) follows same-block aliases , 
a field typed `x.A` inside its own literal makes `x∙a` an alias of `x∙A`,
which now resolves like any other alias, and a cyclic alias resolves to `⊤`.

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
