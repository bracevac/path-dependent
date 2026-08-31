import Coercions.ManySortedFC.TheoryMapValidity
import Coercions.ManySortedFC.Erasure

/-!
# Checked laws for cross-shape theory maps

`TheoryMap.symbolAt` already states sort preservation intrinsically, and
`TheoryMap.constraintAt` extracts every destination constraint proof from a
declaratively valid map. This module records the remaining public law
boundary.

Identity and composition remain raw syntax constructors, but
`TheoryMap.identity_hasType` and `TheoryMap.compose_hasType` prove their
generic declarative validity.  Evidence-aware static substitution preserves
proof typing, so the latter theorem transports the second map's derivation
through the first map.  `identity_check_isSome` and `compose_check_isSome`
then expose executable acceptance through checker completeness.

Model restriction is also static. `restrictModelWithPayload?` makes the
application boundary explicit: it checks the target model while returning
the original payload literally unchanged. Any representation adapter is a
separate value-level operation.
-/

namespace ManySortedFC
namespace TheoryMap

/-! ## Checker-backed validity -/

/-- The identity constructor is valid exactly when the independent map
checker accepts it. -/
theorem identity_check_isSome_iff_valid {scope : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    (context : Ctx scope) (theory : Theory scope symbols relations) :
    (check context (identity theory)).isSome = true ↔
      Nonempty (HasType context (identity theory)) :=
  check_isSome_iff

/-- A raw composite is valid exactly when the independent map checker accepts
the evidence-aware substituted map. -/
theorem compose_check_isSome_iff_valid {scope : Sig}
    {sourceSymbols middleSymbols targetSymbols : List StaticSort}
    {sourceRelations middleRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {middle : Theory scope middleSymbols middleRelations}
    {target : Theory scope targetSymbols targetRelations}
    (context : Ctx scope) (first : TheoryMap source middle)
    (second : TheoryMap middle target) :
    (check context (compose first second)).isSome = true ↔
      Nonempty (HasType context (compose first second)) :=
  check_isSome_iff

/-! ## Syntactic composition laws -/

/-- Looking up a composed evidence block performs exactly the substitution
recorded by `TheoryMap.compose`. -/
@[simp]
theorem compose_evidenceAt {scope : Sig}
    {sourceSymbols middleSymbols targetSymbols : List StaticSort}
    {sourceRelations middleRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {middle : Theory scope middleSymbols middleRelations}
    {target : Theory scope targetSymbols targetRelations}
    (first : TheoryMap source middle) (second : TheoryMap middle target)
    {relation : Relation} (reference : ConstraintRef targetRelations relation) :
    (compose first second).evidenceAt reference =
      (second.evidenceAt reference).substitute first.substitution := by
  simp [evidenceAt, compose]

/-! ## Static model restriction with an unchanged payload -/

/-- Restrict a source model and carry an arbitrary payload across the static
view change. This does not claim that the payload has the expected target
representation type; a separately checked value adapter supplies that fact
when the two representation types differ. -/
def restrictModelWithPayload? {scope : Sig} {context : Ctx scope}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (mapping : TheoryMap source target) (model : Theory.Model context source)
    (payload : Tm scope) :
    Option (Theory.CheckedModel context target × Tm scope) := do
  let checked ← checkModel mapping model
  pure (checked, payload)

/-- The model component is exactly the independently checked restriction and
the payload component is the original term. -/
theorem restrictModelWithPayload?_eq_some_iff
    {scope : Sig} {context : Ctx scope}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (mapping : TheoryMap source target) (model : Theory.Model context source)
    (payload : Tm scope) (checked : Theory.CheckedModel context target)
    (resultPayload : Tm scope) :
    restrictModelWithPayload? mapping model payload =
        some (checked, resultPayload) ↔
      checkModel mapping model = some checked ∧ resultPayload = payload := by
  unfold restrictModelWithPayload?
  cases restricted : checkModel mapping model <;> simp [eq_comm]

/-- Model restriction changes only static arguments. Projecting and erasing
the payload from the result is the same as erasing the input payload. -/
theorem restrictModelWithPayload?_erasure
    {scope : Sig} {context : Ctx scope}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (mapping : TheoryMap source target) (model : Theory.Model context source)
    (payload : Tm scope) :
    (restrictModelWithPayload? mapping model payload).map
        (fun result => result.2.erase) =
      (checkModel mapping model).map (fun _ => payload.erase) := by
  unfold restrictModelWithPayload?
  cases checkModel mapping model <;> rfl

/-- Pointwise form of exact payload erasure after successful restriction. -/
theorem restricted_payload_erasure
    {scope : Sig} {context : Ctx scope}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    {mapping : TheoryMap source target} {model : Theory.Model context source}
    {payload resultPayload : Tm scope}
    {checked : Theory.CheckedModel context target}
    (accepted : restrictModelWithPayload? mapping model payload =
      some (checked, resultPayload)) :
    resultPayload.erase = payload.erase := by
  have components :=
    (restrictModelWithPayload?_eq_some_iff mapping model payload checked
      resultPayload).mp accepted
  rw [components.2]

end TheoryMap
end ManySortedFC
