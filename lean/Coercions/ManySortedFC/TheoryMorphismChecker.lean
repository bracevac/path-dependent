import Coercions.ManySortedFC.TheoryMorphism
import Coercions.ManySortedFC.EvidenceChecker

/-!
# Declarative and executable checking of theory morphisms

A morphism from `source` to `target` is checked after opening `source` in the
ambient context.  Each supplied certificate must prove the corresponding
target proposition, with that proposition weakened across the complete
evidence block shared by both theories.

The target theory is never opened while its certificates are checked.  Thus a
target obligation cannot cite the very assumption it is meant to establish;
only ambient evidence and assumptions exported by `source` are available.
-/

namespace ManySortedFC
namespace TheoryMorphism

/-- Pointwise validation of target propositions in one fixed complete static
scope.  `allRelations` remains unchanged during recursion, ensuring that every
target proposition is weakened through the full evidence block rather than
only through the recursive tail. -/
inductive Validates {scope : Sig} {symbols : List StaticSort}
    {allRelations : List Relation}
    (context : Ctx (StaticScope scope symbols allRelations)) :
    {relations : List Relation} →
      Theory scope symbols relations →
      EvidenceArgs (StaticScope scope symbols allRelations) relations →
      Type where
  | nil : Validates context (.nil : Theory scope symbols []) .nil
  | cons {relation : Relation} {relations : List Relation}
      {proposition : Proposition relation (SymbolScope scope symbols)}
      {rest : Theory scope symbols relations}
      {newest : Evidence relation
        (StaticScope scope symbols allRelations)}
      {older : EvidenceArgs
        (StaticScope scope symbols allRelations) relations}
      (head : Evidence.Proves context newest
        (proposition.rename
          (Rename.weakenMany (SymbolScope scope symbols)
            (evidenceKinds allRelations))))
      (tail : Validates context rest older) :
      Validates context (.cons proposition rest) (.cons newest older)

/-- Declarative validity of a raw theory morphism.  The source theory alone is
opened; the target is merely validated proposition by proposition. -/
abbrev HasType {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} {source target : Theory scope symbols relations}
    (context : Ctx scope) (morphism : TheoryMorphism source target) : Type :=
  Validates (allRelations := relations) (context.extendTheory source)
    target morphism.evidence

/-- Structurally validate a target theory against a supplied certificate
block in one fixed complete static scope. -/
def checkValidates {scope : Sig} {symbols : List StaticSort}
    {allRelations : List Relation}
    (context : Ctx (StaticScope scope symbols allRelations)) :
    {relations : List Relation} →
      (target : Theory scope symbols relations) →
      (evidence : EvidenceArgs
        (StaticScope scope symbols allRelations) relations) →
      Option (Validates context target evidence)
  | [], .nil, .nil => some .nil
  | _ :: _, .cons proposition rest, .cons newest older => do
      let checked ← Evidence.check context newest
      let expected := proposition.rename
        (Rename.weakenMany (SymbolScope scope symbols)
          (evidenceKinds allRelations))
      if propositionMatches : checked.proposition = expected then
        let head : Evidence.Proves context newest expected := by
          simpa [propositionMatches] using checked.typing
        let tail ← checkValidates context rest older
        pure (.cons head tail)
      else
        none

/-- Proof-producing checker for a raw same-shape theory morphism. -/
def check {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} {source target : Theory scope symbols relations}
    (context : Ctx scope) (morphism : TheoryMorphism source target) :
    Option (HasType context morphism) :=
  checkValidates (allRelations := relations) (context.extendTheory source)
    target morphism.evidence

/-- Every successful morphism check returns its exact declarative validation
proof. -/
theorem check_sound {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} {source target : Theory scope symbols relations}
    {context : Ctx scope} {morphism : TheoryMorphism source target}
    {typing : HasType context morphism}
    (_accepted : check context morphism = some typing) :
    Nonempty (HasType context morphism) :=
  ⟨typing⟩

end TheoryMorphism
end ManySortedFC
