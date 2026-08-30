import Coercions.ManySortedFC.TheoryModel
import Coercions.ManySortedFC.EvidenceChecker

/-!
# Structural checking of local-theory models

The checker validates every supplied certificate against the corresponding
proposition after simultaneous symbol instantiation.  All checks run in the
ambient context passed by the caller.  In particular, this module never opens
the modeled theory with `Ctx.extendTheory`: exported assumptions are not in
scope while certificates for the model are checked.
-/

namespace ManySortedFC
namespace Theory

/-- Structurally validate a supplied evidence block against a names-first
theory and a simultaneous symbol assignment.

The unchanged `context` in both the head and recursive calls is the executable
no-self-discharge boundary. -/
def checkSatisfaction {scope : Sig} (context : Ctx scope)
    {symbols : List StaticSort} (arguments : SymbolArgs scope symbols) :
    {relations : List Relation} ->
      (theory : Theory scope symbols relations) ->
      (evidence : EvidenceArgs scope relations) ->
      Option (SatisfiedBy context arguments theory evidence)
  | [], .nil, .nil => some .nil
  | _ :: _, .cons proposition rest, .cons newest older => do
      let checked ← Evidence.check context newest
      let expected := proposition.instantiateSymbols arguments
      if propositionMatches : checked.proposition = expected then
        let head : Evidence.Proves context newest expected := by
          simpa [propositionMatches] using checked.typing
        let tail ← checkSatisfaction context arguments rest older
        pure (.cons head tail)
      else
        none

/-- A successful checker result packages the chosen witnesses, supplied
certificates, and the declarative ambient-context satisfaction derivation. -/
structure CheckedModel {scope : Sig} (context : Ctx scope)
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory scope symbols relations) where
  symbols : SymbolArgs scope symbols
  evidence : EvidenceArgs scope relations
  satisfies : SatisfiedBy context symbols theory evidence

namespace CheckedModel

/-- Forget that a model was obtained by the executable checker. -/
def toModel {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    (checked : CheckedModel context theory) : Model context theory :=
  ⟨checked.symbols, checked.evidence, checked.satisfies⟩

end CheckedModel

/-- Check and package one complete model of a local theory. -/
def checkModel {scope : Sig} (context : Ctx scope)
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory scope symbols relations)
    (arguments : SymbolArgs scope symbols)
    (evidence : EvidenceArgs scope relations) :
    Option (CheckedModel context theory) := do
  let satisfaction ← checkSatisfaction context arguments theory evidence
  pure ⟨arguments, evidence, satisfaction⟩

/-- Soundness is carried by the result of every successful satisfaction
check. -/
theorem checkSatisfaction_sound {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {arguments : SymbolArgs scope symbols}
    {relations : List Relation} {theory : Theory scope symbols relations}
    {evidence : EvidenceArgs scope relations}
    {satisfaction : SatisfiedBy context arguments theory evidence}
    (_accepted : checkSatisfaction context arguments theory evidence =
      some satisfaction) :
    Nonempty (SatisfiedBy context arguments theory evidence) :=
  ⟨satisfaction⟩

/-- A successful packaged check always contains a declarative model. -/
theorem checkModel_sound {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {relations : List Relation}
    {theory : Theory scope symbols relations}
    {arguments : SymbolArgs scope symbols}
    {evidence : EvidenceArgs scope relations}
    {checked : CheckedModel context theory}
    (_accepted : checkModel context theory arguments evidence = some checked) :
    Nonempty (Model context theory) :=
  ⟨checked.toModel⟩

end Theory
end ManySortedFC
