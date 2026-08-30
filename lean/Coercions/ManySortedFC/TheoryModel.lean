import Coercions.ManySortedFC.Context
import Coercions.ManySortedFC.Evidence
import Coercions.ManySortedFC.Substitution

/-!
# Models of names-first local theories

A model chooses one ambient witness for every static symbol and supplies one
logical certificate for every proposition.  The certificates and witnesses
are both scoped in the ambient context.  In particular, the evidence binders
exported by the modeled theory are not available while its model is checked;
this is the syntactic no-self-discharge boundary used by existential package
formation.
-/

namespace ManySortedFC

/-- One ambient logical certificate for every relation in a theory.

The list head is the newest evidence entry, matching `evidenceKinds` and the
constructor order of `Theory`. -/
inductive EvidenceArgs (scope : Sig) : List Relation -> Type where
  | nil : EvidenceArgs scope []
  | cons {relation : Relation} {relations : List Relation}
      (newest : Evidence relation scope)
      (older : EvidenceArgs scope relations) :
      EvidenceArgs scope (relation :: relations)
deriving DecidableEq

namespace EvidenceArgs

/-- Rename every certificate in an evidence argument block. -/
def rename {source target : Sig} {relations : List Relation}
    (arguments : EvidenceArgs source relations)
    (rho : Rename source target) : EvidenceArgs target relations :=
  match arguments with
  | .nil => .nil
  | .cons newest older =>
      .cons (newest.rename rho) (older.rename rho)

/-- Weaken a complete evidence supply below one new binder. -/
def weaken {scope : Sig} {relations : List Relation}
    {kind : BinderKind} (arguments : EvidenceArgs scope relations) :
    EvidenceArgs (scope ▹ kind) relations :=
  arguments.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} {relations : List Relation}
    (arguments : EvidenceArgs scope relations) :
    arguments.rename Rename.id = arguments := by
  induction arguments with
  | nil => rfl
  | cons newest older induction =>
      simp only [rename, Evidence.rename_id, induction]

@[simp]
theorem rename_comp {first second third : Sig}
    {relations : List Relation} (arguments : EvidenceArgs first relations)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (arguments.rename rho₁).rename rho₂ =
      arguments.rename (rho₁.comp rho₂) := by
  induction arguments with
  | nil => rfl
  | cons newest older induction =>
      simp only [rename, Evidence.rename_comp, induction]

end EvidenceArgs

namespace Theory

/-- Declarative satisfaction of a local theory by ambient witnesses.

`context` is deliberately the outer context.  The proof cannot be phrased in
`context.extendTheory theory`, so a theory's own assumptions cannot justify
the evidence used to construct its model. -/
inductive SatisfiedBy {scope : Sig} (context : Ctx scope)
    {symbols : List StaticSort} (arguments : SymbolArgs scope symbols) :
    {relations : List Relation} -> Theory scope symbols relations ->
      EvidenceArgs scope relations -> Type where
  | nil : SatisfiedBy context arguments (.nil : Theory scope symbols [])
      .nil
  | cons {relation : Relation} {relations : List Relation}
      {proposition : Proposition relation (SymbolScope scope symbols)}
      {rest : Theory scope symbols relations}
      {evidence : Evidence relation scope}
      {evidenceRest : EvidenceArgs scope relations}
      (head : Evidence.Proves context evidence
        (proposition.instantiateSymbols arguments))
      (tail : SatisfiedBy context arguments rest evidenceRest) :
      SatisfiedBy context arguments (.cons proposition rest)
        (.cons evidence evidenceRest)

/-- A complete, proof-carrying model of one names-first local theory. -/
structure Model {scope : Sig} (context : Ctx scope)
    {symbols : List StaticSort} {relations : List Relation}
    (theory : Theory scope symbols relations) where
  symbols : SymbolArgs scope symbols
  evidence : EvidenceArgs scope relations
  satisfies : SatisfiedBy context symbols theory evidence

/-- Inversion for the newest proposition in a nonempty theory model. -/
def SatisfiedBy.head {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {arguments : SymbolArgs scope symbols}
    {relation : Relation} {relations : List Relation}
    {proposition : Proposition relation (SymbolScope scope symbols)}
    {rest : Theory scope symbols relations}
    {evidence : Evidence relation scope}
    {evidenceRest : EvidenceArgs scope relations}
    (satisfaction : SatisfiedBy context arguments
      (.cons proposition rest) (.cons evidence evidenceRest)) :
    Evidence.Proves context evidence
      (proposition.instantiateSymbols arguments) := by
  cases satisfaction with
  | cons head _ => exact head

/-- The tail of a nonempty theory model is a model of the remaining theory. -/
def SatisfiedBy.tail {scope : Sig} {context : Ctx scope}
    {symbols : List StaticSort} {arguments : SymbolArgs scope symbols}
    {relation : Relation} {relations : List Relation}
    {proposition : Proposition relation (SymbolScope scope symbols)}
    {rest : Theory scope symbols relations}
    {evidence : Evidence relation scope}
    {evidenceRest : EvidenceArgs scope relations}
    (satisfaction : SatisfiedBy context arguments
      (.cons proposition rest) (.cons evidence evidenceRest)) :
    SatisfiedBy context arguments rest evidenceRest := by
  cases satisfaction with
  | cons _ tail => exact tail

end Theory

end ManySortedFC
