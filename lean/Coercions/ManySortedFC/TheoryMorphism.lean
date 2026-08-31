import Coercions.ManySortedFC.TheoryModel

/-!
# Identity-on-symbols morphisms between local theories

A theory morphism relates two names-first theories with exactly the same
static-symbol and relation shape.  It keeps the symbols fixed and supplies,
in the complete scope opened by the source theory, one certificate for every
proposition required by the target theory.

The syntax is deliberately raw: this module records certificates and their
structural renaming only.  `TheoryMorphismChecker` gives their declarative
validation and executable checker.  There is no general symbol map,
composition operation, or proposition search.
-/

namespace ManySortedFC

/-- Raw evidence implementing an identity-on-symbols map from `source` to
`target`.  The shared list indices enforce equal symbol and relation shape.
Every certificate lives in the complete static scope exported by `source`. -/
structure TheoryMorphism {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    (source target : Theory scope symbols relations) where
  evidence : EvidenceArgs (StaticScope scope symbols relations) relations

deriving instance DecidableEq for TheoryMorphism

namespace TheoryMorphism

@[ext]
theorem ext {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    {source target : Theory scope symbols relations}
    {first second : TheoryMorphism source target}
    (evidence : first.evidence = second.evidence) : first = second := by
  cases first
  cases second
  simp_all

/-- Rename the ambient scope of both endpoint theories and every supplied
certificate.  Bound symbols and evidence slots are preserved structurally. -/
def rename {sourceScope targetScope : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    {source target : Theory sourceScope symbols relations}
    (morphism : TheoryMorphism source target)
    (rho : Rename sourceScope targetScope) :
    TheoryMorphism (source.rename rho) (target.rename rho) where
  evidence := morphism.evidence.rename
    (rho.liftStatic symbols relations)

/-- Transport only the phantom theory endpoints of a morphism.  Its raw
certificate block is unchanged.  This explicit transport is needed because
the theory renaming laws are propositional rather than definitional. -/
def castEndpoints {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    {source₁ source₂ target₁ target₂ : Theory scope symbols relations}
    (sourceEq : source₁ = source₂) (targetEq : target₁ = target₂)
    (morphism : TheoryMorphism source₁ target₁) :
    TheoryMorphism source₂ target₂ := by
  subst source₂
  subst target₂
  exact morphism

@[simp]
theorem castEndpoints_evidence {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    {source₁ source₂ target₁ target₂ : Theory scope symbols relations}
    (sourceEq : source₁ = source₂) (targetEq : target₁ = target₂)
    (morphism : TheoryMorphism source₁ target₁) :
    (castEndpoints sourceEq targetEq morphism).evidence =
      morphism.evidence := by
  subst source₂
  subst target₂
  rfl

/-- Endpoint transport changes only the type indices of a raw morphism. -/
theorem castEndpoints_heq {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    {source₁ source₂ target₁ target₂ : Theory scope symbols relations}
    (sourceEq : source₁ = source₂) (targetEq : target₁ = target₂)
    (morphism : TheoryMorphism source₁ target₁) :
    HEq (castEndpoints sourceEq targetEq morphism) morphism := by
  subst source₂
  subst target₂
  rfl

/-- Renaming by the identity is identity after the unavoidable endpoint
transport. -/
@[simp]
theorem rename_id {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    {source target : Theory scope symbols relations}
    (morphism : TheoryMorphism source target) :
    castEndpoints (Theory.rename_id source) (Theory.rename_id target)
      (morphism.rename Rename.id) = morphism := by
  apply ext
  simp [rename]

/-- Heterogeneous form of `rename_id`, convenient when a surrounding
dependent constructor transports the endpoint theories implicitly. -/
@[simp]
theorem rename_id_heq {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    {source target : Theory scope symbols relations}
    (morphism : TheoryMorphism source target) :
    HEq (morphism.rename Rename.id) morphism :=
  (castEndpoints_heq (Theory.rename_id source) (Theory.rename_id target)
    (morphism.rename Rename.id)).symm.trans
      (heq_of_eq (rename_id morphism))

/-- Successive ambient renamings compose, modulo transport along the
corresponding endpoint-theory equalities. -/
@[simp]
theorem rename_comp {first second third : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    {source target : Theory first symbols relations}
    (morphism : TheoryMorphism source target)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    castEndpoints (Theory.rename_comp source rho₁ rho₂)
      (Theory.rename_comp target rho₁ rho₂)
      ((morphism.rename rho₁).rename rho₂) =
        morphism.rename (rho₁.comp rho₂) := by
  apply ext
  simp [rename, EvidenceArgs.rename_comp, Rename.liftStatic_comp]

/-- Heterogeneous form of `rename_comp`, for dependent enclosing syntax. -/
@[simp]
theorem rename_comp_heq {first second third : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    {source target : Theory first symbols relations}
    (morphism : TheoryMorphism source target)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    HEq ((morphism.rename rho₁).rename rho₂)
      (morphism.rename (rho₁.comp rho₂)) :=
  (castEndpoints_heq (Theory.rename_comp source rho₁ rho₂)
    (Theory.rename_comp target rho₁ rho₂)
    ((morphism.rename rho₁).rename rho₂)).symm.trans
      (heq_of_eq (rename_comp morphism rho₁ rho₂))

end TheoryMorphism

end ManySortedFC
