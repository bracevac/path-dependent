import Coercions.ManySortedFC.ModalContext
import Coercions.ManySortedFC.TheoryMapChecker

/-!
# Maps between primitive modal requirements

Modal theories bind no static symbols.  A map from the requirements available
under a target lock to the requirements needed by a source lock therefore
consists exactly of one evidence argument for every source requirement.  The
`toTheoryMap` projection exposes the ordinary cross-shape `TheoryMap` checked
by the target kernel.
-/

namespace ManySortedFC

/-- Evidence that the `available` modal requirements entail the `required`
requirements.  Evidence is formed under the available modal scope. -/
structure ModalTheoryMap (scope : Sig)
    (availableSeparationCount : Nat) (availableModes : List CaptureMode)
    (requiredSeparationCount : Nat) (requiredModes : List CaptureMode) where
  evidence : EvidenceArgs
    (ModalScope scope availableSeparationCount availableModes)
    (modalRelations requiredSeparationCount requiredModes)

deriving instance DecidableEq for ModalTheoryMap

namespace ModalTheoryMap

/-- Expose a modal requirement map as the ordinary zero-symbol TheoryMap that
the independent target checker validates. -/
def toTheoryMap {scope : Sig}
    {requiredSeparationCount availableSeparationCount : Nat}
    {requiredModes availableModes : List CaptureMode}
    (mapping : ModalTheoryMap scope availableSeparationCount availableModes
      requiredSeparationCount requiredModes)
    (available : ModalContext availableSeparationCount availableModes scope)
    (required : ModalContext requiredSeparationCount requiredModes scope) :
    TheoryMap available.toTheory required.toTheory where
  symbols := .nil
  evidence := mapping.evidence

/-- Rename the ambient captures mentioned by both modal interfaces and their
evidence implementation. -/
def rename {source target : Sig}
    {requiredSeparationCount availableSeparationCount : Nat}
    {requiredModes availableModes : List CaptureMode}
    (mapping : ModalTheoryMap source availableSeparationCount availableModes
      requiredSeparationCount requiredModes)
    (rho : Rename source target) :
    ModalTheoryMap target availableSeparationCount availableModes
      requiredSeparationCount requiredModes where
  evidence := mapping.evidence.rename
    (rho.liftModal availableSeparationCount availableModes)

@[simp]
theorem rename_id {scope : Sig}
    {requiredSeparationCount availableSeparationCount : Nat}
    {requiredModes availableModes : List CaptureMode}
    (mapping : ModalTheoryMap scope availableSeparationCount availableModes
      requiredSeparationCount requiredModes) :
    mapping.rename Rename.id = mapping := by
  cases mapping
  simp [rename]

@[simp]
theorem rename_comp {first second third : Sig}
    {requiredSeparationCount availableSeparationCount : Nat}
    {requiredModes availableModes : List CaptureMode}
    (mapping : ModalTheoryMap first availableSeparationCount availableModes
      requiredSeparationCount requiredModes)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (mapping.rename rho₁).rename rho₂ =
      mapping.rename (rho₁.comp rho₂) := by
  cases mapping
  simp [rename, EvidenceArgs.rename_comp, Rename.liftModal_comp]

/-- Declarative validity is exactly validity of the projected TheoryMap. -/
abbrev HasType {scope : Sig}
    {requiredSeparationCount availableSeparationCount : Nat}
    {requiredModes availableModes : List CaptureMode}
    (context : Ctx scope)
    (available : ModalContext availableSeparationCount availableModes scope)
    (required : ModalContext requiredSeparationCount requiredModes scope)
    (mapping : ModalTheoryMap scope availableSeparationCount availableModes
      requiredSeparationCount requiredModes) : Type :=
  TheoryMap.HasType context (mapping.toTheoryMap available required)

/-- Check a modal requirement map with the ordinary independent TheoryMap
checker. -/
def check {scope : Sig}
    {requiredSeparationCount availableSeparationCount : Nat}
    {requiredModes availableModes : List CaptureMode}
    (context : Ctx scope)
    (available : ModalContext availableSeparationCount availableModes scope)
    (required : ModalContext requiredSeparationCount requiredModes scope)
    (mapping : ModalTheoryMap scope availableSeparationCount availableModes
      requiredSeparationCount requiredModes) :
    Option (HasType context available required mapping) :=
  TheoryMap.check context (mapping.toTheoryMap available required)

end ModalTheoryMap

end ManySortedFC
