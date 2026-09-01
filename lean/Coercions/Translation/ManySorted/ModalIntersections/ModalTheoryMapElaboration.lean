import Coercions.Translation.ManySorted.ModalIntersections.EvidenceContext
import Coercions.Translation.ManySorted.ModalIntersections.PreparationMetatheory
import Coercions.ManySortedFC.ModalTheoryMap

/-!
# Checked cumulative modal-theory maps

The source implication is represented by a `Satisfies` derivation whose lock
stack has been extended with the available requirements.  Elaboration mirrors
that statement exactly: it pushes only the available prepared target frame,
compiles the required satisfaction evidence there, builds the existing
`ManySortedFC.ModalTheoryMap`, and invokes its standalone checker back in the
ambient context.

The required frame is never pushed.  Consequently, its obligations cannot be
used to discharge themselves.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.ModalTheoryMapElaboration

open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext

namespace Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev ModalRequirements := DOTCapture.ModalIntersections.ModalRequirements

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev ModalContext := ManySortedFC.ModalContext
abbrev ModalTheoryMap := ManySortedFC.ModalTheoryMap

end Target

/-- Prepare the required interface below the available target lock.  Pushing
a modal frame changes only the target scope, so the ambient preparation is
renamed below the available evidence block. -/
def openedRequired {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {availableSeparationCount requiredSeparationCount : Nat}
    {availableModes requiredModes : List DOTCapture.ModalIntersections.CaptureMode}
    {available : Source.ModalRequirements availableSeparationCount
      availableModes sourceScope}
    {required : Source.ModalRequirements requiredSeparationCount
      requiredModes sourceScope}
    (preparedAvailable : PreparedModal context.core available)
    (preparedRequired : PreparedModal context.core required) :
    PreparedModal (context.push available preparedAvailable).core required :=
  let rho := ManySortedFC.Rename.weakenModal targetScope
    availableSeparationCount (Preparation.translateModes availableModes)
  { requirements := preparedRequired.requirements.rename rho
    prepared := by
      have follows := Preparation.translateRequirements_follows
        (Preparation.Layout.Follows.renameTarget context.core.layout rho)
        required
      simpa only [DOTCapture.ModalIntersections.ModalRequirements.rename_id,
        preparedRequired.prepared] using follows }

/-- The required preparation below the available lock is exactly the ambient
prepared interface weakened through that lock's evidence block. -/
@[simp]
theorem openedRequired_requirements {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {availableSeparationCount requiredSeparationCount : Nat}
    {availableModes requiredModes : List DOTCapture.ModalIntersections.CaptureMode}
    {available : Source.ModalRequirements availableSeparationCount
      availableModes sourceScope}
    {required : Source.ModalRequirements requiredSeparationCount
      requiredModes sourceScope}
    (preparedAvailable : PreparedModal context.core available)
    (preparedRequired : PreparedModal context.core required) :
    (openedRequired context preparedAvailable preparedRequired).requirements =
      preparedRequired.requirements.rename
        (ManySortedFC.Rename.weakenModal targetScope
          availableSeparationCount
          (Preparation.translateModes availableModes)) := rfl

/-- A source-indexed modal implication whose generated candidate has crossed
both the cumulative satisfaction compiler and the standalone target map
checker. -/
structure CompiledMap {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {availableSeparationCount requiredSeparationCount : Nat}
    {availableModes requiredModes : List DOTCapture.ModalIntersections.CaptureMode}
    {available : Source.ModalRequirements availableSeparationCount
      availableModes sourceScope}
    {required : Source.ModalRequirements requiredSeparationCount
      requiredModes sourceScope}
    (preparedAvailable : PreparedModal context.core available)
    (preparedRequired : PreparedModal context.core required)
    (satisfaction : DOTCapture.ModalIntersections.Satisfies
      environment.bindings (environment.push available).locks required) where
  opened : PreparedModal (context.push available preparedAvailable).core
    required
  opened_eq : opened = openedRequired context preparedAvailable preparedRequired
  candidate : CompiledPreparedSatisfaction opened
  candidateCompiled :
    (context.push available preparedAvailable).compiler.compileSatisfies?
      opened satisfaction = some candidate
  mapping : Target.ModalTheoryMap targetScope availableSeparationCount
    (Preparation.translateModes availableModes) requiredSeparationCount
    (Preparation.translateModes requiredModes)
  mappingEvidence : mapping.evidence = candidate.evidence
  typing : ManySortedFC.ModalTheoryMap.HasType context.core.target
    preparedAvailable.requirements preparedRequired.requirements mapping
  checkerAcceptance : ManySortedFC.ModalTheoryMap.check context.core.target
    preparedAvailable.requirements preparedRequired.requirements mapping =
      some typing

/-- Compile a source modal implication in the available lock and independently
check the resulting existing target `ModalTheoryMap`. -/
def compile? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {availableSeparationCount requiredSeparationCount : Nat}
    {availableModes requiredModes : List DOTCapture.ModalIntersections.CaptureMode}
    {available : Source.ModalRequirements availableSeparationCount
      availableModes sourceScope}
    {required : Source.ModalRequirements requiredSeparationCount
      requiredModes sourceScope}
    (preparedAvailable : PreparedModal context.core available)
    (preparedRequired : PreparedModal context.core required)
    (satisfaction : DOTCapture.ModalIntersections.Satisfies
      environment.bindings (environment.push available).locks required) :
    Option (CompiledMap context preparedAvailable preparedRequired
      satisfaction) :=
  let pushed := context.push available preparedAvailable
  let opened := openedRequired context preparedAvailable preparedRequired
  match candidateCompiled : pushed.compiler.compileSatisfies? opened
      satisfaction with
  | none => none
  | some candidate =>
      let mapping : Target.ModalTheoryMap targetScope
          availableSeparationCount
          (Preparation.translateModes availableModes)
          requiredSeparationCount
          (Preparation.translateModes requiredModes) :=
        { evidence := candidate.evidence }
      match checkerAcceptance : ManySortedFC.ModalTheoryMap.check
          context.core.target preparedAvailable.requirements
          preparedRequired.requirements mapping with
      | none => none
      | some typing => some
          { opened
            opened_eq := rfl
            candidate
            candidateCompiled
            mapping
            mappingEvidence := rfl
            typing
            checkerAcceptance }

end DOTCaptureToManySortedFC.ModalIntersections.ModalTheoryMapElaboration
