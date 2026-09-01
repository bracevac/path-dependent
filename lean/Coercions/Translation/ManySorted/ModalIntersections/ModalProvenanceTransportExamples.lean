import Coercions.Translation.ManySorted.ModalIntersections.ModalProvenanceTransport
import Coercions.ManySortedFC.ModalPreservation

/-! Focused regressions for simultaneous source and target transport. -/

namespace DOTCaptureToManySortedFC.ModalIntersections.ModalProvenanceTransportExamples

open DOTCaptureToManySortedFC.ModalIntersections

def sourceModes : Source.ModeContext [.writable, .readOnly] [] :=
  .cons (.cons .nil .empty) .empty

def sourceSeparation : Source.SeparationContext 2 [] :=
  .cons (.cons .nil .empty) .empty

def sourceRequirements : Source.ModalRequirements 2
    [.writable, .readOnly] [] :=
  .mk sourceSeparation sourceModes

def targetRequirements : Target.ModalContext 2
    [.writable, .readOnly] [] :=
  mapRequirements (fun _ => (.empty : Target.Capture [])) sourceRequirements

abbrev FirstTargetScope : Target.Sig :=
  ManySortedFC.ModalScope [] 2 [.writable, .readOnly]

def firstTargetContext : Target.Ctx FirstTargetScope :=
  ManySortedFC.Ctx.nil.extendModal targetRequirements

noncomputable def active : ActiveProvenance
    (.push .nil sourceRequirements) firstTargetContext
    (fun _ => (.empty : Target.Capture FirstTargetScope)) := by
  simpa [firstTargetContext, targetRequirements] using
    (ActiveProvenance.nil ManySortedFC.Ctx.nil
      (fun _ => (.empty : Target.Capture []))).push
        sourceSeparation sourceModes

abbrev SecondSourceScope : Source.Sig := [] ▹ .term

def sourceWeakening : Source.Rename [] SecondSourceScope :=
  DOTCapture.BinderOnly.Rename.succ

abbrev SecondTargetScope : Target.Sig := FirstTargetScope ▹ .term

def targetBinding : ManySortedFC.Binding FirstTargetScope .term :=
  .term .one

def targetWeakening :
    ManySortedFC.TermStaticSubst FirstTargetScope SecondTargetScope :=
  ManySortedFC.TermStaticSubst.ofRename ManySortedFC.Rename.succ

noncomputable def targetWeakeningPreserves :
    targetWeakening.Preserves firstTargetContext
      (firstTargetContext.extend targetBinding) :=
  ManySortedFC.TermStaticSubst.Preserves.weaken firstTargetContext
    targetBinding

noncomputable def transported : ActiveProvenance
    ((DOTCapture.ModalIntersections.ModalAssumptions.push
      .nil sourceRequirements).rename sourceWeakening)
    (firstTargetContext.extend targetBinding)
    (fun _ => (.empty : Target.Capture SecondTargetScope)) :=
  active.renameSource sourceWeakening targetWeakening
    targetWeakeningPreserves
    (fun _ => (.empty : Target.Capture SecondTargetScope))
    (by intro capture; rfl)

/-- Renaming retains the older read-only occurrence and target weakening
adds exactly one binder above its original evidence coordinate. -/
noncomputable def compiledOlderMode : CompiledMode
    (firstTargetContext.extend targetBinding) .empty .readOnly :=
  transported.modeLock
    DOTCapture.ModalIntersections.ModalAssumptions.Lookup.here
    (DOTCapture.ModalIntersections.ModeContext.Occurs.there
      DOTCapture.ModalIntersections.ModeContext.Occurs.here)

example : compiledOlderMode.evidence =
    ManySortedFC.Evidence.var
      (ManySortedFC.BVar.there
        (ManySortedFC.BVar.there ManySortedFC.BVar.here)) := rfl

/-- Both renamed positions and their reverse distinctness proof are recovered
at the same coordinates; only the target evidence term is weakened. -/
noncomputable def compiledReversePair : CompiledSeparate
    (firstTargetContext.extend targetBinding) .empty .empty :=
  transported.separateLock
    DOTCapture.ModalIntersections.ModalAssumptions.Lookup.here
    (DOTCapture.ModalIntersections.SeparationContext.Position.there
      DOTCapture.ModalIntersections.SeparationContext.Position.here)
    DOTCapture.ModalIntersections.SeparationContext.Position.here
    (DOTCapture.ModalIntersections.SeparationContext.Position.Distinct.thereHere
      DOTCapture.ModalIntersections.SeparationContext.Position.here)

example : compiledReversePair.evidence =
    ManySortedFC.Evidence.separateSymm
      (ManySortedFC.Evidence.var
        (ManySortedFC.BVar.there
          (ManySortedFC.BVar.there
            (ManySortedFC.BVar.there ManySortedFC.BVar.here)))) := rfl

/-! Duplicate frames remain distinguished by stack depth after simultaneous
source and target weakening, even when every stored capture and every
requirement entry is syntactically equal. -/

def secondTargetRequirements : Target.ModalContext 2
    [.writable, .readOnly] FirstTargetScope :=
  mapRequirements (fun _ => (.empty : Target.Capture FirstTargetScope))
    sourceRequirements

noncomputable def duplicateFrames : ActiveProvenance
    (.push (.push .nil sourceRequirements) sourceRequirements)
    (firstTargetContext.extendModal secondTargetRequirements)
    (fun _ => (.empty : Target.Capture
      (ManySortedFC.ModalScope FirstTargetScope 2
        [.writable, .readOnly]))) := by
  simpa [firstTargetContext, secondTargetRequirements] using
    active.push sourceSeparation sourceModes

abbrev DuplicateTargetScope : Target.Sig :=
  ManySortedFC.ModalScope FirstTargetScope 2 [.writable, .readOnly]

abbrev TransportedDuplicateTargetScope : Target.Sig :=
  DuplicateTargetScope ▹ .term

def duplicateTargetBinding : ManySortedFC.Binding DuplicateTargetScope .term :=
  .term .one

def duplicateTargetWeakening :
    ManySortedFC.TermStaticSubst DuplicateTargetScope
      TransportedDuplicateTargetScope :=
  ManySortedFC.TermStaticSubst.ofRename ManySortedFC.Rename.succ

noncomputable def duplicateTargetWeakeningPreserves :
    duplicateTargetWeakening.Preserves
      (firstTargetContext.extendModal secondTargetRequirements)
      ((firstTargetContext.extendModal secondTargetRequirements).extend
        duplicateTargetBinding) :=
  ManySortedFC.TermStaticSubst.Preserves.weaken
    (firstTargetContext.extendModal secondTargetRequirements)
    duplicateTargetBinding

noncomputable def transportedDuplicateFrames : ActiveProvenance
    ((DOTCapture.ModalIntersections.ModalAssumptions.push
      (DOTCapture.ModalIntersections.ModalAssumptions.push
        .nil sourceRequirements) sourceRequirements).rename sourceWeakening)
    ((firstTargetContext.extendModal secondTargetRequirements).extend
      duplicateTargetBinding)
    (fun _ => (.empty : Target.Capture TransportedDuplicateTargetScope)) :=
  duplicateFrames.renameSource sourceWeakening duplicateTargetWeakening
    duplicateTargetWeakeningPreserves
    (fun _ => (.empty : Target.Capture TransportedDuplicateTargetScope))
    (by intro capture; rfl)

noncomputable def duplicateNewestMode : CompiledMode
    ((firstTargetContext.extendModal secondTargetRequirements).extend
      duplicateTargetBinding) .empty .readOnly :=
  transportedDuplicateFrames.modeLock
    DOTCapture.ModalIntersections.ModalAssumptions.Lookup.here
    (DOTCapture.ModalIntersections.ModeContext.Occurs.there
      DOTCapture.ModalIntersections.ModeContext.Occurs.here)

noncomputable def duplicateOlderMode : CompiledMode
    ((firstTargetContext.extendModal secondTargetRequirements).extend
      duplicateTargetBinding) .empty .readOnly :=
  transportedDuplicateFrames.modeLock
    (DOTCapture.ModalIntersections.ModalAssumptions.Lookup.there
      DOTCapture.ModalIntersections.ModalAssumptions.Lookup.here)
    (DOTCapture.ModalIntersections.ModeContext.Occurs.there
      DOTCapture.ModalIntersections.ModeContext.Occurs.here)

example : duplicateNewestMode.evidence =
    ManySortedFC.Evidence.var
      (ManySortedFC.BVar.there
        (ManySortedFC.BVar.there ManySortedFC.BVar.here)) := rfl

example : duplicateOlderMode.evidence =
    ManySortedFC.Evidence.var
      (ManySortedFC.BVar.there
        (ManySortedFC.BVar.there
          (ManySortedFC.BVar.there
            (ManySortedFC.BVar.there
              (ManySortedFC.BVar.there ManySortedFC.BVar.here))))) := rfl

end DOTCaptureToManySortedFC.ModalIntersections.ModalProvenanceTransportExamples
