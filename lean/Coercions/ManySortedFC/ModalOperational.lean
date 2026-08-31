import Coercions.ManySortedFC.Dynamics

/-!
# Stuttering-aware modal erasure

This module lifts a runtime-or-stutter simulation for an ambient computation
relation through the primitive modal step relation.  Modal beta itself remains
a genuine runtime force step.
-/

namespace ManySortedFC

namespace Tm

/-- Runtime work lifts through `force`, while a stutter remains a stutter. -/
theorem ErasedStaticAppStep.force
    {scope : Nat} {first second : Runtime.Tm scope} :
    ErasedStaticAppStep first second →
      ErasedStaticAppStep (.force first) (.force second)
  | .runtime step => .runtime (.forceSuspension step)
  | .stutter => .stutter

/-- A modal scrutinee step preserves the ambient runtime-or-stutter behavior.
Runtime work is performed under `force`; an erased ambient step remains an
erased stutter. -/
theorem ModalStep.erase_scrutinee_behavior
    {computationStep : {scope : Sig} → Tm scope → Tm scope → Prop}
    (simulation : ∀ {scope : Sig} {first second : Tm scope},
      computationStep first second →
        ErasedStaticAppStep first.erase second.erase)
    {scope : Sig} {separationCount : Nat}
    {modes : List CaptureMode}
    {requirements : ModalContext separationCount modes scope}
    {first second : Tm scope}
    {evidenceArguments : EvidenceArgs scope
      (modalRelations separationCount modes)}
    (_firstNotValue : ¬ IsValue first)
    (step : computationStep first second) :
    ErasedStaticAppStep
      (Tm.unlock requirements first evidenceArguments).erase
      (Tm.unlock requirements second evidenceArguments).erase := by
  exact ErasedStaticAppStep.force (simulation step)

/-- Every primitive modal step follows one runtime step or stutters exactly
when its ambient scrutinee step does.  Modal beta is always a runtime step. -/
theorem ModalStep.erase_behavior
    {computationStep : {scope : Sig} → Tm scope → Tm scope → Prop}
    (simulation : ∀ {scope : Sig} {first second : Tm scope},
      computationStep first second →
        ErasedStaticAppStep first.erase second.erase)
    {scope : Sig} {first second : Tm scope}
    (step : ModalStep computationStep first second) :
    ErasedStaticAppStep first.erase second.erase := by
  cases step with
  | scrutinee firstNotValue inner =>
      exact ModalStep.erase_scrutinee_behavior
        simulation firstNotValue inner
  | beta =>
      exact .runtime ModalStep.erase_beta

end Tm

end ManySortedFC
