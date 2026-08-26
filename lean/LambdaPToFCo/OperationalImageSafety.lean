import LambdaPToFCo.OperationalSourceProgress
import LambdaPToFCo.OperationalSafety

/-!
# Finite image traces and source safety

The individual smart constructors in `OperationalStateImage` prove three
facts at once: a native CK step, an image of the successor state, and target
reductions between the two reconstructed target expressions.  This module
packages that common boundary and closes it under finite execution.

The final source-safety argument is deliberately asymmetric.  Target steps
are retained as compiler-correctness evidence, but source non-stuckness comes
from the successor `StateImage` through `StateImage.sourceProgress`; target
safety is not used to manufacture source progress.
-/

namespace LambdaPToFCo
namespace OperationalImageSafety

open OperationalSafety
open OperationalStateImage
open OperationalSourceProgress

/-- One source transition together with images of both endpoints and the
target execution supplied by the corresponding image smart constructor. -/
structure ImageStep
    {sourceSize targetSize : Nat}
    {source : LambdaPFC.State sourceSize}
    {target : LambdaPFC.State targetSize}
    (before : StateImage source) (after : StateImage target) : Prop where
  sourceStep : LambdaPFC.State.Step source target
  targetSteps : SystemFCo.Exp.Steps before.target after.target

namespace ImageStep

/-- Package the source and target theorems of any concrete image transition.
This is the only adapter needed by `letPush`, `path`, `allocate`, `return`,
and the wrapper-aware application smart constructor. -/
def ofEvidence
    (before : StateImage source) (after : StateImage target)
    (sourceStep : LambdaPFC.State.Step source target)
    (targetSteps : SystemFCo.Exp.Steps before.target after.target) :
    ImageStep before after :=
  ⟨sourceStep, targetSteps⟩

/-- The successor image itself entails source progress. -/
theorem after_progress
    {sourceSize targetSize : Nat}
    {source : LambdaPFC.State sourceSize}
    {target : LambdaPFC.State targetSize}
    {before : StateImage source} {after : StateImage target}
    (_step : ImageStep before after) : LambdaPFC.State.Progress target :=
  OperationalSourceProgress.StateImage.sourceProgress after

/-- Consequently, the endpoint of an image step is not source-stuck. -/
theorem after_not_stuck
    {sourceSize targetSize : Nat}
    {source : LambdaPFC.State sourceSize}
    {target : LambdaPFC.State targetSize}
    {before : StateImage source} {after : StateImage target}
    (step : ImageStep before after) :
    Not (OperationalSafety.State.IsStuck target) :=
  OperationalSafety.State.not_stuck_of_progress step.after_progress

end ImageStep

/-- Finite closure of image-preserving source transitions.

Unlike `LambdaPFC.State.Steps`, every intermediate source state comes with a
`StateImage`, and every edge retains its corresponding target execution. -/
inductive ImageSteps :
    {sourceSize : Nat} ->
    {source : LambdaPFC.State sourceSize} ->
    StateImage source ->
    {targetSize : Nat} ->
    {target : LambdaPFC.State targetSize} ->
    StateImage target -> Prop where
  | refl (image : StateImage state) : ImageSteps image image
  | tail
      (head : ImageStep before middle)
      (rest : ImageSteps middle after) :
      ImageSteps before after

namespace ImageSteps

/-- Forget images and target evidence to recover the native heterogeneous CK
execution. -/
theorem source_steps
    {sourceSize targetSize : Nat}
    {source : LambdaPFC.State sourceSize}
    {target : LambdaPFC.State targetSize}
    {before : StateImage source} {after : StateImage target}
    (steps : ImageSteps before after) :
    LambdaPFC.State.Steps source target := by
  induction steps with
  | refl => exact .refl
  | tail head rest ih => exact .tail head.sourceStep ih

/-- Compose the target executions stored on all image edges. -/
theorem target_steps
    {sourceSize targetSize : Nat}
    {source : LambdaPFC.State sourceSize}
    {target : LambdaPFC.State targetSize}
    {before : StateImage source} {after : StateImage target}
    (steps : ImageSteps before after) :
    SystemFCo.Exp.Steps before.target after.target := by
  induction steps with
  | refl => exact .refl
  | tail head rest ih => exact head.targetSteps.trans ih

/-- The endpoint image of any finite image trace entails source progress. -/
theorem after_progress
    {sourceSize targetSize : Nat}
    {source : LambdaPFC.State sourceSize}
    {target : LambdaPFC.State targetSize}
    {before : StateImage source} {after : StateImage target}
    (_steps : ImageSteps before after) : LambdaPFC.State.Progress target :=
  OperationalSourceProgress.StateImage.sourceProgress after

/-- Hence no endpoint represented by a finite image trace is source-stuck. -/
theorem after_not_stuck
    {sourceSize targetSize : Nat}
    {source : LambdaPFC.State sourceSize}
    {target : LambdaPFC.State targetSize}
    {before : StateImage source} {after : StateImage target}
    (steps : ImageSteps before after) :
    Not (OperationalSafety.State.IsStuck target) :=
  OperationalSafety.State.not_stuck_of_progress steps.after_progress

end ImageSteps

/-- Abstract one-step image preservation.

Each concrete source step must be lifted to a successor image and target
execution.  `OperationalOneStepPreservation.preservation` discharges this
interface for every native CK constructor in the operationally admissible
core, using `ImageStep.ofEvidence` to package each concrete transition. -/
def OneStepPreservation : Prop :=
  forall {sourceSize targetSize : Nat}
      {source : LambdaPFC.State sourceSize}
      {target : LambdaPFC.State targetSize},
    (before : StateImage source) ->
    LambdaPFC.State.Step source target ->
    Exists fun after : StateImage target => ImageStep before after

/-- One-step image preservation lifts an arbitrary finite native CK
execution to a finite image trace. -/
theorem lift_source_steps
    (preserves : OneStepPreservation)
    {sourceSize targetSize : Nat}
    {source : LambdaPFC.State sourceSize}
    {target : LambdaPFC.State targetSize}
    (before : StateImage source)
    (steps : LambdaPFC.State.Steps source target) :
    Exists fun after : StateImage target => ImageSteps before after := by
  induction steps with
  | refl => exact ⟨before, .refl before⟩
  | tail head rest ih =>
      rcases preserves before head with ⟨middle, liftedHead⟩
      rcases ih middle with ⟨after, liftedRest⟩
      exact ⟨after, .tail liftedHead liftedRest⟩

/-- A complete one-step image-preservation theorem rules out source failure
for every closed admissible program.

The target component of the lifted trace is available through
`ImageSteps.target_steps`, but the contradiction below uses only the final
image's source-progress theorem. -/
theorem not_goesWrong
    {term : LambdaPFC.Tm 0} {sourceType : LambdaPFC.Ty 0}
    (typing : Fragment.HasType LambdaPFC.Ctx.nil term sourceType)
    (admissible : OperationalAdmissibility.OperationallyAdmissible typing)
    (preserves : OneStepPreservation) :
    Not (OperationalSafety.GoesWrong term) := by
  intro goesWrong
  rcases goesWrong with ⟨size, state, sourceSteps, stuck⟩
  let initial := OperationalStateImage.StateImage.initial typing admissible
  rcases lift_source_steps preserves initial sourceSteps with
    ⟨after, imageSteps⟩
  exact imageSteps.after_not_stuck stuck

end OperationalImageSafety
end LambdaPToFCo
