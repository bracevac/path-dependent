import DotToFCsub.M5.Translation
import DotFCR.Source.Runtime
import FCsub.Simulation

/-!
# Operational correspondence for recursive type-member objects

Recursive type definitions are static in both calculi.  A source `recObj`
erases to runtime unit; the target package erases through its package and
explicit fold wrappers to the same runtime unit.  The only new annotated
computation is canonical `unfoldRec (foldRec v)`, which stutters under
erasure and is covered by FCsub's simulation theorem.
-/

namespace DotToFCsub.M5

open DotFCR.Source

/-- Cross-calculus relation needed by the closed recursive-object slice. -/
inductive RuntimeRelated :
    DotFCR.Source.Runtime.Tm [] → FCsub.Runtime.Tm [] → Prop where
  | unit : RuntimeRelated .unit .unit

@[simp]
theorem erase_source_recursive_object
    (definitions : List (TypeDef ClosedSelfScope)) :
    (Tm.recObj definitions).erase = DotFCR.Source.Runtime.Tm.unit := rfl

@[simp]
theorem erase_target_recursive_object
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) :
    encoding.object.erase = FCsub.Runtime.Tm.unit := rfl

/-- Erasure correspondence for every translated recursive object. -/
theorem recursive_object_erasure_correspondence
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) :
    RuntimeRelated (Tm.recObj definitions).erase encoding.object.erase := by
  simp only [erase_source_recursive_object, erase_target_recursive_object]
  exact .unit

/-- The target package is already an annotated runtime value. -/
theorem target_recursive_object_is_value
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) :
    FCsub.Tm.IsRuntimeValue encoding.object := by
  exact .pack (.foldRec .unit)

/-- Explicit observation of the folded self payload. -/
def observePayload {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) : FCsub.Tm [] :=
  .unfoldRec encoding.block (selfIndex definitions.length) encoding.payload

/-- Canonical fold/unfold computation exposes the erased unit. -/
theorem observePayload_step
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) :
    FCsub.Tm.Step (observePayload encoding) .unit := by
  simpa [observePayload, Encoding.payload] using
    (FCsub.Tm.Step.unfoldFold
      (bodies := encoding.block)
      (index := selfIndex definitions.length)
      (term := (FCsub.Tm.unit : FCsub.Tm []))
      FCsub.Tm.IsRuntimeValue.unit)

/-- The administrative fold/unfold step has identical erasures. -/
theorem observePayload_erasure_stutters
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) :
    (observePayload encoding).erase = (FCsub.Tm.unit : FCsub.Tm []).erase := rfl

/-- The generic FCsub simulation theorem validates the same step at runtime. -/
theorem observePayload_runtime_simulation
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) :
    FCsub.Runtime.Steps (observePayload encoding).erase
      (FCsub.Tm.unit : FCsub.Tm []).erase :=
  (observePayload_step encoding).erase_simulates

/-- Complete operational statement for the exact M5 scope.  Source and target
objects are values, their erasures are related units, and the target's only
recursive observation is the explicit fold/unfold step that stutters after
erasure.  No broader contextual-equivalence claim is made here. -/
structure StaticObjectCorrespondence
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) : Prop where
  sourceValue : DotFCR.Source.Runtime.IsValue
    (Tm.recObj definitions).erase
  targetValue : FCsub.Tm.IsRuntimeValue encoding.object
  erasuresRelated : RuntimeRelated
    (Tm.recObj definitions).erase encoding.object.erase
  observationStep : FCsub.Tm.Step (observePayload encoding) .unit
  observationStutters : (observePayload encoding).erase =
    (FCsub.Tm.unit : FCsub.Tm []).erase

/-- Operational correspondence packaged for every supported static recursive
object translation. -/
theorem static_object_correspondence
    {definitions : List (TypeDef ClosedSelfScope)}
    (encoding : Encoding (target := []) definitions) :
    StaticObjectCorrespondence encoding where
  sourceValue := by
    rw [erase_source_recursive_object]
    exact .unit
  targetValue := target_recursive_object_is_value encoding
  erasuresRelated := recursive_object_erasure_correspondence encoding
  observationStep := observePayload_step encoding
  observationStutters := observePayload_erasure_stutters encoding

end DotToFCsub.M5
