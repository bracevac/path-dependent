import LambdaPCC.CaptureSafety

/-!
Operational bounds supported by the primitive-free CK machine. Application
coverage bounds the paths inspected by application. The returned-value bound
relates the capture set assigned to a returned value at introduction to the
capture set of its result type.
-/

namespace LambdaPCC
namespace Cap

noncomputable section

/-! ## Capture sets assigned to values at introduction -/

/-- The capture set assigned to a value at introduction is below the capture
set of its assigned type. -/
noncomputable def Value.captureRelation
    {n : Nat} {sigma : Store n} {world : World sigma}
    {v : Tm n} {T : Ty n} {Q : CaptureSet n}
    (value : Value world v T Q) : Relation world Q T.captureSet := by
  cases value with
  | abs body suffix => exact suffix.captureRelation
  | pair suffix => exact suffix.captureRelation
  | typePair suffix => exact suffix.captureRelation
  | capturePair suffix => exact suffix.captureRelation

/-! ## Returned values -/

/-- The value returned by a final machine state, either directly or through
the location in the final variable path. -/
inductive State.Returns : State n -> Tm n -> Prop where
| value {n : Nat} {sigma : Store n} {v : Tm n} :
    v.IsValue -> State.Returns (State.mk sigma [] v) v
| location {n : Nat} {sigma : Store n} {x : Fin n} {v : Tm n} :
    Store.Binds sigma x v ->
    State.Returns (State.mk sigma [] (.path (.var x))) v

/-- A returned value together with its assigned capture-set bound. -/
structure FinalCapture
    {n : Nat} {sigma : Store n} {world : World sigma}
    (valid : World.Valid world) (state : State n) (T : Ty n) : Type 1 where
  valueTerm : Tm n
  valueType : Ty n
  assignedCaptureSet : CaptureSet n
  returns : State.Returns state valueTerm
  value : Value world valueTerm valueType assignedCaptureSet
  subcapture : Relation world assignedCaptureSet T.captureSet

/-- A final state has a returned value whose assigned capture set is below
the capture set of the state's result type. -/
theorem StateEvidence.returnedCaptureBound
    {n : Nat} {state : State n} {world : World state.store}
    {valid : World.Valid world} {T : Ty n} {C : CaptureSet n}
    (evidence : StateEvidence valid state T C)
    (final : State.IsFinal state) :
    Nonempty (FinalCapture valid state T) := by
  cases final with
  | @location sigma x =>
      cases evidence with
      | ok continuation term =>
          cases continuation with
          | hole =>
              let entry := valid.entry x
              have captures : Relation world
                  entry.assignedCaptureSet T.captureSet :=
                (Relation.fold Path.Resolve.var entry.lookup).comp
                  term.pathView.suffix.captureRelation
              exact ⟨
                { valueTerm := entry.term
                  valueType := entry.assignedType
                  assignedCaptureSet := entry.assignedCaptureSet
                  returns := .location entry.lookup.binds
                  value := entry.value
                  subcapture := captures }⟩
  | @value sigma v isValue =>
      cases evidence with
      | ok continuation term =>
          cases continuation with
          | hole =>
              rcases term.nonemptyValueView isValue with ⟨view⟩
              exact ⟨
                { valueTerm := v
                  valueType := _
                  assignedCaptureSet := view.assignedCaptureSet
                  returns := .value isValue
                  value := view.value
                  subcapture := view.value.captureRelation }⟩

/-! ## Closed executions -/

/-- Application coverage for a step reached by a closed finite execution. The
bound is the source use set transported through preceding allocations. -/
theorem Tm.Ty.closed_finite_application_coverage
    {term : Tm 0} {T : Ty 0} {C : CaptureSet 0}
    (typing : Tm.Ty Ctx.nil term T C)
    {n m : Nat} {source : State n} {target : State m}
    (steps : State.Steps (State.initial term) source)
    (step : State.Step source target) {p q : Path n}
    (event : State.Step.ApplicationEvent step p q) :
    exists (world : World source.store) (valid : World.Valid world)
      (U : Ty n) (D : CaptureSet n),
      Ty.Extends T U /\ CaptureSet.Extends C D /\
        Nonempty
          (StateEvidence valid source U D ×
            (Relation world (.singleton p) D ×
              Relation world (.singleton q) D)) := by
  obtain ⟨world, valid, U, D, typeExtension, captureExtension,
      ⟨evidence⟩⟩ := typing.closed_finite_preservation steps
  rcases evidence.coversApplication step event with ⟨coverage⟩
  exact ⟨world, valid, U, D, typeExtension, captureExtension,
    ⟨evidence, coverage⟩⟩

/-- Assigned capture-set bound for the value returned by a closed finite
execution. -/
theorem Tm.Ty.closed_finite_returned_capture_bound
    {term : Tm 0} {T : Ty 0} {C : CaptureSet 0}
    (typing : Tm.Ty Ctx.nil term T C)
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial term) target)
    (final : State.IsFinal target) :
    exists (world : World target.store) (valid : World.Valid world)
      (U : Ty n) (D : CaptureSet n),
      Ty.Extends T U /\ CaptureSet.Extends C D /\
        Nonempty (FinalCapture valid target U) := by
  obtain ⟨world, valid, U, D, typeExtension, captureExtension,
      ⟨evidence⟩⟩ := typing.closed_finite_preservation steps
  exact ⟨world, valid, U, D, typeExtension, captureExtension,
    evidence.returnedCaptureBound final⟩

end
end Cap
end LambdaPCC
