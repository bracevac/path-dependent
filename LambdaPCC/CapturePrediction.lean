import LambdaPCC.CaptureSafety

/-!
Public observations supported by the primitive-free CK machine.  Invocation
coverage predicts the paths inspected by application; final-value prediction
relates a returned value's introduction qualifier to its result
type.
-/

namespace LambdaPCC
namespace Cap

noncomputable section

/-! ## Introduction qualifiers of values -/

/-- A value's introduction qualifier is below the outer qualifier of its
assigned type. -/
noncomputable def Value.captureRelation
    {n : Nat} {sigma : Store n} {world : World sigma}
    {v : Tm n} {T : Ty n} {Q : CaptureSet n}
    (value : Value world v T Q) : Relation world Q T.qualifier := by
  cases value with
  | abs body suffix => exact suffix.captureRelation
  | pair qualifier suffix =>
      cases qualifier
      exact suffix.captureRelation
  | typePair qualifier suffix =>
      cases qualifier
      exact suffix.captureRelation
  | capturePair qualifier suffix =>
      cases qualifier
      exact suffix.captureRelation

/-! ## Returned values -/

/-- The value returned by a final machine state, either directly or through
the location in the final variable path. -/
inductive State.Returns : State n -> Tm n -> Prop where
| value {n : Nat} {sigma : Store n} {v : Tm n} :
    v.IsValue -> State.Returns (State.mk sigma [] v) v
| location {n : Nat} {sigma : Store n} {x : Fin n} {v : Tm n} :
    Store.Binds sigma x v ->
    State.Returns (State.mk sigma [] (.path (.var x))) v

/-- Evidence exposed by capture prediction for a final result. -/
structure FinalCapture
    {n : Nat} {sigma : Store n} {world : World sigma}
    (valid : World.Valid world) (state : State n) (T : Ty n) : Type 1 where
  valueTerm : Tm n
  valueType : Ty n
  introductionQualifier : CaptureSet n
  returns : State.Returns state valueTerm
  value : Value world valueTerm valueType introductionQualifier
  subcapture : Relation world introductionQualifier T.qualifier

/-- A final state has a returned value whose introduction qualifier is below
the qualifier of the state's result type. -/
theorem StateEvidence.capturePrediction
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
          | hole resultSuffix useCoverage =>
              let entry := valid.entry x
              have captures : Relation world
                  entry.introductionQualifier T.qualifier :=
                (Relation.fold Path.Resolve.var entry.lookup).comp
                  (term.pathView.suffix.captureRelation.comp
                    resultSuffix.captureRelation)
              exact ⟨
                { valueTerm := entry.term
                  valueType := entry.assignedType
                  introductionQualifier := entry.introductionQualifier
                  returns := .location entry.lookup.binds
                  value := entry.value
                  subcapture := captures }⟩
  | @value sigma v isValue =>
      cases evidence with
      | ok continuation term =>
          cases continuation with
          | hole resultSuffix useCoverage =>
              rcases term.nonemptyValueView isValue with ⟨view⟩
              exact ⟨
                { valueTerm := v
                  valueType := _
                  introductionQualifier := view.introductionQualifier
                  returns := .value isValue
                  value := view.value
                  subcapture := view.value.captureRelation.comp
                    resultSuffix.captureRelation }⟩

/-! ## Closed executions -/

/-- Use prediction for an application reached by a closed finite execution.
The reported bound is the source use set transported through every preceding
allocation. -/
theorem Tm.Ty.closed_finite_use_prediction
    {term : Tm 0} {T : Ty 0} {C : CaptureSet 0}
    (typing : Tm.Ty Ctx.nil term T C)
    {n m : Nat} {source : State n} {target : State m}
    (steps : State.Steps (State.initial term) source)
    (step : State.Step source target) {p q : Path n}
    (event : State.Step.Invokes step p q) :
    exists (world : World source.store) (valid : World.Valid world)
      (U : Ty n) (D : CaptureSet n),
      Ty.Extends T U /\ CaptureSet.Extends C D /\
        Nonempty
          (StateEvidence valid source U D ×
            (Relation world (.singleton p) D ×
              Relation world (.singleton q) D)) := by
  obtain ⟨world, valid, U, D, typeExtension, captureExtension,
      ⟨evidence⟩⟩ := typing.closed_finite_preservation steps
  rcases evidence.coversInvocation step event with ⟨coverage⟩
  exact ⟨world, valid, U, D, typeExtension, captureExtension,
    ⟨evidence, coverage⟩⟩

/-- Capture prediction for a final state reached by a closed finite
execution. -/
theorem Tm.Ty.closed_finite_capture_prediction
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
    evidence.capturePrediction final⟩

end
end Cap
end LambdaPCC
