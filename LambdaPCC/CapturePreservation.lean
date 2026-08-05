import LambdaPCC.CaptureAllocation

/-!
Progress and one-step preservation for the joint typing-and-use invariant.
The application case discharges a closure's capture set through the path used
when it is applied. Allocation extends the valid world and weakens the result
type and use set.
-/

namespace LambdaPCC
namespace Cap

noncomputable section

/-! ## Progress -/

theorem TermEvidence.progress
    {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {term : Tm n} {T : Ty n}
    {C : CaptureSet n} (evidence : TermEvidence valid term T C)
    (cont : Tm.Cont n) : State.Progress (State.mk sigma cont term) := by
  cases evidence with
  | path resolution suffix coverage =>
      rename_i p x
      cases p with
      | var =>
          cases resolution
          exact State.Progress.path_var
      | fst =>
          exact State.Progress.path resolution
            (fun isVariable => by cases isVariable)
      | sel =>
          exact State.Progress.path resolution
            (fun isVariable => by cases isVariable)
  | value value coverage =>
      exact State.Progress.value value.isValue
  | app function argument suffix coverage =>
      let functionView := function.pathView
      let argumentView := argument.pathView
      have possibleFunction :=
        function.pathLocationAt functionView.resolution
      cases possibleFunction with
      | «fun» lookup body input output captures =>
          exact State.Progress.app functionView.resolution
            argumentView.resolution lookup.binds
  | «let» bound body suffix coverage =>
      exact State.Progress.let_term

theorem StateEvidence.progress
    (evidence : StateEvidence valid state T C) : State.Progress state := by
  cases evidence with
  | ok continuation term => exact term.progress _

/-! ## Application reduction -/

private theorem CaptureSet.open_body_use
    (Q : CaptureSet n) (y : Fin n) :
    (CaptureSet.union Q.weaken
      (CaptureSet.singleton (.var 0))).open (.var y) =
      CaptureSet.union Q (CaptureSet.singleton (.var y)) := by
  change CaptureSet.union (Q.weaken.open (.var y))
    (CaptureSet.singleton (.var y)) = _
  rw [CaptureSet.weaken_open]

/-- Reduce one semantically typed application. The capture set of the closure
is folded through the function path, and the formal argument path is aliased
with the concrete argument path. -/
private noncomputable def TermEvidence.beta
    {n : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {p q : Path n}
    {Cf Cp Cq E : CaptureSet n} {S T : Ty n} {U : Ty (n + 1)}
    {f y : Fin n} {A : Ty n} {body : Tm (n + 1)}
    (function : TermEvidence valid (.path p)
      (.capt Cf (.Fun S U)) Cp)
    (argument : TermEvidence valid (.path q) S Cq)
    (suffix : TyCoercion world (U.open q) T)
    (applicationCoverage : Relation world (.union Cp Cq) E)
    (functionResolution : Path.Resolve p sigma (.loc f))
    (argumentResolution : Path.Resolve q sigma (.loc y))
    (binding : Store.Binds sigma f (.abs A body)) :
    TermEvidence valid (body.open y) T E := by
  have possibleFunction := function.pathLocationAt functionResolution
  have possibleArgument := argument.pathLocationAt argumentResolution
  cases possibleFunction with
  | «fun» lookup closure input output captures =>
      cases Store.Binds.unique lookup.binds binding
      have applied := closure.apply (valid := valid)
        (input.actionLocation possibleArgument)
      have instantiated := applied.castType
        (output.instantiate possibleArgument)
      have relocate :
          TyCoercion world (U.open (.var y)) (U.open q) :=
        .runtime (.replace U
          (.symm (.ofResolve argumentResolution .var)))
      have functionUse : Relation world _ Cp :=
        (Relation.fold functionResolution lookup).comp
          function.pathView.coverage
      have argumentUse : Relation world _ Cq :=
        (Relation.alias argumentResolution Path.Resolve.var).comp
          argument.pathView.coverage
      have bodyUse := Relation.unionElim
        (functionUse.comp Relation.unionLeft)
        (argumentUse.comp Relation.unionRight)
      apply (instantiated.castType (relocate.comp suffix)).castUse
      simpa only [CaptureSet.open_body_use] using
        bodyUse.comp applicationCoverage

/-! ## Application coverage -/

/-- An application event extracted from an application transition. -/
inductive State.Step.ApplicationEvent :
    {n m : Nat} -> {source : State n} -> {target : State m} ->
      (step : State.Step source target) -> Path n -> Path n -> Prop where
| app {n : Nat} {sigma : Store n} {p q : Path n} {f y : Fin n}
    {A : Ty n} {body : Tm (n + 1)} {cont : Tm.Cont n}
    (function : Path.Resolve p sigma (.loc f))
    (argument : Path.Resolve q sigma (.loc y))
    (binding : Store.Binds sigma f (.abs A body)) :
    State.Step.ApplicationEvent
      (State.Step.app (k := cont) function argument binding) p q

/-- Both paths inspected by an application transition are covered by the use
set of its runtime term. -/
theorem TermEvidence.coversApplication
    {n m : Nat} {sigma : Store n} {world : World sigma}
    {valid : World.Valid world} {cont : Tm.Cont n} {term : Tm n}
    {target : State m} {T : Ty n} {C : CaptureSet n} {p q : Path n}
    (evidence : TermEvidence valid term T C)
    (step : State.Step (State.mk sigma cont term) target)
    (event : State.Step.ApplicationEvent step p q) :
    Nonempty
      (Relation world (.singleton p) C ×
        Relation world (.singleton q) C) := by
  cases event with
  | app functionResolution argumentResolution binding =>
      let view := evidence.appView
      exact ⟨⟨
        view.function.pathView.coverage.comp
          (Relation.unionLeft.comp view.coverage),
        view.argument.pathView.coverage.comp
          (Relation.unionRight.comp view.coverage)
      ⟩⟩

/-- Application operands are covered by the use set of the complete
machine invariant, including its continuation. -/
theorem StateEvidence.coversApplication
    {n m : Nat} {source : State n} {target : State m}
    {world : World source.store} {valid : World.Valid world}
    {T : Ty n} {C : CaptureSet n} {p q : Path n}
    (evidence : StateEvidence valid source T C)
    (step : State.Step source target)
    (event : State.Step.ApplicationEvent step p q) :
    Nonempty
      (Relation world (.singleton p) C ×
        Relation world (.singleton q) C) := by
  cases source with
  | mk sigma cont runtimeTerm =>
      cases evidence with
      | ok continuation term =>
          rcases term.coversApplication step event with
            ⟨⟨functionCoverage, argumentCoverage⟩⟩
          exact ⟨⟨
            functionCoverage.comp continuation.inputCoverage,
            argumentCoverage.comp continuation.inputCoverage
          ⟩⟩

/-! ## One-step preservation -/

inductive Ty.Extends : {n m : Nat} -> Ty n -> Ty m -> Prop where
| refl : Ty.Extends T T
| alloc : Ty.Extends S T -> Ty.Extends S T.weaken

theorem Ty.Extends.trans
    (first : Ty.Extends S T) (second : Ty.Extends T U) :
    Ty.Extends S U := by
  induction second with
  | refl => exact first
  | alloc _ ih => exact .alloc (ih first)

inductive CaptureSet.Extends :
    {n m : Nat} -> CaptureSet n -> CaptureSet m -> Prop where
| refl : CaptureSet.Extends C C
| alloc : CaptureSet.Extends C D -> CaptureSet.Extends C D.weaken

theorem CaptureSet.Extends.trans
    (first : CaptureSet.Extends C D)
    (second : CaptureSet.Extends D E) : CaptureSet.Extends C E := by
  induction second with
  | refl => exact first
  | alloc _ ih => exact .alloc (ih first)

/-- One transition preserves joint state evidence.  An allocation transition
extends the world and weakens both type and use indices once. -/
theorem StateEvidence.preservation
    {n m : Nat} {source : State n} {target : State m}
    {world : World source.store} {valid : World.Valid world}
    {T : Ty n} {C : CaptureSet n}
    (evidence : StateEvidence valid source T C)
    (step : State.Step source target) :
    exists (targetWorld : World target.store)
      (targetValid : World.Valid targetWorld)
      (U : Ty m) (D : CaptureSet m),
      Ty.Extends T U /\ CaptureSet.Extends C D /\
        Nonempty (StateEvidence targetValid target U D) := by
  cases step with
  | app functionResolution argumentResolution binding =>
      cases evidence with
      | ok continuation term =>
          let view := term.appView
          have reduced := view.function.beta view.argument view.suffix
            view.coverage functionResolution argumentResolution binding
          exact ⟨world, valid, _, _, .refl, .refl,
            ⟨.ok continuation reduced⟩⟩
  | path resolution notVariable =>
      cases evidence with
      | ok continuation term =>
          let view := term.pathView
          have paths : Path.RuntimeEq _ (.var _) _ :=
            .ofResolve .var resolution
          have back : TyCoercion world
              (.capt (.singleton (.var _)) (.Single (.var _)))
              (.capt (.singleton _) (.Single _)) :=
            .runtime (.capt (.singleton paths) (.single paths))
          have uses : Relation world (.singleton (.var _)) _ :=
            (Relation.alias resolution Path.Resolve.var).comp
              view.coverage
          exact ⟨world, valid, _, _, .refl, .refl,
            ⟨.ok continuation (.path .var (back.comp view.suffix) uses)⟩⟩
  | let_push =>
      cases evidence with
      | ok continuation term =>
          let view := term.letView
          have currentCoverage := view.coverage.comp
            continuation.inputCoverage
          exact ⟨world, valid, _, _, .refl, .refl,
            ⟨.ok (.cons continuation view.closure view.suffix
              currentCoverage view.coverage) view.bound⟩⟩
  | «return» =>
      cases evidence with
      | ok continuation term =>
          cases continuation with
          | cons tail closure suffix current bodyCoverage =>
              have argument := term.pathLocationAt Path.Resolve.var
              have resumed := closure.apply (valid := valid) argument
              simp only [Ty.weaken_open,
                CaptureSet.weaken_open] at resumed
              exact ⟨world, valid, _, _, .refl, .refl,
                ⟨.ok tail
                  ((resumed.castType suffix).castUse bodyCoverage)⟩⟩
  | allocate isValue =>
      cases evidence with
      | ok continuation term =>
          cases continuation with
          | cons tail closure suffix current bodyCoverage =>
              rcases term.nonemptyValueView isValue with ⟨view⟩
              let exact := view.value.toExact
              let targetWorld := World.val world exact (vv := isValue)
              let targetValid := valid.extend view.value
                (exact := exact) (vv := isValue)
              have resumed := closure.allocate
                (valid := valid) view.value isValue
              have targetTerm :=
                (resumed.castType (suffix.weaken exact isValue)).castUse
                  (bodyCoverage.weaken exact isValue)
              exact ⟨targetWorld, targetValid, _, _, .alloc .refl,
                .alloc .refl,
                ⟨.ok (tail.weaken view.value isValue) targetTerm⟩⟩

end
end Cap
end LambdaPCC
