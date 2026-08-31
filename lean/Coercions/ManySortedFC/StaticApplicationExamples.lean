import Coercions.ManySortedFC.Dynamics
import Coercions.ManySortedFC.TermCheckerCompleteness
import Coercions.ManySortedFC.TermExamples

/-!
# Computation-capable static-application regressions

These examples exercise the narrow static-elimination extension: a static
application's scrutinee may compute, while static abstraction itself remains
value-only.
-/

namespace ManySortedFC.StaticApplicationExamples

open StaticExamples

abbrev MixedStaticScope : Sig :=
  StaticScope [] [.type, .capture]
    [.equality .type, .equality .capture]

def mixedStaticUnitType : Ty [] :=
  .capturing .empty
    (.forallT exactMixedTheory (.one : Ty MixedStaticScope))

/-- A proper computation returning the real captured type produced by
`staticLam`. -/
def computedStaticUnit : Tm [] :=
  .let' mixedStaticUnitType .empty .unit
    TermExamples.mixedStaticUnit.weaken
    (.captureEmpty .empty)

theorem computed_static_unit_is_not_a_value :
    Tm.checkValue computedStaticUnit = none := rfl

theorem computed_static_unit_has_no_value_derivation :
    ¬ Tm.IsValue computedStaticUnit := by
  intro value
  cases value

theorem computed_static_unit_is_accepted :
    Tm.synth Ctx.nil computedStaticUnit =
      some (.union .empty .empty, mixedStaticUnitType) := by
  native_decide

/-- Static application now accepts that computation directly. -/
def appliedComputedStaticUnit : Tm [] :=
  .sapp exactMixedTheory computedStaticUnit exactMixedWitnesses
    exactMixedEvidence

theorem computed_static_application_is_accepted :
    Tm.synth Ctx.nil appliedComputedStaticUnit =
      some (.union (.union .empty .empty) .empty, .one) := by
  native_decide

/-- The generalized rule still yields a proof accepted by the independent
checker. -/
theorem computed_static_application_has_checked_typing :
    Nonempty (Tm.HasType Ctx.nil appliedComputedStaticUnit
      (.union (.union .empty .empty) .empty) .one) := by
  have accepted := computed_static_application_is_accepted
  unfold Tm.synth at accepted
  obtain ⟨checked, checkedEq, indicesEq⟩ := Option.map_eq_some_iff.mp accepted
  cases checked with
  | mk use type typing =>
      dsimp at indicesEq
      cases Prod.mk.inj indicesEq with
      | intro useEq typeEq =>
          subst use
          subst type
          exact ⟨typing⟩

/-! ## Focused dynamics -/

/-- The one ambient computation step used by this regression.  The static
application relation is parameterized over it rather than claiming to be a
full annotated semantics. -/
inductive ComputationStep : {scope : Sig} -> Tm scope -> Tm scope -> Prop where
  | computed : ComputationStep computedStaticUnit
      TermExamples.mixedStaticUnit

theorem computationStep_erases
    {scope : Sig} {first second : Tm scope}
    (step : ComputationStep first second) :
    Runtime.Step first.erase second.erase := by
  cases step
  exact .zeta .unit

/-- The scrutinee takes exactly its ambient step; witnesses and evidence are
unchanged. -/
theorem computed_scrutinee_steps_in_place :
    Tm.StaticAppStep ComputationStep appliedComputedStaticUnit
      TermExamples.appliedMixedStaticUnit :=
  .function computed_static_unit_has_no_value_derivation .computed

theorem computed_scrutinee_step_matches_runtime :
    Runtime.Step appliedComputedStaticUnit.erase
      TermExamples.appliedMixedStaticUnit.erase :=
  Tm.StaticAppStep.erase_function computationStep_erases
    computed_static_unit_has_no_value_derivation .computed

/-- Once the scrutinee is the real captured static abstraction, static beta
instantiates its complete mixed model. -/
theorem real_static_abstraction_beta :
    Tm.StaticAppStep ComputationStep
      TermExamples.appliedMixedStaticUnit .unit := by
  exact .beta .unit

theorem real_static_abstraction_beta_stutters :
    TermExamples.appliedMixedStaticUnit.erase =
      (Tm.unit : Tm []).erase :=
  Tm.StaticAppStep.erase_beta (.unit : Tm.IsValue
    (.unit : Tm MixedStaticScope))

/-! ### Static beta substitutes the complete model -/

/-- The newest static name below the mixed theory's two proof binders. -/
def mixedAbstractType : Ty MixedStaticScope :=
  .tvar (.there (.there .here))

/-- The body uses both the abstract type name and the newest equality
assumption.  Symmetry turns `a = One` into the adapter `One <= a`. -/
def modelDependentBody : Tm MixedStaticScope :=
  .adapt .unit
    (.cast (.equalityToInclusion (.equalitySymm (.var .here))))

def modelDependentStaticValue : Tm [] :=
  .slam exactMixedTheory .empty modelDependentBody
    (.inclusionRefl (.capture .empty))

theorem model_dependent_static_value_is_accepted :
    Tm.synth Ctx.nil modelDependentStaticValue =
      some (.empty,
        .capturing .empty
          (.forallT exactMixedTheory mixedAbstractType)) := by
  native_decide

def appliedModelDependentStaticValue : Tm [] :=
  .sapp exactMixedTheory modelDependentStaticValue exactMixedWitnesses
    exactMixedEvidence

theorem model_dependent_static_application_is_accepted :
    Tm.synth Ctx.nil appliedModelDependentStaticValue =
      some (.empty, .one) := by
  native_decide

/-- Both the type name and its proof variable are replaced simultaneously. -/
theorem complete_model_is_substituted :
    modelDependentBody.instantiateStatic exactMixedWitnesses
      exactMixedEvidence =
    (.adapt .unit
      (.cast
        (.equalityToInclusion
          (.equalitySymm (.equalityRefl (.type .one))))) : Tm []) :=
  rfl

theorem model_dependent_static_beta :
    Tm.StaticAppStep ComputationStep appliedModelDependentStaticValue
      (modelDependentBody.instantiateStatic exactMixedWitnesses
        exactMixedEvidence) :=
  .beta (.adapt .unit)

theorem model_dependent_static_beta_stutters :
    appliedModelDependentStaticValue.erase =
      (modelDependentBody.instantiateStatic exactMixedWitnesses
        exactMixedEvidence).erase :=
  Tm.StaticAppStep.erase_beta (.adapt .unit)

/-! ## Rejected boundaries -/

def computedMixedBody : Tm MixedStaticScope :=
  .let' .one .empty .unit .unit (.captureEmpty .empty)

/-- Generalizing static application does not generalize static abstraction:
its body must still erase to an already available runtime value. -/
def staticLamWithComputedBody : Tm [] :=
  .slam exactMixedTheory .empty computedMixedBody
    (.inclusionRefl (.capture .empty))

theorem computed_static_abstraction_is_rejected :
    (Tm.check Ctx.nil staticLamWithComputedBody).isNone = true := by
  native_decide

def impossibleStaticUnit : Tm [] :=
  .slam impossibleTypeInterval .empty .unit
    (.inclusionRefl (.capture .empty))

/-- A malformed realization is rejected even though the scrutinee has the
right universal interface. -/
def malformedStaticApplication : Tm [] :=
  .sapp impossibleTypeInterval impossibleStaticUnit impossibleTypeWitness
    reflexiveTypeEvidence

theorem malformed_static_model_is_rejected :
    (Tm.check Ctx.nil malformedStaticApplication).isNone = true := by
  native_decide

end ManySortedFC.StaticApplicationExamples
