import FCsub.Dynamics

/-!
# Closed-program progress for FCsub

The operational value predicate exposes structured casts only when their
matching eliminator is present.  Opaque evidence variables cannot occur in
the empty context, and a closed runtime value cannot have bottom type.
-/

namespace FCsub

namespace Tm

/-- A closed term is either an operational value or can take one annotated
step. -/
abbrev Progress (term : Tm []) : Prop :=
  IsRuntimeValue term ∨ ∃ next, Step term next

theorem noClosedVar {kind : BinderKind} (index : BVar [] kind) : False := by
  cases index

/-- No closed operational value has bottom type. -/
theorem noValueOfBot {term : Tm []}
    (value : IsRuntimeValue term) (typing : HasType Ctx.nil term .bot) :
    False := by
  induction value with
  | unit => cases typing
  | lam => cases typing
  | cast termValue inert induction =>
      cases typing with
      | cast termTyping evidenceTyping =>
          cases inert with
          | var index => cases index
          | top source => cases evidenceTyping
          | bot target =>
              cases evidenceTyping
              exact induction termTyping
          | equality atom =>
              cases atom with
              | var index => cases index
              | symmVar index => cases index
          | arr domain codomain => cases evidenceTyping
          | existsT adaptation sourcePayload targetPayload payload =>
              cases evidenceTyping
          | forallT adaptation sourceBody targetBody body =>
              cases evidenceTyping
  | pack => cases typing
  | slam => cases typing

/-- A closed value at arrow type is an ordinary lambda or an arrow cast, so
application can step once its argument is a value. -/
theorem valueArrowEliminates {function argument : Tm []}
    {domain : Ty []} {codomain : Ty ([] ▹ .term)}
    (functionValue : IsRuntimeValue function)
    (functionTyping : HasType Ctx.nil function (.arr domain codomain))
    (argumentValue : IsRuntimeValue argument) :
    ∃ next, Step (.app function argument) next := by
  cases functionValue with
  | unit => cases functionTyping
  | lam => exact ⟨_, .beta argumentValue⟩
  | cast innerValue inert =>
      cases functionTyping with
      | cast innerTyping evidenceTyping =>
          cases inert with
          | var index => cases index
          | top source => cases evidenceTyping
          | bot target =>
              cases evidenceTyping
              exact False.elim (noValueOfBot innerValue innerTyping)
          | equality atom =>
              cases atom with
              | var index => cases index
              | symmVar index => cases index
          | arr castDomain castCodomain =>
              exact ⟨_, .appCastArrow innerValue argumentValue⟩
          | existsT adaptation sourcePayload targetPayload payload =>
              cases evidenceTyping
          | forallT adaptation sourceBody targetBody body =>
              cases evidenceTyping
  | pack => cases functionTyping
  | slam => cases functionTyping

/-- A closed value at existential type is a package or an existential cast,
so opening it can step. -/
theorem valueExistsEliminates {names constraints : Nat}
    {telescope : Telescope [] names constraints}
    {payloadType : Ty (StaticScope [] names constraints)}
    {package : Tm []} {body : Tm (PayloadScope [] names constraints)}
    (packageValue : IsRuntimeValue package)
    (packageTyping : HasType Ctx.nil package
      (.existsT telescope payloadType)) :
    ∃ next, Step (.open telescope payloadType package body) next := by
  cases packageValue with
  | unit => cases packageTyping
  | lam => cases packageTyping
  | cast innerValue inert =>
      cases packageTyping with
      | cast innerTyping evidenceTyping =>
          cases inert with
          | var index => cases index
          | top source => cases evidenceTyping
          | bot target =>
              cases evidenceTyping
              exact False.elim (noValueOfBot innerValue innerTyping)
          | equality atom =>
              cases atom with
              | var index => cases index
              | symmVar index => cases index
          | arr domain codomain => cases evidenceTyping
          | existsT adaptation sourcePayload targetPayload payload =>
              cases evidenceTyping
              exact ⟨_, by
                exact Step.openCastExists
                  (targetTelescope := telescope)
                  (package := _)
                  (body := body) innerValue⟩
          | forallT adaptation sourceBody targetBody bodyEvidence =>
              cases evidenceTyping
  | pack payloadValue =>
      cases packageTyping
      exact ⟨_, .openPack payloadValue⟩
  | slam => cases packageTyping

/-- A closed value at universal telescope type is a static abstraction or a
universal cast, so static application can step. -/
theorem valueForallEliminates {names constraints : Nat}
    {telescope : Telescope [] names constraints}
    {bodyType : Ty (StaticScope [] names constraints)}
    {function : Tm []} {witnesses : TypeArgs [] names}
    {evidence : LeArgs [] constraints}
    (functionValue : IsRuntimeValue function)
    (functionTyping : HasType Ctx.nil function
      (.forallT telescope bodyType)) :
    ∃ next, Step (.sapp telescope function witnesses evidence) next := by
  cases functionValue with
  | unit => cases functionTyping
  | lam => cases functionTyping
  | cast innerValue inert =>
      cases functionTyping with
      | cast innerTyping evidenceTyping =>
          cases inert with
          | var index => cases index
          | top source => cases evidenceTyping
          | bot target =>
              cases evidenceTyping
              exact False.elim (noValueOfBot innerValue innerTyping)
          | equality atom =>
              cases atom with
              | var index => cases index
              | symmVar index => cases index
          | arr domain codomain => cases evidenceTyping
          | existsT adaptation sourcePayload targetPayload payload =>
              cases evidenceTyping
          | forallT adaptation sourceBody targetBody bodyEvidence =>
              cases evidenceTyping
              exact ⟨_, by
                exact Step.sappCastForall
                  (targetTelescope := telescope)
                  (function := _)
                  (witnesses := witnesses)
                  (evidence := evidence) innerValue⟩
  | pack => cases functionTyping
  | slam bodyValue =>
      cases functionTyping
      exact ⟨_, .sappSlam bodyValue⟩

/-- Conventional progress for closed, well-typed FCsub programs. -/
theorem progress {term : Tm []} {type : Ty []}
    (typing : HasType Ctx.nil term type) : Progress term := by
  cases typing with
  | unit => exact .inl .unit
  | @var _ _ index _ binding => exact False.elim (noClosedVar index)
  | lam bodyTyping => exact .inl .lam
  | app functionTyping argumentTyping nonescape =>
      have functionInduction := progress functionTyping
      have argumentInduction := progress argumentTyping
      cases functionInduction with
      | inr functionSteps =>
          obtain ⟨next, step⟩ := functionSteps
          exact .inr ⟨_, .appFunction step⟩
      | inl functionValue =>
          cases argumentInduction with
          | inr argumentSteps =>
              obtain ⟨next, step⟩ := argumentSteps
              exact .inr ⟨_, .appArgument functionValue step⟩
          | inl argumentValue =>
              exact .inr
                (valueArrowEliminates functionValue functionTyping argumentValue)
  | let' rhsTyping bodyTyping nonescape =>
      have rhsInduction := progress rhsTyping
      cases rhsInduction with
      | inl rhsValue => exact .inr ⟨_, .zeta rhsValue⟩
      | inr rhsSteps =>
          obtain ⟨next, step⟩ := rhsSteps
          exact .inr ⟨_, .letRhs step⟩
  | cast termTyping evidenceTyping =>
      have induction := progress termTyping
      cases induction with
      | inr termSteps =>
          obtain ⟨next, step⟩ := termSteps
          exact .inr ⟨_, .castInner step⟩
      | inl termValue =>
          cases evidenceTyping with
          | @var _ _ index _ _ binding =>
              exact False.elim (noClosedVar index)
          | refl type => exact .inr ⟨_, .castRefl termValue⟩
          | trans firstTyping secondTyping =>
              exact .inr ⟨_, .castTrans termValue⟩
          | top source => exact .inl (.cast termValue (.top _))
          | bot target => exact .inl (.cast termValue (.bot _))
          | eqToLe equalityTyping =>
              cases equalityTyping with
              | @var index _ _ binding =>
                  exact False.elim (noClosedVar index)
              | refl type => exact .inr ⟨_, .castEqRefl termValue⟩
              | symm innerTyping =>
                  cases innerTyping with
                  | @var index _ _ binding =>
                      exact False.elim (noClosedVar index)
                  | refl type => exact .inr ⟨_, .castEqSymmRefl termValue⟩
                  | symm typing => exact .inr ⟨_, .castEqSymmSymm termValue⟩
                  | trans first second =>
                      exact .inr ⟨_, .castEqSymmTrans termValue⟩
              | trans firstTyping secondTyping =>
                  exact .inr ⟨_, .castEqTrans termValue⟩
          | arr domainTyping codomainTyping =>
              exact .inl (.cast termValue (.arr _ _))
          | existsT adaptationTyping payloadTyping =>
              exact .inl (.cast termValue (.existsT _ _ _ _))
          | forallT adaptationTyping bodyTyping =>
              exact .inl (.cast termValue (.forallT _ _ _ _))
  | pack argumentsTyping payloadTyping =>
      have payloadInduction := progress payloadTyping
      cases payloadInduction with
      | inl payloadValue => exact .inl (.pack payloadValue)
      | inr payloadSteps =>
          obtain ⟨next, step⟩ := payloadSteps
          exact .inr ⟨_, .packPayload step⟩
  | openT packageTyping bodyTyping nonescape =>
      have packageInduction := progress packageTyping
      cases packageInduction with
      | inr packageSteps =>
          obtain ⟨next, step⟩ := packageSteps
          exact .inr ⟨_, .openScrutinee step⟩
      | inl packageValue =>
          exact .inr (valueExistsEliminates packageValue packageTyping)
  | slam bodyValue bodyTyping => exact .inl (.slam bodyValue)
  | sapp functionTyping argumentsTyping =>
      have functionInduction := progress functionTyping
      cases functionInduction with
      | inr functionSteps =>
          obtain ⟨next, step⟩ := functionSteps
          exact .inr ⟨_, .sappFunction step⟩
      | inl functionValue =>
          exact .inr (valueForallEliminates functionValue functionTyping)
  | newtype bodyTyping nonescape => exact .inr ⟨_, .newtype⟩
termination_by sizeOf term
decreasing_by
  all_goals
    subst_vars
    simp_all <;> omega

end Tm

end FCsub
