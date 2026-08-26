import SystemFSub.ElaborationRuntimeReverse
import SystemFSub.ElaborationTyping

/-!
# F<: safety through explicit-coercion elaboration

Source reduction first maps to the intrinsically scoped common runtime. Each
runtime step lifts to finitely many target steps, target preservation supplies
typing at the lifted endpoint, and `typedRuntimeProgress` reflects a genuine
source progress alternative. This rules out source stuck states without
assuming termination of all target reductions.
-/

namespace SystemFSub.Elaboration

theorem sourceValue_of_runtimeValue
    {term : SystemFSub.Tm sig}
    (value : Runtime.IsValue (eraseSource term)) :
    SystemFSub.Tm.IsValue term := by
  cases term with
  | var => exact nomatch value
  | abs => exact .abs
  | app => exact nomatch value
  | tabs => exact .tabs
  | tapp => exact nomatch value

theorem sourceAbs_of_erasedAbs
    {term : SystemFSub.Tm sig} {body : Runtime.Term (() :: sourceRuntimeSig sig)}
    (shape : eraseSource term = Runtime.Term.abs body) :
    Exists fun parameter => Exists fun sourceBody =>
      term = SystemFSub.Tm.abs parameter sourceBody := by
  cases term with
  | var index => exact nomatch shape
  | abs parameter sourceBody => exact ⟨parameter, sourceBody, rfl⟩
  | app => exact nomatch shape
  | tabs => exact nomatch shape
  | tapp => exact nomatch shape

theorem sourceTabs_of_erasedTabs
    {term : SystemFSub.Tm sig} {body : Runtime.Term (sourceRuntimeSig sig)}
    (shape : eraseSource term = Runtime.Term.tabs body) :
    Exists fun bound => Exists fun sourceBody =>
      term = SystemFSub.Tm.tabs bound sourceBody := by
  cases term with
  | var index => exact nomatch shape
  | abs => exact nomatch shape
  | app => exact nomatch shape
  | tabs bound sourceBody => exact ⟨bound, sourceBody, rfl⟩
  | tapp => exact nomatch shape

/-- A runtime step from a ready (doubled-phase) source erasure reflects an
actual source step. The intermediate single type phase is never exposed at a
source-state boundary. -/
theorem sourceStep_of_runtimeStep
    {term : SystemFSub.Tm sig} {runtimeResult : Runtime.Term (sourceRuntimeSig sig)}
    (runtimeStep : Runtime.Step (eraseSource term) runtimeResult) :
    Exists fun result => SystemFSub.Tm.Step term result := by
  cases term with
  | var index =>
      simp only [eraseSource] at runtimeStep
      exact nomatch runtimeStep
  | abs parameter body =>
      simp only [eraseSource] at runtimeStep
      exact nomatch runtimeStep
  | app function argument =>
      simp only [eraseSource] at runtimeStep
      generalize functionEq : eraseSource function = runtimeFunction at runtimeStep
      generalize argumentEq : eraseSource argument = runtimeArgument at runtimeStep
      cases runtimeStep with
      | appFunction functionStep =>
          have sourceStep := functionStep
          rw [← functionEq] at sourceStep
          rcases sourceStep_of_runtimeStep sourceStep with ⟨function', step⟩
          exact ⟨.app function' argument, .app_left step⟩
      | appArgument functionValue argumentStep =>
          have sourceValue := functionValue
          rw [← functionEq] at sourceValue
          have sourceArgumentStep := argumentStep
          rw [← argumentEq] at sourceArgumentStep
          rcases sourceStep_of_runtimeStep sourceArgumentStep with
            ⟨argument', step⟩
          exact ⟨.app function argument',
            .app_right (sourceValue_of_runtimeValue sourceValue) step⟩
      | beta argumentValue =>
          rcases sourceAbs_of_erasedAbs functionEq with
            ⟨parameter, body, rfl⟩
          have sourceArgumentValue := argumentValue
          rw [← argumentEq] at sourceArgumentValue
          exact ⟨body.open argument,
            .beta (sourceValue_of_runtimeValue sourceArgumentValue)⟩
  | tabs bound body =>
      simp only [eraseSource] at runtimeStep
      exact nomatch runtimeStep
  | tapp function argument =>
      simp only [eraseSource] at runtimeStep
      generalize functionEq : eraseSource function = runtimeFunction at runtimeStep
      cases runtimeStep with
      | tappFunction innerStep =>
          cases innerStep with
          | tappFunction functionStep =>
              have sourceStep := functionStep
              rw [← functionEq] at sourceStep
              rcases sourceStep_of_runtimeStep sourceStep with ⟨function', step⟩
              exact ⟨.tapp function' argument, .tapp_fun step⟩
          | typeBeta =>
              rcases sourceTabs_of_erasedTabs functionEq with
                ⟨bound, body, rfl⟩
              exact ⟨body.openTy argument, .type_beta⟩
termination_by sizeOf term
decreasing_by
  all_goals
    simp_all
    omega

theorem sourceStuck_erases
    {term : SystemFSub.Tm sig} (stuck : SystemFSub.Tm.IsStuck term) :
    Runtime.IsStuck (eraseSource term) := by
  constructor
  · intro next step
    rcases sourceStep_of_runtimeStep step with ⟨result, sourceStep⟩
    exact stuck.1 result sourceStep
  · intro value
    exact stuck.2 (sourceValue_of_runtimeValue value)

theorem liftRuntimeStepsFrom
    {expression : SystemFCo.Exp []} {ty : SystemFCo.Ty []}
    (typing : SystemFCo.Exp.HasType .empty expression ty)
    {runtimeStart runtimeResult : Runtime.Term []}
    (eraseEq : eraseTarget expression = runtimeStart)
    (runtimeSteps : Runtime.Steps runtimeStart runtimeResult) :
    Exists fun targetResult =>
      SystemFCo.Exp.Steps expression targetResult /\
      eraseTarget targetResult = runtimeResult := by
  induction runtimeSteps generalizing expression with
  | refl => exact ⟨expression, .refl, eraseEq⟩
  | tail runtimeStep remaining ih =>
      have sourceStep := runtimeStep
      rw [← eraseEq] at sourceStep
      rcases liftRuntimeStep typing sourceStep with
        ⟨middle, targetSteps, middleErase⟩
      rcases SystemFCo.Exp.preservation_steps typing targetSteps with
        ⟨middleTyping⟩
      rcases ih middleTyping middleErase with
        ⟨result, remainingSteps, resultErase⟩
      exact ⟨result, targetSteps.trans remainingSteps, resultErase⟩

theorem liftRuntimeSteps
    {expression : SystemFCo.Exp []} {ty : SystemFCo.Ty []}
    (typing : SystemFCo.Exp.HasType .empty expression ty)
    {runtimeResult : Runtime.Term []}
    (runtimeSteps : Runtime.Steps (eraseTarget expression) runtimeResult) :
    Exists fun targetResult =>
      SystemFCo.Exp.Steps expression targetResult /\
      eraseTarget targetResult = runtimeResult :=
  liftRuntimeStepsFrom typing rfl runtimeSteps

/-- Final closed-source safety theorem obtained through target elaboration. -/
theorem source_not_goesWrong
    {term : SystemFSub.Tm.ClosedTerm} {ty : SystemFSub.Ty {}}
    (typing : SystemFSub.Tm.HasType .empty term ty) :
    Not (SystemFSub.Tm.GoesWrong term) := by
  intro goesWrong
  rcases goesWrong with ⟨result, sourceSteps, sourceStuck⟩
  let target := elaborateTerm typing
  have targetTyping := elaborateTermTyping typing
  have runtimeSteps : Runtime.Steps (eraseTarget target) (eraseSource result) := by
    rw [erase_elaborateTerm typing]
    exact eraseSource_steps sourceSteps
  rcases liftRuntimeSteps targetTyping runtimeSteps with
    ⟨targetResult, targetSteps, targetErase⟩
  rcases SystemFCo.Exp.preservation_steps targetTyping targetSteps with
    ⟨targetResultTyping⟩
  have runtimeProgress := typedRuntimeProgress targetResultTyping
  rw [targetErase] at runtimeProgress
  have runtimeStuck := sourceStuck_erases sourceStuck
  rcases runtimeProgress with value | ⟨next, step⟩
  · exact runtimeStuck.2 value
  · exact runtimeStuck.1 next step

end SystemFSub.Elaboration
