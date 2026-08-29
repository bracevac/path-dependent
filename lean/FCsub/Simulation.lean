import FCsub.ErasureMetatheory

/-!
# Erasure simulation

Every annotated step is simulated by zero or more steps of FCsub's own
runtime.  Computational beta, zeta, and package-opening rules take one
runtime step; certificate normalization and static computation stutter.
-/

namespace FCsub

namespace Runtime.Steps

/-- Multi-step closure under the function position of application. -/
theorem appFunction {scope : Sig} {function function' argument : Runtime.Tm scope}
    (steps : Runtime.Steps function function') :
    Runtime.Steps (.app function argument) (.app function' argument) := by
  induction steps with
  | refl => exact .refl
  | tail initial final induction =>
      exact .tail induction (.appFunction final)

/-- Multi-step closure under the argument position once the function is a
value. -/
theorem appArgument {scope : Sig} {function argument argument' : Runtime.Tm scope}
    (functionValue : Runtime.IsValue function)
    (steps : Runtime.Steps argument argument') :
    Runtime.Steps (.app function argument) (.app function argument') := by
  induction steps with
  | refl => exact .refl
  | tail initial final induction =>
      exact .tail induction (.appArgument functionValue final)

/-- Multi-step closure under a let right-hand side. -/
theorem letRhs {scope : Sig} {rhs rhs' : Runtime.Tm scope}
    {body : Runtime.Tm (scope ▹ .term)} (steps : Runtime.Steps rhs rhs') :
    Runtime.Steps (.let' rhs body) (.let' rhs' body) := by
  induction steps with
  | refl => exact .refl
  | tail initial final induction =>
      exact .tail induction (.letRhs final)

end Runtime.Steps

namespace Tm.Step

/-- Every annotated reduction step is simulated by the erased runtime's
reflexive-transitive closure. -/
theorem erase_simulates {scope : Sig} {term next : Tm scope}
    (step : Tm.Step term next) : Runtime.Steps term.erase next.erase := by
  induction step with
  | appFunction step induction =>
      exact Runtime.Steps.appFunction induction
  | appArgument functionValue step induction =>
      exact Runtime.Steps.appArgument functionValue.erase induction
  | beta argumentValue =>
      simpa only [Tm.erase_app, Tm.erase_lam, Tm.erase_instantiateTerm] using
        Runtime.Steps.single (.beta argumentValue.erase)
  | appCastArrow functionValue argumentValue =>
      exact .refl
  | letRhs step induction =>
      exact Runtime.Steps.letRhs induction
  | zeta rhsValue =>
      simpa only [Tm.erase_let, Tm.erase_instantiateTerm] using
        Runtime.Steps.single (.zeta rhsValue.erase)
  | castInner step induction =>
      exact induction
  | castRefl termValue =>
      exact .refl
  | castTrans termValue =>
      exact .refl
  | castEqRefl termValue =>
      exact .refl
  | castEqSymmRefl termValue =>
      exact .refl
  | castEqSymmSymm termValue =>
      exact .refl
  | castEqSymmTrans termValue =>
      exact .refl
  | castEqTrans termValue =>
      exact .refl
  | castEqUnfoldRec termValue =>
      exact .refl
  | castEqSymmUnfoldRec termValue =>
      exact .refl
  | packPayload step induction =>
      exact induction
  | openScrutinee step induction =>
      exact Runtime.Steps.letRhs induction
  | openPack payloadValue =>
      simpa only [Tm.erase_open, Tm.erase_pack,
        Tm.erase_instantiatePayload] using
        Runtime.Steps.single (.zeta payloadValue.erase)
  | openCastExists packageValue =>
      simpa only [Tm.erase_open, Tm.erase_cast, Tm.erase_substitute,
        Runtime.Tm.subst_comp,
        TelMor.eraseRuntime_payloadSubstitution_comp_dropPayload] using
        (Runtime.Steps.refl : Runtime.Steps _ _)
  | sappFunction step induction =>
      exact induction
  | sappSlam bodyValue =>
      simpa only [Tm.erase_sapp, Tm.erase_slam,
        Tm.erase_instantiateStatic] using
        (Runtime.Steps.refl : Runtime.Steps _ _)
  | sappCastForall functionValue =>
      exact .refl
  | newtype =>
      simpa only [Tm.erase_newtype, Tm.erase_instantiateNewtype] using
        (Runtime.Steps.refl : Runtime.Steps _ _)
  | foldRecInner step induction =>
      exact induction
  | unfoldRecInner step induction =>
      exact induction
  | unfoldFold termValue =>
      exact .refl

end Tm.Step

end FCsub
