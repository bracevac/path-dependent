import LambdaPFC.CoercionMachine

/-!
Terminating abstract-member coercion runs.  The upper-bound run retrieves and
schedules a reflexive coercion.  The lower-bound run additionally exercises the
frame that hides the witness behind the surface selection.  Both reach a final
state without changing the classified runtime location.
-/

namespace LambdaPFC.CoercionProbe

open LambdaP LambdaPFC

def label : Name := 0
def packagePath : Path 1 := .var 0

def packageLocation : Fin 2 := 0
def valueLocation : Fin 2 := 1

def valuation : Valuation 1 2 := fun _ => packageLocation

def model : Model 2 := fun x =>
  if x = packageLocation then
    .pair valueLocation label (.type .Top)
  else
    .atom

/-- The single statically checked member available in the probe. -/
inductive Check : {n : Nat} -> Path n -> Name -> Ty n -> Ty n -> Prop where
| member : Check packagePath label .Top .Top

def signature : MemberSignature where
  Check := Check

def checked : signature.Check packagePath label .Top .Top :=
  .member

def world : CoWorld signature valuation where
  model := model
  witness := fun _ _ => .Top
  resolves := by
    intro p A L U h
    cases h
    apply Resolve.sel Resolve.var
    apply Select.hit (y := valueLocation)
    simp [model, packageLocation, valuation, instantiateTy, Ty.subst]
  lower := by
    intro p A L U h
    cases h
    exact .static .refl
  upper := by
    intro p A L U h
    cases h
    exact .static .refl

def selectedValue :
    ValueAt world valueLocation (.TSel packagePath label) :=
  .selected checked (.base .top)

def code : Coercion signature (.TSel packagePath label) .Top :=
  .selHi checked

def initial : State world .Top :=
  .start code selectedValue

def afterLookup : State world .Top :=
  ⟨.Top, valueLocation, selectedValue.unselect checked,
    .apply (.static .refl) .done⟩

def final : State world .Top :=
  ⟨.Top, valueLocation,
    Evidence.actionAt .refl (selectedValue.unselect checked), .done⟩

theorem lookup_step : initial.Step afterLookup := by
  simpa [initial, State.start, afterLookup, world] using
    State.Step.upper checked valueLocation selectedValue (Stack.done)

theorem static_step : afterLookup.Step final :=
  State.Step.static .refl valueLocation
    (selectedValue.unselect checked) Stack.done

theorem normalizes : initial.Steps final :=
  .tail lookup_step (.tail static_step .refl)

theorem final_state : final.Final :=
  .done _ _

def run : code.Run selectedValue where
  finish := final
  steps := normalizes
  final := final_state

theorem result_realizes_target :
    ValueAt world valueLocation .Top :=
  run.result

theorem execution_preserves_runtime : final.erase = initial.erase :=
  normalizes.preserves_erase

/-! The lower-bound direction exercises the witness-hiding stack frame. -/

def plainValue : ValueAt world valueLocation .Top :=
  .base .top

def lowerCode : Coercion signature .Top (.TSel packagePath label) :=
  .selLo checked

def lowerInitial : State world (.TSel packagePath label) :=
  .start lowerCode plainValue

def lowerAfterLookup : State world (.TSel packagePath label) :=
  ⟨.Top, valueLocation, plainValue,
    .apply (.static .refl) (.hide checked .done)⟩

def lowerAfterStatic : State world (.TSel packagePath label) :=
  ⟨.Top, valueLocation, Evidence.actionAt .refl plainValue,
    .hide checked .done⟩

def lowerFinal : State world (.TSel packagePath label) :=
  ⟨.TSel packagePath label, valueLocation,
    .selected checked (Evidence.actionAt .refl plainValue), .done⟩

theorem lower_lookup_step : lowerInitial.Step lowerAfterLookup := by
  simpa [lowerInitial, State.start, lowerAfterLookup, world] using
    State.Step.lower checked valueLocation plainValue Stack.done

theorem lower_static_step : lowerAfterLookup.Step lowerAfterStatic :=
  State.Step.static .refl valueLocation plainValue (.hide checked .done)

theorem lower_pack_step : lowerAfterStatic.Step lowerFinal :=
  State.Step.pack checked valueLocation
    (Evidence.actionAt .refl plainValue) Stack.done

theorem lower_normalizes : lowerInitial.Steps lowerFinal :=
  .tail lower_lookup_step
    (.tail lower_static_step (.tail lower_pack_step .refl))

def lowerRun : lowerCode.Run plainValue where
  finish := lowerFinal
  steps := lower_normalizes
  final := .done _ _

theorem lower_result_realizes_selection :
    ValueAt world valueLocation (.TSel packagePath label) :=
  lowerRun.result

end LambdaPFC.CoercionProbe
