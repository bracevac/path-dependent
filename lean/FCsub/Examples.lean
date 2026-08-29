import FCsub.Checker
import FCsub.Erasure

/-!
# Standalone FCsub kernel examples

This module deliberately imports no source language.  It exercises genuinely
general names-first telescopes, independently supplied package certificates,
structural telescope views, morphism composition, and erased execution.
-/

namespace FCsub.Examples

/-! ## A two-name, three-constraint package -/

abbrev TwoNameScope : Sig := TypeScope [] 2

/-- The older of the two simultaneously allocated names. -/
def alpha : Ty TwoNameScope := .tvar (.there .here)

/-- The newer of the two simultaneously allocated names. -/
def beta : Ty TwoNameScope := .tvar .here

def lowerAlpha : Proposition TwoNameScope :=
  .inclusion .bot alpha

def alphaBelowBeta : Proposition TwoNameScope :=
  .inclusion alpha beta

def betaUpper : Proposition TwoNameScope :=
  .inclusion beta .top

/-- A genuinely generic telescope: two names are allocated before three
constraints, and no lower/upper pair convention is built into FCsub. -/
def multiTelescope : Telescope [] 2 3 :=
  .snoc (.snoc (.snoc .nil lowerAlpha) alphaBelowBeta) betaUpper

/-- Simultaneous witnesses `alpha := bot` and `beta := top`. -/
def multiWitnesses : TypeArgs [] 2 :=
  .snoc (.snoc .nil .bot) .top

/-- Every certificate is constructed in the ambient empty context. -/
def multiEvidence : LeArgs [] 3 :=
  .snoc (.snoc (.snoc .nil (.refl .bot)) (.top .bot)) (.refl .top)

/-- A runtime redex used as the package payload. -/
def payloadRedex : Tm [] :=
  .app (.lam .one (.var .here)) .unit

def multiPackage : Tm [] :=
  .pack multiTelescope .one multiWitnesses multiEvidence payloadRedex

def multiPackageType : Ty [] :=
  .existsT multiTelescope .one

theorem multi_arguments_are_checked :
    checkArgs Ctx.nil multiTelescope multiWitnesses multiEvidence = true := by
  native_decide

theorem multi_package_is_checked :
    synthTm Ctx.nil multiPackage = some multiPackageType := by
  native_decide

theorem multi_package_is_well_typed :
    Nonempty (Tm.HasType Ctx.nil multiPackage multiPackageType) :=
  synthTm_sound multi_package_is_checked

theorem multi_package_erases_to_payload :
    multiPackage.erase =
      (.app (.lam (.var .here)) .unit : Runtime.Tm []) := by
  native_decide

theorem multi_package_runtime_beta :
    Runtime.Step multiPackage.erase (.unit : Runtime.Tm []) := by
  rw [multi_package_erases_to_payload]
  exact Runtime.Step.beta Runtime.IsValue.unit

/-! ## Package evidence cannot discharge itself -/

/-- There is no inclusion-evidence variable in the ambient empty scope from
which package arguments must be built.  In particular, the constraint a
package is about to introduce is not available as an argument variable. -/
theorem no_ambient_constraint_variable
    (index : BVar ([] : Sig) (.evidence .inclusion)) : False :=
  nomatch index

def impossibleTelescope : Telescope [] 0 1 :=
  .snoc .nil (.inclusion .top .bot)

def unjustifiedEvidence : LeArgs [] 1 :=
  .snoc .nil (.refl .top)

/-- The attempted package cannot use its own `top <= bot` assumption—the
assumption is intrinsically out of scope—and the supplied ambient reflexivity
certificate is rejected. -/
def selfDischargeAttempt : Tm [] :=
  .pack impossibleTelescope .one .nil unjustifiedEvidence .unit

theorem self_discharge_arguments_rejected :
    checkArgs Ctx.nil impossibleTelescope .nil unjustifiedEvidence = false := by
  native_decide

theorem self_discharge_package_rejected :
    synthTm Ctx.nil selfDischargeAttempt = none := by
  native_decide

/-! ## Structural projection -/

/-- Keep the oldest and newest constraints while forgetting `alpha <= beta`. -/
def projectedTelescope : Telescope [] 2 2 :=
  .snoc (.snoc .nil lowerAlpha) betaUpper

/-- Telescope indices are newest-first: projected index zero selects source
zero, while projected index one selects source index two. -/
def projectionIndex : Fin 2 → Fin 3
  | ⟨0, _⟩ => ⟨0, by omega⟩
  | ⟨_ + 1, _⟩ => ⟨2, by omega⟩

def dropMiddleProjection :
    Telescope.Projection multiTelescope projectedTelescope where
  constraint := projectionIndex
  preserves := by native_decide

def projectionMorphism : TelMor [] 2 3 2 2 :=
  TelMor.ofProjection dropMiddleProjection

theorem projection_morphism_is_checked :
    synthMor Ctx.nil projectionMorphism =
      some (multiTelescope, projectedTelescope) := by
  native_decide

theorem projection_morphism_is_well_typed :
    Nonempty (TelMor.HasType Ctx.nil projectionMorphism
      multiTelescope projectedTelescope) :=
  synthMor_sound projection_morphism_is_checked

/-! ## Constraint permutation and morphism composition -/

/-- Reverse the order of all three independent constraints. -/
def reversedTelescope : Telescope [] 2 3 :=
  .snoc (.snoc (.snoc .nil betaUpper) alphaBelowBeta) lowerAlpha

def reverseThree (index : Fin 3) : Fin 3 :=
  ⟨2 - index.val, by omega⟩

def reversePermutation :
    Telescope.Permutation multiTelescope reversedTelescope where
  forward := reverseThree
  backward := reverseThree
  forward_backward := by native_decide
  backward_forward := by native_decide
  preserves := by native_decide

def permutationMorphism : TelMor [] 2 3 2 3 :=
  TelMor.ofPermutation reversePermutation

theorem permutation_morphism_is_checked :
    synthMor Ctx.nil permutationMorphism =
      some (multiTelescope, reversedTelescope) := by
  native_decide

/-- The syntax is explicitly a composition of the forward and inverse maps. -/
def permutationRoundTrip : TelMor [] 2 3 2 3 :=
  TelMor.permutationRoundTrip reversePermutation

theorem permutation_round_trip_is_composed :
    permutationRoundTrip =
      .trans (TelMor.ofPermutation reversePermutation)
        (TelMor.ofPermutation reversePermutation.symm) := rfl

theorem composed_morphism_is_checked :
    synthMor Ctx.nil permutationRoundTrip =
      some (multiTelescope, multiTelescope) := by
  native_decide

theorem composed_morphism_is_well_typed :
    Nonempty (TelMor.HasType Ctx.nil permutationRoundTrip
      multiTelescope multiTelescope) :=
  synthMor_sound composed_morphism_is_checked

end FCsub.Examples
