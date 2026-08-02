import LambdaP.StructuralPreciseProgress
import LambdaP.StructuralPrecisePreservation

/-!
Finite-run safety for exact structural states.

This layer is independent of the realization proof.  Progress assumes exact
singleton-head pushback; beta preservation assumes exact function pushback.
Both properties are required at every reached, precisely typed state.

Machine allocation changes the intrinsic scope.  Consequently the step
closure and the typing result are heterogeneous: the final context is an
explicit sequence of `snoc` extensions, and the observed result type is
weakened once per allocation.
-/

namespace LambdaP

/-! ## Current-store assumptions -/

/-- The two exact-store properties consumed by progress and preservation at
one machine state. -/
structure Store.PreciseStructSafetyWorld
    (Gamma : Ctx n) (sigma : Store n) : Prop where
  head : Store.StructPreciseSingletonHeadPushback Gamma sigma
  function : Store.StructExactFunctionPushback Gamma sigma

/-- A store-typing-indexed form of the two assumptions.  The mapped
realization theorem discharges finite-run safety by constructing this record
from its unconditional exact-store corollaries. -/
structure Store.PreciseStructSafetyLaws : Prop where
  head : forall {n : Nat} {Gamma : Ctx n} {sigma : Store n},
    Store.StructPreciseTy Gamma sigma ->
    Store.StructPreciseSingletonHeadPushback Gamma sigma
  function : forall {n : Nat} {Gamma : Ctx n} {sigma : Store n},
    Store.StructPreciseTy Gamma sigma ->
    Store.StructExactFunctionPushback Gamma sigma

theorem Store.PreciseStructSafetyLaws.world
    (hlaws : Store.PreciseStructSafetyLaws)
    (hstore : Store.StructPreciseTy Gamma sigma) :
    Store.PreciseStructSafetyWorld Gamma sigma :=
  ⟨hlaws.head hstore, hlaws.function hstore⟩

/-! ## One-step safety -/

/-- Preservation-carrying progress for an exact structural state. -/
inductive State.PreciseStructSafetyOutcome
    (Gamma : Ctx n) (source : State n)
    (T : LambdaP.Ty n) : Prop where
| final :
    source.IsFinal ->
    State.PreciseStructSafetyOutcome Gamma source T
| step :
    State.Step source target ->
    PreciseStructPreserve Gamma target T ->
    State.PreciseStructSafetyOutcome Gamma source T

theorem State.PreciseStructSafetyOutcome.progress
    (h : State.PreciseStructSafetyOutcome Gamma source T) :
    State.Progress source := by
  cases h with
  | final hfinal => exact .final hfinal
  | step hstep hpreserve => exact .step hstep

/-- Conditional one-step safety for a precisely typed state. -/
theorem State.PreciseStructTy.one_step_safety
    (hworld : Store.PreciseStructSafetyWorld Gamma source.σ)
    (ht : State.PreciseStructTy Gamma source T) :
    State.PreciseStructSafetyOutcome Gamma source T := by
  cases State.PreciseStructTy.progress hworld.head ht with
  | final hfinal => exact .final hfinal
  | step hstep =>
      exact .step hstep
        (hstep.precise_preservation_of_exactPushback hworld.function ht)

/-- One-step wrapper in the form directly discharged by realization laws. -/
theorem State.PreciseStructTy.one_step_safety_of_laws
    (hlaws : Store.PreciseStructSafetyLaws)
  (ht : State.PreciseStructTy Gamma source T) :
    State.PreciseStructSafetyOutcome Gamma source T := by
  cases ht with
  | ok hstore hcont hterm =>
      exact State.PreciseStructTy.one_step_safety
        (hlaws.world hstore) (.ok hstore hcont hterm)

/-! ## Honest context growth -/

/-- Reflexive-transitive allocation growth.  Each `snoc` weakens the
currently observed result type once. -/
inductive State.PreciseStructExtension :
    {n m : Nat} -> Ctx n -> LambdaP.Ty n ->
      Ctx m -> LambdaP.Ty m -> Prop where
| refl : State.PreciseStructExtension Gamma T Gamma T
| snoc {n m : Nat} {Gamma : Ctx n} {T : LambdaP.Ty n}
    {Delta : Ctx m} {U : LambdaP.Ty m} :
    State.PreciseStructExtension Gamma T Delta U ->
    (S : LambdaP.Ty m) ->
    State.PreciseStructExtension Gamma T (Delta.snoc S) U.weaken

theorem State.PreciseStructExtension.trans
    (h1 : State.PreciseStructExtension Gamma T Delta U)
    (h2 : State.PreciseStructExtension Delta U Theta V) :
    State.PreciseStructExtension Gamma T Theta V := by
  induction h2 with
  | refl => exact h1
  | snoc h S ih => exact .snoc (ih h1) S

/-- Turn one-step exact preservation into an explicit target context, target
type, and extension witness. -/
theorem PreciseStructPreserve.to_extension
    (h : PreciseStructPreserve Gamma target T) :
    exists Delta U,
      State.PreciseStructExtension Gamma T Delta U /\
      State.PreciseStructTy Delta target U := by
  cases h with
  | same ht => exact ⟨_, _, .refl, ht⟩
  | extend ht => exact ⟨_, _, .snoc .refl _, ht⟩

/-! ## Heterogeneous finite executions -/

/-- Reflexive-transitive closure of machine steps across possible store
allocations and hence across intrinsic scope indices. -/
inductive State.PreciseSteps :
    {n m : Nat} -> State n -> State m -> Prop where
| refl : State.PreciseSteps source source
| tail :
    State.Step source middle ->
    State.PreciseSteps middle target ->
    State.PreciseSteps source target

/-- Finite executions compose. -/
theorem State.PreciseSteps.trans
    (h1 : State.PreciseSteps source middle)
    (h2 : State.PreciseSteps middle target) :
    State.PreciseSteps source target := by
  induction h1 with
  | refl => exact h2
  | tail hstep hrest ih => exact .tail hstep (ih h2)

/-- A finite execution preserves exact structural typing.  The world
premise is intentionally pointwise over precisely typed states reached from
the initial configuration. -/
theorem State.PreciseSteps.preservation
    {n m : Nat} {Gamma : Ctx n} {source : State n}
    {target : State m} {T : LambdaP.Ty n}
    (hsteps : State.PreciseSteps source target)
    (ht : State.PreciseStructTy Gamma source T)
    (hworld : forall {j : Nat} {Delta : Ctx j} {u : State j}
        {U : LambdaP.Ty j},
      State.PreciseSteps source u ->
      State.PreciseStructTy Delta u U ->
      Store.PreciseStructSafetyWorld Delta u.σ) :
    exists Delta U,
      State.PreciseStructExtension Gamma T Delta U /\
      State.PreciseStructTy Delta target U := by
  induction hsteps with
  | refl => exact ⟨_, _, .refl, ht⟩
  | @tail n j m source middle target hstep hrest ih =>
      have hw := hworld State.PreciseSteps.refl ht
      obtain ⟨Delta, U, hext, hmiddle⟩ :=
        (hstep.precise_preservation_of_exactPushback
          hw.function ht).to_extension
      have hworld' : forall {l : Nat} {Theta : Ctx l} {u : State l}
          {V : LambdaP.Ty l},
          State.PreciseSteps middle u ->
          State.PreciseStructTy Theta u V ->
          Store.PreciseStructSafetyWorld Theta u.σ := by
        intro l Theta u V hreach htyped
        exact hworld (.tail hstep hreach) htyped
      obtain ⟨Theta, V, hext', htarget⟩ :=
        ih hmiddle hworld'
      exact ⟨Theta, V, hext.trans hext', htarget⟩

/-- Every finite-run endpoint remains precisely typed and is final or can
take a preservation-carrying step. -/
theorem State.PreciseSteps.safety
    {n m : Nat} {Gamma : Ctx n} {source : State n}
    {target : State m} {T : LambdaP.Ty n}
    (hsteps : State.PreciseSteps source target)
    (ht : State.PreciseStructTy Gamma source T)
    (hworld : forall {j : Nat} {Delta : Ctx j} {u : State j}
        {U : LambdaP.Ty j},
      State.PreciseSteps source u ->
      State.PreciseStructTy Delta u U ->
      Store.PreciseStructSafetyWorld Delta u.σ) :
    exists Delta U,
      State.PreciseStructExtension Gamma T Delta U /\
      State.PreciseStructTy Delta target U /\
      State.PreciseStructSafetyOutcome Delta target U := by
  obtain ⟨Delta, U, hext, htarget⟩ :=
    hsteps.preservation ht hworld
  have hw := hworld hsteps htarget
  exact ⟨Delta, U, hext, htarget,
    htarget.one_step_safety hw⟩

/-- Explicit finite-run non-stuckness, obtained by forgetting the
preservation witness from `safety`. -/
theorem State.PreciseSteps.nonstuck
    {n m : Nat} {Gamma : Ctx n} {source : State n}
    {target : State m} {T : LambdaP.Ty n}
    (hsteps : State.PreciseSteps source target)
    (ht : State.PreciseStructTy Gamma source T)
    (hworld : forall {j : Nat} {Delta : Ctx j} {u : State j}
        {U : LambdaP.Ty j},
      State.PreciseSteps source u ->
      State.PreciseStructTy Delta u U ->
      Store.PreciseStructSafetyWorld Delta u.σ) :
    State.Progress target := by
  obtain ⟨Delta, U, hext, htarget, houtcome⟩ :=
    hsteps.safety ht hworld
  exact houtcome.progress

/-! ## Wrappers for realization corollaries -/

/-- Finite-run preservation from exact-store-indexed laws. -/
theorem State.PreciseSteps.preservation_of_laws
    (hlaws : Store.PreciseStructSafetyLaws)
    (hsteps : State.PreciseSteps source target)
    (ht : State.PreciseStructTy Gamma source T) :
    exists Delta U,
      State.PreciseStructExtension Gamma T Delta U /\
      State.PreciseStructTy Delta target U := by
  apply hsteps.preservation ht
  intro j Delta u U hreach htyped
  cases htyped with
  | ok hstore hcont hterm =>
      exact hlaws.world hstore

/-- Complete finite-run exact safety from the two realization-shaped laws. -/
theorem State.PreciseSteps.safety_of_laws
    (hlaws : Store.PreciseStructSafetyLaws)
    (hsteps : State.PreciseSteps source target)
    (ht : State.PreciseStructTy Gamma source T) :
    exists Delta U,
      State.PreciseStructExtension Gamma T Delta U /\
      State.PreciseStructTy Delta target U /\
      State.PreciseStructSafetyOutcome Delta target U := by
  apply hsteps.safety ht
  intro j Delta u U hreach htyped
  cases htyped with
  | ok hstore hcont hterm =>
      exact hlaws.world hstore

/-- Finite-run non-stuckness in the form consumed by the unconditional
mapped-realization laws. -/
theorem State.PreciseSteps.nonstuck_of_laws
    (hlaws : Store.PreciseStructSafetyLaws)
    (hsteps : State.PreciseSteps source target)
    (ht : State.PreciseStructTy Gamma source T) :
    State.Progress target := by
  apply hsteps.nonstuck ht
  intro j Delta u U hreach htyped
  cases htyped with
  | ok hstore hcont hterm =>
      exact hlaws.world hstore

end LambdaP
