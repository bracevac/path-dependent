import LambdaP.Original.StructuralProgress
import LambdaP.Original.StructuralPreservation

/-!
Conditional safety for the structural machine invariant.

The store-facing assumptions are deliberately separated from state typing.
`StructOperational` supplies the pair/function shapes needed by progress;
`StructPreciseFunctionPushback` supplies the function-signature inversion
needed only by beta preservation; dependent result opening is proved
unconditionally.  The resulting theorem is a
genuine one-step safety statement, but remains conditional on these two
semantic store properties.

Allocation changes the intrinsic scope.  The finite-run theorem therefore
tracks context extension and weakening of the observed result type
explicitly, rather than pretending that every reached state has the initial
index.
-/

namespace LambdaP.Original

/-! ## The current-store safety world -/

/-- Exactly the two current-store properties consumed by progress and
preservation. -/
structure Store.StructSafetyWorld
    (Gamma : Ctx n) (sigma : Store n) : Prop where
  operational : Store.StructOperational Gamma sigma
  application : Store.StructPreciseFunctionPushback Gamma sigma

/-! ## One-step safety -/

/-- The preservation-carrying form of "final or steps".  In the step case
the target index is existential and `StructPreserve` records whether the
typing context stayed fixed or grew by one allocation. -/
inductive State.StructSafetyOutcome
    (Gamma : Ctx n) (source : State n)
    (T : LambdaP.Original.Ty n) : Prop where
| final : source.IsFinal -> State.StructSafetyOutcome Gamma source T
| step :
    State.Step source target ->
    StructPreserve Gamma target T ->
    State.StructSafetyOutcome Gamma source T

/-- Conditional one-step safety for the complete historical machine. -/
theorem State.StructTy.one_step_safety
    (hworld : Store.StructSafetyWorld Gamma source.σ)
    (ht : State.StructTy Gamma source T) :
    State.StructSafetyOutcome Gamma source T := by
  cases State.StructTy.progress hworld.operational ht with
  | final hfinal => exact .final hfinal
  | step hstep =>
      exact .step hstep
        (hstep.struct_preservation_of_pushback hworld.application ht)

/-! ## Honest context growth -/

/-- Reflexive-transitive allocation growth.  Each `snoc` extends the current
context by one cell and weakens the currently observed result type once. -/
inductive State.StructExtension :
    {n m : Nat} -> Ctx n -> LambdaP.Original.Ty n ->
      Ctx m -> LambdaP.Original.Ty m -> Prop where
| refl : State.StructExtension Gamma T Gamma T
| snoc {n m : Nat} {Gamma : Ctx n} {T : LambdaP.Original.Ty n}
    {Delta : Ctx m} {U : LambdaP.Original.Ty m} :
    State.StructExtension Gamma T Delta U ->
    (S : LambdaP.Original.Ty m) ->
    State.StructExtension Gamma T (Delta.snoc S) U.weaken

theorem State.StructExtension.trans
    (h1 : State.StructExtension Gamma T Delta U)
    (h2 : State.StructExtension Delta U Theta V) :
    State.StructExtension Gamma T Theta V := by
  induction h2 with
  | refl => exact h1
  | snoc h S ih => exact .snoc (ih h1) S

/-- Unpack the one-step preservation disjunction into an explicit target
context, target type, and extension witness. -/
theorem StructPreserve.to_extension
    (h : StructPreserve Gamma target T) :
    exists Delta U,
      State.StructExtension Gamma T Delta U /\
      State.StructTy Delta target U := by
  cases h with
  | same ht => exact ⟨_, _, .refl, ht⟩
  | extend ht =>
      exact ⟨_, _, .snoc .refl _, ht⟩

/-! ## Finite executions -/

/-- Heterogeneous reflexive-transitive closure of machine steps. -/
inductive State.Steps : {n m : Nat} -> State n -> State m -> Prop where
| refl : State.Steps source source
| tail :
    State.Step source middle ->
    State.Steps middle target ->
    State.Steps source target

/-- A finite execution preserves structural typing, provided the safety
world holds for every structurally typed configuration reached from the
initial state.  This premise states the currently unproved allocation
closure honestly and only for reached states. -/
theorem State.Steps.struct_preservation
    {n m : Nat} {Gamma : Ctx n} {source : State n}
    {target : State m} {T : LambdaP.Original.Ty n}
    (hsteps : State.Steps source target)
    (ht : State.StructTy Gamma source T)
    (hworld : forall {j : Nat} {Delta : Ctx j} {u : State j}
        {U : LambdaP.Original.Ty j},
      State.Steps source u ->
      State.StructTy Delta u U ->
      Store.StructSafetyWorld Delta u.σ) :
    exists Delta U,
      State.StructExtension Gamma T Delta U /\
      State.StructTy Delta target U := by
  induction hsteps with
  | refl => exact ⟨_, _, .refl, ht⟩
  | @tail n j m source middle target hstep hrest ih =>
      have hw := hworld State.Steps.refl ht
      obtain ⟨Delta, U, hext, hmiddle⟩ :=
        (hstep.struct_preservation_of_pushback hw.application ht).to_extension
      have hworld' : forall {l : Nat} {Theta : Ctx l} {u : State l}
          {V : LambdaP.Original.Ty l},
          State.Steps middle u ->
          State.StructTy Theta u V ->
          Store.StructSafetyWorld Theta u.σ := by
        intro l Theta u V hreach htyped
        exact hworld (.tail hstep hreach) htyped
      obtain ⟨Theta, V, hext', htarget⟩ :=
        ih hmiddle hworld'
      exact ⟨Theta, V, hext.trans hext', htarget⟩

/-- Every state reached by a finite execution is well typed at an explicitly
extended context and is itself final or can take a preservation-carrying
step.  The world premise is required at each reached typed state, including
the endpoint. -/
theorem State.Steps.struct_safety
    {n m : Nat} {Gamma : Ctx n} {source : State n}
    {target : State m} {T : LambdaP.Original.Ty n}
    (hsteps : State.Steps source target)
    (ht : State.StructTy Gamma source T)
    (hworld : forall {j : Nat} {Delta : Ctx j} {u : State j}
        {U : LambdaP.Original.Ty j},
      State.Steps source u ->
      State.StructTy Delta u U ->
      Store.StructSafetyWorld Delta u.σ) :
    exists Delta U,
      State.StructExtension Gamma T Delta U /\
      State.StructTy Delta target U /\
      State.StructSafetyOutcome Delta target U := by
  obtain ⟨Delta, U, hext, htarget⟩ :=
    hsteps.struct_preservation ht hworld
  have hw := hworld hsteps htarget
  exact ⟨Delta, U, hext, htarget,
    htarget.one_step_safety hw⟩

end LambdaP.Original
