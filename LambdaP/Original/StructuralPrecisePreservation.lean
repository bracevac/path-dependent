import LambdaP.Original.StructuralPreciseStore
import LambdaP.Original.StructuralPreservation

/-!
Preservation for the exact structural store invariant.

The ordinary structural proof already establishes all term-level
transformations.  This module retains the stronger store invariant across
those transformations.  Allocation uses `PreciseStructPreserve.lift`: the
stored value is indexed by its syntax-directed introduction type and the
suspended body is narrowed to that type.  Beta reduction is factored through
the same observation-sized function-pushback property as the ordinary proof;
the exact-store canonical-form theorem will discharge that property.
-/

namespace LambdaP.Original

/-! ## Store-preserving transitions -/

theorem PreciseStructPreserve.path
    (hr : Path.reduce p sigma x)
    (h : State.PreciseStructTy Gamma
      ⟨sigma, k, Tm.path p⟩ T) :
    PreciseStructPreserve Gamma
      ⟨sigma, k, Tm.path (Path.var x)⟩ T := by
  cases h with
  | ok hstore hcont hterm =>
      exact .same (.ok hstore hcont (hterm.reduce_path hr))

theorem PreciseStructPreserve.let_push
    (h : State.PreciseStructTy Gamma
      ⟨sigma, k, Tm.let s t⟩ T) :
    PreciseStructPreserve Gamma
      ⟨sigma, Tm.Frame.let t :: k, s⟩ T := by
  cases h with
  | ok hstore hcont hterm =>
      obtain ⟨S, hs, _, hbody⟩ := hterm.let_inv
      exact .same (.ok hstore (.cons hcont (.let hbody)) hs)

theorem PreciseStructPreserve.ascribe
    (h : State.PreciseStructTy Gamma
      ⟨sigma, k, Tm.typed t A⟩ T) :
    PreciseStructPreserve Gamma ⟨sigma, k, t⟩ T := by
  cases h with
  | ok hstore hcont hterm =>
      exact .same (.ok hstore hcont hterm.typed_inv.1)

theorem PreciseStructPreserve.rename
    (h : State.PreciseStructTy Gamma
      ⟨sigma, Tm.Frame.let t :: k,
        Tm.path (Path.var x)⟩ T) :
    PreciseStructPreserve Gamma ⟨sigma, k, t.open x⟩ T := by
  cases h with
  | ok hstore hcont harg =>
      cases hcont with
      | cons hrest hframe =>
          cases hframe with
          | «let» hbody =>
              have hopened := hbody.open_var_of_path_term
                (Path.RuntimeEq.isEquivCongr sigma) harg
              apply PreciseStructPreserve.same
              apply State.PreciseStructTy.ok hstore hrest
              simpa only [Ty.weaken, Ty.rename_rename,
                FinFun.openAt_weaken, Ty.rename_id] using hopened

/-! ## Beta reduction -/

/-- Beta reduction leaves the exact store unchanged.  Store precision is
therefore needed only to retain the invariant; signature inversion is kept as
the single explicit premise until exact-store canonical forms discharge it. -/
theorem PreciseStructPreserve.app
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {k : Tm.Cont n} {p q : Path n}
    {x y : Fin n} {A : LambdaP.Original.Ty n}
    {body : Tm (n + 1)} {T : LambdaP.Original.Ty n}
    (hpush : Store.StructPreciseFunctionPushback Gamma sigma)
    (hp : Path.reduce p sigma x)
    (hq : Path.reduce q sigma y)
    (hbind : Store.Binds sigma x (Tm.abs A body))
    (h : State.PreciseStructTy Gamma
      ⟨sigma, k, Tm.app p q⟩ T) :
    PreciseStructPreserve Gamma ⟨sigma, k, body.open y⟩ T := by
  cases h with
  | ok hstore hcont happ =>
      obtain ⟨S, U, hfun, harg, post⟩ := happ.app_inversion
      have hopened := hstore.toStructTy
        |>.open_application_of_preciseFunctionReflection
          hpush.to_preciseFunctionReflection hp hq hbind hfun harg
      exact .same (.ok hstore hcont (post hopened))

/-! ## Complete conditional preservation -/

/-- Every machine transition preserves the exact structural invariant.  The
only premise is the function-signature pushback used in the beta case. -/
theorem State.Step.precise_preservation
    {n m : Nat} {Gamma : Ctx n} {source : State n} {target : State m}
    {T : LambdaP.Original.Ty n}
    (hpush : Store.StructPreciseFunctionPushback Gamma source.σ)
    (step : State.Step source target)
    (ht : State.PreciseStructTy Gamma source T) :
    PreciseStructPreserve Gamma target T := by
  cases step with
  | app hp hq hbind =>
      exact PreciseStructPreserve.app hpush hp hq hbind ht
  | path hr hnonvar =>
      exact PreciseStructPreserve.path hr ht
  | let_push =>
      exact PreciseStructPreserve.let_push ht
  | rename =>
      exact PreciseStructPreserve.rename ht
  | lift hv =>
      exact PreciseStructPreserve.lift hv ht
  | ascribe =>
      exact PreciseStructPreserve.ascribe ht

end LambdaP.Original
