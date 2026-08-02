import LambdaP.Original.StructuralApplicationCompatibility

/-!
The complete structural preservation theorem, factored through the one
remaining function-reflection property of the current store.

All non-application transitions are unconditional.  Beta reduction uses the
syntax-directed abstraction witness recovered from store inversion, so the
observation-sized `StructPreciseFunctionReflection` premise is sufficient;
the stronger, earlier `StructAppCompatibility` contract is unnecessary.
-/

namespace LambdaP.Original

/-- Beta preservation from the precise function-reflection property. -/
theorem StructPreserve.app_precise
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {k : Tm.Cont n} {p q : Path n}
    {x y : Fin n} {A : LambdaP.Original.Ty n}
    {body : Tm (n + 1)} {T : LambdaP.Original.Ty n}
    (hreflect : Store.StructPreciseFunctionReflection Gamma sigma)
    (hp : Path.reduce p sigma x)
    (hq : Path.reduce q sigma y)
    (hbind : Store.Binds sigma x (Tm.abs A body))
    (h : State.StructTy Gamma ⟨sigma, k, Tm.app p q⟩ T) :
    StructPreserve Gamma ⟨sigma, k, body.open y⟩ T := by
  cases h with
  | ok hstore hcont happ =>
      obtain ⟨S, U, hfun, harg, post⟩ := happ.app_inversion
      have hopened := hstore.open_application_of_preciseFunctionReflection
        hreflect hp hq hbind hfun harg
      exact .same (.ok hstore hcont (post hopened))

/-- Every machine transition preserves the structural state invariant,
assuming precise function reflection for the source store.  The result may
extend the context by one cell in the allocation case. -/
theorem State.Step.struct_preservation
    {n m : Nat} {Gamma : Ctx n} {source : State n} {target : State m}
    {T : LambdaP.Original.Ty n}
    (hreflect : Store.StructPreciseFunctionReflection Gamma source.σ)
    (step : State.Step source target)
    (ht : State.StructTy Gamma source T) :
    StructPreserve Gamma target T := by
  cases step with
  | app hp hq hbind =>
      exact StructPreserve.app_precise hreflect hp hq hbind ht
  | path hr hnonvar =>
      exact StructPreserve.path hr ht
  | let_push =>
      exact StructPreserve.let_push ht
  | rename =>
      exact StructPreserve.rename ht
  | lift hv =>
      exact StructPreserve.lift hv ht
  | ascribe =>
      exact StructPreserve.ascribe ht

/-- The same complete theorem with the remaining premise reduced to
function-signature pushback.  Dependent result opening is unconditional. -/
theorem State.Step.struct_preservation_of_pushback
    {n m : Nat} {Gamma : Ctx n} {source : State n} {target : State m}
    {T : LambdaP.Original.Ty n}
    (hpush : Store.StructPreciseFunctionPushback Gamma source.σ)
    (step : State.Step source target)
    (ht : State.StructTy Gamma source T) :
    StructPreserve Gamma target T :=
  step.struct_preservation hpush.to_preciseFunctionReflection ht

end LambdaP.Original
