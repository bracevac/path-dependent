import LambdaP.Realization
import LambdaP.StructuralPreciseCanonical
import LambdaP.StructuralPreciseSafety

/-!
Canonical forms discharged by proof-relevant semantic maps.

The fundamental theorem in `Realization` turns a structural
subtyping derivation in an exact store into a finite semantic map.  Applying
that map to the location denoted by a term singleton exposes the constructor
of the target type.  Function realizers additionally retain exactly the
domain and codomain subtyping residues needed by beta preservation.
-/

namespace LambdaP

/-! ## Singleton pushback -/

/-- Semantic interpretation of a subtype whose source is an exact store
location.  This is the common canonical-forms step for functions and pairs. -/
theorem Tau.StructSub.mappedPossible_of_singleton
    (hstore : Store.StructPreciseTy Gamma sigma)
    (hsub : Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single (Path.var x))) (Tau.ty T)) :
    Store.MappedPossible Gamma sigma x T := by
  have htarget := (hsub.mapped hstore).action (.val x)
    (Path.Endpoint.MappedRealizes.val
      (Store.MappedPossible.single Path.Resolve.var))
  cases htarget with
  | val hpossible => exact hpossible

/-- Exact stores satisfy both concrete-head observations used by progress. -/
theorem Store.StructPreciseTy.mapped_singletonHeadPushback
    (hstore : Store.StructPreciseTy Gamma sigma) :
    Store.StructPreciseSingletonHeadPushback Gamma sigma := by
  constructor
  · intro x S U _ hsub
    have hpossible := hsub.mappedPossible_of_singleton hstore
    cases hpossible with
    | «fun» hbind hctx hprecise hdom hcod =>
        exact ⟨_, _, hbind⟩
  · intro x S a k d _ hsub
    have hpossible := hsub.mappedPossible_of_singleton hstore
    cases hpossible with
    | pair hbind hfirst hfirstPossible hmember =>
        exact ⟨_, _, hbind⟩

/-! ## Function-signature pushback -/

/-- A singleton-to-function map exposes the stored closure's exact
signature.  Function realization already contains contravariant domain and
covariant codomain residues; context functionality identifies that signature
with the exact type named by the premise. -/
theorem Store.StructPreciseTy.mapped_singletonFunctionPushback
    (hstore : Store.StructPreciseTy Gamma sigma) :
    Store.StructPreciseSingletonFunctionPushback Gamma sigma := by
  intro x S A U B _ hctx hsub
  have hpossible := hsub.mappedPossible_of_singleton hstore
  cases hpossible with
  | «fun» hbind hctx' hprecise hdom hcod =>
      cases hctx'.unique hctx
      exact ⟨hdom, hcod⟩

/-- Exact function pushback, in the interface consumed by beta
preservation. -/
theorem Store.StructPreciseTy.mapped_exactFunctionPushback
    (hstore : Store.StructPreciseTy Gamma sigma) :
    Store.StructExactFunctionPushback Gamma sigma :=
  Store.StructPreciseSingletonFunctionPushback.to_exact
    hstore.mapped_singletonFunctionPushback

/-! ## Unconditional laws -/

/-- The semantic-map fundamental theorem discharges all conditional
canonical assumptions in finite-run safety. -/
theorem Store.mappedPreciseStructSafetyLaws :
    Store.PreciseStructSafetyLaws where
  head hstore := hstore.mapped_singletonHeadPushback
  function hstore := hstore.mapped_exactFunctionPushback

end LambdaP
