import LambdaPToFCo.OperationalSourceProgress

/-!
# Source capabilities for existing-location return

Target result contexts can adapt one closed behavioral interface to another,
but they cannot prove that a physical source location has a canonical head.
This module records the strictly source-only fact needed when a resolved path
is returned through a saved frame.

The executable core has two return modes.  A noncanonical expected type asks
nothing of the physical head.  An expected arrow requires the current typed
path itself to retain a `FunctionPathSpine`, which rules out selection-to-arrow
detours.  Member results have no constructor: admitted paths start at a
singleton and generic path subsumption cannot target a member package.
-/

namespace LambdaPToFCo
namespace OperationalReturnPathCapability

open StaticTranslation
open OperationalCode
open OperationalStoreEnvironment
open OperationalApplicationSpine
open OperationalFunctionPathSpine
open OperationalAdmissibility
open OperationalMachineImage
open OperationalStateImage

/-- Source-head compatibility between a current typed path and the result
type expected by a saved frame.  The two types may live in different lexical
contexts; only their possible canonical runtime head is related. -/
inductive ReturnPathCapability
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {currentType : LambdaPFC.Ty n}
    (typing : Fragment.HasType sourceContext (.path path) currentType) :
    {m : Nat} -> LambdaPFC.Ty m -> Type where
  | nonCanonical
      {m : Nat} {expectedType : LambdaPFC.Ty m}
      (shape : NonCanonicalResultShape expectedType) :
      ReturnPathCapability typing expectedType
  | arrow
      {m : Nat}
      {currentDomain currentCodomain : LambdaPFC.Ty n}
      {expectedDomain expectedCodomain : LambdaPFC.Ty m}
      (typeEq : currentType =
        .Fun currentDomain currentCodomain.weaken)
      (spine : FunctionPathSpine (typeEq ▸ typing)) :
      ReturnPathCapability typing
        (.Fun expectedDomain expectedCodomain.weaken)

namespace ReturnPathCapability

/-- Every return type admitted by the capability uses one ordinary target
binder and therefore cannot demand a member-package source head. -/
def expectedShape
    {typing : Fragment.HasType sourceContext (.path path) currentType} :
    ReturnPathCapability typing expectedType -> OrdinaryShape expectedType
  | .nonCanonical shape => shape.ordinary
  | .arrow _ _ => .arrow

/-- Member-cell provenance is vacuous for every admitted path return. -/
theorem memberCell
    {typing : Fragment.HasType sourceContext (.path path) currentType}
    {expectedArity : Nat} {expectedType : LambdaPFC.Ty expectedArity}
    (capability : ReturnPathCapability typing expectedType)
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {expectedValuation : SourceValuation expectedArity current}
    {location : Fin current} :
    MemberCell expectedType sourceStore expectedValuation location :=
  MemberCell.ofNotMember capability.expectedShape.notMember

/-- The physical function-head witness selected by the current path can be
reused at any expected arrow type.  FunctionCell deliberately records only
the abstraction head, not a relationship between arrow components. -/
theorem functionCell
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceStore : LambdaPFC.Store current}
    {sourceValuation : SourceValuation n current}
    {sig : SystemFCo.Sig} {targetContext : SystemFCo.Ctx sig}
    {scope : Scope sourceContext targetContext}
    {closing : OperationalEnvironment.ClosingEnv sig []}
    (environment : StoreEnvironment sourceContext sourceStore sourceValuation
      targetContext scope closing)
    {path : LambdaPFC.Path n} {currentType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path path) currentType}
    {expectedArity : Nat} {expectedType : LambdaPFC.Ty expectedArity}
    (capability : ReturnPathCapability typing expectedType)
    (expectedValuation : SourceValuation expectedArity current)
    (location : Fin current)
    (location_eq : location =
      sourceValuation (typedPathReferent typing)) :
    FunctionCell expectedType sourceStore expectedValuation location := by
  cases capability with
  | nonCanonical shape =>
      intro domain codomain typeEq
      exact (shape.notArrow
        { domain := domain
          codomain := codomain.weaken
          equality := typeEq }).elim
  | arrow typeEq spine =>
      cases typeEq
      rcases
          OperationalSourceProgress.FunctionPathSpine.source_function
            environment spine with
        ⟨runtimeDomain, runtimeBody, binds⟩
      intro _ _ _
      refine ⟨runtimeDomain, runtimeBody, ?_⟩
      rw [location_eq]
      exact binds

end ReturnPathCapability

namespace OperationallyAdmissible

/-- The repaired admissibility grammar exposes a same-interface return
capability for every typed path. -/
def returnPathCapability
    {typing : Fragment.HasType sourceContext (.path path) sourceType} :
    OperationallyAdmissible typing -> ReturnPathCapability typing sourceType
  | .path _ => .nonCanonical .singleton
  | .functionPath spine => .arrow rfl spine
  | .neutralSub .path _ _ targetShape => .nonCanonical targetShape

end OperationallyAdmissible

namespace ResolvedPathView

/-- Frame-typed member provenance selected by a source return capability. -/
theorem frameMemberCell
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody)
    {origin : CurrentOrigin sourceStore}
    {path : LambdaPFC.Path origin.original.arity}
    {location : Fin current}
    (resolved : ResolvedPathView origin path location)
    (capability : ReturnPathCapability resolved.typing frame.image.holeType) :
    MemberCell frame.image.holeType sourceStore frame.image.valuation
      location :=
  capability.memberCell

/-- Frame-typed abstraction provenance selected by a source return
capability and the resolved path's retained lexical store environment. -/
theorem frameFunctionCell
    {current : Nat} {sourceStore : LambdaPFC.Store current}
    {runtimeBody : LambdaPFC.Tm (current + 1)}
    (frame : CapturedFrame sourceStore runtimeBody)
    {origin : CurrentOrigin sourceStore}
    {path : LambdaPFC.Path origin.original.arity}
    {location : Fin current}
    (resolved : ResolvedPathView origin path location)
    (capability : ReturnPathCapability resolved.typing frame.image.holeType) :
    FunctionCell frame.image.holeType sourceStore frame.image.valuation
      location :=
  capability.functionCell origin.environment frame.image.valuation location
    resolved.location_eq

end ResolvedPathView

end OperationalReturnPathCapability
end LambdaPToFCo
