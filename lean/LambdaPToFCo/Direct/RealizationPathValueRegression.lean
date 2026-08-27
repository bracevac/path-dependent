import LambdaPToFCo.Direct.Realization

/-!
# Sealed path-value regressions

Every capability in this file starts from `PathValue.lookup`; the private
constructor is intentionally unavailable.  The gates cover exact target and
singleton preservation, direct source opening, opening beneath a retained
pair first component, and lexical weakening beneath that component followed
by a second exact source opening.
-/

namespace LambdaPToFCo.Direct.Internal.RealizationPathValueRegression

open SystemFCo
open Representation
open Realization

/-! ## Public capability preservation -/

noncomputable def lookupTargetRename
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceSig targetSig : Sig}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    (environment : Env sourceContext sourceBase) (index : Fin n)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceBase targetBase mapping) :
    PathValue (environment.targetRename mapping typed) (.var index)
      (sourceContext.lookup index)
      ((environment.lookup index).targetRename mapping typed) :=
  (PathValue.lookup environment index).targetRename mapping typed

noncomputable def lookupTargetSubst
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sourceSig targetSig : Sig}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    (environment : Env sourceContext sourceBase) (index : Fin n)
    (substitution : Subst sourceSig targetSig)
    (typed : Subst.Typed sourceBase targetBase substitution) :
    PathValue (environment.targetSubst substitution typed) (.var index)
      (sourceContext.lookup index)
      ((environment.lookup index).targetSubst substitution typed) :=
  (PathValue.lookup environment index).targetSubst substitution typed

noncomputable def lookupSingleton
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base) (index : Fin n) :
    PathValue environment (.var index) (.Single (.var index))
      (singletonSlot (.var index) (environment.lookup index)) :=
  (PathValue.lookup environment index).singleton

/-! ## Exact source-opening gates -/

/-- Contract a dependent realization along the exact variable Slot retained
by the raw environment. -/
noncomputable def lookupSourceOpenAt
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base) (index : Fin n)
    (firstRealizes : Realizes environment (environment.lookup index).rep
      (.value (environment.lookup index).interface))
    {dependentSource : LambdaPFC.Ty (n + 1)}
    {dependentShape : Shape sig}
    {dependentRep : Rep base dependentSource dependentShape}
    {mode : Mode}
    {availability : Availability base dependentShape mode}
    (dependentRealizes : Realizes
      (extendAtInterface environment (sourceContext.lookup index)
        (environment.lookup index).interface
        (environment.lookup index).rep)
      dependentRep availability) :
    Realizes environment
      (dependentRep.sourceSubst
        (LambdaPFC.PathSubst.openAt (.var index)))
      availability :=
  Realizes.sourceOpenAt environment (PathValue.lookup environment index)
    firstRealizes dependentRealizes

/-- The same lookup authority contracts a dependent family while preserving
one additional exact pair-first extension. -/
noncomputable def lookupSourceOpenUnderFirst
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base) (index : Fin n)
    (boundRealizes : Realizes environment (environment.lookup index).rep
      (.value (environment.lookup index).interface))
    {firstSource : LambdaPFC.Ty (n + 1)}
    {firstShape : Shape sig}
    {firstRep : Rep base firstSource firstShape}
    (firstInterface : Shape.Interface base firstShape)
    {dependentSource : LambdaPFC.Ty (n + 2)}
    {dependentShape : Shape sig}
    {dependentRep : Rep base dependentSource dependentShape}
    {mode : Mode}
    {availability : Availability base dependentShape mode}
    (dependentRealizes : Realizes
      (extendAtInterface
        (extendAtInterface environment (sourceContext.lookup index)
          (environment.lookup index).interface
          (environment.lookup index).rep)
        firstSource firstInterface firstRep)
      dependentRep availability) :
    Realizes
      (extendAtInterface environment
        (firstSource.subst
          (LambdaPFC.PathSubst.openAt (.var index)))
        firstInterface
        (firstRep.sourceSubst
          (LambdaPFC.PathSubst.openAt (.var index))))
      (dependentRep.sourceSubst
        (LambdaPFC.PathSubst.openAt (.var index)).lift)
      availability :=
  Realizes.sourceOpenUnderFirst environment
    (PathValue.lookup environment index) boundRealizes firstInterface
    dependentRealizes

/-- Named nested/lexical gate.  An endpoint demand is first weakened beneath
an unrelated newly retained binding.  The older variable is then resolved
by public lookup in that literal extended environment, and its exact Slot
contracts the weakened family. -/
noncomputable def lookupLexicalNestedEndpoint
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {base : Ctx sig}
    (environment : Env sourceContext base) (index : Fin n)
    (firstRealizes : Realizes environment (environment.lookup index).rep
      (.value (environment.lookup index).interface))
    {outerSource : LambdaPFC.Ty n}
    {outerShape : Shape sig}
    {outerRep : Rep base outerSource outerShape}
    (outerInterface : Shape.Interface base outerShape)
    {endpointSource : LambdaPFC.Ty (n + 1)}
    {endpointShape : Shape (environment.lookup index).shape.scope}
    {endpointRep : Rep
      ((environment.lookup index).shape.context base)
      endpointSource endpointShape}
    {mode : Mode}
    {availability : Availability base
      (endpointShape.subst
        (environment.lookup index).interface.substitution) mode}
    (endpointRealizes : Realizes
      (extendAtInterface environment (sourceContext.lookup index)
        (environment.lookup index).interface
        (environment.lookup index).rep)
      (endpointRep.targetSubst
        (environment.lookup index).interface.substitution
        (environment.lookup index).interface.arguments.substitution_typed)
      availability) :
    let outerEnvironment :=
      extendAtInterface environment outerSource outerInterface outerRep
    let weakenedEndpoint :=
      (endpointRep.sourceRename LambdaPFC.FinFun.weaken.ext).targetSubst
        (environment.lookup index).interface.substitution
        (environment.lookup index).interface.arguments.substitution_typed
    Realizes outerEnvironment
      (weakenedEndpoint.sourceSubst
        (LambdaPFC.PathSubst.openAt (.var index.succ)))
      availability := by
  dsimp only
  let outerEnvironment :=
    extendAtInterface environment outerSource outerInterface outerRep
  let firstAtOuter := Realizes.sourceExtendAligned firstRealizes outerSource
    outerInterface outerRep
  have pathValue : PathValue outerEnvironment (.var index.succ)
      (sourceContext.lookup index).weaken
      ((environment.lookup index).sourceRename LambdaPFC.FinFun.weaken) := by
    simpa only [LambdaPFC.Ctx.lookup, extendAtInterface_there] using
      PathValue.lookup outerEnvironment index.succ
  apply Realizes.sourceOpenAt outerEnvironment pathValue firstAtOuter
  exact Realizes.sourceExtendUnderFirst environment endpointRealizes

end LambdaPToFCo.Direct.Internal.RealizationPathValueRegression
