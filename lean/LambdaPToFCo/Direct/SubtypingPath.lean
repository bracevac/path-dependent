import LambdaPToFCo.Direct.SubtypingAtomic
import LambdaPToFCo.Direct.FormedPath

/-!
# Formation-aware path subtyping atoms

Widening and singleton symmetry are value-specific path rules.  Their two
endpoint Slots are materialized by the same literal `Path.Ty` derivation and
the same formed environment.  Nested pair projections and closed carriers
therefore retain the actual selected package; no child interface is rebuilt
from an erased representation.

At the root, the source singleton and its target denote one distinguished
path value.  The ordinary System FCo conversion may consequently return the
materialized target package independently of its argument.  The beta theorem
below records exactly that operational fact.  It is not an inverse, a
round-trip law, or a source-type equivalence.

This leaf is intentionally restricted to one root formed environment.
It must not be reused beneath a pair/function rule whose source and target
binder contexts differ.  That case still needs a scope-aware formed-path
interpreter: run the literal path in the proof-side environment and resolve
the opposite endpoint recursively through the sealed slot alignment.  Until
that layer exists, contextual path atoms remain an explicit structural
integration blocker.
-/

namespace LambdaPToFCo.Direct.Internal.SubtypingPath

open SystemFCo
open Representation
open Formation
open FormedPath
open SubtypingScope

/-- Ignore an input package and return one exact materialized path package. -/
private noncomputable def valueSpecificConversion
    {base : Ctx sig} {target : Shape sig}
    (targetInterface : Shape.Interface base target)
    (sourceType : Ty sig) : Conversion base sourceType target.inputTy :=
  let typed := Rename.Typed.weaken base (.var sourceType)
  Conversion.ofFunction
    (Adapter.ofBody sourceType
      (targetInterface.package.rename (Rename.weaken .var)))
    (Adapter.ofBody_hasType (by
      simpa only [Ty.weaken, Shape.inputTy_rename] using
        targetInterface.package_hasType.rename typed))

/-- Applying the value-specific conversion takes one ordinary beta step to
the retained target package. -/
private theorem valueSpecificConversion_beta
    {base : Ctx sig} {target : Shape sig}
    (targetInterface : Shape.Interface base target)
    (sourceType : Ty sig)
    (argument : Exp sig) (argumentValue : Exp.IsValue argument) :
    Exp.Step
      (Adapter.apply
        (valueSpecificConversion targetInterface sourceType).function
        argument)
      targetInterface.package := by
  change Exp.Step
    (.app (.abs sourceType
      (targetInterface.package.rename (Rename.weaken .var))) argument)
    targetInterface.package
  have step := Exp.Step.beta (parameter := sourceType)
    (body := targetInterface.package.rename (Rename.weaken .var))
    argumentValue
  have cancel := targetInterface.package.weaken_subst_cancel
    (Subst.openVar argument) (Subst.weakenAsSubst_comp_openVar argument)
  change
    (targetInterface.package.rename (Rename.weaken .var)).subst
      (Subst.openVar argument) = targetInterface.package at cancel
  rw [cancel] at step
  exact step

/-- Relate two exact materialized Slots by returning the distinguished target
package.  This helper is sealed inside derivation-indexed path atoms. -/
private noncomputable def valueSpecificRelation
    {sourceContext : LambdaPFC.Ctx n} {base : Ctx sig}
    {sourceType targetType : LambdaPFC.Ty n}
    (source : Slot sourceContext base sourceType)
    (target : Slot sourceContext base targetType) :
    Relation base sourceType targetType source.shape target.shape :=
  Relation.ofConversion source.formation.rep target.formation.rep
    (valueSpecificConversion target.interface source.shape.inputTy)

/-- Exact widening relation after both endpoints have been materialized by
the literal path derivation. -/
private noncomputable def widenAt
    {sourceContext : LambdaPFC.Ctx n} {base : Ctx sig}
    {path : LambdaPFC.Path n} {targetType : LambdaPFC.Ty n}
    (_typing : LambdaPFC.Path.Ty sourceContext path (.ty targetType))
    (source : Slot sourceContext base (.Single path))
    (target : Slot sourceContext base targetType) :
    Relation base (.Single path) targetType source.shape target.shape :=
  valueSpecificRelation source target

/-- Exact symmetry relation after both endpoints have been materialized by
the literal path derivation. -/
private noncomputable def symmAt
    {sourceContext : LambdaPFC.Ctx n} {base : Ctx sig}
    {path referentPath : LambdaPFC.Path n}
    (_typing : LambdaPFC.Path.Ty sourceContext path
      (.ty (.Single referentPath)))
    (source : Slot sourceContext base (.Single referentPath))
    (target : Slot sourceContext base (.Single path)) :
    Relation base (.Single referentPath) (.Single path)
      source.shape target.shape :=
  valueSpecificRelation source target

/-- Compile singleton widening from one exact formed environment.

`materializeSingleton` is the source endpoint produced by path introduction;
`materialize` is the exact selected target.  Both pass through the same real
receiver packages and are closed back to the same root. -/
noncomputable def widen
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {targetType : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty targetType))
    {base : Ctx sig}
    (environment : Formation.Env sourceContext base) :
    let source := FormedPath.materializeSingleton typing environment
    let target := FormedPath.materialize typing environment
    CutView (Scope.root environment .source) (.widen typing)
      source.shape target.shape := by
  dsimp only
  let source := FormedPath.materializeSingleton typing environment
  let target := FormedPath.materialize typing environment
  exact CutView.ofRelation source.formation target.formation
    (widenAt typing source target)

/-- Compile singleton symmetry from one exact formed environment.

The selected path already has the source singleton type.  Reclosing that
selected Slot gives the source endpoint; introducing and reclosing its
singleton gives the target endpoint. -/
noncomputable def symm
    {sourceContext : LambdaPFC.Ctx n}
    {path referentPath : LambdaPFC.Path n}
    (typing : LambdaPFC.Path.Ty sourceContext path
      (.ty (.Single referentPath)))
    {base : Ctx sig}
    (environment : Formation.Env sourceContext base) :
    let source := FormedPath.materialize typing environment
    let target := FormedPath.materializeSingleton typing environment
    CutView (Scope.root environment .source) (.symm typing)
      source.shape target.shape := by
  dsimp only
  let source := FormedPath.materialize typing environment
  let target := FormedPath.materializeSingleton typing environment
  exact CutView.ofRelation source.formation target.formation
    (symmAt typing source target)

/-- Operational qualification for materialized widening: its conversion
returns the exact target path package after one beta step. -/
theorem widen_beta
    {sourceContext : LambdaPFC.Ctx n} {base : Ctx sig}
    {path : LambdaPFC.Path n} {targetType : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty targetType))
    (environment : Formation.Env sourceContext base)
    (argument : Exp sig) (argumentValue : Exp.IsValue argument) :
    let target := FormedPath.materialize typing environment
    Exp.Step
      (Adapter.apply (widen typing environment).relation.conversion.function
        argument)
      target.interface.package := by
  dsimp only [widen]
  exact valueSpecificConversion_beta _ _ argument argumentValue

/-- Operational qualification for materialized symmetry: its conversion
returns the exact singleton-of-path package after one beta step. -/
theorem symm_beta
    {sourceContext : LambdaPFC.Ctx n} {base : Ctx sig}
    {path referentPath : LambdaPFC.Path n}
    (typing : LambdaPFC.Path.Ty sourceContext path
      (.ty (.Single referentPath)))
    (environment : Formation.Env sourceContext base)
    (argument : Exp sig) (argumentValue : Exp.IsValue argument) :
    let target := FormedPath.materializeSingleton typing environment
    Exp.Step
      (Adapter.apply (symm typing environment).relation.conversion.function
        argument)
      target.interface.package := by
  dsimp only [symm]
  exact valueSpecificConversion_beta _ _ argument argumentValue

end LambdaPToFCo.Direct.Internal.SubtypingPath
