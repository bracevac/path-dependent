import LambdaPToFCo.Direct.Relation

/-!
# Sealed relations between direct compiler contexts

Dependent pair and function rules recurse under source contexts whose newest
bindings may differ.  A `Scope` retains the two exact raw representation
environments and one ordinary target relation for each corresponding slot.
The relation is oriented from the endpoint selected by `ProofSide` to the
opposite endpoint.

The constructor is sealed.  Scopes arise only by aliasing one root
environment or by extending an existing scope with the exact interfaces,
representations, and head relation available in a structural continuation.
No well-formedness tree, source proof history, or target-shape equality is
stored here.
-/

namespace LambdaPToFCo.Direct.Internal.ContextRelation

open SystemFCo
open Representation

/-- Rename the two source-syntax indices of a relation independently.  The
target programs and target Shapes are unchanged. -/
private noncomputable def relationSourceRename
    {base : Ctx sig}
    {sourceType targetType : LambdaPFC.Ty n}
    {source target : Shape sig}
    (relation : Relation base sourceType targetType source target)
    (sourceMapping targetMapping : LambdaPFC.FinFun n m) :
    Relation base (sourceType.rename sourceMapping)
      (targetType.rename targetMapping) source target where
  sourceRep := relation.sourceRep.sourceRename sourceMapping
  targetRep := relation.targetRep.sourceRename targetMapping
  conversion := relation.conversion
  interfaceMap := relation.interfaceMap

/-- A sealed pointwise relation between two raw source environments.

Pair-member recursion is source-oriented.  Function-codomain recursion is
target-oriented because its domain premise is contravariant. -/
structure Scope
    (sourceContext targetContext : LambdaPFC.Ctx n)
    (side : ProofSide) (base : Ctx sig) : Type where
  private mk ::
  source : Env sourceContext base
  target : Env targetContext base
  aligned : match side with
    | .source => (index : Fin n) ->
        Relation base (sourceContext.lookup index)
          (targetContext.lookup index)
          (source.lookup index).shape (target.lookup index).shape
    | .target => (index : Fin n) ->
        Relation base (targetContext.lookup index)
          (sourceContext.lookup index)
          (target.lookup index).shape (source.lookup index).shape

namespace Scope

/-- Forget only the pointwise alignment and pass the two exact raw
environments to a frozen structural kernel. -/
def endpointEnvs
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide} {base : Ctx sig}
    (scope : Scope sourceContext targetContext side base) :
    EndpointEnvs sourceContext targetContext base where
  source := scope.source
  target := scope.target

/-- Create a contextual relation by aliasing one exact raw environment at
both endpoints. -/
noncomputable def root
    {sourceContext : LambdaPFC.Ctx n} {base : Ctx sig}
    (environment : Env sourceContext base) (side : ProofSide) :
    Scope sourceContext sourceContext side base := by
  cases side with
  | source =>
      exact .mk environment environment (fun index =>
        Relation.refl (environment.lookup index).rep)
  | target =>
      exact .mk environment environment (fun index =>
        Relation.refl (environment.lookup index).rep)

/-- Reindex both raw environments and every pointwise relation through one
typed target renaming. -/
noncomputable def targetRename
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {side : ProofSide}
    {sourceBase : Ctx sourceSig} {targetBase : Ctx targetSig}
    (scope : Scope sourceContext targetContext side sourceBase)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceBase targetBase mapping) :
    Scope sourceContext targetContext side targetBase := by
  cases side with
  | source =>
      exact .mk
        (scope.source.targetRename mapping typed)
        (scope.target.targetRename mapping typed)
        (fun index => (scope.aligned index).targetRename mapping typed)
  | target =>
      exact .mk
        (scope.source.targetRename mapping typed)
        (scope.target.targetRename mapping typed)
        (fun index => (scope.aligned index).targetRename mapping typed)

/-- Extend a source-oriented scope in the exact common continuation of a
dependent pair's first-component interface map. -/
noncomputable def extendPair
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (scope : Scope sourceContext targetContext .source base)
    {sourceType targetType : LambdaPFC.Ty n}
    {sourceShape targetShape : Shape sig}
    (sourceInterface : Shape.Interface base sourceShape)
    (sourceRep : Rep base sourceType sourceShape)
    (targetInterface : Shape.Interface base targetShape)
    (targetRep : Rep base targetType targetShape)
    (head : Relation base sourceType targetType sourceShape targetShape) :
    Scope (sourceContext.snoc sourceType)
      (targetContext.snoc targetType) .source base := by
  let sourceEnvironment := scope.source.extend Rename.id
    (TypedRename.id base) sourceType sourceInterface
    (sourceRep.sourceRename LambdaPFC.FinFun.weaken)
  let targetEnvironment := scope.target.extend Rename.id
    (TypedRename.id base) targetType targetInterface
    (targetRep.sourceRename LambdaPFC.FinFun.weaken)
  apply Scope.mk sourceEnvironment targetEnvironment
  intro index
  refine Fin.cases ?_ (fun older => ?_) index
  · simpa only [LambdaPFC.Ctx.lookup, sourceEnvironment, targetEnvironment,
      Env.extend_here] using
      relationSourceRename head LambdaPFC.FinFun.weaken
        LambdaPFC.FinFun.weaken
  · simp only [LambdaPFC.Ctx.lookup, sourceEnvironment, targetEnvironment,
      Env.extend_there, LambdaPFC.Ty.weaken, Fin.cases_succ,
      Slot.targetRename, Slot.sourceRename, Shape.rename_id]
    change Relation base
      ((sourceContext.lookup older).rename LambdaPFC.FinFun.weaken)
      ((targetContext.lookup older).rename LambdaPFC.FinFun.weaken)
      (scope.source.lookup older).shape (scope.target.lookup older).shape
    exact relationSourceRename (scope.aligned older)
      LambdaPFC.FinFun.weaken LambdaPFC.FinFun.weaken

/-- Extend a target-oriented scope in the exact common continuation of a
dependent function's reversed-domain interface map. -/
noncomputable def extendFunction
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (scope : Scope sourceContext targetContext .target base)
    {sourceType targetType : LambdaPFC.Ty n}
    {sourceShape targetShape : Shape sig}
    (sourceInterface : Shape.Interface base sourceShape)
    (sourceRep : Rep base sourceType sourceShape)
    (targetInterface : Shape.Interface base targetShape)
    (targetRep : Rep base targetType targetShape)
    (head : Relation base targetType sourceType targetShape sourceShape) :
    Scope (sourceContext.snoc sourceType)
      (targetContext.snoc targetType) .target base := by
  let sourceEnvironment := scope.source.extend Rename.id
    (TypedRename.id base) sourceType sourceInterface
    (sourceRep.sourceRename LambdaPFC.FinFun.weaken)
  let targetEnvironment := scope.target.extend Rename.id
    (TypedRename.id base) targetType targetInterface
    (targetRep.sourceRename LambdaPFC.FinFun.weaken)
  apply Scope.mk sourceEnvironment targetEnvironment
  intro index
  refine Fin.cases ?_ (fun older => ?_) index
  · simpa only [LambdaPFC.Ctx.lookup, sourceEnvironment, targetEnvironment,
      Env.extend_here] using
      relationSourceRename head LambdaPFC.FinFun.weaken
        LambdaPFC.FinFun.weaken
  · simp only [LambdaPFC.Ctx.lookup, sourceEnvironment, targetEnvironment,
      Env.extend_there, LambdaPFC.Ty.weaken, Fin.cases_succ,
      Slot.targetRename, Slot.sourceRename, Shape.rename_id]
    change Relation base
      ((targetContext.lookup older).rename LambdaPFC.FinFun.weaken)
      ((sourceContext.lookup older).rename LambdaPFC.FinFun.weaken)
      (scope.target.lookup older).shape (scope.source.lookup older).shape
    exact relationSourceRename (scope.aligned older)
      LambdaPFC.FinFun.weaken LambdaPFC.FinFun.weaken

end Scope

end LambdaPToFCo.Direct.Internal.ContextRelation
