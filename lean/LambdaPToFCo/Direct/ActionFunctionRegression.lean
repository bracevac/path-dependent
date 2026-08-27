import LambdaPToFCo.Direct.Action

/-!
# Dependent-function Action regressions

The whole gate retains the contravariant domain Action and exact delayed
codomain callback under the literal target-oriented scope extension. The
callback gate invokes the enriched compiler once and recovers the Relation
and recursive Action from that same opening.
-/

namespace LambdaPToFCo.Direct.Internal.ActionFunctionRegression

open SystemFCo
open Representation

/-- The literal source `.fun` rule and `compileExact` erasure are accepted
together without an endpoint equality or arbitrary whole Relation. -/
private noncomputable def wholeGate
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx root}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape root}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    {scope : ContextRelation.Scope sourceContext targetContext .target base}
    {domainSubtyping : LambdaPFC.Tau.Sub targetContext
      (.ty targetDomainType) (.ty sourceDomainType)}
    {codomainSubtyping : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)}
    {domainRelation : Relation base targetDomainType sourceDomainType
      targetDomain sourceDomain}
    (domain : Action scope domainSubtyping (.proper domainRelation))
    (sourceCodomainRep : Rep (sourceDomain.context base)
      sourceCodomainType sourceCodomain)
    (targetCodomainRep : Rep (targetDomain.context base)
      targetCodomainType targetCodomain)
    (codomainRelation : Action.FunctionCodomainRelations
      (base := base)
      (sourceCodomainType := sourceCodomainType)
      (targetCodomainType := targetCodomainType)
      (sourceDomain := sourceDomain)
      (targetDomain := targetDomain)
      (sourceCodomain := sourceCodomain)
      (targetCodomain := targetCodomain))
    (codomainAction : {final : Sig} -> {finalContext : Ctx final} ->
      (next : Rename
        (FunctionSubtyping.ExactCodomainCompiler.CallbackSig sourceDomain
          sourceCodomain targetDomain) final) ->
      (nextTyped : Rename.Typed
        (FunctionSubtyping.ExactCodomainCompiler.CallbackContext base
          sourceDomain sourceCodomain targetDomain) finalContext next) ->
      (sourceInterface : Shape.Interface finalContext
        (FunctionSubtyping.ExactCodomainCompiler.SourceDomainAt sourceDomain
          targetDomain sourceCodomain next)) ->
      (targetInterface : Shape.Interface finalContext
        (FunctionSubtyping.ExactCodomainCompiler.TargetDomainAt sourceDomain
          targetDomain sourceCodomain next)) ->
      Action
        (FunctionSubtyping.codomainActionScopeAt scope domainRelation next
          nextTyped sourceInterface targetInterface)
        codomainSubtyping
        (.proper (codomainRelation next nextTyped sourceInterface
          targetInterface))) :=
  Action.function scope domain sourceCodomainRep targetCodomainRep
    codomainRelation codomainAction

/-- One enriched callback invocation returns the exact codomain Relation
paired with its Action under the literal extended scope. -/
private noncomputable def codomainGate
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx root} {finalContext : Ctx final}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape root}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    {scope : ContextRelation.Scope sourceContext targetContext .target base}
    {domainRelation : Relation base targetDomainType sourceDomainType
      targetDomain sourceDomain}
    {codomainSubtyping : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)}
    (codomainRelation : Action.FunctionCodomainRelations
      (base := base)
      (sourceCodomainType := sourceCodomainType)
      (targetCodomainType := targetCodomainType)
      (sourceDomain := sourceDomain)
      (targetDomain := targetDomain)
      (sourceCodomain := sourceCodomain)
      (targetCodomain := targetCodomain))
    (codomainAction : {future : Sig} -> {futureContext : Ctx future} ->
      (next : Rename
        (FunctionSubtyping.ExactCodomainCompiler.CallbackSig sourceDomain
          sourceCodomain targetDomain) future) ->
      (nextTyped : Rename.Typed
        (FunctionSubtyping.ExactCodomainCompiler.CallbackContext base
          sourceDomain sourceCodomain targetDomain) futureContext next) ->
      (sourceInterface : Shape.Interface futureContext
        (FunctionSubtyping.ExactCodomainCompiler.SourceDomainAt sourceDomain
          targetDomain sourceCodomain next)) ->
      (targetInterface : Shape.Interface futureContext
        (FunctionSubtyping.ExactCodomainCompiler.TargetDomainAt sourceDomain
          targetDomain sourceCodomain next)) ->
      Action
        (FunctionSubtyping.codomainActionScopeAt scope domainRelation next
          nextTyped sourceInterface targetInterface)
        codomainSubtyping
        (.proper (codomainRelation next nextTyped sourceInterface
          targetInterface)))
    (next : Rename
      (FunctionSubtyping.ExactCodomainCompiler.CallbackSig sourceDomain
        sourceCodomain targetDomain) final)
    (nextTyped : Rename.Typed
      (FunctionSubtyping.ExactCodomainCompiler.CallbackContext base
        sourceDomain sourceCodomain targetDomain) finalContext next)
    (sourceInterface : Shape.Interface finalContext
      (FunctionSubtyping.ExactCodomainCompiler.SourceDomainAt sourceDomain
        targetDomain sourceCodomain next))
    (targetInterface : Shape.Interface finalContext
      (FunctionSubtyping.ExactCodomainCompiler.TargetDomainAt sourceDomain
        targetDomain sourceCodomain next)) :=
  (Action.functionEnriched codomainRelation codomainAction).compile next
    nextTyped sourceInterface targetInterface

/-- The delayed codomain closure is excluded from the static Action size. -/
private theorem wholeGate_treeSize
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx root}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape root}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    {scope : ContextRelation.Scope sourceContext targetContext .target base}
    {domainSubtyping : LambdaPFC.Tau.Sub targetContext
      (.ty targetDomainType) (.ty sourceDomainType)}
    {codomainSubtyping : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)}
    {domainRelation : Relation base targetDomainType sourceDomainType
      targetDomain sourceDomain}
    (domain : Action scope domainSubtyping (.proper domainRelation))
    (sourceCodomainRep : Rep (sourceDomain.context base)
      sourceCodomainType sourceCodomain)
    (targetCodomainRep : Rep (targetDomain.context base)
      targetCodomainType targetCodomain)
    (codomainRelation : Action.FunctionCodomainRelations
      (base := base)
      (sourceCodomainType := sourceCodomainType)
      (targetCodomainType := targetCodomainType)
      (sourceDomain := sourceDomain)
      (targetDomain := targetDomain)
      (sourceCodomain := sourceCodomain)
      (targetCodomain := targetCodomain))
    (codomainAction : {final : Sig} -> {finalContext : Ctx final} ->
      (next : Rename
        (FunctionSubtyping.ExactCodomainCompiler.CallbackSig sourceDomain
          sourceCodomain targetDomain) final) ->
      (nextTyped : Rename.Typed
        (FunctionSubtyping.ExactCodomainCompiler.CallbackContext base
          sourceDomain sourceCodomain targetDomain) finalContext next) ->
      (sourceInterface : Shape.Interface finalContext
        (FunctionSubtyping.ExactCodomainCompiler.SourceDomainAt sourceDomain
          targetDomain sourceCodomain next)) ->
      (targetInterface : Shape.Interface finalContext
        (FunctionSubtyping.ExactCodomainCompiler.TargetDomainAt sourceDomain
          targetDomain sourceCodomain next)) ->
      Action
        (FunctionSubtyping.codomainActionScopeAt scope domainRelation next
          nextTyped sourceInterface targetInterface)
        codomainSubtyping
        (.proper (codomainRelation next nextTyped sourceInterface
          targetInterface))) :
    (wholeGate domain sourceCodomainRep targetCodomainRep codomainRelation
      codomainAction).treeSize = domain.treeSize + 1 := by
  rfl

end LambdaPToFCo.Direct.Internal.ActionFunctionRegression
