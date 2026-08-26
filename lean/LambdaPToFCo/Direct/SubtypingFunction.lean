import LambdaPToFCo.Direct.SubtypingAtomic
import LambdaPToFCo.Direct.FunctionSubtyping

/-!
# Formation-aware dependent-function subtyping

This layer connects the literal source `Tau.Sub.fun` rule to the ordinary
target function package transformer.  Domain subtyping is contravariant, so
the retained domain cut is oriented from the target function's domain to the
source function's domain.  Codomain recursion happens only after that exact
reversed interface map has supplied both real domain interfaces.

The recursive boundary is indexed by the literal codomain derivation and can
return a cut only for the two formations constructed in that continuation.
There are no shape equalities, target callbacks, or source-proof certificates.
-/

namespace LambdaPToFCo.Direct.Internal.SubtypingFunction

open SystemFCo
open Representation
open Formation
open SubtypingScope

/-- Exact contravariant domain cut.  Its endpoint formations keep their
ordinary source/target ownership even though the relation runs target to
source. -/
structure DomainCut
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    (scope : Scope sourceContext targetContext .target base)
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    (_derivation : LambdaPFC.Tau.Sub targetContext
      (.ty targetDomainType) (.ty sourceDomainType))
    (sourceDomain targetDomain : Shape sig) : Type where
  private mk ::
  sourceFormation : Formation sourceContext base sourceDomainType sourceDomain
  targetFormation : Formation targetContext base targetDomainType targetDomain
  relation : Relation base targetDomainType sourceDomainType
    targetDomain sourceDomain

namespace DomainCut

noncomputable def ofRelation
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {scope : Scope sourceContext targetContext .target base}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {derivation : LambdaPFC.Tau.Sub targetContext
      (.ty targetDomainType) (.ty sourceDomainType)}
    {sourceDomain targetDomain : Shape sig}
    (sourceFormation : Formation sourceContext base sourceDomainType
      sourceDomain)
    (targetFormation : Formation targetContext base targetDomainType
      targetDomain)
    (relation : Relation base targetDomainType sourceDomainType
      targetDomain sourceDomain) :
    DomainCut scope derivation sourceDomain targetDomain :=
  .mk sourceFormation targetFormation relation

end DomainCut

private noncomputable def packageTyped
    (base : Ctx sig) (sourceDomain : Shape sig)
    (sourceCodomain : Shape sourceDomain.scope) :
    Rename.Typed base
      (base.bindVar (Function.plan sourceDomain sourceCodomain).inputTy)
      (FunctionSubtyping.packageMapping sig) :=
  Rename.Typed.weaken base
    (.var (Function.plan sourceDomain sourceCodomain).inputTy)

private noncomputable def observationTyped
    (base : Ctx sig) (sourceDomain : Shape sig)
    (sourceCodomain : Shape sourceDomain.scope) :
    Rename.Typed
      (base.bindVar (Function.plan sourceDomain sourceCodomain).inputTy)
      (Stable.openedContext base
        (Function.plan sourceDomain sourceCodomain))
      (FunctionSubtyping.observationMapping sourceDomain sourceCodomain) :=
  (Stable.sourceAtBinder
    (Function.plan sourceDomain sourceCodomain)).telescope.weaken_typed
      (base.bindVar (Function.plan sourceDomain sourceCodomain).inputTy)

private noncomputable def identityTyped
    (base : Ctx sig) (sourceDomain : Shape sig)
    (sourceCodomain : Shape sourceDomain.scope) :
    Rename.Typed
      (Stable.openedContext base
        (Function.plan sourceDomain sourceCodomain))
      (FunctionSubtyping.exactContext base sourceDomain sourceCodomain)
      (FunctionSubtyping.identityMapping sourceDomain sourceCodomain) :=
  Rename.Typed.weaken
    (Stable.openedContext base
      (Function.plan sourceDomain sourceCodomain))
    (.var (Stable.sourceAtBinder
      (Function.plan sourceDomain sourceCodomain)).identityTy)

/-- The sealed target-oriented scope at the exact codomain continuation. -/
noncomputable def codomainScopeAt
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceDomain targetDomain : Shape sig}
    {sourceCodomain : Shape sourceDomain.scope}
    {rootScope : Scope sourceContext targetContext .target base}
    {domainDerivation : LambdaPFC.Tau.Sub targetContext
      (.ty targetDomainType) (.ty sourceDomainType)}
    (domain : DomainCut rootScope domainDerivation sourceDomain targetDomain)
    (next : Rename
      (FunctionSubtyping.observedDomain sourceDomain sourceCodomain
        targetDomain).scope final)
    (nextTyped : Rename.Typed
      ((FunctionSubtyping.observedDomain sourceDomain sourceCodomain
        targetDomain).context
          (FunctionSubtyping.exactContext base sourceDomain sourceCodomain))
      finalContext next)
    (sourceInterface : Shape.Interface finalContext
      (FunctionSubtyping.sourceDomainAt sourceDomain targetDomain
        sourceCodomain next))
    (targetInterface : Shape.Interface finalContext
      (FunctionSubtyping.targetDomainAt sourceDomain targetDomain
        sourceCodomain next)) :
    Scope (sourceContext.snoc sourceDomainType)
      (targetContext.snoc targetDomainType) .target finalContext := by
  let packageMap := FunctionSubtyping.packageMapping sig
  let packageMapTyped := packageTyped base sourceDomain sourceCodomain
  let observationMap := FunctionSubtyping.observationMapping sourceDomain
    sourceCodomain
  let observationMapTyped := observationTyped base sourceDomain
    sourceCodomain
  let identityMap := FunctionSubtyping.identityMapping sourceDomain
    sourceCodomain
  let identityMapTyped := identityTyped base sourceDomain sourceCodomain
  let currentContext := FunctionSubtyping.exactContext base sourceDomain
    sourceCodomain
  let targetDomainCurrent := FunctionSubtyping.observedDomain sourceDomain
    sourceCodomain targetDomain
  let opening := targetDomainCurrent.binders.weaken
  let openingTyped := targetDomainCurrent.binders.weaken_typed currentContext
  let scopePackage := rootScope.targetRename packageMap packageMapTyped
  let scopeObserved := scopePackage.targetRename observationMap
    observationMapTyped
  let scopeCurrent := scopeObserved.targetRename identityMap identityMapTyped
  let scopeOpened := scopeCurrent.targetRename opening openingTyped
  let scopeFinal := scopeOpened.targetRename next nextTyped
  let sourcePackage := domain.sourceFormation.targetRename packageMap
    packageMapTyped
  let sourceObserved := sourcePackage.targetRename observationMap
    observationMapTyped
  let sourceCurrent := sourceObserved.targetRename identityMap identityMapTyped
  let sourceOpened := sourceCurrent.targetRename opening openingTyped
  let sourceFinal := sourceOpened.targetRename next nextTyped
  let targetPackage := domain.targetFormation.targetRename packageMap
    packageMapTyped
  let targetObserved := targetPackage.targetRename observationMap
    observationMapTyped
  let targetCurrent := targetObserved.targetRename identityMap identityMapTyped
  let targetOpened := targetCurrent.targetRename opening openingTyped
  let targetFinal := targetOpened.targetRename next nextTyped
  let relationPackage := domain.relation.targetRename packageMap
    packageMapTyped
  let relationObserved := relationPackage.targetRename observationMap
    observationMapTyped
  let relationCurrent := relationObserved.targetRename identityMap
    identityMapTyped
  let relationOpened := relationCurrent.targetRename opening openingTyped
  let relationFinal := relationOpened.targetRename next nextTyped
  exact scopeFinal.extendFunction sourceInterface sourceFinal
    targetInterface targetFinal relationFinal

noncomputable def sourceCodomainFormationAt
    {sourceContext : LambdaPFC.Ctx n}
    {sourceDomainType : LambdaPFC.Ty n}
    {sourceCodomainType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceDomain targetDomain : Shape sig}
    {sourceCodomain : Shape sourceDomain.scope}
    (formation : Formation (sourceContext.snoc sourceDomainType)
      (sourceDomain.context base) sourceCodomainType sourceCodomain)
    (next : Rename
      (FunctionSubtyping.observedDomain sourceDomain sourceCodomain
        targetDomain).scope final)
    (nextTyped : Rename.Typed
      ((FunctionSubtyping.observedDomain sourceDomain sourceCodomain
        targetDomain).context
          (FunctionSubtyping.exactContext base sourceDomain sourceCodomain))
      finalContext next)
    (sourceInterface : Shape.Interface finalContext
      (FunctionSubtyping.sourceDomainAt sourceDomain targetDomain
        sourceCodomain next)) :
    Formation (sourceContext.snoc sourceDomainType) finalContext
      sourceCodomainType
      (FunctionSubtyping.sourceCodomainAt sourceDomain targetDomain
        sourceCodomain next sourceInterface) := by
  let packageMap := FunctionSubtyping.packageMapping sig
  let packageMapTyped := packageTyped base sourceDomain sourceCodomain
  let sourcePackage := sourceDomain.rename packageMap
  let observationMap := FunctionSubtyping.observationMapping sourceDomain
    sourceCodomain
  let observationMapTyped := observationTyped base sourceDomain
    sourceCodomain
  let sourceObserved := sourcePackage.rename observationMap
  let identityMap := FunctionSubtyping.identityMapping sourceDomain
    sourceCodomain
  let identityMapTyped := identityTyped base sourceDomain sourceCodomain
  let sourceCurrent := sourceObserved.rename identityMap
  let targetCurrent := FunctionSubtyping.observedDomain sourceDomain
    sourceCodomain targetDomain
  let currentContext := FunctionSubtyping.exactContext base sourceDomain
    sourceCodomain
  let opening := targetCurrent.binders.weaken
  let openingTyped := targetCurrent.binders.weaken_typed currentContext
  let sourceOpened := sourceCurrent.rename opening
  let atPackage := formation.targetRename
    (sourceDomain.liftRename packageMap)
    (sourceDomain.liftRename_typed packageMapTyped)
  let atObservation := atPackage.targetRename
    (sourcePackage.liftRename observationMap)
    (sourcePackage.liftRename_typed observationMapTyped)
  let atIdentity := atObservation.targetRename
    (sourceObserved.liftRename identityMap)
    (sourceObserved.liftRename_typed identityMapTyped)
  let atOpening := atIdentity.targetRename
    (sourceCurrent.liftRename opening)
    (sourceCurrent.liftRename_typed openingTyped)
  let atNext := atOpening.targetRename
    (sourceOpened.liftRename next)
    (sourceOpened.liftRename_typed nextTyped)
  exact atNext.targetSubst sourceInterface.substitution
    sourceInterface.arguments.substitution_typed

noncomputable def targetCodomainFormationAt
    {targetContext : LambdaPFC.Ctx n}
    {targetDomainType : LambdaPFC.Ty n}
    {targetCodomainType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig} {finalContext : Ctx final}
    {sourceDomain targetDomain : Shape sig}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    (formation : Formation (targetContext.snoc targetDomainType)
      (targetDomain.context base) targetCodomainType targetCodomain)
    (next : Rename
      (FunctionSubtyping.observedDomain sourceDomain sourceCodomain
        targetDomain).scope final)
    (nextTyped : Rename.Typed
      ((FunctionSubtyping.observedDomain sourceDomain sourceCodomain
        targetDomain).context
          (FunctionSubtyping.exactContext base sourceDomain sourceCodomain))
      finalContext next) :
    Formation (targetContext.snoc targetDomainType) finalContext
      targetCodomainType
      (FunctionSubtyping.targetCodomainAt sourceDomain targetDomain
        sourceCodomain targetCodomain next) := by
  let packageMap := FunctionSubtyping.packageMapping sig
  let packageMapTyped := packageTyped base sourceDomain sourceCodomain
  let targetPackage := targetDomain.rename packageMap
  let observationMap := FunctionSubtyping.observationMapping sourceDomain
    sourceCodomain
  let observationMapTyped := observationTyped base sourceDomain
    sourceCodomain
  let targetObserved := targetPackage.rename observationMap
  let identityMap := FunctionSubtyping.identityMapping sourceDomain
    sourceCodomain
  let identityMapTyped := identityTyped base sourceDomain sourceCodomain
  let atPackage := formation.targetRename
    (targetDomain.liftRename packageMap)
    (targetDomain.liftRename_typed packageMapTyped)
  let atObservation := atPackage.targetRename
    (targetPackage.liftRename observationMap)
    (targetPackage.liftRename_typed observationMapTyped)
  let atIdentity := atObservation.targetRename
    (targetObserved.liftRename identityMap)
    (targetObserved.liftRename_typed identityMapTyped)
  exact atIdentity.targetRename next nextTyped

/-- Literal codomain recursion at the one exact continuation constructed by
the reversed domain interface map. -/
structure CodomainCompiler
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceDomain targetDomain : Shape sig}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    {rootScope : Scope sourceContext targetContext .target base}
    {domainDerivation : LambdaPFC.Tau.Sub targetContext
      (.ty targetDomainType) (.ty sourceDomainType)}
    (domain : DomainCut rootScope domainDerivation sourceDomain targetDomain)
    (sourceCodomainFormation : Formation
      (sourceContext.snoc sourceDomainType) (sourceDomain.context base)
      sourceCodomainType sourceCodomain)
    (targetCodomainFormation : Formation
      (targetContext.snoc targetDomainType) (targetDomain.context base)
      targetCodomainType targetCodomain)
    (_derivation : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)) : Type where
  compile : {final : Sig} -> {finalContext : Ctx final} ->
    (next : Rename
      (FunctionSubtyping.observedDomain sourceDomain sourceCodomain
        targetDomain).scope final) ->
    (nextTyped : Rename.Typed
      ((FunctionSubtyping.observedDomain sourceDomain sourceCodomain
        targetDomain).context
          (FunctionSubtyping.exactContext base sourceDomain sourceCodomain))
      finalContext next) ->
    (sourceInterface : Shape.Interface finalContext
      (FunctionSubtyping.sourceDomainAt sourceDomain targetDomain
        sourceCodomain next)) ->
    (targetInterface : Shape.Interface finalContext
      (FunctionSubtyping.targetDomainAt sourceDomain targetDomain
        sourceCodomain next)) ->
    CutView
      (codomainScopeAt domain next nextTyped sourceInterface targetInterface)
      _derivation
      (FunctionSubtyping.sourceCodomainAt sourceDomain targetDomain
        sourceCodomain next sourceInterface)
      (FunctionSubtyping.targetCodomainAt sourceDomain targetDomain
        sourceCodomain targetCodomain next)

private noncomputable def codomainAdapter
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceDomain targetDomain : Shape sig}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    {rootScope : Scope sourceContext targetContext .target base}
    {domainDerivation : LambdaPFC.Tau.Sub targetContext
      (.ty targetDomainType) (.ty sourceDomainType)}
    (domain : DomainCut rootScope domainDerivation sourceDomain targetDomain)
    (sourceCodomainFormation : Formation
      (sourceContext.snoc sourceDomainType) (sourceDomain.context base)
      sourceCodomainType sourceCodomain)
    (targetCodomainFormation : Formation
      (targetContext.snoc targetDomainType) (targetDomain.context base)
      targetCodomainType targetCodomain)
    {codomainDerivation : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)}
    (compiler : CodomainCompiler domain sourceCodomainFormation
      targetCodomainFormation codomainDerivation) :
    FunctionSubtyping.ExactCodomainCompiler
      (sourceContext := sourceContext)
      (targetContext := targetContext)
      (sourceDomainType := sourceDomainType)
      (targetDomainType := targetDomainType)
      (sourceCodomainType := sourceCodomainType)
      (targetCodomainType := targetCodomainType)
      (rootContext := base)
      (sourceDomain := sourceDomain)
      (targetDomain := targetDomain)
      (sourceCodomain := sourceCodomain)
      (targetCodomain := targetCodomain)
      codomainDerivation := by
  refine { compile := ?_ }
  intro final finalContext next nextTyped sourceInterface targetInterface
  exact (compiler.compile next nextTyped sourceInterface targetInterface).relation

/-- Compile one literal dependent-function subtyping rule under a sealed
target-oriented contextual alignment. -/
noncomputable def compile
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    {sourceDomain targetDomain : Shape sig}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    {scope : Scope sourceContext targetContext .target base}
    {domainDerivation : LambdaPFC.Tau.Sub targetContext
      (.ty targetDomainType) (.ty sourceDomainType)}
    (domain : DomainCut scope domainDerivation sourceDomain targetDomain)
    (sourceCodomainFormation : Formation
      (sourceContext.snoc sourceDomainType) (sourceDomain.context base)
      sourceCodomainType sourceCodomain)
    (targetCodomainFormation : Formation
      (targetContext.snoc targetDomainType) (targetDomain.context base)
      targetCodomainType targetCodomain)
    {codomainDerivation : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)}
    (codomain : CodomainCompiler domain sourceCodomainFormation
      targetCodomainFormation codomainDerivation) :
    CutView scope (.fun domainDerivation codomainDerivation)
      (.stable (Function.plan sourceDomain sourceCodomain))
      (.stable (Function.plan targetDomain targetCodomain)) :=
  let domainCompilation : FunctionSubtyping.DomainCompilation base
      domainDerivation targetDomain sourceDomain := {
    relation := domain.relation
  }
  let recursive := codomainAdapter domain sourceCodomainFormation
    targetCodomainFormation codomain
  let relation := FunctionSubtyping.compileExact domainCompilation
    sourceCodomainFormation.rep targetCodomainFormation.rep recursive
  CutView.ofRelation
    (.function domain.sourceFormation sourceCodomainFormation)
    (.function domain.targetFormation targetCodomainFormation)
    relation

end LambdaPToFCo.Direct.Internal.SubtypingFunction
