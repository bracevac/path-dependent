import LambdaPToFCo.Direct.Relation

/-!
# Direct dependent-function subtyping

This module implements the source `Tau.Sub.fun` rule as an ordinary
`SystemFCo` package transformation.  It opens the source function package,
keeps its actual hidden identity and payload, and replaces only the retained
`identity -> code` observation.  The replacement code maps a target-domain
interface contravariantly, invokes the source code, and maps the resulting
codomain interface covariantly before reclosing it.

The only higher-order boundary is `CodomainCompiler`.  It is indexed by the
literal codomain premise of `Tau.Sub.fun`; the recursive dispatcher supplies
it, and it may return a relation only for the exact two member views assembled
by `Relation.runFunctionMembers`.  It is not emitted target evidence.
-/

namespace LambdaPToFCo.Direct.Internal.FunctionSubtyping

open SystemFCo
open Representation

/-- Derivation-directed recursive compilation of the function codomain.

The codomain premise is checked in the target-domain source context, exactly
as prescribed by `LambdaPFC.Tau.Sub.fun`.  Both endpoint interfaces have been
placed in one future target scope before this compiler is invoked. -/
structure CodomainCompiler
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    (_derivation : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)) : Type where
  compile : {sig : Sig} -> {base : Ctx sig} ->
    (scope : MemberScope sourceContext targetContext
      sourceDomainType targetDomainType sourceCodomainType
      targetCodomainType base) ->
    Relation base sourceCodomainType targetCodomainType
      scope.source.memberShape scope.target.memberShape

/-! The compact `MemberScope` above is sufficient for the target-only
transformer, but deliberately forgets how its two domain interfaces were
obtained.  A formation-aware recursive compiler needs those exact interfaces
and renamings in order to extend a sealed contextual scope.  The following
shape functions and compiler boundary retain just that information. -/

def packageMapping (sig : Sig) : Rename sig (sig ,, .var) :=
  Rename.weaken .var

def observationMapping (sourceDomain : Shape sig)
    (sourceCodomain : Shape sourceDomain.scope) :
    Rename (sig ,, .var)
      (Stable.sourceAtBinder
        (Function.plan sourceDomain sourceCodomain)).scope :=
  (Stable.sourceAtBinder
    (Function.plan sourceDomain sourceCodomain)).telescope.weaken

def identityMapping (sourceDomain : Shape sig)
    (sourceCodomain : Shape sourceDomain.scope) :
    Rename
      (Stable.sourceAtBinder
        (Function.plan sourceDomain sourceCodomain)).scope
      ((Stable.sourceAtBinder
        (Function.plan sourceDomain sourceCodomain)).scope ,, .var) :=
  Rename.weaken .var

def exactContext (base : Ctx sig) (sourceDomain : Shape sig)
    (sourceCodomain : Shape sourceDomain.scope) :
    Ctx ((Stable.sourceAtBinder
      (Function.plan sourceDomain sourceCodomain)).scope ,, .var) :=
  (Stable.openedContext base
    (Function.plan sourceDomain sourceCodomain)).bindVar
      (Stable.sourceAtBinder
        (Function.plan sourceDomain sourceCodomain)).identityTy

def observedDomain (sourceDomain : Shape sig)
    (sourceCodomain : Shape sourceDomain.scope)
    (domain : Shape sig) :
    Shape ((Stable.sourceAtBinder
      (Function.plan sourceDomain sourceCodomain)).scope ,, .var) :=
  (((domain.rename (packageMapping sig)).rename
    (observationMapping sourceDomain sourceCodomain)).rename
      (identityMapping sourceDomain sourceCodomain))

def observedCodomain (sourceDomain : Shape sig)
    (sourceCodomain : Shape sourceDomain.scope)
    (domain : Shape sig) (codomain : Shape domain.scope) :
    Shape (observedDomain sourceDomain sourceCodomain domain).scope :=
  let packageDomain := domain.rename (packageMapping sig)
  let packageCodomain := Function.renameCodomain domain codomain
    (packageMapping sig)
  let openedDomain := packageDomain.rename
    (observationMapping sourceDomain sourceCodomain)
  let openedCodomain := Function.renameCodomain packageDomain packageCodomain
    (observationMapping sourceDomain sourceCodomain)
  Function.renameCodomain openedDomain openedCodomain
    (identityMapping sourceDomain sourceCodomain)

/-- Source domain shape in the continuation selected by the reversed domain
interface map. -/
def sourceDomainAt
    (sourceDomain targetDomain : Shape root)
    (sourceCodomain : Shape sourceDomain.scope)
    (next : Rename
      (observedDomain sourceDomain sourceCodomain
        targetDomain).scope final) : Shape final :=
  (((observedDomain sourceDomain sourceCodomain sourceDomain).rename
    (observedDomain sourceDomain sourceCodomain
      targetDomain).binders.weaken).rename next)

/-- Target domain shape in the same continuation. -/
def targetDomainAt
    (sourceDomain targetDomain : Shape root)
    (sourceCodomain : Shape sourceDomain.scope)
    (next : Rename
      (observedDomain sourceDomain sourceCodomain
        targetDomain).scope final) : Shape final :=
  (((observedDomain sourceDomain sourceCodomain targetDomain).rename
    (observedDomain sourceDomain sourceCodomain
      targetDomain).binders.weaken).rename next)

/-- Source codomain shape after the mapped source interface has instantiated
its dependency. -/
def sourceCodomainAt
    (sourceDomain targetDomain : Shape root)
    (sourceCodomain : Shape sourceDomain.scope)
    (next : Rename
      (observedDomain sourceDomain sourceCodomain
        targetDomain).scope final)
    {finalContext : Ctx final}
    (sourceInterface : Shape.Interface finalContext
      (sourceDomainAt sourceDomain targetDomain sourceCodomain next)) :
    Shape final :=
  let sourceObserved := observedDomain sourceDomain sourceCodomain sourceDomain
  let sourceCodomainObserved := observedCodomain sourceDomain sourceCodomain
    sourceDomain sourceCodomain
  let opening := (observedDomain sourceDomain sourceCodomain
    targetDomain).binders.weaken
  let sourceOpened := sourceObserved.rename opening
  let sourceCodomainOpened := Function.renameCodomain sourceObserved
    sourceCodomainObserved opening
  (Function.renameCodomain sourceOpened sourceCodomainOpened next).subst
    sourceInterface.substitution

/-- Target codomain shape retained under the literally opened target-domain
telescope. -/
def targetCodomainAt
    (sourceDomain targetDomain : Shape root)
    (sourceCodomain : Shape sourceDomain.scope)
    (targetCodomain : Shape targetDomain.scope)
    (next : Rename
      (observedDomain sourceDomain sourceCodomain
        targetDomain).scope final) : Shape final :=
  (observedCodomain sourceDomain sourceCodomain targetDomain
    targetCodomain).rename next

/-- Exact, derivation-indexed codomain recursion for the formation-aware
function rule.

The deterministic observation helpers above record all target binders opened
while observing the source function package. `next` is chosen by the
reversed-domain interface map.
Consequently both supplied interfaces are the actual runtime interfaces in
one target context, not independently reconstructed packages. -/
structure ExactCodomainCompiler
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {root : Sig} {rootContext : Ctx root}
    {sourceDomain targetDomain : Shape root}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    (_derivation : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)) : Type where
  compile : {final : Sig} -> {finalContext : Ctx final} ->
    (next : Rename
      (observedDomain sourceDomain sourceCodomain
        targetDomain).scope final) ->
    (nextTyped : Rename.Typed
      ((observedDomain sourceDomain sourceCodomain
        targetDomain).context
          (exactContext rootContext sourceDomain sourceCodomain))
      finalContext next) ->
    (sourceInterface : Shape.Interface finalContext
      (sourceDomainAt sourceDomain targetDomain sourceCodomain next)) ->
    (targetInterface : Shape.Interface finalContext
      (targetDomainAt sourceDomain targetDomain sourceCodomain next)) ->
    Relation finalContext sourceCodomainType targetCodomainType
      (sourceCodomainAt sourceDomain targetDomain sourceCodomain next
        sourceInterface)
      (targetCodomainAt sourceDomain targetDomain sourceCodomain
        targetCodomain next)

/-- Function-specific continuation that retains the statically known source
domain shape.  `MemberScope` intentionally stays compact; the exact interface
needed to apply executable source code is supplied separately here. -/
private abbrev ExactDomainConsumer
    {origin : Sig} (base : Ctx origin) (sourceDomain : Shape origin)
    (answer : Ty origin) : Type :=
  {final : Sig} -> (mapping : Rename origin final) ->
    (finalContext : Ctx final) ->
    (typed : Rename.Typed base finalContext mapping) ->
    Shape.Interface finalContext (sourceDomain.rename mapping) ->
    Path.Body finalContext (answer.rename mapping)

private noncomputable def exactDomainContinuation
    {base : Ctx origin} {sourceDomain : Shape origin}
    (answer : Ty origin)
    (consumer : ExactDomainConsumer base sourceDomain answer) :
    InterfaceMap.Continuation base sourceDomain answer where
  body mapping finalContext typed sourceInterface :=
    (consumer mapping finalContext typed sourceInterface).expression
  body_hasType mapping finalContext typed sourceInterface :=
    (consumer mapping finalContext typed sourceInterface).typing

/-- Run the same reversed-domain interface map as `runFunctionMembers`, while
retaining the exact source interface type needed by executable code. -/
private noncomputable def runExactDomain
    {base : Ctx origin} {targetDomain sourceDomain : Shape origin}
    (targetInterface : Shape.Interface base targetDomain)
    (domainRelation : InterfaceMap base targetDomain sourceDomain)
    (answer : Ty origin)
    (consumer : ExactDomainConsumer base sourceDomain answer) :
    Path.Body base answer where
  expression := domainRelation.run targetInterface answer
    (exactDomainContinuation answer consumer)
  typing := domainRelation.run_hasType targetInterface answer
    (exactDomainContinuation answer consumer)

/-- Exact member scope used while constructing target function code.

The target-domain telescope is the telescope currently being abstracted by
the target code itself.  Its codomain representation therefore already lives
in `base`; reopening a renamed copy would create an unnecessary duplicate
domain scope.  Only the mapped source domain must be opened and substituted. -/
private noncomputable def makeExactMemberScope
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx origin} {finalContext : Ctx final}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape origin}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape origin}
    (environments : EndpointEnvs sourceContext targetContext base)
    (sourceDomainRep : Rep base sourceDomainType sourceDomain)
    (targetDomainRep : Rep base targetDomainType targetDomain)
    (sourceCodomainRep : Rep (sourceDomain.context base)
      sourceCodomainType sourceCodomain)
    (targetCodomainRep : Rep base targetCodomainType targetCodomain)
    (targetInterface : Shape.Interface base targetDomain)
    (mapping : Rename origin final)
    (typed : Rename.Typed base finalContext mapping)
    (sourceInterface : Shape.Interface finalContext
      (sourceDomain.rename mapping)) :
    MemberScope sourceContext targetContext sourceDomainType targetDomainType
      sourceCodomainType targetCodomainType finalContext :=
  let sourceDomainRepAt := sourceDomainRep.targetRename mapping typed
  let sourceCodomainRepAt := sourceCodomainRep.targetRename
    (sourceDomain.liftRename mapping)
    (sourceDomain.liftRename_typed typed)
  let sourceMemberRep := sourceCodomainRepAt.targetSubst
    sourceInterface.substitution
    sourceInterface.arguments.substitution_typed
  let targetEnvironment := extendAtInterface environments.target
    targetDomainType targetInterface targetDomainRep
  {
    source := {
      environment := extendAtInterface
        (environments.source.targetRename mapping typed)
        sourceDomainType sourceInterface sourceDomainRepAt
      memberShape :=
        (sourceCodomain.rename (sourceDomain.liftRename mapping)).subst
          sourceInterface.substitution
      memberRep := sourceMemberRep
    }
    target := {
      environment := targetEnvironment.targetRename mapping typed
      memberShape := targetCodomain.rename mapping
      memberRep := targetCodomainRep.targetRename mapping typed
    }
  }

private noncomputable def transformCode
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape sig}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (domainRelation : Relation base targetDomainType sourceDomainType
      targetDomain sourceDomain)
    (sourceCodomainRep : Rep (sourceDomain.context base)
      sourceCodomainType sourceCodomain)
    (targetCodomainRep : Rep (targetDomain.context base)
      targetCodomainType targetCodomain)
    {derivation : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)}
    (compiler : CodomainCompiler
      (sourceContext := sourceContext)
      (targetContext := targetContext)
      (sourceDomainType := sourceDomainType)
      (targetDomainType := targetDomainType)
      (sourceCodomainType := sourceCodomainType)
      (targetCodomainType := targetCodomainType)
      derivation)
    (sourceCode : Exp sig)
    (sourceCodeTyping : Exp.HasType base sourceCode
      (Function.codeTy sourceDomain sourceCodomain)) :
    Path.Body base (Function.codeTy targetDomain targetCodomain) := by
  let mapping := targetDomain.binders.weaken
  let typed := targetDomain.binders.weaken_typed base
  let currentContext := targetDomain.context base
  let environmentsAt := environments.targetRename mapping typed
  let domainRelationAt := domainRelation.targetRename mapping typed
  let sourceCodomainRepAt := sourceCodomainRep.targetRename
    (sourceDomain.liftRename mapping)
    (sourceDomain.liftRename_typed typed)
  let targetInterface := Shape.Interface.canonical base targetDomain
  let sourceCodeAt := sourceCode.rename mapping
  have sourceCodeAtTyping : Exp.HasType currentContext sourceCodeAt
      (Function.codeTy (sourceDomain.rename mapping)
        (Function.renameCodomain sourceDomain sourceCodomain mapping)) := by
    simpa only [Function.codeTy_rename] using
      sourceCodeTyping.rename typed
  let body := runExactDomain targetInterface domainRelationAt.interfaceMap
    targetCodomain.inputTy
    (fun next finalContext nextTyped sourceInterface => by
      let scope := makeExactMemberScope environmentsAt
        domainRelationAt.targetRep domainRelationAt.sourceRep
        sourceCodomainRepAt targetCodomainRep targetInterface
        next nextTyped sourceInterface
      let codomainRelation := compiler.compile scope
      let codeAt := sourceCodeAt.rename next
      have codeAtTyping : Exp.HasType finalContext codeAt
          (Function.codeTy
            ((sourceDomain.rename mapping).rename next)
            (Function.renameCodomain (sourceDomain.rename mapping)
              (Function.renameCodomain sourceDomain sourceCodomain mapping)
              next)) := by
        simpa only [Function.codeTy_rename] using
          sourceCodeAtTyping.rename nextTyped
      let sourceResult := sourceInterface.arguments.apply codeAt
      have sourceResultTyping : Exp.HasType finalContext sourceResult
          scope.source.memberShape.inputTy := by
        have applied := sourceInterface.arguments.apply_hasType codeAtTyping
        rw [Telescope.Args.instantiate_eq_subst] at applied
        change Exp.HasType finalContext sourceResult
          ((Function.renameCodomain (sourceDomain.rename mapping)
            (Function.renameCodomain sourceDomain sourceCodomain mapping)
            next).subst sourceInterface.substitution).inputTy
        rw [← Shape.inputTy_subst]
        exact applied
      let targetResult := Adapter.apply
        codomainRelation.conversion.function sourceResult
      have targetResultTyping : Exp.HasType finalContext targetResult
          (targetCodomain.inputTy.rename next) := by
        have raw := Adapter.apply_hasType
          codomainRelation.conversion.functionTyping sourceResultTyping
        change Exp.HasType finalContext targetResult
          (targetCodomain.rename next).inputTy at raw
        simpa only [Shape.inputTy_rename] using raw
      exact { expression := targetResult, typing := targetResultTyping })
  exact {
    expression := targetDomain.binders.lambda body.expression
    typing := targetDomain.binders.lambda_hasType body.typing
  }

/-- Formation-aware variant of `transformCode`.  It reports both typed
renaming stages and both exact domain interfaces to the recursive compiler;
the target program is otherwise the same ordinary function transformation. -/
private noncomputable def transformCodeExact
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape sig}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    (domainRelation : Relation base targetDomainType sourceDomainType
      targetDomain sourceDomain)
    {derivation : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)}
    (compiler : ExactCodomainCompiler
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
      derivation)
    (sourceCode : Exp
      ((Stable.sourceAtBinder
        (Function.plan sourceDomain sourceCodomain)).scope ,, .var))
    (sourceCodeTyping : Exp.HasType
      (exactContext base sourceDomain sourceCodomain) sourceCode
      (Function.codeTy
        (observedDomain sourceDomain sourceCodomain sourceDomain)
        (observedCodomain sourceDomain sourceCodomain sourceDomain
          sourceCodomain))) :
    Path.Body (exactContext base sourceDomain sourceCodomain)
      (Function.codeTy
        (observedDomain sourceDomain sourceCodomain targetDomain)
        (observedCodomain sourceDomain sourceCodomain targetDomain
          targetCodomain)) := by
  let sourcePlan := Function.plan sourceDomain sourceCodomain
  let sourceAt := Stable.sourceAtBinder sourcePlan
  let packageContext := base.bindVar sourcePlan.inputTy
  let packageTyped := Rename.Typed.weaken base (.var sourcePlan.inputTy)
  let observationTyped := sourceAt.telescope.weaken_typed packageContext
  let openContext := Stable.openedContext base sourcePlan
  let identity := sourceAt.identityTy
  let identityTyped := Rename.Typed.weaken openContext (.var identity)
  let currentContext := exactContext base sourceDomain sourceCodomain
  let sourceDomainCurrent := observedDomain sourceDomain sourceCodomain
    sourceDomain
  let targetDomainCurrent := observedDomain sourceDomain sourceCodomain
    targetDomain
  let sourceCodomainCurrent := observedCodomain sourceDomain sourceCodomain
    sourceDomain sourceCodomain
  let targetCodomainCurrent := observedCodomain sourceDomain sourceCodomain
    targetDomain targetCodomain
  let opening := targetDomainCurrent.binders.weaken
  let openingTyped := targetDomainCurrent.binders.weaken_typed currentContext
  let openedContext := targetDomainCurrent.context currentContext
  let domainPackage := domainRelation.targetRename (packageMapping sig)
    packageTyped
  let domainObservation := domainPackage.targetRename
    (observationMapping sourceDomain sourceCodomain) observationTyped
  let domainCurrent := domainObservation.targetRename
    (identityMapping sourceDomain sourceCodomain) identityTyped
  let domainOpened := domainCurrent.targetRename opening openingTyped
  let targetInterface := Shape.Interface.canonical currentContext
    targetDomainCurrent
  let sourceCodeOpened := sourceCode.rename opening
  have sourceCodeOpenedTyping : Exp.HasType openedContext sourceCodeOpened
      (Function.codeTy (sourceDomainCurrent.rename opening)
        (Function.renameCodomain sourceDomainCurrent sourceCodomainCurrent
          opening)) := by
    simpa only [Function.codeTy_rename] using
      sourceCodeTyping.rename openingTyped
  let body := runExactDomain targetInterface domainOpened.interfaceMap
    targetCodomainCurrent.inputTy
    (fun next finalContext nextTyped sourceInterface => by
      let targetInterfaceAt := targetInterface.rename next nextTyped
      let codomainRelation := compiler.compile next nextTyped
        sourceInterface targetInterfaceAt
      let codeAt := sourceCodeOpened.rename next
      have codeAtTyping : Exp.HasType finalContext codeAt
          (Function.codeTy
            ((sourceDomainCurrent.rename opening).rename next)
            (Function.renameCodomain (sourceDomainCurrent.rename opening)
              (Function.renameCodomain sourceDomainCurrent
                sourceCodomainCurrent opening) next)) := by
        simpa only [Function.codeTy_rename] using
          sourceCodeOpenedTyping.rename nextTyped
      let sourceResult := sourceInterface.arguments.apply codeAt
      have sourceResultTyping : Exp.HasType finalContext sourceResult
          (sourceCodomainAt sourceDomain targetDomain sourceCodomain next
            sourceInterface).inputTy := by
        have applied := sourceInterface.arguments.apply_hasType codeAtTyping
        rw [Telescope.Args.instantiate_eq_subst] at applied
        change Exp.HasType finalContext sourceResult
          ((Function.renameCodomain (sourceDomainCurrent.rename opening)
            (Function.renameCodomain sourceDomainCurrent
              sourceCodomainCurrent
              opening) next).subst sourceInterface.substitution).inputTy
        rw [← Shape.inputTy_subst]
        exact applied
      let targetResult := Adapter.apply
        codomainRelation.conversion.function sourceResult
      have targetResultTyping : Exp.HasType finalContext targetResult
          ((targetCodomainCurrent.rename next).inputTy) := by
        have raw := Adapter.apply_hasType
          codomainRelation.conversion.functionTyping sourceResultTyping
        exact raw
      exact {
        expression := targetResult
        typing := by
          simpa only [Shape.inputTy_rename] using targetResultTyping
      })
  exact {
    expression := targetDomainCurrent.binders.lambda body.expression
    typing := targetDomainCurrent.binders.lambda_hasType body.typing
  }

private noncomputable def openedToCode
    (base : Ctx sig)
    (sourceDomain : Shape sig)
    (sourceCodomain : Shape sourceDomain.scope) :
    Path.Body
      (Stable.openedContext base
        (Function.plan sourceDomain sourceCodomain))
      (.arrow
        (Stable.sourceAtBinder
          (Function.plan sourceDomain sourceCodomain)).identityTy
        (Function.finalCodeTy
          (sourceDomain.rename (Rename.weaken .var))
          (Function.renameCodomain sourceDomain sourceCodomain
            (Rename.weaken .var)))) := by
  let sourcePlan := Function.plan sourceDomain sourceCodomain
  let mapping : Rename sourcePlan.scope
      (Stable.sourceAtBinder sourcePlan).scope :=
    sourcePlan.telescope.liftRename (Rename.weaken .var)
  let typed : Rename.Typed (sourcePlan.context base)
      (Stable.openedContext base sourcePlan) mapping :=
    sourcePlan.telescope.liftRename_typed
      (Rename.Typed.weaken base (.var sourcePlan.inputTy))
  let expression := (Function.toCode sourceDomain sourceCodomain).rename mapping
  have typing :=
    (Function.toCode_hasType base sourceDomain sourceCodomain).rename typed
  exact {
    expression := expression
    typing := by
      change Exp.HasType (Stable.openedContext base sourcePlan) expression
        (.arrow (sourcePlan.identityTy.rename mapping)
          ((Function.finalCodeTy sourceDomain sourceCodomain).rename mapping))
        at typing
      dsimp only [mapping] at typing
      have identityEq := sourcePlan.identityTy_rename
        (Rename.weaken .var)
      have codeEq := Function.finalCodeTy_rename sourceDomain sourceCodomain
        (Rename.weaken .var)
      have typeEq :
          (Ty.arrow
            (sourcePlan.identityTy.rename
              (sourcePlan.telescope.liftRename (Rename.weaken .var)))
            ((Function.finalCodeTy sourceDomain sourceCodomain).rename
              (sourcePlan.telescope.liftRename (Rename.weaken .var)))) =
          (Ty.arrow
            (Stable.sourceAtBinder sourcePlan).identityTy
            (Function.finalCodeTy
              (sourceDomain.rename (Rename.weaken .var))
              (Function.renameCodomain sourceDomain sourceCodomain
                (Rename.weaken .var)))) := by
        rw [identityEq, codeEq]
        rfl
      exact typeEq ▸ typing
  }

private noncomputable def transformObservation
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape sig}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (domainRelation : Relation base targetDomainType sourceDomainType
      targetDomain sourceDomain)
    (sourceCodomainRep : Rep (sourceDomain.context base)
      sourceCodomainType sourceCodomain)
    (targetCodomainRep : Rep (targetDomain.context base)
      targetCodomainType targetCodomain)
    {derivation : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)}
    (compiler : CodomainCompiler
      (sourceContext := sourceContext)
      (targetContext := targetContext)
      (sourceDomainType := sourceDomainType)
      (targetDomainType := targetDomainType)
      (sourceCodomainType := sourceCodomainType)
      (targetCodomainType := targetCodomainType)
      derivation) :
    let sourcePlan := Function.plan sourceDomain sourceCodomain
    let openContext := Stable.openedContext base sourcePlan
    let outerMapping : Rename sig (sig ,, .var) := Rename.weaken .var
    let targetDomainOuter := targetDomain.rename outerMapping
    let targetCodomainOuter := Function.renameCodomain targetDomain
      targetCodomain outerMapping
    let openMapping := (Stable.sourceAtBinder sourcePlan).telescope.weaken
    let targetDomainOpen := targetDomainOuter.rename openMapping
    let targetCodomainOpen := Function.renameCodomain targetDomainOuter
      targetCodomainOuter openMapping
    Path.Body openContext
      (.arrow (Stable.sourceAtBinder sourcePlan).identityTy
        (Function.codeTy targetDomainOpen targetCodomainOpen)) := by
  let sourcePlan := Function.plan sourceDomain sourceCodomain
  let sourceAt := Stable.sourceAtBinder sourcePlan
  let outerContext := base.bindVar sourcePlan.inputTy
  let outerMapping : Rename sig (sig ,, .var) := Rename.weaken .var
  let outerTyped := Rename.Typed.weaken base (.var sourcePlan.inputTy)
  let sourceDomainOuter := sourceDomain.rename outerMapping
  let sourceCodomainOuter := Function.renameCodomain sourceDomain
    sourceCodomain outerMapping
  let targetDomainOuter := targetDomain.rename outerMapping
  let targetCodomainOuter := Function.renameCodomain targetDomain
    targetCodomain outerMapping
  let openContext := Stable.openedContext base sourcePlan
  let openMapping := sourceAt.telescope.weaken
  let openTyped := sourceAt.telescope.weaken_typed outerContext
  let sourceDomainOpen := sourceDomainOuter.rename openMapping
  let sourceCodomainOpen := Function.renameCodomain sourceDomainOuter
    sourceCodomainOuter openMapping
  let targetDomainOpen := targetDomainOuter.rename openMapping
  let targetCodomainOpen := Function.renameCodomain targetDomainOuter
    targetCodomainOuter openMapping
  let identity := sourceAt.identityTy
  let underIdentity := openContext.bindVar identity
  let identityMapping : Rename sourceAt.scope (sourceAt.scope ,, .var) :=
    Rename.weaken .var
  let identityTyped := Rename.Typed.weaken openContext (.var identity)
  let environmentsOuter := environments.targetRename outerMapping outerTyped
  let environmentsOpen := environmentsOuter.targetRename openMapping openTyped
  let environmentsUnder := environmentsOpen.targetRename
    identityMapping identityTyped
  let domainOuter := domainRelation.targetRename outerMapping outerTyped
  let domainOpen := domainOuter.targetRename openMapping openTyped
  let domainUnder := domainOpen.targetRename identityMapping identityTyped
  let sourceCodomainOuterRep := sourceCodomainRep.targetRename
    (sourceDomain.liftRename outerMapping)
    (sourceDomain.liftRename_typed outerTyped)
  let sourceCodomainOpenRep := sourceCodomainOuterRep.targetRename
    (sourceDomainOuter.liftRename openMapping)
    (sourceDomainOuter.liftRename_typed openTyped)
  let sourceCodomainUnderRep := sourceCodomainOpenRep.targetRename
    (sourceDomainOpen.liftRename identityMapping)
    (sourceDomainOpen.liftRename_typed identityTyped)
  let targetCodomainOuterRep := targetCodomainRep.targetRename
    (targetDomain.liftRename outerMapping)
    (targetDomain.liftRename_typed outerTyped)
  let targetCodomainOpenRep := targetCodomainOuterRep.targetRename
    (targetDomainOuter.liftRename openMapping)
    (targetDomainOuter.liftRename_typed openTyped)
  let targetCodomainUnderRep := targetCodomainOpenRep.targetRename
    (targetDomainOpen.liftRename identityMapping)
    (targetDomainOpen.liftRename_typed identityTyped)
  have openMappingEq :
      (Function.plan sourceDomainOuter sourceCodomainOuter).telescope.weaken =
        openMapping := by
    rfl
  let opened := openedToCode base sourceDomain sourceCodomain
  let sourceCode := Adapter.apply (opened.expression.weaken .var) (.var .here)
  have sourceCodeTyping : Exp.HasType underIdentity sourceCode
      (Function.codeTy
        (sourceDomainOpen.rename identityMapping)
        (Function.renameCodomain sourceDomainOpen sourceCodomainOpen
          identityMapping)) := by
    have raw := Adapter.apply_hasType
      (opened.typing.weaken (.var identity))
      (Exp.HasType.var (context := underIdentity) Ctx.Lookup.here)
    have openCodeEq :
        Function.finalCodeTy sourceDomainOuter sourceCodomainOuter =
          Function.codeTy sourceDomainOpen sourceCodomainOpen := by
      unfold Function.finalCodeTy
      rw [openMappingEq]
      exact Function.codeTy_rename sourceDomainOuter sourceCodomainOuter
        openMapping
    have underCodeEq :
        (Function.finalCodeTy sourceDomainOuter sourceCodomainOuter).rename
          identityMapping =
        Function.codeTy (sourceDomainOpen.rename identityMapping)
          (Function.renameCodomain sourceDomainOpen sourceCodomainOpen
            identityMapping) := by
      rw [openCodeEq]
      exact Function.codeTy_rename sourceDomainOpen sourceCodomainOpen
        identityMapping
    exact underCodeEq ▸ raw
  let transformed := transformCode environmentsUnder domainUnder
    sourceCodomainUnderRep targetCodomainUnderRep compiler
    sourceCode sourceCodeTyping
  exact {
    expression := Adapter.ofBody identity transformed.expression
    typing := by
      apply Adapter.ofBody_hasType
      simpa only [Function.codeTy_rename, Ty.weaken] using transformed.typing
  }

private noncomputable def functionAdapter
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape sig}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (domainRelation : Relation base targetDomainType sourceDomainType
      targetDomain sourceDomain)
    (sourceCodomainRep : Rep (sourceDomain.context base)
      sourceCodomainType sourceCodomain)
    (targetCodomainRep : Rep (targetDomain.context base)
      targetCodomainType targetCodomain)
    {derivation : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)}
    (compiler : CodomainCompiler
      (sourceContext := sourceContext)
      (targetContext := targetContext)
      (sourceDomainType := sourceDomainType)
      (targetDomainType := targetDomainType)
      (sourceCodomainType := sourceCodomainType)
      (targetCodomainType := targetCodomainType)
      derivation) :
    Stable.Adapter base
      (Function.plan sourceDomain sourceCodomain)
      (Function.plan targetDomain targetCodomain) := by
  apply Stable.Adapter.ofRepack
  let observation := transformObservation environments domainRelation
    sourceCodomainRep targetCodomainRep compiler
  refine { observations := .var observation.expression ?_ .nil }
  simpa only [Stable.observationTelescope, Stable.targetAtSource,
    Function.plan_rename, Function.toCodeField_rename,
    Function.toCodeField_open] using observation.typing

/-- Exact observation transformer used by the formation-aware structural
layer.  The single `outer` renaming passed to recursive codomain compilation
is the composition of the source package, observation, and identity openings. -/
private noncomputable def transformObservationExact
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape sig}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    (domainRelation : Relation base targetDomainType sourceDomainType
      targetDomain sourceDomain)
    {derivation : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)}
    (compiler : ExactCodomainCompiler
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
      derivation) :
    let sourcePlan := Function.plan sourceDomain sourceCodomain
    let openContext := Stable.openedContext base sourcePlan
    let packageMapping : Rename sig (sig ,, .var) := Rename.weaken .var
    let targetDomainOuter := targetDomain.rename packageMapping
    let targetCodomainOuter := Function.renameCodomain targetDomain
      targetCodomain packageMapping
    let observationMapping :=
      (Stable.sourceAtBinder sourcePlan).telescope.weaken
    let targetDomainOpen := targetDomainOuter.rename observationMapping
    let targetCodomainOpen := Function.renameCodomain targetDomainOuter
      targetCodomainOuter observationMapping
    Path.Body openContext
      (.arrow (Stable.sourceAtBinder sourcePlan).identityTy
        (Function.codeTy targetDomainOpen targetCodomainOpen)) := by
  let sourcePlan := Function.plan sourceDomain sourceCodomain
  let sourceAt := Stable.sourceAtBinder sourcePlan
  let packageContext := base.bindVar sourcePlan.inputTy
  let packageMapping : Rename sig (sig ,, .var) := Rename.weaken .var
  let packageTyped := Rename.Typed.weaken base (.var sourcePlan.inputTy)
  let sourceDomainOuter := sourceDomain.rename packageMapping
  let sourceCodomainOuter := Function.renameCodomain sourceDomain
    sourceCodomain packageMapping
  let targetDomainOuter := targetDomain.rename packageMapping
  let targetCodomainOuter := Function.renameCodomain targetDomain
    targetCodomain packageMapping
  let openContext := Stable.openedContext base sourcePlan
  let observationMapping := sourceAt.telescope.weaken
  let observationTyped := sourceAt.telescope.weaken_typed packageContext
  let sourceDomainOpen := sourceDomainOuter.rename observationMapping
  let sourceCodomainOpen := Function.renameCodomain sourceDomainOuter
    sourceCodomainOuter observationMapping
  let targetDomainOpen := targetDomainOuter.rename observationMapping
  let targetCodomainOpen := Function.renameCodomain targetDomainOuter
    targetCodomainOuter observationMapping
  let identity := sourceAt.identityTy
  let underIdentity := openContext.bindVar identity
  let identityMapping : Rename sourceAt.scope (sourceAt.scope ,, .var) :=
    Rename.weaken .var
  let identityTyped := Rename.Typed.weaken openContext (.var identity)
  have openMappingEq :
      (Function.plan sourceDomainOuter sourceCodomainOuter).telescope.weaken =
        observationMapping := by
    rfl
  let opened := openedToCode base sourceDomain sourceCodomain
  let sourceCode := Adapter.apply (opened.expression.weaken .var) (.var .here)
  have sourceCodeTyping : Exp.HasType underIdentity sourceCode
      (Function.codeTy
        (sourceDomainOpen.rename identityMapping)
        (Function.renameCodomain sourceDomainOpen sourceCodomainOpen
          identityMapping)) := by
    have raw := Adapter.apply_hasType
      (opened.typing.weaken (.var identity))
      (Exp.HasType.var (context := underIdentity) Ctx.Lookup.here)
    have openCodeEq :
        Function.finalCodeTy sourceDomainOuter sourceCodomainOuter =
          Function.codeTy sourceDomainOpen sourceCodomainOpen := by
      unfold Function.finalCodeTy
      rw [openMappingEq]
      exact Function.codeTy_rename sourceDomainOuter sourceCodomainOuter
        observationMapping
    have underCodeEq :
        (Function.finalCodeTy sourceDomainOuter sourceCodomainOuter).rename
          identityMapping =
        Function.codeTy (sourceDomainOpen.rename identityMapping)
          (Function.renameCodomain sourceDomainOpen sourceCodomainOpen
            identityMapping) := by
      rw [openCodeEq]
      exact Function.codeTy_rename sourceDomainOpen sourceCodomainOpen
        identityMapping
    exact underCodeEq ▸ raw
  have sourceCodeExact : Exp.HasType underIdentity sourceCode
      (Function.codeTy
        (observedDomain sourceDomain sourceCodomain sourceDomain)
        (observedCodomain sourceDomain sourceCodomain sourceDomain
          sourceCodomain)) := by
    exact sourceCodeTyping
  let transformed := transformCodeExact domainRelation compiler sourceCode
    sourceCodeExact
  exact {
    expression := Adapter.ofBody identity transformed.expression
    typing := by
      apply Adapter.ofBody_hasType
      simpa only [observedDomain, observedCodomain, packageMapping,
        observationMapping, identityMapping, Function.codeTy_rename,
        Ty.weaken] using transformed.typing
  }

private noncomputable def functionAdapterExact
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape sig}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    (domainRelation : Relation base targetDomainType sourceDomainType
      targetDomain sourceDomain)
    {derivation : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)}
    (compiler : ExactCodomainCompiler
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
      derivation) :
    Stable.Adapter base
      (Function.plan sourceDomain sourceCodomain)
      (Function.plan targetDomain targetCodomain) := by
  apply Stable.Adapter.ofRepack
  let observation := transformObservationExact domainRelation compiler
  refine { observations := .var observation.expression ?_ .nil }
  simpa only [Stable.observationTelescope, Stable.targetAtSource,
    Function.plan_rename, Function.toCodeField_rename,
    Function.toCodeField_open] using observation.typing

/-- Compiled contravariant domain premise, indexed by the literal first
premise of `Tau.Sub.fun`.  The wrapper prevents an unrelated relation from
being passed to the function rule. -/
structure DomainCompilation
    {targetContext : LambdaPFC.Ctx n}
    {targetDomainType sourceDomainType : LambdaPFC.Ty n}
    (base : Ctx sig)
    (_derivation : LambdaPFC.Tau.Sub targetContext
      (.ty targetDomainType) (.ty sourceDomainType))
    (targetDomain sourceDomain : Shape sig) : Type where
  relation : Relation base targetDomainType sourceDomainType
    targetDomain sourceDomain

/-- Compile the literal dependent-function rule.

The two proof arguments are precisely the premises used to construct
`LambdaPFC.Tau.Sub.fun domainDerivation codomainDerivation`.  Runtime output
is only an ordinary stable-package conversion in unchanged System FCo. -/
noncomputable def compile
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape sig}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    {domainDerivation : LambdaPFC.Tau.Sub targetContext
      (.ty targetDomainType) (.ty sourceDomainType)}
    (domain : DomainCompilation base domainDerivation
      targetDomain sourceDomain)
    (sourceCodomainRep : Rep (sourceDomain.context base)
      sourceCodomainType sourceCodomain)
    (targetCodomainRep : Rep (targetDomain.context base)
      targetCodomainType targetCodomain)
    {codomainDerivation : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)}
    (codomain : CodomainCompiler
      (sourceContext := sourceContext)
      (targetContext := targetContext)
      (sourceDomainType := sourceDomainType)
      (targetDomainType := targetDomainType)
      (sourceCodomainType := sourceCodomainType)
      (targetCodomainType := targetCodomainType)
      codomainDerivation) :
    Relation base
      (.Fun sourceDomainType sourceCodomainType)
      (.Fun targetDomainType targetCodomainType)
      (.stable (Function.plan sourceDomain sourceCodomain))
      (.stable (Function.plan targetDomain targetCodomain)) :=
  let adapter := functionAdapter environments domain.relation
    sourceCodomainRep targetCodomainRep codomain
  Relation.ofConversion
    (.function domain.relation.targetRep sourceCodomainRep)
    (.function domain.relation.sourceRep targetCodomainRep)
    (Conversion.ofStableAdapter adapter)

/-- Compile the literal dependent-function rule while retaining the exact
runtime domain interfaces for formation-aware codomain recursion.  This is
the same target transformation as `compile`; only the private recursive
boundary is more precise. -/
noncomputable def compileExact
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sig}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape sig}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    {domainDerivation : LambdaPFC.Tau.Sub targetContext
      (.ty targetDomainType) (.ty sourceDomainType)}
    (domain : DomainCompilation base domainDerivation
      targetDomain sourceDomain)
    (sourceCodomainRep : Rep (sourceDomain.context base)
      sourceCodomainType sourceCodomain)
    (targetCodomainRep : Rep (targetDomain.context base)
      targetCodomainType targetCodomain)
    {codomainDerivation : LambdaPFC.Tau.Sub
      (targetContext.snoc targetDomainType)
      (.ty sourceCodomainType) (.ty targetCodomainType)}
    (codomain : ExactCodomainCompiler
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
      codomainDerivation) :
    Relation base
      (.Fun sourceDomainType sourceCodomainType)
      (.Fun targetDomainType targetCodomainType)
      (.stable (Function.plan sourceDomain sourceCodomain))
      (.stable (Function.plan targetDomain targetCodomain)) :=
  let adapter := functionAdapterExact domain.relation codomain
  Relation.ofConversion
    (.function domain.relation.targetRep sourceCodomainRep)
    (.function domain.relation.sourceRep targetCodomainRep)
    (Conversion.ofStableAdapter adapter)

end LambdaPToFCo.Direct.Internal.FunctionSubtyping
