import LambdaPToFCo.Direct.InterfaceMap
import LambdaPToFCo.Direct.Path

/-!
# Compact direct subtyping context

Subtyping recursion retains two exact source environments: the source
endpoint view and the target endpoint view.  A single side tag says which of
those environments interprets the current source proof context.  Pair-member
recursion selects the source side; function-codomain recursion selects the
target side.

The current type endpoints are represented only by `Representation.Rep`.
There is no fabricated interface for a well-formed type.  Actual interfaces
enter this kernel only inside an `InterfaceMap` continuation, where both
dependent member representations can be instantiated in one target context.
`Relation` is an internal result assembled by the rule compiler; its two
target programs are not a public evidence callback or source proof concept.
-/

namespace LambdaPToFCo.Direct.Internal

open SystemFCo
open Representation

/-- Which exact endpoint environment interprets the current source proof. -/
inductive ProofSide where
| source
| target
deriving DecidableEq

namespace ProofSide

def choose (side : ProofSide) (source target : α) : α :=
  match side with
  | .source => source
  | .target => target

@[simp] theorem choose_source (source target : α) :
    choose .source source target = source := rfl

@[simp] theorem choose_target (source target : α) :
    choose .target source target = target := rfl

end ProofSide

/-- The two exact source-variable views needed by subtyping recursion. -/
structure EndpointEnvs
    (sourceContext targetContext : LambdaPFC.Ctx n)
    (base : Ctx sig) : Type where
  source : Env sourceContext base
  target : Env targetContext base

namespace EndpointEnvs

def proofContext
    {sourceContext targetContext : LambdaPFC.Ctx n} {base : Ctx sig}
    (_environments : EndpointEnvs sourceContext targetContext base)
    (side : ProofSide) : LambdaPFC.Ctx n :=
  side.choose sourceContext targetContext

def environment
    {sourceContext targetContext : LambdaPFC.Ctx n} {base : Ctx sig}
    (environments : EndpointEnvs sourceContext targetContext base)
    (side : ProofSide) : Env (environments.proofContext side) base :=
  match side with
  | .source => environments.source
  | .target => environments.target

def slot
    {sourceContext targetContext : LambdaPFC.Ctx n} {base : Ctx sig}
    (environments : EndpointEnvs sourceContext targetContext base)
    (side : ProofSide) (index : Fin n) :
    Slot base ((environments.proofContext side).lookup index) :=
  (environments.environment side).lookup index

/-- Reindex both endpoint environments through one typed target renaming. -/
noncomputable def targetRename
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sourceSig} {renamedBase : Ctx targetSig}
    (environments : EndpointEnvs sourceContext targetContext base)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed base renamedBase mapping) :
    EndpointEnvs sourceContext targetContext renamedBase where
  source := environments.source.targetRename mapping typed
  target := environments.target.targetRename mapping typed

@[simp] theorem targetRename_environment
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx sourceSig} {renamedBase : Ctx targetSig}
    (environments : EndpointEnvs sourceContext targetContext base)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed base renamedBase mapping)
    (side : ProofSide) :
    (environments.targetRename mapping typed).environment side =
      (environments.environment side).targetRename mapping typed := by
  cases side <;> rfl

end EndpointEnvs

namespace InterfaceMap

/-- Rebase a CPS interface map after one typed target renaming.  The only
transports reassociate `Shape.rename`; no identity equality is assumed. -/
noncomputable def targetRename
    {sourceSig targetSig : Sig}
    {sourceContext : Ctx sourceSig} {targetContext : Ctx targetSig}
    {source target : Shape sourceSig}
    (interfaceMap : InterfaceMap sourceContext source target)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    InterfaceMap targetContext (source.rename mapping)
      (target.rename mapping) where
  runAt next finalContext nextTyped sourceInterface answer continuation :=
    interfaceMap.runAt (mapping.comp next) finalContext
      (TypedRename.comp typed nextTyped)
      (by simpa only [Shape.rename_comp] using sourceInterface)
      answer
      (by simpa only [Shape.rename_comp] using continuation)
  runAt_hasType next finalContext nextTyped sourceInterface answer
      continuation :=
    interfaceMap.runAt_hasType (mapping.comp next) finalContext
      (TypedRename.comp typed nextTyped)
      (by simpa only [Shape.rename_comp] using sourceInterface)
      answer
      (by simpa only [Shape.rename_comp] using continuation)

end InterfaceMap

/-- One direct proper-type subtyping result.  The ordinary conversion emits
target syntax; the interface map preserves exact hidden identities while
rule recursion continues under package openings. -/
structure Relation (base : Ctx sig)
    (sourceType targetType : LambdaPFC.Ty n)
    (source target : Shape sig) : Type where
  sourceRep : Rep base sourceType source
  targetRep : Rep base targetType target
  conversion : Conversion base source.inputTy target.inputTy
  interfaceMap : InterfaceMap base source target

namespace Relation

def rep
    {base : Ctx sig} {sourceType targetType : LambdaPFC.Ty n}
    {source target : Shape sig}
    (relation : Relation base sourceType targetType source target)
    (side : ProofSide) :
    Rep base (side.choose sourceType targetType)
      (side.choose source target) :=
  match side with
  | .source => relation.sourceRep
  | .target => relation.targetRep

/-- Exact reflexivity keeps the supplied interface rather than reopening an
identity package through the ordinary identity function. -/
noncomputable def refl
    {base : Ctx sig} {sourceType : LambdaPFC.Ty n}
    {shape : Shape sig} (rep : Rep base sourceType shape) :
    Relation base sourceType sourceType shape shape where
  sourceRep := rep
  targetRep := rep
  conversion := Conversion.refl base shape.inputTy
  interfaceMap := InterfaceMap.refl base shape

/-- Use an ordinary conversion when no rule-specific exact interface map is
available.  Target elimination remains scoped inside the CPS continuation. -/
noncomputable def ofConversion
    {base : Ctx sig} {sourceType targetType : LambdaPFC.Ty n}
    {source target : Shape sig}
    (sourceRep : Rep base sourceType source)
    (targetRep : Rep base targetType target)
    (conversion : Conversion base source.inputTy target.inputTy) :
    Relation base sourceType targetType source target where
  sourceRep := sourceRep
  targetRep := targetRep
  conversion := conversion
  interfaceMap := InterfaceMap.ofConversion base source target conversion

/-- Reindex a relation through a typed target renaming. -/
noncomputable def targetRename
    {sourceSig targetSig : Sig}
    {sourceContext : Ctx sourceSig} {targetContext : Ctx targetSig}
    {sourceType targetType : LambdaPFC.Ty n}
    {source target : Shape sourceSig}
    (relation : Relation sourceContext sourceType targetType source target)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Relation targetContext sourceType targetType
      (source.rename mapping) (target.rename mapping) where
  sourceRep := relation.sourceRep.targetRename mapping typed
  targetRep := relation.targetRep.targetRename mapping typed
  conversion := by
    simpa only [Shape.inputTy_rename] using
      relation.conversion.rename mapping typed
  interfaceMap := relation.interfaceMap.targetRename mapping typed

/-- Compile raw transitivity by exact middle-shape composition. -/
noncomputable def trans
    {base : Ctx sig}
    {sourceType middleType targetType : LambdaPFC.Ty n}
    {source middle target : Shape sig}
    (first : Relation base sourceType middleType source middle)
    (second : Relation base middleType targetType middle target) :
    Relation base sourceType targetType source target where
  sourceRep := first.sourceRep
  targetRep := second.targetRep
  conversion := first.conversion.compose second.conversion
  interfaceMap := first.interfaceMap.compose second.interfaceMap

end Relation

/-- Extend one environment with an interface already present in the current
target context.  The newest slot retains that exact interface. -/
noncomputable def extendAtInterface
    {sourceContext : LambdaPFC.Ctx n} {base : Ctx sig}
    (environment : Env sourceContext base)
    (sourceType : LambdaPFC.Ty n) {shape : Shape sig}
    (interface : Shape.Interface base shape)
    (rep : Rep base sourceType shape) :
    Env (sourceContext.snoc sourceType) base :=
  environment.extend Rename.id (TypedRename.id base) sourceType interface
    (rep.sourceRename LambdaPFC.FinFun.weaken)

/-- One dependent endpoint in the common continuation scope.  The newest
environment slot already retains the exact first interface and first
representation, so they are not duplicated here. -/
structure EndpointView
    (sourceContext : LambdaPFC.Ctx n)
    (firstType : LambdaPFC.Ty n)
    (memberType : LambdaPFC.Ty (n + 1))
    (base : Ctx sig) : Type where
  environment : Env (sourceContext.snoc firstType) base
  memberShape : Shape sig
  memberRep : Rep base memberType memberShape

namespace EndpointView

def newestSlot
    {sourceContext : LambdaPFC.Ctx n} {firstType : LambdaPFC.Ty n}
    {memberType : LambdaPFC.Ty (n + 1)} {base : Ctx sig}
    (view : EndpointView sourceContext firstType memberType base) :
    Slot base ((sourceContext.snoc firstType).lookup 0) :=
  view.environment.lookup 0

end EndpointView

/-- Both dependent endpoints in the single future target context chosen by
an interface map. -/
structure MemberScope
    (sourceContext targetContext : LambdaPFC.Ctx n)
    (sourceFirstType targetFirstType : LambdaPFC.Ty n)
    (sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1))
    (base : Ctx sig) : Type where
  source : EndpointView sourceContext sourceFirstType sourceMemberType base
  target : EndpointView targetContext targetFirstType targetMemberType base

namespace MemberScope

def proofContext
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    (_scope : MemberScope sourceContext targetContext sourceFirstType
      targetFirstType sourceMemberType targetMemberType base)
    (side : ProofSide) : LambdaPFC.Ctx (n + 1) :=
  side.choose (sourceContext.snoc sourceFirstType)
    (targetContext.snoc targetFirstType)

def environment
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    (scope : MemberScope sourceContext targetContext sourceFirstType
      targetFirstType sourceMemberType targetMemberType base)
    (side : ProofSide) : Env (scope.proofContext side) base :=
  match side with
  | .source => scope.source.environment
  | .target => scope.target.environment

def memberShape
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    (scope : MemberScope sourceContext targetContext sourceFirstType
      targetFirstType sourceMemberType targetMemberType base)
    (side : ProofSide) : Shape sig :=
  side.choose scope.source.memberShape scope.target.memberShape

def memberRep
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    (scope : MemberScope sourceContext targetContext sourceFirstType
      targetFirstType sourceMemberType targetMemberType base)
    (side : ProofSide) :
    Rep base (side.choose sourceMemberType targetMemberType)
      (scope.memberShape side) :=
  match side with
  | .source => scope.source.memberRep
  | .target => scope.target.memberRep

def newestSlot
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {base : Ctx sig}
    (scope : MemberScope sourceContext targetContext sourceFirstType
      targetFirstType sourceMemberType targetMemberType base)
    (side : ProofSide) :
    Slot base ((scope.proofContext side).lookup 0) :=
  match side with
  | .source => scope.source.newestSlot
  | .target => scope.target.newestSlot

end MemberScope

/-- Build the recursive member scope once both first-component interfaces
are present in the same future target context.  Each dependent representation
is substituted by its own interface; source binders remain live. -/
noncomputable def makeMemberScopeAt
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx origin} {finalContext : Ctx final}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape origin}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (sourceFirstRep : Rep base sourceFirstType sourceFirst)
    (targetFirstRep : Rep base targetFirstType targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    (mapping : Rename origin final)
    (typed : Rename.Typed base finalContext mapping)
    (sourceFirstInterface : Shape.Interface finalContext
      (sourceFirst.rename mapping))
    (targetFirstInterface : Shape.Interface finalContext
      (targetFirst.rename mapping)) :
    MemberScope sourceContext targetContext sourceFirstType targetFirstType
      sourceMemberType targetMemberType finalContext := by
  let sourceFirstRepAt := sourceFirstRep.targetRename mapping typed
  let targetFirstRepAt := targetFirstRep.targetRename mapping typed
  let sourceMemberRepAt := sourceMemberRep.targetRename
    (sourceFirst.liftRename mapping) (sourceFirst.liftRename_typed typed)
  let targetMemberRepAt := targetMemberRep.targetRename
    (targetFirst.liftRename mapping) (targetFirst.liftRename_typed typed)
  let sourceMemberInstantiated := sourceMemberRepAt.targetSubst
    sourceFirstInterface.substitution
    sourceFirstInterface.arguments.substitution_typed
  let targetMemberInstantiated := targetMemberRepAt.targetSubst
    targetFirstInterface.substitution
    targetFirstInterface.arguments.substitution_typed
  exact {
    source := {
      environment := extendAtInterface
        (environments.source.targetRename mapping typed)
        sourceFirstType sourceFirstInterface sourceFirstRepAt
      memberShape :=
        (sourceMember.rename (sourceFirst.liftRename mapping)).subst
          sourceFirstInterface.substitution
      memberRep := sourceMemberInstantiated
    }
    target := {
      environment := extendAtInterface
        (environments.target.targetRename mapping typed)
        targetFirstType targetFirstInterface targetFirstRepAt
      memberShape :=
        (targetMember.rename (targetFirst.liftRename mapping)).subst
          targetFirstInterface.substitution
      memberRep := targetMemberInstantiated
    }
  }

/-- Pair covariance starts with the source first interface and receives the
target first interface from the forward first-component map. -/
noncomputable def makePairMemberScope
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx origin} {finalContext : Ctx final}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape origin}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (sourceFirstInterface : Shape.Interface base sourceFirst)
    (sourceFirstRep : Rep base sourceFirstType sourceFirst)
    (targetFirstRep : Rep base targetFirstType targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    (mapping : Rename origin final)
    (typed : Rename.Typed base finalContext mapping)
    (targetFirstInterface : Shape.Interface finalContext
      (targetFirst.rename mapping)) :
    MemberScope sourceContext targetContext sourceFirstType targetFirstType
      sourceMemberType targetMemberType finalContext :=
  makeMemberScopeAt environments sourceFirstRep targetFirstRep
    sourceMemberRep targetMemberRep mapping typed
    (sourceFirstInterface.rename mapping typed) targetFirstInterface

/-- Function contravariance starts with the target-domain interface and
receives the source-domain interface from the reversed domain map. -/
noncomputable def makeFunctionMemberScope
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx origin} {finalContext : Ctx final}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape origin}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (targetDomainInterface : Shape.Interface base targetDomain)
    (sourceDomainRep : Rep base sourceDomainType sourceDomain)
    (targetDomainRep : Rep base targetDomainType targetDomain)
    (sourceCodomainRep : Rep (sourceDomain.context base)
      sourceCodomainType sourceCodomain)
    (targetCodomainRep : Rep (targetDomain.context base)
      targetCodomainType targetCodomain)
    (mapping : Rename origin final)
    (typed : Rename.Typed base finalContext mapping)
    (sourceDomainInterface : Shape.Interface finalContext
      (sourceDomain.rename mapping)) :
    MemberScope sourceContext targetContext sourceDomainType targetDomainType
      sourceCodomainType targetCodomainType finalContext :=
  makeMemberScopeAt environments sourceDomainRep targetDomainRep
    sourceCodomainRep targetCodomainRep mapping typed sourceDomainInterface
    (targetDomainInterface.rename mapping typed)

/-- A recursive member consumer natural in the future target scope chosen by
the first-component interface map. -/
abbrev MemberConsumer
    {origin : Sig} (base : Ctx origin)
    (sourceContext targetContext : LambdaPFC.Ctx n)
    (sourceFirstType targetFirstType : LambdaPFC.Ty n)
    (sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1))
    (answer : Ty origin) : Type :=
  {final : Sig} -> (mapping : Rename origin final) ->
    (finalContext : Ctx final) ->
    (typed : Rename.Typed base finalContext mapping) ->
    MemberScope sourceContext targetContext sourceFirstType targetFirstType
      sourceMemberType targetMemberType finalContext ->
    Path.Body finalContext (answer.rename mapping)

private noncomputable def pairMemberContinuation
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx origin}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape origin}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (sourceFirstInterface : Shape.Interface base sourceFirst)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    (answer : Ty origin)
    (consumer : MemberConsumer base sourceContext targetContext
      sourceFirstType targetFirstType sourceMemberType targetMemberType
      answer) :
    InterfaceMap.Continuation base targetFirst answer where
  body mapping finalContext typed targetFirstInterface :=
    (consumer mapping finalContext typed
      (makePairMemberScope environments sourceFirstInterface
        firstRelation.sourceRep firstRelation.targetRep sourceMemberRep
        targetMemberRep mapping typed targetFirstInterface)).expression
  body_hasType mapping finalContext typed targetFirstInterface :=
    (consumer mapping finalContext typed
      (makePairMemberScope environments sourceFirstInterface
        firstRelation.sourceRep firstRelation.targetRep sourceMemberRep
        targetMemberRep mapping typed targetFirstInterface)).typing

/-- Run pair-member recursion under the exact source and mapped target first
interfaces. -/
noncomputable def runPairMembers
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx origin}
    {sourceFirstType targetFirstType : LambdaPFC.Ty n}
    {sourceMemberType targetMemberType : LambdaPFC.Ty (n + 1)}
    {sourceFirst targetFirst : Shape origin}
    {sourceMember : Shape sourceFirst.scope}
    {targetMember : Shape targetFirst.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (sourceFirstInterface : Shape.Interface base sourceFirst)
    (firstRelation : Relation base sourceFirstType targetFirstType
      sourceFirst targetFirst)
    (sourceMemberRep : Rep (sourceFirst.context base)
      sourceMemberType sourceMember)
    (targetMemberRep : Rep (targetFirst.context base)
      targetMemberType targetMember)
    (answer : Ty origin)
    (consumer : MemberConsumer base sourceContext targetContext
      sourceFirstType targetFirstType sourceMemberType targetMemberType
      answer) : Path.Body base answer where
  expression := firstRelation.interfaceMap.run sourceFirstInterface answer
    (pairMemberContinuation environments sourceFirstInterface firstRelation
      sourceMemberRep targetMemberRep answer consumer)
  typing := firstRelation.interfaceMap.run_hasType sourceFirstInterface answer
    (pairMemberContinuation environments sourceFirstInterface firstRelation
      sourceMemberRep targetMemberRep answer consumer)

private noncomputable def functionMemberContinuation
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx origin}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape origin}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (targetDomainInterface : Shape.Interface base targetDomain)
    (domainRelation : Relation base targetDomainType sourceDomainType
      targetDomain sourceDomain)
    (sourceCodomainRep : Rep (sourceDomain.context base)
      sourceCodomainType sourceCodomain)
    (targetCodomainRep : Rep (targetDomain.context base)
      targetCodomainType targetCodomain)
    (answer : Ty origin)
    (consumer : MemberConsumer base sourceContext targetContext
      sourceDomainType targetDomainType sourceCodomainType targetCodomainType
      answer) :
    InterfaceMap.Continuation base sourceDomain answer where
  body mapping finalContext typed sourceDomainInterface :=
    (consumer mapping finalContext typed
      (makeFunctionMemberScope environments targetDomainInterface
        domainRelation.targetRep domainRelation.sourceRep sourceCodomainRep
        targetCodomainRep mapping typed sourceDomainInterface)).expression
  body_hasType mapping finalContext typed sourceDomainInterface :=
    (consumer mapping finalContext typed
      (makeFunctionMemberScope environments targetDomainInterface
        domainRelation.targetRep domainRelation.sourceRep sourceCodomainRep
        targetCodomainRep mapping typed sourceDomainInterface)).typing

/-- Run function-codomain recursion under the mapped source-domain and exact
target-domain interfaces. -/
noncomputable def runFunctionMembers
    {sourceContext targetContext : LambdaPFC.Ctx n}
    {base : Ctx origin}
    {sourceDomainType targetDomainType : LambdaPFC.Ty n}
    {sourceCodomainType targetCodomainType : LambdaPFC.Ty (n + 1)}
    {sourceDomain targetDomain : Shape origin}
    {sourceCodomain : Shape sourceDomain.scope}
    {targetCodomain : Shape targetDomain.scope}
    (environments : EndpointEnvs sourceContext targetContext base)
    (targetDomainInterface : Shape.Interface base targetDomain)
    (domainRelation : Relation base targetDomainType sourceDomainType
      targetDomain sourceDomain)
    (sourceCodomainRep : Rep (sourceDomain.context base)
      sourceCodomainType sourceCodomain)
    (targetCodomainRep : Rep (targetDomain.context base)
      targetCodomainType targetCodomain)
    (answer : Ty origin)
    (consumer : MemberConsumer base sourceContext targetContext
      sourceDomainType targetDomainType sourceCodomainType targetCodomainType
      answer) : Path.Body base answer where
  expression := domainRelation.interfaceMap.run targetDomainInterface answer
    (functionMemberContinuation environments targetDomainInterface
      domainRelation sourceCodomainRep targetCodomainRep answer consumer)
  typing := domainRelation.interfaceMap.run_hasType targetDomainInterface
    answer (functionMemberContinuation environments targetDomainInterface
      domainRelation sourceCodomainRep targetCodomainRep answer consumer)

end LambdaPToFCo.Direct.Internal
