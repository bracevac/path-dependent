import LambdaPToFCo.Direct.SubtypingFunction

/-!
# Formation-aware dependent-function subtyping regression

This checks the literal rule

`(Top -> Bottom) <: (Bottom -> Top)`.

The domain changes contravariantly by `Bottom <: Top`.  Codomain recursion is
then performed in the sealed target-oriented scope extended with the actual
Bottom and Top domain interfaces supplied by the reversed interface map.
-/

namespace LambdaPToFCo.Direct.SubtypingFunctionRegression

noncomputable section

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Formation
open LambdaPToFCo.Direct.Internal.SubtypingScope
open LambdaPToFCo.Direct.Internal.SubtypingFunction

abbrev RootContext : LambdaPFC.Ctx 0 := .nil
abbrev TargetContext : Ctx [] := Ctx.empty

noncomputable def environment : Formation.Env RootContext TargetContext :=
  Formation.Env.empty TargetContext

noncomputable def scope : Scope RootContext RootContext .target
    TargetContext :=
  Scope.root environment .target

abbrev SourceDomainType : LambdaPFC.Ty 0 := .Top
abbrev TargetDomainType : LambdaPFC.Ty 0 := .Bot
abbrev SourceCodomainType : LambdaPFC.Ty 1 := .Bot
abbrev TargetCodomainType : LambdaPFC.Ty 1 := .Top

abbrev SourceDomain : Shape [] := .stable (Top.plan [])
abbrev TargetDomain : Shape [] := .stable (Bot.plan [])
abbrev SourceCodomain : Shape SourceDomain.scope :=
  .stable (Bot.plan SourceDomain.scope)
abbrev TargetCodomain : Shape TargetDomain.scope :=
  .stable (Top.plan TargetDomain.scope)

noncomputable def sourceDomainFormation : Formation RootContext TargetContext
    SourceDomainType SourceDomain :=
  .top

noncomputable def targetDomainFormation : Formation RootContext TargetContext
    TargetDomainType TargetDomain :=
  .bottom

noncomputable def sourceCodomainFormation : Formation
    (RootContext.snoc SourceDomainType) (SourceDomain.context TargetContext)
    SourceCodomainType SourceCodomain :=
  .bottom

noncomputable def targetCodomainFormation : Formation
    (RootContext.snoc TargetDomainType) (TargetDomain.context TargetContext)
    TargetCodomainType TargetCodomain :=
  .top

def domainDerivation : LambdaPFC.Tau.Sub RootContext
    (.ty TargetDomainType) (.ty SourceDomainType) :=
  .top

def codomainDerivation : LambdaPFC.Tau.Sub
    (RootContext.snoc TargetDomainType)
    (.ty SourceCodomainType) (.ty TargetCodomainType) :=
  .top

def derivation : LambdaPFC.Tau.Sub RootContext
    (.ty (.Fun SourceDomainType SourceCodomainType))
    (.ty (.Fun TargetDomainType TargetCodomainType)) :=
  .fun domainDerivation codomainDerivation

noncomputable def domainCut : DomainCut scope domainDerivation
    SourceDomain TargetDomain :=
  DomainCut.ofRelation sourceDomainFormation targetDomainFormation
    (AtomicSubtyping.top {
      shape := TargetDomain
      rep := targetDomainFormation.rep
    }).relation

noncomputable def codomainCompiler : CodomainCompiler domainCut
    sourceCodomainFormation targetCodomainFormation codomainDerivation where
  compile next nextTyped sourceInterface targetInterface := by
    let scopeAt := codomainScopeAt domainCut next nextTyped sourceInterface
      targetInterface
    let sourceAt := sourceCodomainFormationAt sourceCodomainFormation next
      nextTyped sourceInterface
    let targetAt := targetCodomainFormationAt
      (sourceDomain := SourceDomain) (sourceCodomain := SourceCodomain)
      targetCodomainFormation next nextTyped
    let relation := (AtomicSubtyping.top {
      shape := FunctionSubtyping.sourceCodomainAt SourceDomain TargetDomain
        SourceCodomain next sourceInterface
      rep := sourceAt.rep
    }).relation
    exact CutView.ofRelation sourceAt targetAt relation

/-- Formation-aware function cut with a genuinely changed contravariant
domain and recursive codomain compilation under `.target` alignment. -/
noncomputable def cut : CutView scope derivation
    (.stable (Function.plan SourceDomain SourceCodomain))
    (.stable (Function.plan TargetDomain TargetCodomain)) :=
  SubtypingFunction.compile domainCut sourceCodomainFormation
    targetCodomainFormation codomainCompiler

example : Exp.HasType TargetContext cut.relation.conversion.function
    (.arrow (Function.plan SourceDomain SourceCodomain).inputTy
      (Function.plan TargetDomain TargetCodomain).inputTy) :=
  cut.relation.conversion.functionTyping

end
end LambdaPToFCo.Direct.SubtypingFunctionRegression
