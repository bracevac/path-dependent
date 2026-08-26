import LambdaPToFCo.Direct.FunctionSubtyping
import LambdaPToFCo.Direct.AtomicSubtyping
import LambdaPToFCo.Direct.Wf

/-!
# Dependent-function subtyping regression

This exercises the literal rule

`(Top -> Bottom) <: (Bottom -> Top)`

with `.fun .top .top`.  The target-domain Bottom package is mapped
contravariantly to the source-domain Top package; the source result is then
mapped covariantly from Bottom to Top in the exact member continuation scope.
-/

namespace LambdaPToFCo.Direct.FunctionSubtypingRegression

noncomputable section

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.FunctionSubtyping

abbrev SourceContext : LambdaPFC.Ctx 0 := .nil
abbrev TargetContext : Ctx [] := Ctx.empty

noncomputable def environment : Env SourceContext TargetContext :=
  Env.empty TargetContext

noncomputable def environments :
    EndpointEnvs SourceContext SourceContext TargetContext where
  source := environment
  target := environment

noncomputable def sourceDomain :
    Wf.Proper TargetContext (.Top : LambdaPFC.Ty 0) :=
  Wf.Proper.top TargetContext

noncomputable def targetDomain :
    Wf.Proper TargetContext (.Bot : LambdaPFC.Ty 0) :=
  Wf.Proper.bottom TargetContext

noncomputable def sourceCodomain :
    Wf.Proper (sourceDomain.shape.context TargetContext)
      (.Bot : LambdaPFC.Ty 1) :=
  Wf.Proper.bottom (sourceDomain.shape.context TargetContext)

noncomputable def targetCodomain :
    Wf.Proper (targetDomain.shape.context TargetContext)
      (.Top : LambdaPFC.Ty 1) :=
  Wf.Proper.top (targetDomain.shape.context TargetContext)

def domainDerivation : LambdaPFC.Tau.Sub SourceContext
    (.ty (.Bot : LambdaPFC.Ty 0)) (.ty .Top) :=
  .top

def codomainDerivation : LambdaPFC.Tau.Sub
    (SourceContext.snoc .Bot)
    (.ty (.Bot : LambdaPFC.Ty 1)) (.ty .Top) :=
  .top

/-- The exact source derivation indexed by this regression. -/
def derivation : LambdaPFC.Tau.Sub SourceContext
    (.ty (.Fun .Top .Bot)) (.ty (.Fun .Bot .Top)) :=
  .fun domainDerivation codomainDerivation

noncomputable def domainCompilation :
    DomainCompilation TargetContext domainDerivation
      targetDomain.shape sourceDomain.shape where
  relation :=
    (AtomicSubtyping.top targetDomain).relation

/-- The material codomain instance used by the recursive Formation
dispatcher.  A generic `CodomainCompiler` can no longer erase its endpoint
formations to arbitrary `Rep`s: closed endpoints require those formations to
be exposed in lockstep. -/
abbrev CodomainContext := sourceDomain.shape.context TargetContext

noncomputable def materialCodomain : Relation CodomainContext
    (.Bot : LambdaPFC.Ty 1) (.Top : LambdaPFC.Ty 1)
    (.stable (Bot.plan sourceDomain.shape.scope))
    (.stable (Top.plan sourceDomain.shape.scope)) :=
  (AtomicSubtyping.top (Wf.Proper.bottom CodomainContext)).relation

example : Exp.HasType CodomainContext materialCodomain.conversion.function
    (.arrow (Bot.plan sourceDomain.shape.scope).inputTy
      (Top.plan sourceDomain.shape.scope).inputTy) :=
  materialCodomain.conversion.functionTyping

end
end LambdaPToFCo.Direct.FunctionSubtypingRegression
