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

noncomputable def codomainCompilation : CodomainCompiler
    (sourceContext := SourceContext)
    (targetContext := SourceContext)
    (sourceDomainType := (.Top : LambdaPFC.Ty 0))
    (targetDomainType := (.Bot : LambdaPFC.Ty 0))
    (sourceCodomainType := (.Bot : LambdaPFC.Ty 1))
    (targetCodomainType := (.Top : LambdaPFC.Ty 1))
    codomainDerivation where
  compile scope := by
    cases scope with
    | mk sourceView targetView =>
        cases sourceView with
        | mk sourceEnvironment sourceShape sourceRep =>
            cases targetView with
            | mk targetEnvironment targetShape targetRep =>
                cases sourceRep
                cases targetRep
                exact (AtomicSubtyping.top (Wf.Proper.bottom _)).relation

/-- Direct compilation of the exact `.fun .top .top` derivation. -/
noncomputable def compiled : Relation TargetContext
    (.Fun (.Top : LambdaPFC.Ty 0) (.Bot : LambdaPFC.Ty 1))
    (.Fun (.Bot : LambdaPFC.Ty 0) (.Top : LambdaPFC.Ty 1))
    (.stable (Function.plan sourceDomain.shape sourceCodomain.shape))
    (.stable (Function.plan targetDomain.shape targetCodomain.shape)) :=
  compile environments domainCompilation sourceCodomain.rep
    targetCodomain.rep codomainCompilation

/-- The emitted program is an ordinary unchanged-SystemFCo function between
the two stable function package types. -/
example : Exp.HasType TargetContext compiled.conversion.function
    (.arrow
      (Function.plan sourceDomain.shape sourceCodomain.shape).inputTy
      (Function.plan targetDomain.shape targetCodomain.shape).inputTy) :=
  compiled.conversion.functionTyping

end
end LambdaPToFCo.Direct.FunctionSubtypingRegression
