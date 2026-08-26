import LambdaPFC.RecordRegression
import LambdaPToFCo.Full.IntroductionCompiler
import LambdaPToFCo.Full.LetPlanning

/-!
# Static compilation of the Record implementation binding

The first bound term in `LambdaPFC.RecordRegression.term` is the closed
identity implementation `fun (x : Top) => x`, whose body reaches `Top` by
the full-calculus singleton widening rule.  This regression compiles that
actual source abstraction to a typed `SystemFCoExt` package.  It supplies no
path resolver or target adapter: the bound variable package is obtained from
the certified scope installed for the function domain.
-/

namespace LambdaPToFCo.Full.RecordImplementationStaticRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

noncomputable section

def rootScope : ScopeModel LambdaPFC.Ctx.nil SystemFCoExt.Ctx.empty :=
  ScopeModel.empty SystemFCoExt.Ctx.empty

def domainResult := WfPlan.Proper.top rootScope

noncomputable def functionBodyScope :=
  rootScope.bindBidirectional domainResult.model

/-- The exact body typing used by the existing source regression. -/
def bodyTyping :
    Tm.Ty (LambdaPFC.Ctx.nil.snoc .Top) (.path (.var 0)) .Top :=
  .sub (.path .var) (.widen .var) .top

/-- The bound variable already carries the exact `Top` package required by
the function codomain. -/
noncomputable def bodyPath :=
  functionBodyScope.variablePath (0 : Fin 1)

def codomainResult := WfPlan.Proper.top functionBodyScope

/-- Compilation of the concrete source abstraction before any enclosing
`let` opens its package. -/
noncomputable def compiled : OrdinaryProducer LambdaPFC.Ctx.nil
    SystemFCoExt.Ctx.empty rootScope
    LambdaPFC.RecordRegression.implementationType := by
  simpa [LambdaPFC.RecordRegression.implementationType] using
    (IntroductionCompiler.abstraction rootScope bodyTyping domainResult
      codomainResult.positive bodyPath.package)

/-- The exact existing source typing represented by `compiled`. -/
def sourceTyping :
    Tm.Ty LambdaPFC.Ctx.nil LambdaPFC.RecordRegression.implementation
      LambdaPFC.RecordRegression.implementationType := by
  simpa [LambdaPFC.RecordRegression.implementation,
    LambdaPFC.RecordRegression.implementationType] using
    (Tm.Ty.abs bodyTyping (Tau.Wf.top : Tau.Wf LambdaPFC.Ctx.nil (.ty .Top)))

theorem compiled_origin_eq : compiled.origin =
    ProducerOrigin.value sourceTyping .abs := by
  rfl

/-- Concrete target expression produced for the source implementation. -/
noncomputable def targetTerm := compiled.package.expression

/-- End-to-end target typing for the compiled implementation package. -/
noncomputable def targetTerm_hasType :
    Exp.HasType SystemFCoExt.Ctx.empty targetTerm compiled.plan.inputTy :=
  compiled.package.typing

/-- The concrete scope opened for the rest of the existing nested-let
record program. -/
noncomputable def letBodyScope :=
  LetPlanning.bodyScope rootScope compiled

/-- `RecordRegression.term` ultimately returns `Top`; this is its certified
root result plan. -/
def rootResult := WfPlan.Proper.top rootScope

/-- Exact negative plan against which the remainder of the nested-let body
must compile before the implementation package can be eliminated. -/
noncomputable def bodyDemand :=
  LetPlanning.bodyDemand rootScope compiled rootResult

end

end LambdaPToFCo.Full.RecordImplementationStaticRegression
