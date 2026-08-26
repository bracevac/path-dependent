import LambdaPToFCo.Full.NormalizedTermCompilation
import LambdaPToFCo.Full.LetPlanning

/-!
# Certified direct let introduction

This leaf closes one already compiled let body through the exact package of
an already certified ordinary bound term.  The root result is demand-local:
one `WfPlan.Proper` determines both the body demand and the plan returned after
Church elimination.

The result is the direct syntax-directed producer with
`ProducerOrigin.letResult`, together with its `NormalizedTermCompilation` at
the direct `Tm.Ty.let` derivation.  It does not compile either subterm, apply a
subtyping suffix, or claim total term compilation.  No raw package, adapter,
or callback is accepted.
-/

namespace LambdaPToFCo.Full.LetIntroductionCompiler

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

/-- One exact body term compilation whose selected plan is the demand-local
let body plan.  `TermCompilation` keeps the plan behind its indexed producer,
so the equality is the narrow remaining bridge; this wrapper seals it once
and exposes only the transported certified package. -/
structure BodyCompilationAtDemand
    (scope : ScopeModel sourceContext targetContext)
    {boundType resultType : LambdaPFC.Ty n}
    (bound : OrdinaryProducer sourceContext targetContext scope boundType)
    (result : WfPlan.Proper sourceContext targetContext scope resultType)
    {body : LambdaPFC.Tm (n + 1)}
    (bodyTyping : Tm.Ty (sourceContext.snoc boundType) body
      resultType.weaken) : Type where
  producer : ProperProducer (sourceContext.snoc boundType)
    (bound.plan.context targetContext) (LetPlanning.bodyScope scope bound)
    resultType.weaken
  compilation : TermCompilation bodyTyping (LetPlanning.bodyScope scope bound)
    producer
  plan_eq : compilation.plan = (LetPlanning.bodyDemand scope bound result).plan

namespace BodyCompilationAtDemand

/-- The exact body package expected by `LetPlanning.closeBody`. -/
noncomputable def package
    {scope : ScopeModel sourceContext targetContext}
    {boundType resultType : LambdaPFC.Ty n}
    {bound : OrdinaryProducer sourceContext targetContext scope boundType}
    {result : WfPlan.Proper sourceContext targetContext scope resultType}
    {body : LambdaPFC.Tm (n + 1)}
    {bodyTyping : Tm.Ty (sourceContext.snoc boundType) body
      resultType.weaken}
    (compiled : BodyCompilationAtDemand scope bound result bodyTyping) :
    CompiledPackage (bound.plan.context targetContext)
      (LetPlanning.bodyDemand scope bound result).plan := by
  rw [← compiled.plan_eq]
  exact compiled.compilation.package

end BodyCompilationAtDemand

/-- The direct source typing introduced by this compiler leaf. -/
def sourceTyping
    {scope : ScopeModel sourceContext targetContext}
    {boundTerm : LambdaPFC.Tm n} {boundType resultType : LambdaPFC.Ty n}
    (boundTyping : Tm.Ty sourceContext boundTerm boundType)
    (result : WfPlan.Proper sourceContext targetContext scope resultType)
    {body : LambdaPFC.Tm (n + 1)}
    (bodyTyping : Tm.Ty (sourceContext.snoc boundType) body
      resultType.weaken) :
    Tm.Ty sourceContext (.let boundTerm body) resultType :=
  .let boundTyping result.wf bodyTyping

/-- Close the certified body package and install the exact direct let origin. -/
noncomputable def producer
    {scope : ScopeModel sourceContext targetContext}
    {boundTerm : LambdaPFC.Tm n} {boundType resultType : LambdaPFC.Ty n}
    {bound : OrdinaryProducer sourceContext targetContext scope boundType}
    (boundTyping : Tm.Ty sourceContext boundTerm boundType)
    (_boundCompilation : TermCompilation boundTyping scope (.ordinary bound))
    (result : WfPlan.Proper sourceContext targetContext scope resultType)
    {body : LambdaPFC.Tm (n + 1)}
    (bodyTyping : Tm.Ty (sourceContext.snoc boundType) body
      resultType.weaken)
    (compiledBody : BodyCompilationAtDemand scope bound result bodyTyping) :
    OrdinaryProducer sourceContext targetContext scope resultType where
  origin := .letResult boundTyping result.wf bodyTyping
  model := ⟨result.plan, result.model.producer⟩
  package := LetPlanning.closeBody scope bound result compiledBody.package

/-- Package the direct let producer at the exact normalized introduction
boundary.  Its `TypingView` suffix is reflexivity; a caller may subsequently
finish a larger accumulated suffix through `NormalizedTermCompilation.finish`.
-/
noncomputable def compile
    {scope : ScopeModel sourceContext targetContext}
    {boundTerm : LambdaPFC.Tm n} {boundType resultType : LambdaPFC.Ty n}
    {bound : OrdinaryProducer sourceContext targetContext scope boundType}
    (boundTyping : Tm.Ty sourceContext boundTerm boundType)
    (boundCompilation : TermCompilation boundTyping scope (.ordinary bound))
    (result : WfPlan.Proper sourceContext targetContext scope resultType)
    {body : LambdaPFC.Tm (n + 1)}
    (bodyTyping : Tm.Ty (sourceContext.snoc boundType) body
      resultType.weaken)
    (compiledBody : BodyCompilationAtDemand scope bound result bodyTyping) :
    NormalizedTermCompilation
      (sourceTyping boundTyping result bodyTyping) scope
      (.ordinary (producer (resultType := resultType) boundTyping
        boundCompilation result bodyTyping compiledBody)) where
  root_origin_eq := rfl

end LambdaPToFCo.Full.LetIntroductionCompiler
