import LambdaPToFCo.Full.NormalizedTermCompilation
import LambdaPToFCo.Full.GeneralPairLetPlanningRegression

/-!
# One-suffix normalization regression

The bound abstraction from the GeneralPair regression is introduced exactly
at `Top -> Top` and advertised as `Top` through source subsumption.  Its
`TypingView` suffix is proof-relevantly `.trans .refl .top`, rather than the
standalone `.top` used by the earlier hand-written checkpoint.

This regression consumes that exact normalized suffix once through the core
opaque adaptation, then certifies the resulting target package against the
original `.sub` typing.  It demonstrates why the normalized seam must not
recurse through `Tm.Ty.sub` or replace the accumulated derivation with an
extensionally equivalent rule.
-/

namespace LambdaPToFCo.Full.NormalizedTermCompilationRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces
open DemandDirectedSubtyping

noncomputable section

abbrev SourceTyping :=
  GeneralPairLetPlanningRegression.boundSourceTyping

/-- The existing abstraction compiler result is the exact syntax-directed
root below the normalized suffix. -/
noncomputable def normalized : NormalizedTermCompilation SourceTyping
    GeneralPairLetPlanningRegression.rootScope
    (.ordinary GeneralPairLetPlanningRegression.exactFunction) where
  root_origin_eq := rfl

/-- `TypingView.cast` retains the initial reflexive introduction suffix and
composes the source Top rule after it. -/
theorem suffix_eq : normalized.suffix =
    Tau.Sub.trans Tau.Sub.refl
      GeneralPairLetPlanningRegression.functionSubtyping := by
  rfl

noncomputable def coreAdaptation : FusedAdaptation
    (ScopeAlignment.identity GeneralPairLetPlanningRegression.rootScope.view)
    normalized.suffix
    (.ordinary GeneralPairLetPlanningRegression.exactFunction)
    GeneralPairLetPlanningRegression.topDemand :=
  FusedAdaptation.toOpaque
    (ScopeAlignment.identity GeneralPairLetPlanningRegression.rootScope.view)
    normalized.suffix
    (.ordinary GeneralPairLetPlanningRegression.exactFunction)
    (DemandTrace.ofWf .top)

noncomputable def adaptation : StaticAdaptation
    (ScopeAlignment.identity GeneralPairLetPlanningRegression.rootScope.view)
    normalized.suffix
    (.ordinary GeneralPairLetPlanningRegression.exactFunction)
    GeneralPairLetPlanningRegression.topDemand :=
  StaticAdaptation.ofCore coreAdaptation

/-- Exact compilation of the original subsumed abstraction typing. -/
noncomputable def compilation : TermCompilation SourceTyping
    GeneralPairLetPlanningRegression.rootScope
    (.ordinary (normalized.finishedProducer adaptation
      GeneralPairLetPlanningRegression.domainResult.model.producer)) :=
  normalized.finish adaptation
    GeneralPairLetPlanningRegression.domainResult.model.producer

noncomputable def compiledPackage : CompiledPackage SystemFCoExt.Ctx.empty
    compilation.plan :=
  compilation.package

noncomputable def targetTerm_hasType :
    Exp.HasType SystemFCoExt.Ctx.empty compiledPackage.expression
      compilation.plan.inputTy :=
  compilation.typing

end

end LambdaPToFCo.Full.NormalizedTermCompilationRegression
