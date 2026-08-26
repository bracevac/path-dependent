import LambdaPFC.RecordRegression
import LambdaPToFCo.Full.PairIntroductionCompiler

/-!
# Static full-calculus value-member regression

`LambdaPFC.RecordRegression.secondValue` is the first value-member pair in the
closed record example. The restricted translation has no value-member pair
introduction, so this is a small source term that exercises a genuinely Full
constructor without pretending that a total Full term compiler already
exists.

This regression builds a concrete source/target scope from
`SystemFCoExt.Ctx.empty`. Both preceding source-slot models are constructed
only from the public structural `WfPlan` roots; no path resolver, callback, or
assumed target package is supplied. `PairIntroductionCompiler.valuePair` then
produces the actual target package, and the final declaration exposes its
`SystemFCoExt.Exp.HasType` derivation.
-/

namespace LambdaPToFCo.Full.RecordIntroductionStaticRegression

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

namespace Source

/-- The source context immediately before `RecordRegression.secondValue`. -/
abbrev context1 : LambdaPFC.Ctx 1 :=
  LambdaPFC.Ctx.nil.snoc LambdaPFC.RecordRegression.implementationType

abbrev context2 : LambdaPFC.Ctx 2 :=
  context1.snoc LambdaPFC.RecordRegression.firstRecord

/-- The direct introduction type, before the enclosing record regression's
subsumption changes both dependent components. -/
abbrev exactSecondType : LambdaPFC.Ty 2 :=
  .Pair (.Single (.var 0)) LambdaPFC.RecordRegression.valueLabel
    (.ty (.Single ((Path.var 1).weaken)))

def typing : Tm.Ty context2 LambdaPFC.RecordRegression.secondValue
    exactSecondType := by
  simpa [LambdaPFC.RecordRegression.secondValue] using
    (Tm.Ty.pair (Γ := context2) (y := (0 : Fin 2))
      (a := LambdaPFC.RecordRegression.valueLabel) (z := (1 : Fin 2)))

end Source

/-- The path-free implementation type has a structural bidirectional model
under every already-certified scope. -/
noncomputable def implementationResult
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}
    (scope : ScopeModel sourceContext targetContext) :
    WfPlan.Proper sourceContext targetContext scope
      LambdaPFC.RecordRegression.implementationType := by
  let domain := WfPlan.Proper.top scope
  let codomainScope := scope.bindBidirectional domain.model
  let codomain := WfPlan.Proper.top codomainScope
  simpa [LambdaPFC.RecordRegression.implementationType] using
    (WfPlan.Proper.function scope domain codomain)

def rootScope : ScopeModel LambdaPFC.Ctx.nil SystemFCoExt.Ctx.empty :=
  ScopeModel.empty SystemFCoExt.Ctx.empty

noncomputable def rootImplementation := implementationResult rootScope

noncomputable def context1Scope : ScopeModel Source.context1
    (rootImplementation.plan.context SystemFCoExt.Ctx.empty) :=
  rootScope.bindBidirectional rootImplementation.model

/-- The preceding interval record is also path-free: its first component and
both interval endpoints reuse the structural implementation model. -/
noncomputable def firstRecordResult :
    WfPlan.Proper Source.context1
      (rootImplementation.plan.context SystemFCoExt.Ctx.empty)
      context1Scope LambdaPFC.RecordRegression.firstRecord := by
  let first := implementationResult context1Scope
  let memberScope := context1Scope.bindBidirectional first.model
  let lower := implementationResult memberScope
  let member := WfPlan.Interval.bounds memberScope lower lower Tau.Sub.refl
  simpa [LambdaPFC.RecordRegression.firstRecord,
    LambdaPFC.RecordRegression.implementationType, LambdaPFC.Tau.weaken,
    LambdaPFC.Ty.weaken, LambdaPFC.Tau.rename, LambdaPFC.Ty.rename] using
    (WfPlan.Proper.intervalPair context1Scope first member)

noncomputable def context2Scope : ScopeModel Source.context2
    (firstRecordResult.plan.context
      (rootImplementation.plan.context SystemFCoExt.Ctx.empty)) :=
  context1Scope.bindBidirectional firstRecordResult.model

/-- Public Full compilation of the existing source value-member term. -/
noncomputable def compiled :=
  PairIntroductionCompiler.valuePair context2Scope (0 : Fin 2) (1 : Fin 2)
    LambdaPFC.RecordRegression.valueLabel

noncomputable abbrev TargetContext :=
  firstRecordResult.plan.context
    (rootImplementation.plan.context SystemFCoExt.Ctx.empty)

/-- The compiler retained the exact existing source term and introduction
derivation, rather than merely constructing an extensionally similar target
package. -/
def sourceOrigin : ProducerOrigin Source.context2 Source.exactSecondType :=
  .value Source.typing .pair

theorem compiled_origin_eq : compiled.origin = sourceOrigin := by
  rfl

/-- The concrete target package expression produced by the Full compiler. -/
noncomputable def targetTerm := compiled.package.expression

/-- End-to-end static target typing for the compiled package expression. -/
noncomputable def targetTerm_hasType :
    Exp.HasType TargetContext targetTerm compiled.plan.inputTy :=
  compiled.package.typing

end LambdaPToFCo.Full.RecordIntroductionStaticRegression
