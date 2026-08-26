import LambdaPToFCo.Full.StaticAdaptation

/-!
# Exact full-term compilation results

This high carrier connects one already compiled proper producer to the exact
full-calculus source typing derivation from which it came.  It is deliberately
not a total compiler: construction starts from a sealed `ProperProducer`, and
the sole certificate states that the producer's source origin is exactly the
canonical `ProducerOrigin.ofTyping` of the supplied derivation.

The public eliminators reveal only the producer's selected plan, compiled
package, and target typing.  In particular, there is no constructor accepting
a raw target package or adapter.
-/

namespace LambdaPToFCo.Full

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

/-- Certification that an existing proper producer compiles one exact source
term derivation.  Keeping `producer` as an index prevents the certificate from
silently replacing its plan, package, or ordinary/absurd status. -/
structure TermCompilation
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    (sourceTyping : LambdaPFC.Tm.Ty sourceContext term sourceType)
    (scope : ScopeModel sourceContext targetContext)
    (producer : ProperProducer sourceContext targetContext scope sourceType) :
    Type where
  origin_eq : producer.origin = ProducerOrigin.ofTyping sourceTyping

namespace TermCompilation

/-- The exact plan selected by the indexed producer. -/
def plan
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {sourceTyping : LambdaPFC.Tm.Ty sourceContext term sourceType}
    {scope : ScopeModel sourceContext targetContext}
    {producer : ProperProducer sourceContext targetContext scope sourceType}
    (_compilation : TermCompilation sourceTyping scope producer) :
    ValuePlan sig :=
  producer.plan

/-- The producer's already sealed target package. -/
def package
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {sourceTyping : LambdaPFC.Tm.Ty sourceContext term sourceType}
    {scope : ScopeModel sourceContext targetContext}
    {producer : ProperProducer sourceContext targetContext scope sourceType}
    (compilation : TermCompilation sourceTyping scope producer) :
    CompiledPackage targetContext compilation.plan :=
  producer.package

/-- Concrete target typing of the compiled package. -/
def typing
    {term : LambdaPFC.Tm n} {sourceType : LambdaPFC.Ty n}
    {sourceTyping : LambdaPFC.Tm.Ty sourceContext term sourceType}
    {scope : ScopeModel sourceContext targetContext}
    {producer : ProperProducer sourceContext targetContext scope sourceType}
    (compilation : TermCompilation sourceTyping scope producer) :
    Exp.HasType targetContext compilation.package.expression
      compilation.plan.inputTy :=
  compilation.package.typing

/-!
A generic two-input subsumption constructor is intentionally absent.  A
`StaticAdaptation` fixes a target `ProperDemand`, hence only a negative
`DemandPlanModel`.  Constructing the ordinary producer required by a new
`TermCompilation` additionally needs positive `ProducerPlanModel` evidence
for that exact demand plan.  `StaticAdaptation.toOrdinary` exposes this
requirement explicitly; this carrier does not fabricate it or hide it in a
callback.
-/

end TermCompilation

end LambdaPToFCo.Full
