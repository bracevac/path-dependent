import LambdaPToFCo.OperationalPathCoherenceGenerated
import LambdaPToFCo.OperationalTypedPathView

/-!
# Raw-slot coherence of generated typed paths

`ClosedPathView` is intentionally an abstract package, so an arbitrary value
of that type need not satisfy the raw-slot law.  The path compiler's concrete
`build` function always finishes with a direct ordinary instantiation; this
module records that stronger generated-view property externally.
-/

namespace LambdaPToFCo
namespace OperationalTypedPathCoherence

open SystemFCo
open StaticTranslation
open OperationalCode
open OperationalEnvironment
open OperationalBindingView
open OperationalApplicationSpine
open OperationalStoreEnvironment
open OperationalPathCoherence
open OperationalPathCoherenceGenerated
open OperationalResultContext
open OperationalTypedPathView
open OperationalAdmissibility

namespace ClosedPathView

/-- A closed ordinary path view constructed from a value normalization has a
coherent raw binder projection. -/
theorem ofNormalization_rawSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {typing : Fragment.HasType sourceContext (.path path) sourceType}
    {environment : ClosingEnv sig []}
    (shape : OrdinaryShape sourceType)
    (normalization : ValueNormalization
      (environment.closeExp (TermTranslation.elaborate scope typing))) :
    RawSlot (ClosedPathView.ofNormalization shape normalization).view := by
  dsimp only [ClosedPathView.ofNormalization]
  apply rawSlot_castPlan
  exact rawSlot_ofInstantiation _ _

end ClosedPathView

/-- Adding a generated ordinary cast layer preserves the raw-slot law
because the resulting view is rebuilt by `ofNormalization`. -/
theorem ClosedPathView.adapt_rawSlot
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {source target : LambdaPFC.Ty n}
    {innerTyping : Fragment.HasType sourceContext (.path path) source}
    (subtype : Fragment.Sub sourceContext source target)
    (targetShape : OrdinaryShape target)
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    (innerImage : ClosedPathView scope innerTyping environment) :
    RawSlot (ClosedPathView.adapt subtype targetShape innerImage).view := by
  dsimp only [ClosedPathView.adapt]
  apply ClosedPathView.ofNormalization_rawSlot

/-- The restricted function-path compiler also ends in a direct ordinary
view, including after any outer structural function-coercion layer. -/
theorem buildFunctionPath_rawSlot
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {domain codomain : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path path)
      (.Fun domain codomain.weaken)}
    (spine : OperationalFunctionPathSpine.FunctionPathSpine typing)
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment)
    (coherent : StorePathCoherence store) :
    RawSlot
      (OperationalTypedPathView.buildFunctionPath spine store coherent).view := by
  cases spine with
  | widen pathTyping domainWf codomainWf domainShape =>
      exact ClosedPathView.adapt_rawSlot _ .arrow _
  | sub inner coercion =>
      exact ClosedPathView.adapt_rawSlot _ .arrow _

/-- Every closed path view produced by the admissible typed-path compiler has
a coherent raw binder projection. -/
theorem build_rawSlot
    {n current : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    {typing : Fragment.HasType sourceContext (.path path) sourceType}
    (admissible : OperationallyAdmissible typing)
    {sourceStore : LambdaPFC.Store current}
    {valuation : SourceValuation n current}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    {environment : ClosingEnv sig []}
    (store : StoreEnvironment sourceContext sourceStore valuation
      targetContext scope environment)
    (coherent : StorePathCoherence store) :
    RawSlot (OperationalTypedPathView.build admissible store coherent).view := by
  cases admissible with
  | path pathTyping =>
      simpa only [OperationalTypedPathView.build] using
        ClosedPathView.ofNormalization_rawSlot
          (scope := scope) (environment := environment) .singleton
          (OperationalTypedPathView.baseNormalization store coherent pathTyping)
  | functionPath spine =>
      simpa only [OperationalTypedPathView.build] using
        buildFunctionPath_rawSlot spine store coherent
  | neutralSub neutral inner subtype targetShape =>
      cases neutral
      simpa only [OperationalTypedPathView.build] using
        ClosedPathView.adapt_rawSlot subtype targetShape.ordinary _

end OperationalTypedPathCoherence
end LambdaPToFCo
