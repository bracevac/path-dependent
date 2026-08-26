import LambdaPToFCo.TermTranslation
import LambdaPToFCo.StaticTranslationExactNaturality

/-! Binder naturality consumed by the term type-preservation theorem. -/

namespace LambdaPToFCo
namespace TermTranslation

open SystemFCo
open StaticTranslation

/-- Type translation commutes with whichever target plan is selected for a
supported source binder. -/
theorem compileBinder_naturality
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    {sourceType resultType : LambdaPFC.Ty n}
    (binderWf : Fragment.Wf sourceContext sourceType)
    (resultWf : Fragment.Wf sourceContext resultType) :
    let binder := compileBinder scope binderWf
    translateType binder.extended (resultWf.weaken sourceType) =
      (translateType scope resultWf).rename binder.plan.weaken := by
  cases binderWf with
  | top =>
      exact translateType_weaken_ordinary scope .top
        (translateType scope .top) resultWf
  | singleton pathTyping =>
      exact translateType_weaken_ordinary scope .singleton
        (translateType scope (.singleton pathTyping)) resultWf
  | selection member nonempty =>
      exact translateType_weaken_ordinary scope .selection
        (translateType scope (.selection member nonempty)) resultWf
  | @memberPackage first label lower upper lowerWf upperWf nonempty =>
      exact translateType_weaken_member scope first label lower upper lowerWf
        upperWf nonempty (translateType scope lowerWf)
        (translateType scope upperWf) (scope.lookup first).path.targetType
        resultWf
  | arrow domainWf codomainWf =>
      exact translateType_weaken_ordinary scope .arrow
        (translateType scope (.arrow domainWf codomainWf)) resultWf

end TermTranslation
end LambdaPToFCo
