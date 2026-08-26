import LambdaPToFCo.StaticTranslationIrrel

/-!
The static coherence invariant on the compiler's one mixed scope relation. It records
well-formedness of every source binding, relates translated paths to their
target slots, and states that both evidence projections of an exact slot meet
at the translation of the source witness.
-/

namespace LambdaPToFCo
namespace StaticTranslation

open SystemFCo

namespace Scope

structure Coherent
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext) : Type where
  lookup_wf :
    ∀ (index : Fin n),
      Fragment.Wf sourceContext (sourceContext.lookup index)
  path_eq :
    ∀ {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
      (typing : Fragment.PathTy sourceContext path sourceType)
      (wf : Fragment.Wf sourceContext sourceType),
      (translatePath scope typing).targetType = translateType scope wf
  lower_eq :
    ∀ {package first : Fin n} {label : LambdaPFC.Name}
      {lower upper : LambdaPFC.Ty n}
      (member : Fragment.BoundMember sourceContext package label
        lower upper first)
      (wf : Fragment.Wf sourceContext lower),
      translateType scope wf = (scope.lookupMember member).lowerBound
  upper_eq :
    ∀ {package first : Fin n} {label : LambdaPFC.Name}
      {lower upper : LambdaPFC.Ty n}
      (member : Fragment.BoundMember sourceContext package label
        lower upper first)
      (wf : Fragment.Wf sourceContext upper),
      translateType scope wf = (scope.lookupMember member).upperBound

namespace Coherent

theorem typeIrrel (_coherent : scope.Coherent)
    (left right : Fragment.Wf sourceContext sourceType) :
    translateType scope left = translateType scope right :=
  translateType_irrel scope left right

theorem widen_eq (coherent : scope.Coherent)
    (typing : Fragment.PathTy sourceContext path sourceType)
    (wf : Fragment.Wf sourceContext sourceType) :
    translateType scope (.singleton typing) = translateType scope wf := by
  change (translatePath scope typing).targetType = translateType scope wf
  exact coherent.path_eq typing wf

end Coherent
end Scope

end StaticTranslation
end LambdaPToFCo
