import LambdaPToFCo.StaticTranslationExactNaturality

namespace LambdaPToFCo
namespace StaticTranslation

open SystemFCo

/-- Recover the lower-bound well-formedness hidden by a package equality. -/
noncomputable def memberLowerWf
    {packageType lower upper : LambdaPFC.Ty n} {first : Fin n}
    {label : LambdaPFC.Name}
    (packageWf : Fragment.Wf sourceContext packageType)
    (typeEq : packageType =
      Fragment.memberPackageTy first label lower upper) :
    Fragment.Wf sourceContext lower := by
  cases packageWf with
  | top | singleton _ | selection _ _ | arrow _ _ => cases typeEq
  | memberPackage storedLowerWf storedUpperWf storedNonempty =>
      have parts := Fragment.memberPackageTy_injective typeEq
      cases parts.1
      cases parts.2.1
      cases parts.2.2.1
      cases parts.2.2.2
      exact storedLowerWf

/-- Recover the upper-bound well-formedness hidden by a package equality. -/
noncomputable def memberUpperWf
    {packageType lower upper : LambdaPFC.Ty n} {first : Fin n}
    {label : LambdaPFC.Name}
    (packageWf : Fragment.Wf sourceContext packageType)
    (typeEq : packageType =
      Fragment.memberPackageTy first label lower upper) :
    Fragment.Wf sourceContext upper := by
  cases packageWf with
  | top | singleton _ | selection _ _ | arrow _ _ => cases typeEq
  | memberPackage storedLowerWf storedUpperWf storedNonempty =>
      have parts := Fragment.memberPackageTy_injective typeEq
      cases parts.1
      cases parts.2.1
      cases parts.2.2.1
      cases parts.2.2.2
      exact storedUpperWf

namespace Scope.Coherent

noncomputable def memberLowerWf
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {package first : Fin n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty n}
    {scope : Scope sourceContext targetContext}
    (coherent : Scope.Coherent scope)
    (member : Fragment.BoundMember sourceContext package label lower upper
      first) : Fragment.Wf sourceContext lower :=
  StaticTranslation.memberLowerWf
    (coherent.lookup_wf package) member.lookup_eq

noncomputable def memberUpperWf
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {package first : Fin n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty n}
    {scope : Scope sourceContext targetContext}
    (coherent : Scope.Coherent scope)
    (member : Fragment.BoundMember sourceContext package label lower upper
      first) : Fragment.Wf sourceContext upper :=
  StaticTranslation.memberUpperWf
    (coherent.lookup_wf package) member.lookup_eq

/-- Compatibility helper for exact packages. -/
noncomputable def memberWf
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {package first : Fin n} {label : LambdaPFC.Name}
    {witness : LambdaPFC.Ty n}
    {scope : Scope sourceContext targetContext}
    (coherent : Scope.Coherent scope)
    (member : Fragment.BoundExactMember sourceContext package label witness
      first) : Fragment.Wf sourceContext witness :=
  coherent.memberLowerWf member

def empty : Scope.empty.Coherent where
  lookup_wf index := Fin.elim0 index
  path_eq typing := nomatch typing
  lower_eq member := nomatch member
  upper_eq member := nomatch member

end Scope.Coherent

end StaticTranslation
end LambdaPToFCo
