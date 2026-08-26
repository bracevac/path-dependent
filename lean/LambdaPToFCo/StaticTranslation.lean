import LambdaPToFCo.StaticTranslationCore

/-!
# Static translation for the restricted LambdaP fragment

`Scope` is the only context relation. A source variable maps to either one
ordinary target variable or the raw/type/evidence/payload interface of an
abstract-member package. Older mappings cross a complete mixed `BinderPlan`.
-/

namespace LambdaPToFCo
namespace StaticTranslation

open SystemFCo

@[simp] theorem translateType_top
    (scope : Scope sourceContext targetContext) :
    translateType scope (Fragment.Wf.top : Fragment.Wf sourceContext .Top) =
      .top := rfl

@[simp] theorem translateType_singleton
    (scope : Scope sourceContext targetContext)
    (pathTyping : Fragment.PathTy sourceContext path sourceType) :
    translateType scope (.singleton pathTyping) =
      (translatePath scope pathTyping).targetType := rfl

@[simp] theorem translateType_selection
    (scope : Scope sourceContext targetContext)
    (member : Fragment.BoundMember sourceContext package label lower upper
      first)
    (nonempty : Fragment.Sub sourceContext lower upper) :
    translateType scope (.selection member nonempty) =
      (scope.lookupMember member).interface.witness := rfl

@[simp] theorem translateType_memberPackage
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {lower upper : LambdaPFC.Ty n}
    (scope : Scope sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    (lowerWf : Fragment.Wf sourceContext lower)
    (upperWf : Fragment.Wf sourceContext upper)
    (nonempty : Fragment.Sub sourceContext lower upper) :
    translateType scope
        (.memberPackage (first := first) (label := label)
          lowerWf upperWf nonempty) =
      Ty.member (translateType scope lowerWf)
        (translateType scope upperWf)
        (payloadFamily (scope.lookup first).path.targetType) := rfl

@[simp] theorem translateType_exactPackage
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {witness : LambdaPFC.Ty n}
    (scope : Scope sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    (witnessWf : Fragment.Wf sourceContext witness) :
    translateType scope
        (Fragment.Wf.exactPackage (first := first) (label := label)
          witnessWf) =
      Ty.member (translateType scope witnessWf)
        (translateType scope witnessWf)
        (payloadFamily (scope.lookup first).path.targetType) := rfl

@[simp] theorem translateType_arrow
    (scope : Scope sourceContext targetContext)
    (domainWf : Fragment.Wf sourceContext domain)
    (codomainWf : Fragment.Wf sourceContext codomain) :
    translateType scope (.arrow domainWf codomainWf) =
      .arrow (translateType scope domainWf)
        (translateType scope codomainWf) := rfl

/-! ## Smart scope construction -/

noncomputable def Scope.bindOrdinary
    (scope : Scope sourceContext targetContext)
    (wf : Fragment.Wf sourceContext sourceType)
    (shape : OrdinaryShape sourceType) :
    Scope (sourceContext.snoc sourceType)
      ((Interface.BinderPlan.ordinary (translateType scope wf)).context
        targetContext) :=
  .ordinary scope sourceType shape (translateType scope wf)

noncomputable def Scope.bindMember
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    {lower upper : LambdaPFC.Ty n}
    (lowerWf : Fragment.Wf sourceContext lower)
    (upperWf : Fragment.Wf sourceContext upper)
    (nonempty : Fragment.Sub sourceContext lower upper) :
    Scope
      (sourceContext.snoc
        (Fragment.memberPackageTy first label lower upper))
      ((Interface.BinderPlan.exact
        (translateType scope lowerWf) (translateType scope upperWf)
        (payloadFamily (scope.lookup first).path.targetType))
        |>.context targetContext) :=
  .member scope first label lower upper lowerWf upperWf nonempty
    (translateType scope lowerWf) (translateType scope upperWf)
    (scope.lookup first).path.targetType

/-- Compatibility smart constructor for an exact package binder. -/
noncomputable def Scope.bindExact
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    {witness : LambdaPFC.Ty n}
    (witnessWf : Fragment.Wf sourceContext witness) :
    Scope
      (sourceContext.snoc (Fragment.exactPackageTy first label witness))
      ((Interface.BinderPlan.exact
        (translateType scope witnessWf) (translateType scope witnessWf)
        (payloadFamily (scope.lookup first).path.targetType))
        |>.context targetContext) :=
  scope.bindMember first label witnessWf witnessWf (.refl witnessWf)

end StaticTranslation
end LambdaPToFCo
