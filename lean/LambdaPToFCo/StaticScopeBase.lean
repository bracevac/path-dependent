import LambdaPToFCo.StaticSlots

namespace LambdaPToFCo
namespace StaticTranslation

open SystemFCo

structure MemberShape (sourceType : LambdaPFC.Ty n) : Type where
  first : Fin n
  label : LambdaPFC.Name
  lower : LambdaPFC.Ty n
  upper : LambdaPFC.Ty n
  equality : sourceType =
    Fragment.memberPackageTy first label lower upper

def NotMember (sourceType : LambdaPFC.Ty n) : Type :=
  MemberShape sourceType -> Empty

/-- Exactly the source forms represented by one ordinary target variable. -/
inductive OrdinaryShape : LambdaPFC.Ty n -> Type where
| top : OrdinaryShape .Top
| singleton : OrdinaryShape (.Single path)
| selection : OrdinaryShape (.TSel path label)
| arrow : OrdinaryShape (.Fun domain codomain)

namespace OrdinaryShape

def notMember : OrdinaryShape sourceType -> NotMember sourceType
| .top, ⟨_, _, _, _, equality⟩ => by cases equality
| .singleton, ⟨_, _, _, _, equality⟩ => by cases equality
| .selection, ⟨_, _, _, _, equality⟩ => by cases equality
| .arrow, ⟨_, _, _, _, equality⟩ => by cases equality

end OrdinaryShape

/-- The one relation between a dependent source context and the mixed target
telescope. Member nodes retain canonical source well-formedness and interval
validity derivations. -/
inductive Scope : {n : Nat} -> LambdaPFC.Ctx n ->
    {sig : Sig} -> Ctx sig -> Type where
| empty : Scope .nil .empty
| ordinary {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (sourceType : LambdaPFC.Ty n) (shape : OrdinaryShape sourceType)
    (targetType : Ty sig) :
    Scope (sourceContext.snoc sourceType)
      ((Interface.BinderPlan.ordinary targetType).context targetContext)
| member {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    (lower upper : LambdaPFC.Ty n)
    (lowerWf : Fragment.Wf sourceContext lower)
    (upperWf : Fragment.Wf sourceContext upper)
    (nonempty : Fragment.Sub sourceContext lower upper)
    (targetLower targetUpper targetFirst : Ty sig) :
    Scope
      (sourceContext.snoc
        (Fragment.memberPackageTy first label lower upper))
      ((Interface.BinderPlan.exact targetLower targetUpper
        (payloadFamily targetFirst)).context targetContext)

namespace Scope

noncomputable def lookup : {n : Nat} ->
    {sourceContext : LambdaPFC.Ctx n} -> {sig : Sig} ->
    {targetContext : Ctx sig} ->
    Scope sourceContext targetContext -> Fin n ->
    TypedInterfaceSlot targetContext
| _, _, _, _, .empty, index => Fin.elim0 index
| _, _, _, _, .ordinary scope sourceType _shape targetType, index =>
    Fin.cases
      (.ordinary (newestOrdinary _ targetType))
      (fun older =>
        (lookup scope older).rename
          ((Interface.BinderPlan.ordinary targetType).weakenTyped _))
      index
| _, _, _, _,
    .member scope first label lower upper _lowerWf _upperWf _nonempty
      targetLower targetUpper targetFirst,
    index =>
    let plan := Interface.BinderPlan.exact targetLower targetUpper
      (payloadFamily targetFirst)
    Fin.cases
      (.exact (newestExact _ targetLower targetUpper
        (payloadFamily targetFirst)))
      (fun older =>
        (lookup scope older).rename (plan.weakenTyped _))
      index

@[simp] theorem lookup_here_ordinary
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (sourceType : LambdaPFC.Ty n) (shape : OrdinaryShape sourceType)
    (targetType : Ty sig) :
    lookup (.ordinary scope sourceType shape targetType) 0 =
      .ordinary (newestOrdinary targetContext targetType) := rfl

@[simp] theorem lookup_there_ordinary
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (sourceType : LambdaPFC.Ty n) (shape : OrdinaryShape sourceType)
    (targetType : Ty sig) (index : Fin n) :
    lookup (.ordinary scope sourceType shape targetType) index.succ =
      (lookup scope index).rename
        ((Interface.BinderPlan.ordinary targetType).weakenTyped
          targetContext) := rfl

@[simp] theorem lookup_here_member
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    (lower upper : LambdaPFC.Ty n)
    (lowerWf : Fragment.Wf sourceContext lower)
    (upperWf : Fragment.Wf sourceContext upper)
    (nonempty : Fragment.Sub sourceContext lower upper)
    (targetLower targetUpper targetFirst : Ty sig) :
    lookup
        (.member scope first label lower upper lowerWf upperWf nonempty
          targetLower targetUpper targetFirst)
        0 =
      .exact (newestExact targetContext targetLower targetUpper
        (payloadFamily targetFirst)) := rfl

@[simp] theorem lookup_there_member
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    (scope : Scope sourceContext targetContext)
    (first : Fin n) (label : LambdaPFC.Name)
    (lower upper : LambdaPFC.Ty n)
    (lowerWf : Fragment.Wf sourceContext lower)
    (upperWf : Fragment.Wf sourceContext upper)
    (nonempty : Fragment.Sub sourceContext lower upper)
    (targetLower targetUpper targetFirst : Ty sig) (index : Fin n) :
    lookup
        (.member scope first label lower upper lowerWf upperWf nonempty
          targetLower targetUpper targetFirst)
        index.succ =
      (lookup scope index).rename
        ((Interface.BinderPlan.exact targetLower targetUpper
          (payloadFamily targetFirst)).weakenTyped targetContext) := rfl

end Scope

def topNotMember : NotMember (.Top : LambdaPFC.Ty n) :=
  OrdinaryShape.top.notMember

def singletonNotMember (path : LambdaPFC.Path n) :
    NotMember (.Single path) := OrdinaryShape.singleton.notMember

def selectionNotMember (path : LambdaPFC.Path n)
    (label : LambdaPFC.Name) : NotMember (.TSel path label) :=
  OrdinaryShape.selection.notMember

def arrowNotMember (domain : LambdaPFC.Ty n)
    (codomain : LambdaPFC.Ty (n + 1)) : NotMember (.Fun domain codomain) :=
  OrdinaryShape.arrow.notMember

end StaticTranslation
end LambdaPToFCo
