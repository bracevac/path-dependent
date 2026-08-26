import LambdaPToFCo.StaticCoherenceOrdinary

namespace LambdaPToFCo
namespace StaticTranslation

/-- A member in an older binding, with just the equations introduced by
crossing one source binder. -/
structure OlderMember
    {n : Nat} (base : LambdaPFC.Ctx n) (package : Fin n)
    (label : LambdaPFC.Name)
    (lower upper : LambdaPFC.Ty (n + 1))
    (first : Fin (n + 1)) : Type where
  oldLower : LambdaPFC.Ty n
  oldUpper : LambdaPFC.Ty n
  oldFirst : Fin n
  old : Fragment.BoundMember base package label oldLower oldUpper oldFirst
  lowerEq : oldLower.weaken = lower
  upperEq : oldUpper.weaken = upper
  firstEq : oldFirst.succ = first

noncomputable def olderMemberAux
    {n : Nat} {memberContext : LambdaPFC.Ctx (n + 1)}
    {base : LambdaPFC.Ctx n} {boundType : LambdaPFC.Ty n}
    {memberPackage : Fin (n + 1)} {package : Fin n}
    {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty (n + 1)} {first : Fin (n + 1)}
    (member : Fragment.BoundMember memberContext memberPackage label
      lower upper first)
    (packageEq : memberPackage = package.succ)
    (contextEq : memberContext = base.snoc boundType) :
    OlderMember base package label lower upper first := by
  cases member with
  | @here n parent oldFirst label oldLower oldUpper =>
      cases packageEq
  | @there n parent oldPackage oldFirst label oldLower oldUpper U old =>
      have oldPackageEq := Fin.succ_inj.mp packageEq
      cases oldPackageEq
      have parentEq := (LambdaPFC.Ctx.snoc.inj contextEq).1
      cases parentEq
      exact
        { oldLower := oldLower
          oldUpper := oldUpper
          oldFirst := oldFirst
          old := old
          lowerEq := rfl
          upperEq := rfl
          firstEq := rfl }

noncomputable def olderMember
    {n : Nat} {base : LambdaPFC.Ctx n} {boundType : LambdaPFC.Ty n}
    {package : Fin n} {label : LambdaPFC.Name}
    {lower upper : LambdaPFC.Ty (n + 1)} {first : Fin (n + 1)}
    (member : Fragment.BoundMember (base.snoc boundType) package.succ
      label lower upper first) :
    OlderMember base package label lower upper first :=
  olderMemberAux member rfl rfl

end StaticTranslation
end LambdaPToFCo
