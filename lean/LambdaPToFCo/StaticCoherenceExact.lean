import LambdaPToFCo.StaticCoherenceMemberView

/-!
Coherence preservation for an interval-package binder. The fresh package is
represented by its complete target interface; older slots are renamed through
that interface plan. `OlderMember` isolates the one-step source equalities
needed in the dependent member cases.
-/

namespace LambdaPToFCo.StaticTranslation
open SystemFCo

namespace Scope.Coherent

/-- Extend a coherent compiler scope with an interval-package binding. -/
noncomputable def bindMember
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    (coherent : Scope.Coherent scope)
    (first : Fin n) (label : LambdaPFC.Name)
    {lower upper : LambdaPFC.Ty n}
    (lowerWf : Fragment.Wf sourceContext lower)
    (upperWf : Fragment.Wf sourceContext upper)
    (nonempty : Fragment.Sub sourceContext lower upper) :
    Scope.Coherent
      (scope.bindMember first label lowerWf upperWf nonempty) := by
  unfold Scope.bindMember
  let boundType := Fragment.memberPackageTy first label lower upper
  let targetLower := translateType scope lowerWf
  let targetUpper := translateType scope upperWf
  let targetFirst := (scope.lookup first).path.targetType
  let plan := Interface.BinderPlan.exact targetLower targetUpper
    (payloadFamily targetFirst)
  let extended := Scope.member scope first label lower upper lowerWf upperWf
    nonempty targetLower targetUpper targetFirst
  change Scope.Coherent extended
  refine {
    lookup_wf := ?_
    path_eq := ?_
    lower_eq := ?_
    upper_eq := ?_
  }
  · intro index
    refine Fin.cases ?_ (fun older => ?_) index
    · exact (Fragment.Wf.memberPackage lowerWf upperWf nonempty).weaken
        boundType
    · exact (coherent.lookup_wf older).weaken boundType
  · intro path pathType typing currentWf
    cases typing with
    | @var index =>
        cases index using Fin.cases with
        | zero =>
          let packageWf : Fragment.Wf sourceContext boundType :=
            .memberPackage lowerWf upperWf nonempty
          change (Ty.member targetLower targetUpper
              (payloadFamily targetFirst)).rename plan.weaken =
            translateType extended currentWf
          exact
            (translateType_weaken_member scope first label lower upper lowerWf
              upperWf nonempty targetLower targetUpper targetFirst
              packageWf).symm.trans
            (translateType_irrel extended (packageWf.weaken boundType)
              currentWf)
        | succ older =>
          let oldWf := coherent.lookup_wf older
          let oldPath : Fragment.PathTy sourceContext (.var older)
              (sourceContext.lookup older) := .var
          simp only [translatePath]
          rw [Scope.lookup_there_member]
          cases slotEq : scope.lookup older with
          | ordinary oldSlot =>
              have baseEq := coherent.path_eq oldPath oldWf
              dsimp [oldPath] at baseEq
              change (scope.lookup older).path.targetType =
                translateType scope oldWf at baseEq
              rw [slotEq] at baseEq
              change oldSlot.targetType.rename plan.weaken =
                translateType extended currentWf
              calc
                oldSlot.targetType.rename plan.weaken =
                    (translateType scope oldWf).rename plan.weaken :=
                  congrArg (Ty.rename · plan.weaken) baseEq
                _ = translateType extended (oldWf.weaken boundType) :=
                  (translateType_weaken_member scope first label lower upper
                    lowerWf upperWf nonempty targetLower targetUpper
                    targetFirst oldWf).symm
                _ = translateType extended currentWf :=
                  translateType_irrel extended _ _
          | exact oldSlot =>
              have baseEq := coherent.path_eq oldPath oldWf
              dsimp [oldPath] at baseEq
              change (scope.lookup older).path.targetType =
                translateType scope oldWf at baseEq
              rw [slotEq] at baseEq
              change oldSlot.rawType.rename plan.weaken =
                translateType extended currentWf
              calc
                oldSlot.rawType.rename plan.weaken =
                    (translateType scope oldWf).rename plan.weaken :=
                  congrArg (Ty.rename · plan.weaken) baseEq
                _ = translateType extended (oldWf.weaken boundType) :=
                  (translateType_weaken_member scope first label lower upper
                    lowerWf upperWf nonempty targetLower targetUpper
                    targetFirst oldWf).symm
                _ = translateType extended currentWf :=
                  translateType_irrel extended _ _
    | @exactFst package memberFirst memberLabel memberLower memberUpper
        member =>
        cases package using Fin.cases with
        | zero =>
            have memberTypeEq := member.lookup_eq
            change boundType.weaken =
              Fragment.memberPackageTy memberFirst memberLabel memberLower
                memberUpper
              at memberTypeEq
            have storedEq :
                Fragment.memberPackageTy first.succ label lower.weaken
                    upper.weaken =
                  Fragment.memberPackageTy memberFirst memberLabel memberLower
                    memberUpper := by
              rw [← memberTypeEq]
              change Fragment.memberPackageTy first.succ label lower.weaken
                  upper.weaken =
                (Fragment.memberPackageTy first label lower upper).weaken
              exact (Fragment.memberPackageTy_rename first label lower upper
                LambdaPFC.FinFun.weaken).symm
            have parts := Fragment.memberPackageTy_injective storedEq
            let newest := Fragment.BoundMember.here
              (Γ := sourceContext) (first := first) (label := label)
              (lower := lower) (upper := upper)
            have slotEq := Scope.lookupMember_irrel extended member newest
            change (extended.lookupMember member).payloadType =
              translateType extended currentWf
            rw [slotEq]
            change
              (payloadFamily targetFirst).rename
                  (Interface.BinderPlan.payloadWeaken targetLower
                    targetUpper (payloadFamily targetFirst)) =
                translateType extended currentWf
            rw [payloadFamily_rename_exact]
            let firstPath : Fragment.PathTy sourceContext (.var first)
                (sourceContext.lookup first) := .var
            let firstWf : Fragment.Wf sourceContext
                (.Single (.var first)) := .singleton firstPath
            have singletonEq :
                (LambdaPFC.Ty.Single (.var first.succ)) =
                  .Single (.var memberFirst) :=
              congrArg (fun index => LambdaPFC.Ty.Single (.var index))
                parts.1
            calc
              targetFirst.rename plan.weaken =
                  (translateType scope firstWf).rename plan.weaken :=
                rfl
              _ = translateType extended (firstWf.weaken boundType) :=
                (translateType_weaken_member scope first label lower upper
                  lowerWf upperWf nonempty targetLower targetUpper targetFirst
                  firstWf).symm
              _ = translateType extended currentWf :=
                translateType_irrel_of_type_eq extended
                  (firstWf.weaken boundType) currentWf singletonEq
        | succ oldPackage =>
            let older := olderMember member
            have slotEq := Scope.lookupMember_irrel extended member
              older.old.there
            change (extended.lookupMember member).payloadType =
              translateType extended currentWf
            rw [slotEq]
            change (scope.lookupMember older.old).payloadType.rename
              plan.weaken = translateType extended currentWf
            let oldWf : Fragment.Wf sourceContext
                (.Single (.var older.oldFirst)) :=
              .singleton (.var (x := older.oldFirst))
            let oldPath := Fragment.PathTy.exactFst older.old
            have singletonEq :
                (LambdaPFC.Ty.Single (.var older.oldFirst.succ)) =
                  .Single (.var memberFirst) :=
              congrArg (fun index => LambdaPFC.Ty.Single (.var index))
                older.firstEq
            calc
              (scope.lookupMember older.old).payloadType.rename plan.weaken =
                  (translateType scope oldWf).rename plan.weaken :=
                congrArg (Ty.rename · plan.weaken)
                  (coherent.path_eq oldPath oldWf)
              _ = translateType extended (oldWf.weaken boundType) :=
                (translateType_weaken_member scope first label lower upper
                  lowerWf upperWf nonempty targetLower targetUpper targetFirst
                  oldWf).symm
              _ = translateType extended currentWf :=
                translateType_irrel_of_type_eq extended
                  (oldWf.weaken boundType) currentWf singletonEq
  · intro package memberFirst memberLabel memberLower memberUpper member
      currentWf
    cases package using Fin.cases with
    | zero =>
        have memberTypeEq := member.lookup_eq
        change boundType.weaken =
          Fragment.memberPackageTy memberFirst memberLabel memberLower
            memberUpper
          at memberTypeEq
        have storedEq :
            Fragment.memberPackageTy first.succ label lower.weaken
                upper.weaken =
              Fragment.memberPackageTy memberFirst memberLabel memberLower
                memberUpper := by
          rw [← memberTypeEq]
          change Fragment.memberPackageTy first.succ label lower.weaken
              upper.weaken =
            (Fragment.memberPackageTy first label lower upper).weaken
          exact (Fragment.memberPackageTy_rename first label lower upper
            LambdaPFC.FinFun.weaken).symm
        have parts := Fragment.memberPackageTy_injective storedEq
        let newest := Fragment.BoundMember.here
          (Γ := sourceContext) (first := first) (label := label)
          (lower := lower) (upper := upper)
        have slotEq := Scope.lookupMember_irrel extended member newest
        rw [slotEq]
        change translateType extended currentWf =
          targetLower.rename plan.weaken
        calc
          translateType extended currentWf =
              translateType extended (lowerWf.weaken boundType) :=
            translateType_irrel_of_type_eq extended currentWf
              (lowerWf.weaken boundType) parts.2.2.1.symm
          _ = targetLower.rename plan.weaken :=
            translateType_weaken_member scope first label lower upper lowerWf
              upperWf nonempty targetLower targetUpper targetFirst lowerWf
    | succ oldPackage =>
        let older := olderMember member
        let oldWf := coherent.memberLowerWf older.old
        have slotEq := Scope.lookupMember_irrel extended member older.old.there
        rw [slotEq]
        change translateType extended currentWf =
          (scope.lookupMember older.old).lowerBound.rename plan.weaken
        calc
          translateType extended currentWf =
              translateType extended (oldWf.weaken boundType) :=
            translateType_irrel_of_type_eq extended currentWf
              (oldWf.weaken boundType) older.lowerEq.symm
          _ = (translateType scope oldWf).rename plan.weaken :=
            translateType_weaken_member scope first label lower upper lowerWf
              upperWf nonempty targetLower targetUpper targetFirst oldWf
          _ = (scope.lookupMember older.old).lowerBound.rename plan.weaken :=
            congrArg (Ty.rename · plan.weaken)
              (coherent.lower_eq older.old oldWf)
  · intro package memberFirst memberLabel memberLower memberUpper member
      currentWf
    cases package using Fin.cases with
    | zero =>
        have memberTypeEq := member.lookup_eq
        change boundType.weaken =
          Fragment.memberPackageTy memberFirst memberLabel memberLower
            memberUpper
          at memberTypeEq
        have storedEq :
            Fragment.memberPackageTy first.succ label lower.weaken
                upper.weaken =
              Fragment.memberPackageTy memberFirst memberLabel memberLower
                memberUpper := by
          rw [← memberTypeEq]
          change Fragment.memberPackageTy first.succ label lower.weaken
              upper.weaken =
            (Fragment.memberPackageTy first label lower upper).weaken
          exact (Fragment.memberPackageTy_rename first label lower upper
            LambdaPFC.FinFun.weaken).symm
        have parts := Fragment.memberPackageTy_injective storedEq
        let newest := Fragment.BoundMember.here
          (Γ := sourceContext) (first := first) (label := label)
          (lower := lower) (upper := upper)
        have slotEq := Scope.lookupMember_irrel extended member newest
        rw [slotEq]
        change translateType extended currentWf =
          targetUpper.rename plan.weaken
        calc
          translateType extended currentWf =
              translateType extended (upperWf.weaken boundType) :=
            translateType_irrel_of_type_eq extended currentWf
              (upperWf.weaken boundType) parts.2.2.2.symm
          _ = targetUpper.rename plan.weaken :=
            translateType_weaken_member scope first label lower upper lowerWf
              upperWf nonempty targetLower targetUpper targetFirst upperWf
    | succ oldPackage =>
        let older := olderMember member
        let oldWf := coherent.memberUpperWf older.old
        have slotEq := Scope.lookupMember_irrel extended member older.old.there
        rw [slotEq]
        change translateType extended currentWf =
          (scope.lookupMember older.old).upperBound.rename plan.weaken
        calc
          translateType extended currentWf =
              translateType extended (oldWf.weaken boundType) :=
            translateType_irrel_of_type_eq extended currentWf
              (oldWf.weaken boundType) older.upperEq.symm
          _ = (translateType scope oldWf).rename plan.weaken :=
            translateType_weaken_member scope first label lower upper lowerWf
              upperWf nonempty targetLower targetUpper targetFirst oldWf
          _ = (scope.lookupMember older.old).upperBound.rename plan.weaken :=
            congrArg (Ty.rename · plan.weaken)
              (coherent.upper_eq older.old oldWf)

/-- Compatibility theorem for the exact-bound specialization. -/
noncomputable def bindExact
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {scope : Scope sourceContext targetContext}
    (coherent : Scope.Coherent scope)
    (first : Fin n) (label : LambdaPFC.Name)
    {witness : LambdaPFC.Ty n}
    (witnessWf : Fragment.Wf sourceContext witness) :
    Scope.Coherent (scope.bindExact first label witnessWf) :=
  coherent.bindMember first label witnessWf witnessWf (.refl witnessWf)

end Scope.Coherent
end LambdaPToFCo.StaticTranslation
