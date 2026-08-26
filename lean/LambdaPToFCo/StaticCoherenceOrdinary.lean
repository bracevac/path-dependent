import LambdaPToFCo.StaticCoherenceCore

namespace LambdaPToFCo
namespace StaticTranslation

open SystemFCo

namespace Scope.Coherent

/-- Extend a coherent compiler scope with an ordinary source binding. -/
noncomputable def bindOrdinary
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {sig : Sig} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    {scope : Scope sourceContext targetContext}
    (coherent : Scope.Coherent scope)
    (wf : Fragment.Wf sourceContext sourceType)
    (shape : OrdinaryShape sourceType) :
    Scope.Coherent (scope.bindOrdinary wf shape) := by
  unfold Scope.bindOrdinary
  let targetType := translateType scope wf
  let extended := Scope.ordinary scope sourceType shape targetType
  let plan := Interface.BinderPlan.ordinary targetType
  change Scope.Coherent extended
  refine {
    lookup_wf := ?_
    path_eq := ?_
    lower_eq := ?_
    upper_eq := ?_
  }
  · intro index
    refine Fin.cases ?_ (fun older => ?_) index
    · exact wf.weaken sourceType
    · exact (coherent.lookup_wf older).weaken sourceType
  · intro path pathType typing currentWf
    cases typing with
    | @var index =>
        cases index using Fin.cases with
        | zero =>
          change targetType.rename plan.weaken =
            translateType extended currentWf
          exact (translateType_weaken_ordinary scope shape targetType wf).symm.trans
            (translateType_irrel extended (wf.weaken sourceType) currentWf)
        | succ older =>
          let oldWf := coherent.lookup_wf older
          let oldPath : Fragment.PathTy sourceContext (.var older)
              (sourceContext.lookup older) := .var
          simp only [translatePath]
          rw [Scope.lookup_there_ordinary]
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
                _ = translateType extended (oldWf.weaken sourceType) :=
                  (translateType_weaken_ordinary scope shape targetType oldWf).symm
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
                _ = translateType extended (oldWf.weaken sourceType) :=
                  (translateType_weaken_ordinary scope shape targetType oldWf).symm
                _ = translateType extended currentWf :=
                  translateType_irrel extended _ _
    | exactFst member =>
        cases member with
        | @here _ parent first label lower upper =>
            exact Empty.elim (shape.notMember
              { first := first
                label := _
                lower := lower
                upper := upper
                equality := rfl })
        | @there _ _ package first label lower upper boundType oldMember =>
            let oldWf : Fragment.Wf sourceContext (.Single (.var first)) :=
              .singleton (.var (x := first))
            let oldPath := Fragment.PathTy.exactFst oldMember
            change
              ((scope.lookupMember oldMember).payloadType.rename plan.weaken) =
                translateType extended currentWf
            calc
              (scope.lookupMember oldMember).payloadType.rename plan.weaken =
                  (translateType scope oldWf).rename plan.weaken :=
                congrArg (Ty.rename · plan.weaken)
                  (coherent.path_eq oldPath oldWf)
              _ = translateType extended (oldWf.weaken sourceType) :=
                (translateType_weaken_ordinary scope shape targetType oldWf).symm
              _ = translateType extended currentWf :=
                translateType_irrel extended _ _
  · intro package first label lower upper member currentWf
    cases member with
    | @here _ parent memberFirst memberLabel memberLower memberUpper =>
        exact Empty.elim (shape.notMember
          { first := memberFirst
            label := _
            lower := memberLower
            upper := memberUpper
            equality := rfl })
    | @there _ _ package first label lower upper boundType oldMember =>
        let oldWf := coherent.memberLowerWf oldMember
        change translateType extended currentWf =
          (scope.lookupMember oldMember).lowerBound.rename plan.weaken
        calc
          translateType extended currentWf =
              translateType extended (oldWf.weaken sourceType) :=
            translateType_irrel extended _ _
          _ = (translateType scope oldWf).rename plan.weaken :=
            translateType_weaken_ordinary scope shape targetType oldWf
          _ = (scope.lookupMember oldMember).lowerBound.rename plan.weaken :=
            congrArg (Ty.rename · plan.weaken)
              (coherent.lower_eq oldMember oldWf)
  · intro package first label lower upper member currentWf
    cases member with
    | @here _ parent memberFirst memberLabel memberLower memberUpper =>
        exact Empty.elim (shape.notMember
          { first := memberFirst
            label := _
            lower := memberLower
            upper := memberUpper
            equality := rfl })
    | @there _ _ package first label lower upper boundType oldMember =>
        let oldWf := coherent.memberUpperWf oldMember
        change translateType extended currentWf =
          (scope.lookupMember oldMember).upperBound.rename plan.weaken
        calc
          translateType extended currentWf =
              translateType extended (oldWf.weaken sourceType) :=
            translateType_irrel extended _ _
          _ = (translateType scope oldWf).rename plan.weaken :=
            translateType_weaken_ordinary scope shape targetType oldWf
          _ = (scope.lookupMember oldMember).upperBound.rename plan.weaken :=
            congrArg (Ty.rename · plan.weaken)
              (coherent.upper_eq oldMember oldWf)

end Scope.Coherent

end StaticTranslation
end LambdaPToFCo
