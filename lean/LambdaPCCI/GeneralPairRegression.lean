import LambdaPCCI.CaptureSafety

/-!
Regression for unrestricted covariance of dependent pairs.

The first component of each source and target pair type is `Top`.  Stored type
and capture-set definitions are nevertheless related to intervals mentioning
the first-component binder.  The examples therefore exercise the general
pair rule for both abstract member forms.
-/

namespace LambdaPCCI.GeneralPairRegression

noncomputable section

def label : Name := 0

def pureTop (n : Nat) : Ty n := .capt .empty .Top

def source : Ty 0 :=
  .capt .empty
    (.Pair (pureTop 0) label
      (.type (.Single (.var 0)) (.Single (.var 0))))

def target : Ty 0 :=
  .capt .empty
    (.Pair (pureTop 0) label (.type .Bot .Top))

/- The helper derivations are context-polymorphic because their only free
   variable is the first-component binder introduced by the pair type. -/

private def sourceSubTarget {n : Nat} {Gamma : Ctx n} :
    Ty.Sub Gamma
      (.capt .empty
        (.Pair (pureTop n) label
          (.type (.Single (.var 0)) (.Single (.var 0)))))
      (.capt .empty
        (.Pair (pureTop n) label (.type .Bot .Top))) :=
  .capt .refl (.pair .refl (.type .bot .top .refl))

def source_sub_target : Ty.Sub .nil source target :=
  sourceSubTarget

private def pureTopWf {n : Nat} {Gamma : Ctx n} :
    Ty.Wf Gamma (pureTop n) :=
  .capt .empty .top

private def sourceWf {n : Nat} {Gamma : Ctx n} :
    Ty.Wf Gamma
      (.capt .empty
        (.Pair (pureTop n) label
          (.type (.Single (.var 0)) (.Single (.var 0))))) :=
  .capt .empty
    (.pair pureTopWf
      (.type
        (.singleton .var)
        (.singleton .var)
        .refl))

private def targetWf {n : Nat} {Gamma : Ctx n} :
    Ty.Wf Gamma
      (.capt .empty
        (.Pair (pureTop n) label (.type .Bot .Top))) :=
  .capt .empty (.pair pureTopWf (.type .bot .top .bot))

/-! ## A closed program using the rule -/

def boundResult : Ty 1 :=
  .capt (.singleton (.var 0)) (.Single (.var 0))

def boundType : Ty 0 :=
  .capt .empty (.Fun (pureTop 0) boundResult)

private def boundResultWf {n : Nat} {Gamma : Ctx n} :
    Ty.Wf (Gamma.snoc (pureTop n))
      (.capt (.singleton (.var 0)) (.Single (.var 0))) :=
  .capt (.singleton .var) (.singleton .var)

private def boundBodyTyping :
    Tm.Ty (Ctx.nil.snoc (pureTop 0))
      (.path (.var 0)) boundResult
      (.union .empty (.singleton (.var 0))) :=
  .sub
    (.path .var)
    .refl
    .union_right
    boundResultWf
    (.union .empty (.singleton .var))

private def boundTyping :
    Tm.Ty .nil
      (.abs (pureTop 0) (.path (.var 0))) boundType .empty :=
  .abs boundBodyTyping pureTopWf .empty

private def boundTypeWf {n : Nat} {Gamma : Ctx n} :
    Ty.Wf Gamma
      (.capt .empty
        (.Fun (pureTop n)
          (.capt (.singleton (.var 0)) (.Single (.var 0))))) :=
  .capt .empty (.fun pureTopWf boundResultWf)

def exactFirst : Ty 1 :=
  .capt (.singleton (.var 0)) (.Single (.var 0))

def storedShape : Shape 1 := .Single (.var 0)

def exactBodyType : Ty 1 :=
  .capt (.singleton (.var 0))
    (.Pair exactFirst label
      (.type storedShape.weaken storedShape.weaken))

private def storedShapeWf :
    Shape.Wf (Ctx.nil.snoc boundType) storedShape :=
  .singleton .var

private def exactToSource :
    Ty.Sub (Ctx.nil.snoc boundType) exactBodyType source.weaken :=
  .capt
    (.path .var)
    (.pair
      (.capt (.path .var) .top)
      (.type
        (.singleton_widen .var)
        (.singleton_alias .var)
        .refl))

private def sourceBodyTyping :
    Tm.Ty (Ctx.nil.snoc boundType)
      (.pair 0 label (.type storedShape)) source.weaken .empty :=
  .sub
    (.type_pair storedShapeWf)
    exactToSource
    .refl
    sourceWf
    .empty

private def targetBodyTyping :
    Tm.Ty (Ctx.nil.snoc boundType)
      (.pair 0 label (.type storedShape)) target.weaken .empty :=
  .sub
    sourceBodyTyping
    sourceSubTarget
    .refl
    targetWf
    .empty

def term : Tm 0 :=
  .let
    (.abs (pureTop 0) (.path (.var 0)))
    (.let
      (.pair 0 label (.type storedShape))
      (.path (.var 0)))

private def targetPathTyping :
    Tm.Ty ((Ctx.nil.snoc boundType).snoc target.weaken)
      (.path (.var 0)) target.weaken.weaken .empty :=
  .sub
    (.path .var)
    (.capt (.path .var) (.singleton_widen .var))
    (.path .var)
    targetWf
    .empty

private def targetLetTyping :
    Tm.Ty (Ctx.nil.snoc boundType)
      (.let
        (.pair 0 label (.type storedShape))
        (.path (.var 0)))
      target.weaken .empty :=
  .let targetBodyTyping targetPathTyping targetWf .empty

def term_typing : Tm.Ty .nil term target .empty := by
  unfold term
  exact .let boundTyping targetLetTyping targetWf .empty

def functionValue : Tm 0 :=
  .abs (pureTop 0) (.path (.var 0))

def typeStore1 : Store 1 :=
  .val .empty functionValue .abs

def typePairValue : Tm 1 :=
  .pair 0 label (.type storedShape)

def typeStore2 : Store 2 :=
  .val typeStore1 typePairValue .pair

def typeFinal : State 2 :=
  .mk typeStore2 [] (.path (.var 0))

def term_steps : State.Steps (State.initial term) typeFinal := by
  unfold term typeFinal typeStore2 typePairValue typeStore1 functionValue
  exact .tail .let_push
    (.tail (.allocate .abs)
      (.tail .let_push
        (.tail (.allocate .pair) .refl)))

theorem term_type_safety
    {n : Nat} {final : State n}
    (steps : State.Steps (State.initial term) final) :
    State.Progress final :=
  term_typing.closed_type_safety steps

theorem allocated_type_pair_progress : State.Progress typeFinal :=
  term_typing.closed_type_safety term_steps

/-! ## Capture-set members -/

def captureSource : Ty 0 :=
  .capt .empty
    (.Pair (pureTop 0) label
      (.capture
        (.singleton (.var 0))
        (.singleton (.var 0))))

def captureTarget : Ty 0 :=
  .capt .empty
    (.Pair (pureTop 0) label
      (.capture .empty (.singleton (.var 0))))

private def captureSourceSubCaptureTarget {n : Nat} {Gamma : Ctx n} :
    Ty.Sub Gamma
      (.capt .empty
        (.Pair (pureTop n) label
          (.capture
            (.singleton (.var 0))
            (.singleton (.var 0)))))
      (.capt .empty
        (.Pair (pureTop n) label
          (.capture .empty (.singleton (.var 0))))) :=
  .capt .refl (.pair .refl (.capture .empty .refl .refl))

def captureSource_sub_captureTarget :
    Ty.Sub .nil captureSource captureTarget :=
  captureSourceSubCaptureTarget

private def captureSourceWf {n : Nat} {Gamma : Ctx n} :
    Ty.Wf Gamma
      (.capt .empty
        (.Pair (pureTop n) label
          (.capture
            (.singleton (.var 0))
            (.singleton (.var 0))))) :=
  .capt .empty
    (.pair pureTopWf
      (.capture
        (.singleton .var)
        (.singleton .var)
        .refl))

private def captureTargetWf {n : Nat} {Gamma : Ctx n} :
    Ty.Wf Gamma
      (.capt .empty
        (.Pair (pureTop n) label
          (.capture .empty (.singleton (.var 0))))) :=
  .capt .empty
    (.pair pureTopWf
      (.capture .empty (.singleton .var) .empty))

def storedCapture : CaptureSet 1 := .singleton (.var 0)

def exactCaptureBodyType : Ty 1 :=
  .capt (.singleton (.var 0))
    (.Pair exactFirst label
      (.capture storedCapture.weaken storedCapture.weaken))

private def storedCaptureWf :
    CaptureSet.Wf (Ctx.nil.snoc boundType) storedCapture :=
  .singleton .var

private def exactCaptureToSource :
    Ty.Sub (Ctx.nil.snoc boundType)
      exactCaptureBodyType captureSource.weaken :=
  .capt
    (.path .var)
    (.pair
      (.capt (.path .var) .top)
      (.capture
        (.path .var)
        (.alias .var)
        .refl))

private def captureSourceBodyTyping :
    Tm.Ty (Ctx.nil.snoc boundType)
      (.pair 0 label (.capture storedCapture))
      captureSource.weaken .empty :=
  .sub
    (.capture_pair storedCaptureWf)
    exactCaptureToSource
    .refl
    captureSourceWf
    .empty

private def captureTargetBodyTyping :
    Tm.Ty (Ctx.nil.snoc boundType)
      (.pair 0 label (.capture storedCapture))
      captureTarget.weaken .empty :=
  .sub
    captureSourceBodyTyping
    captureSourceSubCaptureTarget
    .refl
    captureTargetWf
    .empty

def captureTerm : Tm 0 :=
  .let
    (.abs (pureTop 0) (.path (.var 0)))
    (.let
      (.pair 0 label (.capture storedCapture))
      (.path (.var 0)))

private def captureTargetPathTyping :
    Tm.Ty ((Ctx.nil.snoc boundType).snoc captureTarget.weaken)
      (.path (.var 0)) captureTarget.weaken.weaken .empty :=
  .sub
    (.path .var)
    (.capt (.path .var) (.singleton_widen .var))
    (.path .var)
    captureTargetWf
    .empty

private def captureTargetLetTyping :
    Tm.Ty (Ctx.nil.snoc boundType)
      (.let
        (.pair 0 label (.capture storedCapture))
        (.path (.var 0)))
      captureTarget.weaken .empty :=
  .let captureTargetBodyTyping captureTargetPathTyping
    captureTargetWf .empty

def captureTerm_typing :
    Tm.Ty .nil captureTerm captureTarget .empty := by
  unfold captureTerm
  exact .let boundTyping captureTargetLetTyping captureTargetWf .empty

def capturePairValue : Tm 1 :=
  .pair 0 label (.capture storedCapture)

def captureStore2 : Store 2 :=
  .val typeStore1 capturePairValue .pair

def captureFinal : State 2 :=
  .mk captureStore2 [] (.path (.var 0))

def captureTerm_steps :
    State.Steps (State.initial captureTerm) captureFinal := by
  unfold captureTerm captureFinal captureStore2 capturePairValue typeStore1
    functionValue
  exact .tail .let_push
    (.tail (.allocate .abs)
      (.tail .let_push
        (.tail (.allocate .pair) .refl)))

theorem captureTerm_type_safety
    {n : Nat} {final : State n}
    (steps : State.Steps (State.initial captureTerm) final) :
    State.Progress final :=
  captureTerm_typing.closed_type_safety steps

theorem allocated_capture_pair_progress : State.Progress captureFinal :=
  captureTerm_typing.closed_type_safety captureTerm_steps

/-! ## Resolving an abstract capture-set selection -/

private def exactCapturePairTyping :
    Tm.Ty (Ctx.nil.snoc boundType)
      (.pair 0 label (.capture storedCapture))
      exactCaptureBodyType .empty :=
  .capture_pair storedCaptureWf

private def exactCaptureMember :
    Path.Ty
      ((Ctx.nil.snoc boundType).snoc exactCaptureBodyType)
      ((Path.var 0).sel label)
      (.capture
        (.singleton (.var 1))
        (.singleton (.var 1))) := by
  have receiver :
      Path.Ty
        ((Ctx.nil.snoc boundType).snoc exactCaptureBodyType)
        (.var 0) (.term exactCaptureBodyType.weaken) :=
    .var
  simpa [exactCaptureBodyType, exactFirst, storedCapture, label,
    Ctx.lookup, Ty.weaken, Ty.rename, Shape.rename, Tau.rename,
    CaptureSet.weaken, CaptureSet.rename, Path.rename, Tau.open,
    Tau.subst, CaptureSet.subst, Path.subst, PathSubst.openAt] using
    Path.Ty.sel_r receiver

private def captureSelectionToEmpty :
    CaptureSet.Sub
      ((Ctx.nil.snoc boundType).snoc exactCaptureBodyType)
      (.singleton (.var 1)) .empty :=
  .trans
    (.select_lower exactCaptureMember .refl)
    (.trans
      (.select_upper exactCaptureMember .refl)
      (.path (.var (x := 1))))

private def selectedCaptureBodyTyping :
    Tm.Ty
      ((Ctx.nil.snoc boundType).snoc exactCaptureBodyType)
      (.path (.var 1)) boundType.weaken.weaken .empty :=
  .sub
    (.path (.var (x := 1)))
    (.capt
      (.path (.var (x := 1)))
      (.singleton_widen (.var (x := 1))))
    captureSelectionToEmpty
    boundTypeWf
    .empty

private def captureSelectionLetTyping :
    Tm.Ty (Ctx.nil.snoc boundType)
      (.let
        (.pair 0 label (.capture storedCapture))
        (.path (.var 1)))
      boundType.weaken .empty :=
  .let exactCapturePairTyping selectedCaptureBodyTyping
    boundTypeWf .empty

def captureSelectionTerm : Tm 0 :=
  .let
    functionValue
    (.let
      (.pair 0 label (.capture storedCapture))
      (.path (.var 1)))

def captureSelectionTerm_typing :
    Tm.Ty .nil captureSelectionTerm boundType .empty := by
  unfold captureSelectionTerm
  exact .let boundTyping captureSelectionLetTyping boundTypeWf .empty

def captureSelectionFinal : State 2 :=
  .mk captureStore2 [] (.path (.var 1))

def captureSelectionTerm_steps :
    State.Steps (State.initial captureSelectionTerm)
      captureSelectionFinal := by
  unfold captureSelectionTerm captureSelectionFinal captureStore2
    capturePairValue typeStore1 functionValue
  exact .tail .let_push
    (.tail (.allocate .abs)
      (.tail .let_push
        (.tail (.allocate .pair) .refl)))

theorem selected_capture_member_progress :
    State.Progress captureSelectionFinal :=
  captureSelectionTerm_typing.closed_type_safety
    captureSelectionTerm_steps

end
end LambdaPCCI.GeneralPairRegression
