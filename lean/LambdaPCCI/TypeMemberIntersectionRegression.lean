import LambdaPCCI.IntersectionRegression

/-!
A capture-aware mirror of the abstract type-member intersection regression.
Writing only the shape components of its empty-capture types:

```text
F    = Top -> Top
S    = Top -> F
L    = F -> F
R    = F
Q(U) = { A : S..U }

v : S
r : Q(L) ∧ Q(R) = { A = S }
q : Q(L ∧ R)   = r
in v v
```

The precise alias `q` exposes `q.A : S..(L ∧ R)`.  Both occurrences of
`v` first cross the lower bound, then use the left and right projections of
the merged upper bound for a closed self-application.  Every exposed capture
and use set is empty.
-/

namespace LambdaPCCI.TypeMemberIntersectionRegression

noncomputable section

def typeLabel : Name := 0

def recordShape (lower upper : Shape (n + 1)) : Shape n :=
  .Pair (IntersectionRegression.pureTop n) typeLabel (.type lower upper)

def sourceRecord (n : Nat) : Ty n :=
  .capt .empty
    (recordShape
      (IntersectionRegression.sourceShape (n + 1))
      (IntersectionRegression.sourceShape (n + 1)))

def leftRecord (n : Nat) : Ty n :=
  .capt .empty
    (recordShape
      (IntersectionRegression.sourceShape (n + 1))
      (IntersectionRegression.leftViewShape (n + 1)))

def rightRecord (n : Nat) : Ty n :=
  .capt .empty
    (recordShape
      (IntersectionRegression.sourceShape (n + 1))
      (IntersectionRegression.rightViewShape (n + 1)))

def recordIntersection (n : Nat) : Ty n :=
  .capt .empty
    (.Inter
      (recordShape
        (IntersectionRegression.sourceShape (n + 1))
        (IntersectionRegression.leftViewShape (n + 1)))
      (recordShape
        (IntersectionRegression.sourceShape (n + 1))
        (IntersectionRegression.rightViewShape (n + 1))))

def mergedRecord (n : Nat) : Ty n :=
  .capt .empty
    (recordShape
      (IntersectionRegression.sourceShape (n + 1))
      (IntersectionRegression.intersectionShape (n + 1)))

private def pureTopWf {Gamma : Ctx n} :
    Ty.Wf Gamma (IntersectionRegression.pureTop n) :=
  .capt .empty .top

private def functionShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma (IntersectionRegression.functionShape n) :=
  .fun pureTopWf pureTopWf

private def sourceShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma (IntersectionRegression.sourceShape n) :=
  .fun pureTopWf (by
    simpa [IntersectionRegression.functionType,
      IntersectionRegression.functionShape] using
      (IntersectionRegression.functionTypeWf
        (Gamma := Gamma.snoc (IntersectionRegression.pureTop n))))

private def leftViewShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma (IntersectionRegression.leftViewShape n) :=
  .fun IntersectionRegression.functionTypeWf (by
    simpa [IntersectionRegression.functionType,
      IntersectionRegression.functionShape] using
      (IntersectionRegression.functionTypeWf
        (Gamma := Gamma.snoc (IntersectionRegression.functionType n))))

private def rightViewShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma (IntersectionRegression.rightViewShape n) :=
  functionShapeWf

private def intersectionShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma (IntersectionRegression.intersectionShape n) :=
  .inter leftViewShapeWf rightViewShapeWf

private def sourceShapeToIntersection {Gamma : Ctx n} :
    Shape.Sub Gamma
      (IntersectionRegression.sourceShape n)
      (IntersectionRegression.intersectionShape n) :=
  .inter IntersectionRegression.sourceToLeft
    IntersectionRegression.sourceToRight

private def sourceRecordWf {Gamma : Ctx n} :
    Ty.Wf Gamma (sourceRecord n) :=
  .capt .empty
    (.pair pureTopWf (.type sourceShapeWf sourceShapeWf .refl))

private def leftRecordWf {Gamma : Ctx n} :
    Ty.Wf Gamma (leftRecord n) :=
  .capt .empty
    (.pair pureTopWf
      (.type sourceShapeWf leftViewShapeWf
        IntersectionRegression.sourceToLeft))

private def rightRecordWf {Gamma : Ctx n} :
    Ty.Wf Gamma (rightRecord n) :=
  .capt .empty
    (.pair pureTopWf
      (.type sourceShapeWf rightViewShapeWf
        IntersectionRegression.sourceToRight))

private def recordIntersectionWf {Gamma : Ctx n} :
    Ty.Wf Gamma (recordIntersection n) :=
  .capt .empty
    (.inter
      (.pair pureTopWf
        (.type sourceShapeWf leftViewShapeWf
          IntersectionRegression.sourceToLeft))
      (.pair pureTopWf
        (.type sourceShapeWf rightViewShapeWf
          IntersectionRegression.sourceToRight)))

private def mergedRecordWf {Gamma : Ctx n} :
    Ty.Wf Gamma (mergedRecord n) :=
  .capt .empty
    (.pair pureTopWf
      (.type sourceShapeWf intersectionShapeWf sourceShapeToIntersection))

private def sourceShapeToLeftRecordShape {Gamma : Ctx n} :
    Shape.Sub Gamma
      (recordShape
        (IntersectionRegression.sourceShape (n + 1))
        (IntersectionRegression.sourceShape (n + 1)))
      (recordShape
        (IntersectionRegression.sourceShape (n + 1))
        (IntersectionRegression.leftViewShape (n + 1))) :=
  .pair .refl
    (.type .refl IntersectionRegression.sourceToLeft .refl)

private def sourceShapeToRightRecordShape {Gamma : Ctx n} :
    Shape.Sub Gamma
      (recordShape
        (IntersectionRegression.sourceShape (n + 1))
        (IntersectionRegression.sourceShape (n + 1)))
      (recordShape
        (IntersectionRegression.sourceShape (n + 1))
        (IntersectionRegression.rightViewShape (n + 1))) :=
  .pair .refl
    (.type .refl IntersectionRegression.sourceToRight .refl)

private def sourceRecordToIntersection {Gamma : Ctx n} :
    Ty.Sub Gamma (sourceRecord n) (recordIntersection n) :=
  .capt .refl
    (.inter sourceShapeToLeftRecordShape sourceShapeToRightRecordShape)

private def recordIntersectionToMerged {Gamma : Ctx n} :
    Ty.Sub Gamma (recordIntersection n) (mergedRecord n) :=
  .capt .refl .pair_type_inter

/-! ## Closed program -/

def value : Tm 0 :=
  IntersectionRegression.value

/-- Store the exact witness `A = S`. -/
def recordValue : Tm 1 :=
  .pair 0 typeLabel (.type (IntersectionRegression.sourceShape 1))

/-- A single empty-use alias at the merged record type. -/
def mergedRecordAlias : Tm 2 :=
  .path (.var 0)

def body : Tm 3 :=
  .app (.var 2) (.var 2)

def term : Tm 0 :=
  .let value
    (.let recordValue
      (.let mergedRecordAlias body))

private def context1 : Ctx 1 :=
  Ctx.nil.snoc (IntersectionRegression.sourceType 0)

private def context2 : Ctx 2 :=
  context1.snoc (recordIntersection 1)

private def context3 : Ctx 3 :=
  context2.snoc (mergedRecord 2)

private def innerBodyTyping :
    Tm.Ty ((Ctx.nil.snoc (IntersectionRegression.pureTop 0)).snoc
      (IntersectionRegression.pureTop 1))
      (.path (.var 0)) (IntersectionRegression.pureTop 2)
      (.union .empty (.singleton (.var 0))) :=
  .sub
    (.path .var)
    (.capt (.path .var) .top)
    .union_right
    pureTopWf
    (.union .empty (.singleton .var))

private def innerValueTyping :
    Tm.Ty (Ctx.nil.snoc (IntersectionRegression.pureTop 0))
      (.abs (IntersectionRegression.pureTop 1) (.path (.var 0)))
      (IntersectionRegression.functionType 1) .empty :=
  .abs innerBodyTyping pureTopWf .empty

private def outerBodyTyping :
    Tm.Ty (Ctx.nil.snoc (IntersectionRegression.pureTop 0))
      (.abs (IntersectionRegression.pureTop 1) (.path (.var 0)))
      (IntersectionRegression.functionType 0).weaken
      (.union .empty (.singleton (.var 0))) := by
  apply Tm.Ty.sub
  · simpa [IntersectionRegression.functionType,
      IntersectionRegression.functionShape] using innerValueTyping
  · exact .refl
  · exact .empty
  · simpa [IntersectionRegression.functionType,
      IntersectionRegression.functionShape] using
      (IntersectionRegression.functionTypeWf
        (Gamma := Ctx.nil.snoc (IntersectionRegression.pureTop 0)))
  · exact .union .empty (.singleton .var)

private def valueSourceTyping :
    Tm.Ty Ctx.nil value (IntersectionRegression.sourceType 0) .empty :=
  .abs outerBodyTyping pureTopWf .empty

private def valuePathInContext1 :
    Path.Ty context1 (.var 0)
      (.term (IntersectionRegression.sourceType 1)) := by
  simpa [context1, Ctx.lookup, IntersectionRegression.sourceType,
    IntersectionRegression.sourceShape, IntersectionRegression.functionType,
    IntersectionRegression.functionShape] using
    (Path.Ty.var : Path.Ty context1 (.var 0)
      (.term (Ctx.lookup context1 0)))

private def exactRecordToSource :
    Ty.Sub context1
      (.capt (.singleton (.var 0))
        (.Pair
          (.capt (.singleton (.var 0)) (.Single (.var 0)))
          typeLabel
          (.type
            (IntersectionRegression.sourceShape 1).weaken
            (IntersectionRegression.sourceShape 1).weaken)))
      (sourceRecord 1) := by
  simpa [sourceRecord, recordShape, IntersectionRegression.sourceShape,
    IntersectionRegression.functionType,
    IntersectionRegression.functionShape] using
    (Ty.Sub.capt
      (CaptureSet.Sub.path valuePathInContext1)
      (Shape.Sub.pair
        (.capt (CaptureSet.Sub.path valuePathInContext1) .top)
        (.refl : Tau.Sub
          (context1.snoc
            (.capt (.singleton (.var 0)) (.Single (.var 0))))
          (.type
            (IntersectionRegression.sourceShape 1).weaken
            (IntersectionRegression.sourceShape 1).weaken)
          (.type
            (IntersectionRegression.sourceShape 1).weaken
            (IntersectionRegression.sourceShape 1).weaken))))

private def recordValueSourceTyping :
    Tm.Ty context1 recordValue (sourceRecord 1) .empty :=
  .sub
    (.type_pair sourceShapeWf)
    exactRecordToSource
    .refl
    sourceRecordWf
    .empty

private def recordValueIntersectionTyping :
    Tm.Ty context1 recordValue (recordIntersection 1) .empty :=
  .sub recordValueSourceTyping sourceRecordToIntersection .refl
    recordIntersectionWf .empty

private def intersectionPathInContext2 :
    Path.Ty context2 (.var 0) (.term (recordIntersection 2)) := by
  simpa [context2, context1, Ctx.lookup, recordIntersection, recordShape,
    IntersectionRegression.sourceShape, IntersectionRegression.leftViewShape,
    IntersectionRegression.rightViewShape, IntersectionRegression.functionType,
    IntersectionRegression.functionShape] using
    (Path.Ty.var : Path.Ty context2 (.var 0)
      (.term (Ctx.lookup context2 0)))

private def mergedRecordAliasTyping :
    Tm.Ty context2 mergedRecordAlias (mergedRecord 2) .empty :=
  .sub
    (.path intersectionPathInContext2)
    (.trans
      (.capt (.path intersectionPathInContext2)
        (.singleton_widen intersectionPathInContext2))
      recordIntersectionToMerged)
    (.path intersectionPathInContext2)
    mergedRecordWf
    .empty

private def mergedRecordPathTyping :
    Path.Ty context3 (.var 0) (.term (mergedRecord 3)) := by
  simpa [context3, context2, context1, Ctx.lookup, mergedRecord, recordShape,
    IntersectionRegression.sourceShape,
    IntersectionRegression.intersectionShape,
    IntersectionRegression.leftViewShape,
    IntersectionRegression.rightViewShape,
    IntersectionRegression.functionType,
    IntersectionRegression.functionShape] using
    (Path.Ty.var : Path.Ty context3 (.var 0)
      (.term (Ctx.lookup context3 0)))

private def selectedTypePathTyping :
    Path.Ty context3 ((Path.var 0).sel typeLabel)
      (.type
        (IntersectionRegression.sourceShape 3)
        (IntersectionRegression.intersectionShape 3)) := by
  simpa [mergedRecord, recordShape, Tau.open, Ty.open, Shape.open,
    Tau.subst, Ty.subst, Shape.subst, CaptureSet.subst, Path.subst,
    PathSubst.openAt, IntersectionRegression.sourceShape,
    IntersectionRegression.intersectionShape,
    IntersectionRegression.leftViewShape,
    IntersectionRegression.rightViewShape,
    IntersectionRegression.functionType,
    IntersectionRegression.functionShape] using
    mergedRecordPathTyping.sel_r

private def selectedTypeWf :
    Ty.Wf context3
      (.capt .empty (.TSel (.var 0) typeLabel)) :=
  .capt .empty (.select selectedTypePathTyping sourceShapeToIntersection)

private def valuePathTyping :
    Path.Ty context3 (.var 2)
      (.term (IntersectionRegression.sourceType 3)) := by
  simpa [context3, context2, context1, Ctx.lookup,
    IntersectionRegression.sourceType, IntersectionRegression.sourceShape,
    IntersectionRegression.functionType,
    IntersectionRegression.functionShape] using
    (Path.Ty.var : Path.Ty context3 (.var 2)
      (.term (Ctx.lookup context3 2)))

/-- The stored witness crosses the selected member's lower bound. -/
def valueSelectionTyping :
    Tm.Ty context3 (.path (.var 2))
      (.capt .empty (.TSel (.var 0) typeLabel)) .empty :=
  .sub
    (.path valuePathTyping)
    (.capt
      (.path valuePathTyping)
      (.trans
        (.singleton_widen valuePathTyping)
        (.select_lower selectedTypePathTyping sourceShapeToIntersection)))
    (.path valuePathTyping)
    selectedTypeWf
    .empty

/-- The selected type crosses the left projection of its merged upper bound. -/
def functionViewTyping :
    Tm.Ty context3 (.path (.var 2))
      (IntersectionRegression.leftView 3) .empty :=
  .sub
    valueSelectionTyping
    (.capt .refl
      (.trans
        (.select_upper selectedTypePathTyping sourceShapeToIntersection)
        .inter_left))
    .refl
    IntersectionRegression.leftViewWf
    .empty

/-- The same selected type crosses the right projection of its upper bound. -/
def argumentViewTyping :
    Tm.Ty context3 (.path (.var 2))
      (IntersectionRegression.rightView 3) .empty :=
  .sub
    valueSelectionTyping
    (.capt .refl
      (.trans
        (.select_upper selectedTypePathTyping sourceShapeToIntersection)
        .inter_right))
    .refl
    IntersectionRegression.rightViewWf
    .empty

private def bodyTyping :
    Tm.Ty context3 body (IntersectionRegression.functionType 3) .empty := by
  apply Tm.Ty.sub
  · simpa [body, IntersectionRegression.leftView,
      IntersectionRegression.leftViewShape, IntersectionRegression.rightView,
      IntersectionRegression.rightViewShape,
      IntersectionRegression.functionType,
      IntersectionRegression.functionShape, Ty.open, Ty.subst, Shape.subst,
      CaptureSet.subst, Path.subst, PathSubst.openAt] using
      Tm.Ty.app functionViewTyping argumentViewTyping
  · exact .refl
  · exact .union_elim .empty .empty
  · exact IntersectionRegression.functionTypeWf
  · exact .empty

def term_typing :
    Tm.Ty Ctx.nil term (IntersectionRegression.functionType 0) .empty :=
  .let valueSourceTyping
    (.let recordValueIntersectionTyping
      (.let mergedRecordAliasTyping bodyTyping
        IntersectionRegression.functionTypeWf .empty)
      IntersectionRegression.functionTypeWf .empty)
    IntersectionRegression.functionTypeWf .empty

theorem term_type_safety
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial term) target) :
    State.Progress target :=
  term_typing.closed_type_safety steps

end

end LambdaPCCI.TypeMemberIntersectionRegression
