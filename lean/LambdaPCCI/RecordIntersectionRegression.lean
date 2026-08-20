import LambdaPCCI.IntersectionRegression

/-!
A capture-aware regression for two same-label record views of one runtime
record.  Reusing the function types from `IntersectionRegression`, write

```text
Q(X) = { _: Top; f : X }

v     : S
record: Q(L) ∧ Q(R) = { v; f = v }
left  : Q(L)       = record
right : Q(R)       = record
in left.f right.f
```

The two aliases resolve to the same record location, and both selections
therefore resolve to its one stored `f` member.  Their source typings expose
that member through the incomparable views `L = F -> F` and `R = F`.
Every public capture and use set is empty.
-/

namespace LambdaPCCI.RecordIntersectionRegression

noncomputable section

def memberLabel : Name := 0

/-- The record shape `Q(X)`.  Its member type lives under the pair binder. -/
def recordShape (memberType : Ty (n + 1)) : Shape n :=
  .Pair (IntersectionRegression.pureTop n) memberLabel (.term memberType)

def sourceRecord (n : Nat) : Ty n :=
  .capt .empty (recordShape (IntersectionRegression.sourceType (n + 1)))

def leftRecord (n : Nat) : Ty n :=
  .capt .empty (recordShape (IntersectionRegression.leftView (n + 1)))

def rightRecord (n : Nat) : Ty n :=
  .capt .empty (recordShape (IntersectionRegression.rightView (n + 1)))

def recordIntersection (n : Nat) : Ty n :=
  .capt .empty
    (.Inter
      (recordShape (IntersectionRegression.leftView (n + 1)))
      (recordShape (IntersectionRegression.rightView (n + 1))))

private def pureTopWf {Gamma : Ctx n} :
    Ty.Wf Gamma (IntersectionRegression.pureTop n) :=
  .capt .empty .top

private def sourceTypeWf {Gamma : Ctx n} :
    Ty.Wf Gamma (IntersectionRegression.sourceType n) :=
  .capt .empty
    (.fun pureTopWf (by
      simpa [IntersectionRegression.functionType,
        IntersectionRegression.functionShape] using
        (IntersectionRegression.functionTypeWf
          (Gamma := Gamma.snoc (IntersectionRegression.pureTop n)))))

private def sourceRecordShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma
      (recordShape (IntersectionRegression.sourceType (n + 1))) :=
  .pair pureTopWf (.term sourceTypeWf)

private def leftRecordShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma
      (recordShape (IntersectionRegression.leftView (n + 1))) :=
  .pair pureTopWf (.term IntersectionRegression.leftViewWf)

private def rightRecordShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma
      (recordShape (IntersectionRegression.rightView (n + 1))) :=
  .pair pureTopWf (.term IntersectionRegression.rightViewWf)

private def sourceRecordWf {Gamma : Ctx n} :
    Ty.Wf Gamma (sourceRecord n) :=
  .capt .empty sourceRecordShapeWf

private def leftRecordWf {Gamma : Ctx n} :
    Ty.Wf Gamma (leftRecord n) :=
  .capt .empty leftRecordShapeWf

private def rightRecordWf {Gamma : Ctx n} :
    Ty.Wf Gamma (rightRecord n) :=
  .capt .empty rightRecordShapeWf

private def recordIntersectionWf {Gamma : Ctx n} :
    Ty.Wf Gamma (recordIntersection n) :=
  .capt .empty (.inter leftRecordShapeWf rightRecordShapeWf)

private def sourceShapeToLeftRecordShape {Gamma : Ctx n} :
    Shape.Sub Gamma
      (recordShape (IntersectionRegression.sourceType (n + 1)))
      (recordShape (IntersectionRegression.leftView (n + 1))) :=
  .pair .refl
    (.term (.capt .refl IntersectionRegression.sourceToLeft))

private def sourceShapeToRightRecordShape {Gamma : Ctx n} :
    Shape.Sub Gamma
      (recordShape (IntersectionRegression.sourceType (n + 1)))
      (recordShape (IntersectionRegression.rightView (n + 1))) :=
  .pair .refl
    (.term (.capt .refl IntersectionRegression.sourceToRight))

private def sourceRecordToIntersection {Gamma : Ctx n} :
    Ty.Sub Gamma (sourceRecord n) (recordIntersection n) :=
  .capt .refl
    (.inter sourceShapeToLeftRecordShape sourceShapeToRightRecordShape)

/-! ## Closed program -/

def value : Tm 0 :=
  .abs (IntersectionRegression.pureTop 0)
    (.abs (IntersectionRegression.pureTop 1) (.path (.var 0)))

def recordValue : Tm 1 :=
  .pair 0 memberLabel (.val 0)

/-- A path-only let alias; evaluating it does not allocate a new record. -/
def leftRecordAlias : Tm 2 :=
  .path (.var 0)

/-- A second path-only alias of the same original record. -/
def rightRecordAlias : Tm 3 :=
  .path (.var 1)

def body : Tm 4 :=
  .app ((Path.var 1).sel memberLabel) ((Path.var 0).sel memberLabel)

def term : Tm 0 :=
  .let value
    (.let recordValue
      (.let leftRecordAlias
        (.let rightRecordAlias body)))

/-! ## Source typing -/

private def context1 : Ctx 1 :=
  Ctx.nil.snoc (IntersectionRegression.sourceType 0)

private def context2 : Ctx 2 :=
  context1.snoc (recordIntersection 1)

private def context3 : Ctx 3 :=
  context2.snoc (leftRecord 2)

private def context4 : Ctx 4 :=
  context3.snoc (rightRecord 3)

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

private def recordValueSourceTyping :
    Tm.Ty context1 recordValue (sourceRecord 1) .empty := by
  apply Tm.Ty.sub Tm.Ty.pair
  · apply Ty.Sub.capt
    · exact .union_elim (.path .var) (.path .var)
    · apply Shape.Sub.pair
      · exact .capt (.path .var) .top
      · exact .term
          (.capt
            (.path (.var (x := 1)))
            (.singleton_widen (.var (x := 1))))
  · exact .refl
  · exact sourceRecordWf
  · exact .empty

private def recordValueIntersectionTyping :
    Tm.Ty context1 recordValue (recordIntersection 1) .empty :=
  .sub recordValueSourceTyping sourceRecordToIntersection .refl
    recordIntersectionWf .empty

private def intersectionPathInContext2 :
    Path.Ty context2 (.var 0) (.term (recordIntersection 2)) := by
  simpa [context2, context1, Ctx.lookup, recordIntersection, recordShape,
    IntersectionRegression.leftView, IntersectionRegression.leftViewShape,
    IntersectionRegression.rightView, IntersectionRegression.rightViewShape,
    IntersectionRegression.functionType,
    IntersectionRegression.functionShape] using
    (Path.Ty.var : Path.Ty context2 (.var 0)
      (.term (Ctx.lookup context2 0)))

private def leftRecordAliasTyping :
    Tm.Ty context2 leftRecordAlias (leftRecord 2) .empty :=
  .sub
    (.path intersectionPathInContext2)
    (.capt (.path intersectionPathInContext2)
      (.trans (.singleton_widen intersectionPathInContext2) .inter_left))
    (.path intersectionPathInContext2)
    leftRecordWf
    .empty

private def intersectionPathInContext3 :
    Path.Ty context3 (.var 1) (.term (recordIntersection 3)) := by
  simpa [context3, context2, context1, Ctx.lookup, recordIntersection,
    recordShape, IntersectionRegression.leftView,
    IntersectionRegression.leftViewShape, IntersectionRegression.rightView,
    IntersectionRegression.rightViewShape, IntersectionRegression.functionType,
    IntersectionRegression.functionShape] using
    (Path.Ty.var : Path.Ty context3 (.var 1)
      (.term (Ctx.lookup context3 1)))

private def rightRecordAliasTyping :
    Tm.Ty context3 rightRecordAlias (rightRecord 3) .empty :=
  .sub
    (.path intersectionPathInContext3)
    (.capt (.path intersectionPathInContext3)
      (.trans (.singleton_widen intersectionPathInContext3) .inter_right))
    (.path intersectionPathInContext3)
    rightRecordWf
    .empty

private def leftRecordPathTyping :
    Path.Ty context4 (.var 1) (.term (leftRecord 4)) := by
  simpa [context4, context3, context2, context1, Ctx.lookup, leftRecord,
    recordShape, IntersectionRegression.leftView,
    IntersectionRegression.leftViewShape, IntersectionRegression.functionType,
    IntersectionRegression.functionShape] using
    (Path.Ty.var : Path.Ty context4 (.var 1)
      (.term (Ctx.lookup context4 1)))

private def rightRecordPathTyping :
    Path.Ty context4 (.var 0) (.term (rightRecord 4)) := by
  simpa [context4, context3, context2, context1, Ctx.lookup, rightRecord,
    recordShape, IntersectionRegression.rightView,
    IntersectionRegression.rightViewShape, IntersectionRegression.functionType,
    IntersectionRegression.functionShape] using
    (Path.Ty.var : Path.Ty context4 (.var 0)
      (.term (Ctx.lookup context4 0)))

private def leftMemberPathTyping :
    Path.Ty context4 ((Path.var 1).sel memberLabel)
      (.term (IntersectionRegression.leftView 4)) := by
  simpa [leftRecord, recordShape, Tau.open, Ty.open, Shape.open, Tau.subst,
    Ty.subst, Shape.subst, CaptureSet.subst, Path.subst,
    PathSubst.openAt, IntersectionRegression.leftView,
    IntersectionRegression.leftViewShape, IntersectionRegression.functionType,
    IntersectionRegression.functionShape] using leftRecordPathTyping.sel_r

private def rightMemberPathTyping :
    Path.Ty context4 ((Path.var 0).sel memberLabel)
      (.term (IntersectionRegression.rightView 4)) := by
  simpa [rightRecord, recordShape, Tau.open, Ty.open, Shape.open, Tau.subst,
    Ty.subst, Shape.subst, CaptureSet.subst, Path.subst,
    PathSubst.openAt, IntersectionRegression.rightView,
    IntersectionRegression.rightViewShape,
    IntersectionRegression.functionType,
    IntersectionRegression.functionShape] using rightRecordPathTyping.sel_r

private def leftSelectionToEmpty :
    CaptureSet.Sub context4
      (.singleton ((Path.var 1).sel memberLabel)) .empty :=
  .trans (.sel_root leftMemberPathTyping) (.path leftRecordPathTyping)

private def rightSelectionToEmpty :
    CaptureSet.Sub context4
      (.singleton ((Path.var 0).sel memberLabel)) .empty :=
  .trans (.sel_root rightMemberPathTyping) (.path rightRecordPathTyping)

private def leftMemberTyping :
    Tm.Ty context4 (.path ((Path.var 1).sel memberLabel))
      (IntersectionRegression.leftView 4) .empty :=
  .sub
    (.path leftMemberPathTyping)
    (.capt leftSelectionToEmpty (.singleton_widen leftMemberPathTyping))
    leftSelectionToEmpty
    IntersectionRegression.leftViewWf
    .empty

private def rightMemberTyping :
    Tm.Ty context4 (.path ((Path.var 0).sel memberLabel))
      (IntersectionRegression.rightView 4) .empty :=
  .sub
    (.path rightMemberPathTyping)
    (.capt rightSelectionToEmpty (.singleton_widen rightMemberPathTyping))
    rightSelectionToEmpty
    IntersectionRegression.rightViewWf
    .empty

private def bodyTyping :
    Tm.Ty context4 body (IntersectionRegression.functionType 4) .empty := by
  apply Tm.Ty.sub
  · simpa [body, IntersectionRegression.leftView,
      IntersectionRegression.leftViewShape, IntersectionRegression.rightView,
      IntersectionRegression.rightViewShape,
      IntersectionRegression.functionType,
      IntersectionRegression.functionShape, Ty.open,
      Ty.subst, Shape.subst, CaptureSet.subst, Path.subst,
      PathSubst.openAt] using
      Tm.Ty.app leftMemberTyping rightMemberTyping
  · exact .refl
  · exact .union_elim .empty .empty
  · exact IntersectionRegression.functionTypeWf
  · exact .empty

def term_typing :
    Tm.Ty Ctx.nil term (IntersectionRegression.functionType 0) .empty := by
  unfold term
  exact .let valueSourceTyping
    (.let recordValueIntersectionTyping
      (.let leftRecordAliasTyping
        (.let rightRecordAliasTyping bodyTyping
          IntersectionRegression.functionTypeWf .empty)
        IntersectionRegression.functionTypeWf .empty)
      IntersectionRegression.functionTypeWf .empty)
    IntersectionRegression.functionTypeWf .empty

theorem term_type_safety
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial term) target) :
    State.Progress target :=
  term_typing.closed_type_safety steps

end

end LambdaPCCI.RecordIntersectionRegression
