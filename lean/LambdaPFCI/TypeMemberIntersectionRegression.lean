import LambdaPFCI.IntersectionRegression

/-!
A closed regression for merging two views of one abstract type member.  Write

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
`v` first cross the lower bound `S <: q.A`; the function occurrence then
uses the left upper view `L`, and the argument occurrence uses the right
upper view `R`.  Thus the final application exercises both bounds of the
merged interval rather than merely constructing it.
-/

namespace LambdaPFCI.TypeMemberIntersectionRegression

noncomputable section

open IntersectionRegression

def typeLabel : Name := 0

def sourceRecord : Ty n :=
  .Pair .Top typeLabel
    (.intv sourceType.weaken sourceType.weaken)

def leftRecord : Ty n :=
  .Pair .Top typeLabel
    (.intv sourceType.weaken leftView.weaken)

def rightRecord : Ty n :=
  .Pair .Top typeLabel
    (.intv sourceType.weaken rightView.weaken)

def recordIntersection : Ty n :=
  .Inter leftRecord rightRecord

def mergedRecord : Ty n :=
  .Pair .Top typeLabel
    (.intv sourceType.weaken intersectionType.weaken)

private def sourceTypeWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (sourceType (n := n))) :=
  .fun .top functionTypeWf

private def sourceRecordWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (sourceRecord (n := n))) :=
  .pair .top
    (.bounds_wf sourceTypeWf sourceTypeWf .refl)

private def leftRecordWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (leftRecord (n := n))) :=
  .pair .top
    (.bounds_wf sourceTypeWf leftViewWf sourceToLeft)

private def rightRecordWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (rightRecord (n := n))) :=
  .pair .top
    (.bounds_wf sourceTypeWf rightViewWf sourceToRight)

private def recordIntersectionWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (recordIntersection (n := n))) :=
  .inter leftRecordWf rightRecordWf

private def mergedRecordWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (mergedRecord (n := n))) :=
  .pair .top
    (.bounds_wf sourceTypeWf intersectionTypeWf sourceToIntersection)

private def sourceRecordToLeft {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceRecord (n := n)))
      (.ty (leftRecord (n := n))) :=
  .pair .refl (.bounds .refl sourceToLeft .refl)

private def sourceRecordToRight {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceRecord (n := n)))
      (.ty (rightRecord (n := n))) :=
  .pair .refl (.bounds .refl sourceToRight .refl)

private def sourceRecordToIntersection {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceRecord (n := n)))
      (.ty (recordIntersection (n := n))) :=
  .inter sourceRecordToLeft sourceRecordToRight

private def recordIntersectionToMerged {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (recordIntersection (n := n)))
      (.ty (mergedRecord (n := n))) := by
  simpa [recordIntersection, leftRecord, rightRecord, mergedRecord] using
    (Tau.Sub.pair_type_inter (Γ := Gamma)
      (S := .Top) (A := typeLabel)
      (L := sourceType.weaken)
      (U := leftView.weaken) (V := rightView.weaken))

/-! ## Closed program -/

def value : Tm 0 :=
  IntersectionRegression.value

/-- Store the exact witness `A = S`. -/
def recordValue : Tm 1 :=
  .pair 0 typeLabel (.type sourceType)

/-- A single precise alias at the merged record type. -/
def mergedRecordAlias : Tm 2 :=
  .path (.var 0)

/-- The same `S`-typed value is viewed through both upper bounds of `q.A`. -/
def body : Tm 3 :=
  .app (.var 2) (.var 2)

def term : Tm 0 :=
  .let value
    (.let recordValue
      (.let mergedRecordAlias body))

private def context1 : Ctx 1 :=
  Ctx.nil.snoc sourceType

private def context2 : Ctx 2 :=
  context1.snoc recordIntersection

private def context3 : Ctx 3 :=
  context2.snoc mergedRecord

private def valueSourceTyping :
    Tm.Ty Ctx.nil value sourceType :=
  .abs
    (.abs
      (.sub (.path .var) (.widen .var) .top)
      .top)
    .top

private def exactRecordToSource :
    Tau.Sub context1
      (.ty (.Pair (.Single (.var 0)) typeLabel
        (Tau.intv sourceType sourceType).weaken))
      (.ty sourceRecord) :=
  .pair .top .refl

private def recordValueSourceTyping :
    Tm.Ty context1 recordValue sourceRecord :=
  .sub (.tpair sourceTypeWf) exactRecordToSource sourceRecordWf

private def recordValueIntersectionTyping :
    Tm.Ty context1 recordValue recordIntersection :=
  .sub recordValueSourceTyping sourceRecordToIntersection recordIntersectionWf

private def intersectionPathInContext2 :
    Path.Ty context2 (.var 0) (.ty recordIntersection) := by
  simpa [context2, context1, Ctx.lookup, recordIntersection, leftRecord,
    rightRecord, sourceType, leftView, rightView, functionType,
    Ty.weaken, Tau.weaken, Ty.rename, Tau.rename] using
    (Path.Ty.var : Path.Ty context2 (.var 0)
      (.ty (Ctx.lookup context2 0)))

private def mergedRecordAliasTyping :
    Tm.Ty context2 mergedRecordAlias mergedRecord :=
  .sub
    (.path intersectionPathInContext2)
    (.trans
      (.widen intersectionPathInContext2)
      recordIntersectionToMerged)
    mergedRecordWf

private def mergedRecordPathTyping :
    Path.Ty context3 (.var 0) (.ty mergedRecord) := by
  simpa [context3, context2, context1, Ctx.lookup, mergedRecord,
    sourceType, intersectionType, leftView, rightView, functionType,
    Ty.weaken, Tau.weaken, Ty.rename, Tau.rename] using
    (Path.Ty.var : Path.Ty context3 (.var 0)
      (.ty (Ctx.lookup context3 0)))

private def selectedTypePathTyping :
    Path.Ty context3 ((Path.var 0).sel typeLabel)
      (.intv sourceType intersectionType) := by
  simpa [mergedRecord, Tau.weaken_open] using
    mergedRecordPathTyping.sel_r

private def selectedTypeWf :
    Tau.Wf context3 (.ty (.TSel (.var 0) typeLabel)) :=
  .sel selectedTypePathTyping sourceToIntersection

private def valuePathTyping :
    Path.Ty context3 (.var 2) (.ty sourceType) := by
  simpa [context3, context2, context1, Ctx.lookup, sourceType,
    functionType, Ty.weaken, Tau.weaken, Ty.rename, Tau.rename] using
    (Path.Ty.var : Path.Ty context3 (.var 2)
      (.ty (Ctx.lookup context3 2)))

/-- The stored witness crosses the selected member's lower bound. -/
def valueSelectionTyping :
    Tm.Ty context3 (.path (.var 2)) (.TSel (.var 0) typeLabel) :=
  .sub
    (.path valuePathTyping)
    (.trans
      (.widen valuePathTyping)
      (.sel_lo selectedTypePathTyping sourceToIntersection))
    selectedTypeWf

/-- The selected type crosses the left projection of its merged upper bound. -/
def functionViewTyping :
    Tm.Ty context3 (.path (.var 2)) leftView :=
  .sub
    valueSelectionTyping
    (.trans
      (.sel_hi selectedTypePathTyping sourceToIntersection)
      .inter_left)
    leftViewWf

/-- The same selected type crosses the right projection of its upper bound. -/
def argumentViewTyping :
    Tm.Ty context3 (.path (.var 2)) rightView :=
  .sub
    valueSelectionTyping
    (.trans
      (.sel_hi selectedTypePathTyping sourceToIntersection)
      .inter_right)
    rightViewWf

private def bodyTyping :
    Tm.Ty context3 body functionType := by
  simpa [body, leftView, rightView, functionType, Ty.weaken_open] using
    Tm.Ty.app functionViewTyping argumentViewTyping

def term_typing : Tm.Ty Ctx.nil term functionType :=
  .let valueSourceTyping functionTypeWf
    (.let recordValueIntersectionTyping functionTypeWf
      (.let mergedRecordAliasTyping functionTypeWf bodyTyping))

theorem term_type_safety
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial term) target) :
    State.Progress target :=
  term_typing.closed_type_safety steps

end

end LambdaPFCI.TypeMemberIntersectionRegression
