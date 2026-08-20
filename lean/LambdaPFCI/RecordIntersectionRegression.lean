import LambdaPFCI.IntersectionRegression

/-!
A closed regression showing that an opaque intersection can retain two
incomparable views of the same physical record member:

```text
F    = Top -> Top
S    = Top -> F
L    = F -> F
R    = F
Q(X) = { f : X }

v : S
r : Q(L) ∧ Q(R) = { f = v }
left  : Q(L) = r
right : Q(R) = r
in left.f right.f
```

The path-valued lets bind `left` and `right` as aliases of the one stored pair
location.  Their precise branch types then let ordinary path selection expose
the same member as `L` for the function and `R` for its argument, without
adding intersection projection to precise path typing.

The final section merges `Q(L) ∧ Q(R)` into `Q(L ∧ R)`, then checks
`merged.f merged.f` through one precise alias.
-/

namespace LambdaPFCI.RecordIntersectionRegression

noncomputable section

open IntersectionRegression

/-- Both record views describe the same physical member slot. -/
def memberLabel : Name := 0

def sourceRecord : Ty n :=
  .Pair .Top memberLabel (.ty sourceType.weaken)

def leftRecord : Ty n :=
  .Pair .Top memberLabel (.ty leftView.weaken)

def rightRecord : Ty n :=
  .Pair .Top memberLabel (.ty rightView.weaken)

def recordIntersection : Ty n :=
  .Inter leftRecord rightRecord

private def sourceTypeWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (sourceType (n := n))) :=
  .fun .top functionTypeWf

private def sourceRecordWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (sourceRecord (n := n))) :=
  .pair .top sourceTypeWf

private def leftRecordWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (leftRecord (n := n))) :=
  .pair .top leftViewWf

private def rightRecordWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (rightRecord (n := n))) :=
  .pair .top rightViewWf

private def recordIntersectionWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (recordIntersection (n := n))) :=
  .inter leftRecordWf rightRecordWf

private def sourceRecordToLeft {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceRecord (n := n)))
      (.ty (leftRecord (n := n))) :=
  .pair .refl sourceToLeft

private def sourceRecordToRight {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceRecord (n := n)))
      (.ty (rightRecord (n := n))) :=
  .pair .refl sourceToRight

private def sourceRecordToIntersection {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceRecord (n := n)))
      (.ty (recordIntersection (n := n))) :=
  .inter sourceRecordToLeft sourceRecordToRight

/-- One stored pair uses `v` as both its first component and its member value. -/
def recordValue : Tm 1 :=
  .pair 0 memberLabel (.val 0)

/-- A left-view alias of the record location. -/
def leftRecordAlias : Tm 2 :=
  .path (.var 0)

/-- A right-view alias of the same record location, shifted past the left alias. -/
def rightRecordAlias : Tm 3 :=
  .path (.var 1)

/-- The two aliases select the same stored member through different views. -/
def body : Tm 4 :=
  .app ((Path.var 1).sel memberLabel) ((Path.var 0).sel memberLabel)

def term : Tm 0 :=
  .let value
    (.let recordValue
      (.let leftRecordAlias
        (.let rightRecordAlias body)))

private def context1 : Ctx 1 :=
  Ctx.nil.snoc sourceType

private def context2 : Ctx 2 :=
  context1.snoc recordIntersection

private def context3 : Ctx 3 :=
  context2.snoc leftRecord

private def context4 : Ctx 4 :=
  context3.snoc rightRecord

private def valueSourceTyping :
    Tm.Ty Ctx.nil value sourceType :=
  .abs
    (.abs
      (.sub (.path .var) (.widen .var) .top)
      .top)
    .top

private def recordValueExactToSource :
    Tau.Sub context1
      (.ty (.Pair (.Single (.var 0)) memberLabel
        (.ty (.Single (Path.var 0).weaken))))
      (.ty sourceRecord) :=
  .pair .top (.widen .var)

private def recordValueSourceTyping :
    Tm.Ty context1 recordValue sourceRecord :=
  .sub .pair recordValueExactToSource sourceRecordWf

private def recordValueIntersectionTyping :
    Tm.Ty context1 recordValue recordIntersection :=
  .sub recordValueSourceTyping sourceRecordToIntersection recordIntersectionWf

private def leftRecordAliasTyping :
    Tm.Ty context2 leftRecordAlias leftRecord :=
  .sub
    (.path .var)
    (.trans (.widen .var) .inter_left)
    leftRecordWf

private def rightRecordAliasTyping :
    Tm.Ty context3 rightRecordAlias rightRecord :=
  .sub
    (.path .var)
    (.trans (.widen .var) .inter_right)
    rightRecordWf

private def leftRecordPathTyping :
    Path.Ty context4 (.var 1) (.ty leftRecord) := by
  simpa [context4, context3, Ctx.lookup, leftRecord, leftView, functionType,
    Ty.weaken, Tau.weaken, Ty.rename, Tau.rename] using
    (Path.Ty.var : Path.Ty context4 (.var 1) (.ty (Ctx.lookup context4 1)))

private def rightRecordPathTyping :
    Path.Ty context4 (.var 0) (.ty rightRecord) := by
  simpa [context4, Ctx.lookup, rightRecord, rightView, functionType,
    Ty.weaken, Tau.weaken, Ty.rename, Tau.rename] using
    (Path.Ty.var : Path.Ty context4 (.var 0) (.ty (Ctx.lookup context4 0)))

private def leftMemberPathTyping :
    Path.Ty context4 ((Path.var 1).sel memberLabel) (.ty leftView) := by
  simpa [leftRecord, Tau.weaken_open] using leftRecordPathTyping.sel_r

private def rightMemberPathTyping :
    Path.Ty context4 ((Path.var 0).sel memberLabel) (.ty rightView) := by
  simpa [rightRecord, Tau.weaken_open] using rightRecordPathTyping.sel_r

private def leftMemberTyping :
    Tm.Ty context4 (.path ((Path.var 1).sel memberLabel)) leftView :=
  .sub (.path leftMemberPathTyping) (.widen leftMemberPathTyping) leftViewWf

private def rightMemberTyping :
    Tm.Ty context4 (.path ((Path.var 0).sel memberLabel)) rightView :=
  .sub (.path rightMemberPathTyping) (.widen rightMemberPathTyping) rightViewWf

private def bodyTyping :
    Tm.Ty context4 body functionType := by
  simpa [body, leftView, rightView, functionType, Ty.weaken_open] using
    Tm.Ty.app leftMemberTyping rightMemberTyping

def term_typing : Tm.Ty Ctx.nil term functionType :=
  .let valueSourceTyping functionTypeWf
    (.let recordValueIntersectionTyping functionTypeWf
      (.let leftRecordAliasTyping functionTypeWf
        (.let rightRecordAliasTyping functionTypeWf bodyTyping)))

theorem term_type_safety
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial term) target) :
    State.Progress target :=
  term_typing.closed_type_safety steps

/-! ## Merging the two views -/

/-- One precise record view whose stored member retains both function views. -/
def mergedRecord : Ty n :=
  .Pair .Top memberLabel
    (.ty (.Inter leftView.weaken rightView.weaken))

/-- A single alias obtained by merging the two same-slot record views. -/
def mergedRecordAlias : Tm 2 :=
  .path (.var 0)

/-- The same selected member supplies both sides of the application. -/
def mergedBody : Tm 3 :=
  .app ((Path.var 0).sel memberLabel) ((Path.var 0).sel memberLabel)

def mergedTerm : Tm 0 :=
  .let value
    (.let recordValue
      (.let mergedRecordAlias mergedBody))

private def mergedContext3 : Ctx 3 :=
  context2.snoc mergedRecord

private def mergedRecordWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (mergedRecord (n := n))) := by
  apply Tau.Wf.pair .top
  apply Tau.Wf.inter
  · simpa [leftView, functionType] using
      (leftViewWf (Gamma := Gamma.snoc (.Top : Ty n)))
  · simpa [rightView, functionType] using
      (rightViewWf (Gamma := Gamma.snoc (.Top : Ty n)))

private def recordIntersectionToMerged :
    Tau.Sub context2 (.ty recordIntersection) (.ty mergedRecord) := by
  simpa [recordIntersection, leftRecord, rightRecord, mergedRecord] using
    (Tau.Sub.pair_inter (Γ := context2)
      (S := .Top) (a := memberLabel)
      (T := leftView.weaken) (U := rightView.weaken))

private def mergedRecordAliasTyping :
    Tm.Ty context2 mergedRecordAlias mergedRecord :=
  .sub
    (.path .var)
    (.trans (.widen .var) recordIntersectionToMerged)
    mergedRecordWf

private def mergedRecordPathTyping :
    Path.Ty mergedContext3 (.var 0) (.ty mergedRecord) := by
  simpa [mergedContext3, context2, context1, Ctx.lookup, mergedRecord,
    leftView, rightView, functionType, Ty.weaken, Tau.weaken,
    Ty.rename, Tau.rename] using
    (Path.Ty.var : Path.Ty mergedContext3 (.var 0)
      (.ty (Ctx.lookup mergedContext3 0)))

private def mergedMemberPathTyping :
    Path.Ty mergedContext3 ((Path.var 0).sel memberLabel)
      (.ty (.Inter leftView rightView)) := by
  simpa [mergedRecord, Tau.weaken_open] using
    mergedRecordPathTyping.sel_r

private def mergedFunctionTyping :
    Tm.Ty mergedContext3 (.path ((Path.var 0).sel memberLabel)) leftView :=
  .sub
    (.path mergedMemberPathTyping)
    (.trans (.widen mergedMemberPathTyping) .inter_left)
    leftViewWf

private def mergedArgumentTyping :
    Tm.Ty mergedContext3 (.path ((Path.var 0).sel memberLabel)) rightView :=
  .sub
    (.path mergedMemberPathTyping)
    (.trans (.widen mergedMemberPathTyping) .inter_right)
    rightViewWf

private def mergedBodyTyping :
    Tm.Ty mergedContext3 mergedBody functionType := by
  simpa [mergedBody, leftView, rightView, functionType, Ty.weaken_open] using
    Tm.Ty.app mergedFunctionTyping mergedArgumentTyping

def merged_term_typing : Tm.Ty Ctx.nil mergedTerm functionType :=
  .let valueSourceTyping functionTypeWf
    (.let recordValueIntersectionTyping functionTypeWf
      (.let mergedRecordAliasTyping functionTypeWf mergedBodyTyping))

theorem merged_term_type_safety
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial mergedTerm) target) :
    State.Progress target :=
  merged_term_typing.closed_type_safety steps

end

end LambdaPFCI.RecordIntersectionRegression
