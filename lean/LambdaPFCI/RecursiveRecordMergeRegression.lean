import LambdaPFCI.IntersectionRegression

/-!
A closed regression for recursive, binder-aware merging of a mixed record
spine.  Write

```text
F = Top -> Top
S = Top -> F
L = F -> F
R = F

Q0 = { A : S..S }
QL = { A : S..L }
QR = { A : S..R }
QI = { A : S..(L ∩ R) }

P0 = { x : Q0; f : x.A }
PL = { x : QL; f : x.A }
PR = { x : QR; f : R }
PI = { x : QI; f : x.A ∩ R }
```

One physical two-cell spine is given the type `PL ∩ PR`.  A single
recursive `Tau.Merge` plan changes both axes of the outer cell at once: it
descends to merge the inner type-member bounds and also intersects the
different outer member signatures under the merged first-component type.
Thus the resulting later member retains the genuinely dependent component
`x.A` after the earlier member has been merged.

The final alias has type `PI`.  For the operator, its stored `f` first takes
the `x.A` projection and then leaves that selection through `L`; for the
argument it takes the direct `R = F` projection.  The same path can therefore
appear on both sides of `q.f q.f`.
-/

namespace LambdaPFCI.RecursiveRecordMergeRegression

noncomputable section

open IntersectionRegression

def typeLabel : Name := 0
def valueLabel : Name := 1

/-! ## The mixed two-cell spine -/

def sourceTail : Ty n :=
  .Pair .Top typeLabel
    (.intv sourceType.weaken sourceType.weaken)

def leftTail : Ty n :=
  .Pair .Top typeLabel
    (.intv sourceType.weaken leftView.weaken)

def rightTail : Ty n :=
  .Pair .Top typeLabel
    (.intv sourceType.weaken rightView.weaken)

def mergedTail : Ty n :=
  .Pair .Top typeLabel
    (.intv sourceType.weaken intersectionType.weaken)

def sourceOuter : Ty n :=
  .Pair sourceTail valueLabel
    (.ty (.TSel (.var 0) typeLabel))

def leftOuter : Ty n :=
  .Pair leftTail valueLabel
    (.ty (.TSel (.var 0) typeLabel))

def rightOuter : Ty n :=
  .Pair rightTail valueLabel
    (.ty rightView.weaken)

def outerIntersection : Ty n :=
  .Inter leftOuter rightOuter

def mergedOuter : Ty n :=
  .Pair mergedTail valueLabel
    (.ty (.Inter (.TSel (.var 0) typeLabel) rightView.weaken))

private def sourceTypeWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (sourceType (n := n))) :=
  .fun .top functionTypeWf

private def sourceTailWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (sourceTail (n := n))) :=
  .pair .top (.bounds_wf sourceTypeWf sourceTypeWf .refl)

private def leftTailWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (leftTail (n := n))) :=
  .pair .top (.bounds_wf sourceTypeWf leftViewWf sourceToLeft)

private def rightTailWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (rightTail (n := n))) :=
  .pair .top (.bounds_wf sourceTypeWf rightViewWf sourceToRight)

private def mergedTailWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (mergedTail (n := n))) :=
  .pair .top
    (.bounds_wf sourceTypeWf intersectionTypeWf sourceToIntersection)

private def sourceTailSelection
    (typing : Path.Ty Gamma path (.ty sourceTail)) :
    Path.Ty Gamma (path.sel typeLabel)
      (.intv sourceType sourceType) := by
  simpa [sourceTail, Tau.weaken_open] using typing.sel_r

private def leftTailSelection
    (typing : Path.Ty Gamma path (.ty leftTail)) :
    Path.Ty Gamma (path.sel typeLabel)
      (.intv sourceType leftView) := by
  simpa [leftTail, Tau.weaken_open] using typing.sel_r

private def rightTailSelection
    (typing : Path.Ty Gamma path (.ty rightTail)) :
    Path.Ty Gamma (path.sel typeLabel)
      (.intv sourceType rightView) := by
  simpa [rightTail, Tau.weaken_open] using typing.sel_r

private def mergedTailSelection
    (typing : Path.Ty Gamma path (.ty mergedTail)) :
    Path.Ty Gamma (path.sel typeLabel)
      (.intv sourceType intersectionType) := by
  simpa [mergedTail, Tau.weaken_open] using typing.sel_r

private def sourceOuterWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (sourceOuter (n := n))) := by
  apply Tau.Wf.pair sourceTailWf
  exact .sel (sourceTailSelection .var) .refl

private def leftOuterWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (leftOuter (n := n))) := by
  apply Tau.Wf.pair leftTailWf
  exact .sel (leftTailSelection .var) sourceToLeft

private def rightOuterWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (rightOuter (n := n))) := by
  apply Tau.Wf.pair rightTailWf
  exact rightViewWf

private def outerIntersectionWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (outerIntersection (n := n))) :=
  .inter leftOuterWf rightOuterWf

private def mergedOuterWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (mergedOuter (n := n))) := by
  apply Tau.Wf.pair mergedTailWf
  exact .inter
    (.sel (mergedTailSelection .var) sourceToIntersection)
    rightViewWf

/-! ## One recursive merge plan -/

private def sourceTailToLeft {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceTail (n := n)))
      (.ty (leftTail (n := n))) :=
  .pair .refl (.bounds .refl sourceToLeft .refl)

private def sourceTailToRight {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceTail (n := n)))
      (.ty (rightTail (n := n))) :=
  .pair .refl (.bounds .refl sourceToRight .refl)

private def sourceOuterToLeft {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceOuter (n := n)))
      (.ty (leftOuter (n := n))) :=
  .pair sourceTailToLeft .refl

private def sourceOuterToRight {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceOuter (n := n)))
      (.ty (rightOuter (n := n))) :=
  .pair sourceTailToRight
    (.trans
      (.sel_hi (sourceTailSelection .var) .refl)
      sourceToRight)

private def sourceOuterToIntersection {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceOuter (n := n)))
      (.ty (outerIntersection (n := n))) :=
  .inter sourceOuterToLeft sourceOuterToRight

/-- The inner plan merges the upper bounds of the abstract member. -/
def tailMergePlan {n} {Gamma : Ctx n} :
    Tau.Merge Gamma
      (.ty (leftTail (n := n)))
      (.ty (rightTail (n := n)))
      (.ty (mergedTail (n := n))) := by
  simpa [leftTail, rightTail, mergedTail, intersectionType] using
    (Tau.Merge.pair (Γ := Gamma) (a := typeLabel)
      Tau.Merge.same (Tau.Merge.intv Ty.Join.same Tau.Merge.inter))

/-- The outer step simultaneously recurses into the record tail and merges
two different member signatures under `mergedTail`.  Neither of the former
one-axis pair rules expresses this step. -/
def recursiveMergePlan {n} {Gamma : Ctx n} :
    Tau.Merge Gamma
      (.ty (leftOuter (n := n)))
      (.ty (rightOuter (n := n)))
      (.ty (mergedOuter (n := n))) := by
  simpa [leftOuter, rightOuter, mergedOuter] using
    (Tau.Merge.pair (Γ := Gamma) (a := valueLabel)
      (tailMergePlan (Gamma := Gamma)) Tau.Merge.inter)

def outerIntersectionToMerged {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (outerIntersection (n := n)))
      (.ty (mergedOuter (n := n))) :=
  .merge recursiveMergePlan

/-! ## Closed program -/

def value : Tm 0 :=
  IntersectionRegression.value

/-- The older cell stores the exact witness `A = S`. -/
def typeMemberValue : Tm 1 :=
  .pair 0 typeLabel (.type sourceType)

/-- The newer cell stores `v` at the earlier selected type `x.A`. -/
def dependentValue : Tm 2 :=
  .pair 0 valueLabel (.val 1)

/-- A path-only alias exposes the recursively merged spine precisely. -/
def mergedAlias : Tm 3 :=
  .path (.var 0)

def body : Tm 4 :=
  .app ((Path.var 0).sel valueLabel) ((Path.var 0).sel valueLabel)

def term : Tm 0 :=
  .let value
    (.let typeMemberValue
      (.let dependentValue
        (.let mergedAlias body)))

private def context1 : Ctx 1 :=
  Ctx.nil.snoc sourceType

private def context2 : Ctx 2 :=
  context1.snoc sourceTail

private def context3 : Ctx 3 :=
  context2.snoc outerIntersection

private def context4 : Ctx 4 :=
  context3.snoc mergedOuter

private def valueTyping :
    Tm.Ty Ctx.nil value sourceType :=
  .abs
    (.abs
      (.sub (.path .var) (.widen .var) .top)
      .top)
    .top

private def exactTailToSource :
    Tau.Sub context1
      (.ty (.Pair (.Single (.var 0)) typeLabel
        (Tau.intv sourceType sourceType).weaken))
      (.ty sourceTail) :=
  .pair .top .refl

private def typeMemberValueTyping :
    Tm.Ty context1 typeMemberValue sourceTail :=
  .sub (.tpair sourceTypeWf) exactTailToSource sourceTailWf

/- The intermediate type names the allocated tail.  The next coercion
changes that occurrence to the pair binder, exactly as in the ordinary
path-dependent record construction. -/
private def dependentIntermediate : Ty 2 :=
  .Pair sourceTail valueLabel
    (.ty (.TSel (.var 1) typeLabel))

private def dependentExactToIntermediate :
    Tau.Sub context2
      (.ty (.Pair (.Single (.var 0)) valueLabel
        (.ty (.Single (Path.var 1).weaken))))
      (.ty dependentIntermediate) := by
  apply Tau.Sub.pair
  · exact .widen .var
  · exact .trans
      (.widen .var)
      (.sel_lo (sourceTailSelection .var) .refl)

private def dependentIntermediateToSource :
    Tau.Sub context2 (.ty dependentIntermediate) (.ty sourceOuter) := by
  apply Tau.Sub.pair .refl
  exact .trans
    (.sel_hi (sourceTailSelection .var) .refl)
    (.sel_lo (sourceTailSelection .var) .refl)

private def dependentValueSourceTyping :
    Tm.Ty context2 dependentValue sourceOuter :=
  .sub
    .pair
    (.trans dependentExactToIntermediate dependentIntermediateToSource)
    sourceOuterWf

private def dependentValueIntersectionTyping :
    Tm.Ty context2 dependentValue outerIntersection :=
  .sub dependentValueSourceTyping sourceOuterToIntersection outerIntersectionWf

private def intersectionPathTyping :
    Path.Ty context3 (.var 0) (.ty outerIntersection) := by
  simpa [context3, context2, context1, Ctx.lookup, outerIntersection,
    leftOuter, rightOuter, leftTail, rightTail, sourceType, leftView,
    rightView, functionType, Ty.weaken, Tau.weaken, Ty.rename, Tau.rename]
    using
      (Path.Ty.var : Path.Ty context3 (.var 0)
        (.ty (Ctx.lookup context3 0)))

private def mergedAliasTyping :
    Tm.Ty context3 mergedAlias mergedOuter :=
  .sub
    (.path intersectionPathTyping)
    (.trans (.widen intersectionPathTyping) outerIntersectionToMerged)
    mergedOuterWf

private def mergedOuterPathTyping :
    Path.Ty context4 (.var 0) (.ty (mergedOuter (n := 4))) := by
  simpa [context4, context3, context2, context1, Ctx.lookup, mergedOuter,
    mergedTail, intersectionType, sourceType, leftView, rightView,
    functionType, Ty.weaken, Tau.weaken, Ty.rename, Tau.rename] using
    (Path.Ty.var : Path.Ty context4 (.var 0)
      (.ty (Ctx.lookup context4 0)))

/-- The merged outer member contains both the dependent view and the direct
`R` view. -/
def mergedMemberPathTyping :
    Path.Ty context4 ((Path.var 0).sel valueLabel)
      (.ty (.Inter (.TSel (Path.var 0).fst typeLabel) rightView)) := by
  simpa [mergedOuter, Tau.open, Ty.open, Tau.subst, Ty.subst,
    Path.subst, PathSubst.openAt] using mergedOuterPathTyping.sel_r

private def selectedTypePathTyping :
    Path.Ty context4 ((Path.var 0).fst.sel typeLabel)
      (.intv sourceType intersectionType) :=
  mergedTailSelection mergedOuterPathTyping.fst

private def selectedTypeWf :
    Tau.Wf context4
      (.ty (.TSel (Path.var 0).fst typeLabel)) :=
  .sel selectedTypePathTyping sourceToIntersection

private def functionMemberTyping :
    Tm.Ty context4 (.path ((Path.var 0).sel valueLabel)) leftView :=
  .sub
    (.path mergedMemberPathTyping)
    (.trans
      (.widen mergedMemberPathTyping)
      (.trans
        .inter_left
        (.trans
          (.sel_hi selectedTypePathTyping sourceToIntersection)
          .inter_left)))
    leftViewWf

private def argumentMemberTyping :
    Tm.Ty context4 (.path ((Path.var 0).sel valueLabel)) rightView :=
  .sub
    (.path mergedMemberPathTyping)
    (.trans
      (.widen mergedMemberPathTyping)
      .inter_right)
    rightViewWf

private def bodyTyping :
    Tm.Ty context4 body (functionType (n := 4)) := by
  simpa [body, leftView, rightView, functionType, Ty.weaken_open] using
    Tm.Ty.app functionMemberTyping argumentMemberTyping

def term_typing : Tm.Ty Ctx.nil term functionType :=
  .let valueTyping functionTypeWf
    (.let typeMemberValueTyping functionTypeWf
      (.let dependentValueIntersectionTyping functionTypeWf
        (.let mergedAliasTyping functionTypeWf bodyTyping)))

theorem term_type_safety
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial term) target) :
    State.Progress target :=
  term_typing.closed_type_safety steps

end

end LambdaPFCI.RecursiveRecordMergeRegression
