import LambdaPFCI.IntersectionRegression

/-!
A closed regression for merging aligned views of a two-member record spine.
Write `a` for the older member and `b` for the outer member:

```text
F = Top -> Top
S = Top -> F
L = F -> F
R = F

left  = { a : L; b : Top }
right = { a : R; b : Top }
```

One physical nested pair receives the intersection `left ∩ right`.  The
outer `b` signatures are identical, so `pair_first_inter` first merges the
two views of its record tail.  Ordinary `pair_inter` then normalizes that
tail to `{ a : L ∩ R }`, and pair covariance transports the unchanged `b`
signature across the normalization.  A single precise alias can consequently
skip `b`, select the older `a`, and use its two intersection projections in a
self-application.
-/

namespace LambdaPFCI.AlignedRecordIntersectionRegression

noncomputable section

open IntersectionRegression

def innerLabel : Name := 0
def outerLabel : Name := 1

private theorem inner_ne_outer : innerLabel ≠ outerLabel := by decide

/-! ## Aligned record views -/

def sourceTail : Ty n :=
  .Pair .Top innerLabel (.ty (sourceType (n := n + 1)))

def leftTail : Ty n :=
  .Pair .Top innerLabel (.ty (leftView (n := n + 1)))

def rightTail : Ty n :=
  .Pair .Top innerLabel (.ty (rightView (n := n + 1)))

def tailIntersection : Ty n :=
  .Inter leftTail rightTail

def mergedTail : Ty n :=
  .Pair .Top innerLabel (.ty (intersectionType (n := n + 1)))

/-- The two outer views differ only in their first-component record tail. -/
def leftOuter : Ty n :=
  .Pair leftTail outerLabel (.ty .Top)

def rightOuter : Ty n :=
  .Pair rightTail outerLabel (.ty .Top)

def outerIntersection : Ty n :=
  .Inter leftOuter rightOuter

/-- The direct result of merging the outer pair's first-component views. -/
def firstMergedOuter : Ty n :=
  .Pair tailIntersection outerLabel (.ty .Top)

/-- The tail intersection has been normalized to one selectable pair. -/
def normalizedOuter : Ty n :=
  .Pair mergedTail outerLabel (.ty .Top)

private def sourceTypeWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (sourceType (n := n))) :=
  .fun .top functionTypeWf

private def sourceTailWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (sourceTail (n := n))) :=
  .pair .top sourceTypeWf

private def leftTailWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (leftTail (n := n))) :=
  .pair .top leftViewWf

private def rightTailWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (rightTail (n := n))) :=
  .pair .top rightViewWf

private def tailIntersectionWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (tailIntersection (n := n))) :=
  .inter leftTailWf rightTailWf

private def mergedTailWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (mergedTail (n := n))) :=
  .pair .top intersectionTypeWf

private def leftOuterWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (leftOuter (n := n))) :=
  .pair leftTailWf .top

private def rightOuterWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (rightOuter (n := n))) :=
  .pair rightTailWf .top

private def outerIntersectionWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (outerIntersection (n := n))) :=
  .inter leftOuterWf rightOuterWf

private def normalizedOuterWf {n} {Gamma : Ctx n} :
    Tau.Wf Gamma (.ty (normalizedOuter (n := n))) :=
  .pair mergedTailWf .top

private def sourceTailToLeft {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceTail (n := n)))
      (.ty (leftTail (n := n))) :=
  .pair .refl sourceToLeft

private def sourceTailToRight {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceTail (n := n)))
      (.ty (rightTail (n := n))) :=
  .pair .refl sourceToRight

private def sourceTailToIntersection {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (sourceTail (n := n)))
      (.ty (tailIntersection (n := n))) :=
  .inter sourceTailToLeft sourceTailToRight

/-- Normalize the two views of the older `a` slot. -/
def tailIntersectionToMerged {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (tailIntersection (n := n)))
      (.ty (mergedTail (n := n))) := by
  simpa [tailIntersection, leftTail, rightTail, mergedTail,
    intersectionType] using
    (Tau.Sub.pair_inter (Γ := Gamma) (S := .Top)
      (a := innerLabel)
      (T := leftView (n := n + 1))
      (U := rightView (n := n + 1)))

/-- First merge the two outer views without changing their common member. -/
def outerIntersectionToFirstMerged {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (outerIntersection (n := n)))
      (.ty (firstMergedOuter (n := n))) := by
  simpa [outerIntersection, leftOuter, rightOuter, firstMergedOuter] using
    (Tau.Sub.pair_first_inter (Γ := Gamma)
      (S := leftTail (n := n)) (T := rightTail (n := n))
      (a := outerLabel) (d := Tau.ty Ty.Top))

/-- Pair covariance and meet introduction derive the converse view. -/
def firstMergedOuterToIntersection {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (firstMergedOuter (n := n)))
      (.ty (outerIntersection (n := n))) := by
  simpa [outerIntersection, leftOuter, rightOuter, firstMergedOuter] using
    (Tau.Sub.pair_first_inter_reverse (Γ := Gamma)
      (S := leftTail (n := n)) (T := rightTail (n := n))
      (a := outerLabel) (d := Tau.ty Ty.Top))

/-- Pair covariance transports the identical, nondependent `b` signature. -/
def firstMergedOuterToNormalized {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (firstMergedOuter (n := n)))
      (.ty (normalizedOuter (n := n))) :=
  .pair tailIntersectionToMerged .refl

def outerIntersectionToNormalized {n} {Gamma : Ctx n} :
    Tau.Sub Gamma (.ty (outerIntersection (n := n)))
      (.ty (normalizedOuter (n := n))) :=
  .trans outerIntersectionToFirstMerged firstMergedOuterToNormalized

/-! ## One physical telescope -/

def value : Tm 0 :=
  IntersectionRegression.value

/-- The inner pair stores the `a` member. -/
def innerValue : Tm 1 :=
  .pair 0 innerLabel (.val 0)

/-- The outer pair extends the inner record with the nondependent `b` member. -/
def outerValue : Tm 2 :=
  .pair 0 outerLabel (.val 1)

/-- A path-only alias at the normalized telescope type. -/
def normalizedAlias : Tm 3 :=
  .path (.var 0)

/-- Selection skips the outer `b` member; both operands denote the older `a`. -/
def body : Tm 4 :=
  .app ((Path.var 0).sel innerLabel) ((Path.var 0).sel innerLabel)

def term : Tm 0 :=
  .let value
    (.let innerValue
      (.let outerValue
        (.let normalizedAlias body)))

private def context1 : Ctx 1 :=
  Ctx.nil.snoc sourceType

private def context2 : Ctx 2 :=
  context1.snoc tailIntersection

private def context3 : Ctx 3 :=
  context2.snoc outerIntersection

private def context4 : Ctx 4 :=
  context3.snoc normalizedOuter

private def valueSourceTyping :
    Tm.Ty Ctx.nil value sourceType :=
  .abs
    (.abs
      (.sub (.path .var) (.widen .var) .top)
      .top)
    .top

private def innerExactToSource :
    Tau.Sub context1
      (.ty (.Pair (.Single (.var 0)) innerLabel
        (.ty (.Single (Path.var 0).weaken))))
      (.ty sourceTail) :=
  .pair .top (.widen .var)

private def innerValueSourceTyping :
    Tm.Ty context1 innerValue sourceTail :=
  .sub .pair innerExactToSource sourceTailWf

private def innerValueIntersectionTyping :
    Tm.Ty context1 innerValue tailIntersection :=
  .sub innerValueSourceTyping sourceTailToIntersection tailIntersectionWf

private def outerExactToLeft :
    Tau.Sub context2
      (.ty (.Pair (.Single (.var 0)) outerLabel
        (.ty (.Single (Path.var 1).weaken))))
      (.ty leftOuter) :=
  .pair
    (.trans (.widen .var) .inter_left)
    .top

private def outerExactToRight :
    Tau.Sub context2
      (.ty (.Pair (.Single (.var 0)) outerLabel
        (.ty (.Single (Path.var 1).weaken))))
      (.ty rightOuter) :=
  .pair
    (.trans (.widen .var) .inter_right)
    .top

private def outerValueIntersectionTyping :
    Tm.Ty context2 outerValue outerIntersection :=
  .sub .pair (.inter outerExactToLeft outerExactToRight) outerIntersectionWf

private def normalizedAliasTyping :
    Tm.Ty context3 normalizedAlias normalizedOuter :=
  .sub
    (.path .var)
    (.trans (.widen .var) outerIntersectionToNormalized)
    normalizedOuterWf

private def normalizedOuterPathTyping :
    Path.Ty context4 (.var 0) (.ty (normalizedOuter (n := 4))) := by
  simpa [context4, context3, context2, context1, Ctx.lookup,
    normalizedOuter, mergedTail, intersectionType, leftView, rightView,
    functionType, Ty.weaken, Tau.weaken, Ty.rename, Tau.rename] using
    (Path.Ty.var : Path.Ty context4 (.var 0)
      (.ty (Ctx.lookup context4 0)))

/-- Precise lookup walks past `b` and exposes `a : L ∩ R`. -/
def deepMemberPathTyping :
    Path.Ty context4 ((Path.var 0).sel innerLabel)
      (.ty (intersectionType (n := 4))) := by
  apply normalizedOuterPathTyping.sel_l
  · simpa [mergedTail, Tau.weaken_open] using
      normalizedOuterPathTyping.fst.sel_r
  · exact inner_ne_outer

private def deepFunctionTyping :
    Tm.Ty context4 (.path ((Path.var 0).sel innerLabel))
      (leftView (n := 4)) :=
  .sub
    (.path deepMemberPathTyping)
    (.trans (.widen deepMemberPathTyping) .inter_left)
    leftViewWf

private def deepArgumentTyping :
    Tm.Ty context4 (.path ((Path.var 0).sel innerLabel))
      (rightView (n := 4)) :=
  .sub
    (.path deepMemberPathTyping)
    (.trans (.widen deepMemberPathTyping) .inter_right)
    rightViewWf

private def bodyTyping :
    Tm.Ty context4 body (functionType (n := 4)) := by
  simpa [body, leftView, rightView, functionType, Ty.weaken_open] using
    Tm.Ty.app deepFunctionTyping deepArgumentTyping

def term_typing : Tm.Ty Ctx.nil term functionType :=
  .let valueSourceTyping functionTypeWf
    (.let innerValueIntersectionTyping functionTypeWf
      (.let outerValueIntersectionTyping functionTypeWf
        (.let normalizedAliasTyping functionTypeWf bodyTyping)))

theorem term_type_safety
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial term) target) :
    State.Progress target :=
  term_typing.closed_type_safety steps

end

end LambdaPFCI.AlignedRecordIntersectionRegression
