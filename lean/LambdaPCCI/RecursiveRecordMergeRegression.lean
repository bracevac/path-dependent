import LambdaPCCI.IntersectionRegression

/-!
A closed capture-aware regression for recursive aligned-record merging.

The program first allocates a pure capability `c : F`, then a function
`v : {c} S` which genuinely captures `c`.  An inner record stores the exact
capture member `A = {c}`.  Two views of an outer record are then merged:

```text
Q0 = { A : {c}..{c} }
QL = { A : empty..{c} }
QR = Q0
QI = { A : (empty union {c})..{c} }

PL = { x : QL; b : {c} L }
PR = { x : QR; b : x.A R }
PI = { x : QI; b : ({c} union x.A) (L inter R) }
```

The tail step exercises capture-member lower-bound merging.  The outer step
simultaneously recurses into that tail and merges different, nonempty term
capture contracts.  In the final context, selecting `q.b` exposes exactly
the union `{c} union q.fst.A`, while evaluating that path has the empty use
set.  Both shape projections then support the closed self-application
`q.b q.b`.
-/

namespace LambdaPCCI.RecursiveRecordMergeRegression

noncomputable section

open IntersectionRegression

def captureLabel : Name := 0
def valueLabel : Name := 1

/-! ## Capture-dependent record views -/

def capturedSource (p : Path n) : Ty n :=
  .capt (.singleton p) (sourceShape n)

def sourceTail (p : Path n) : Ty n :=
  .capt .empty
    (.Pair (pureTop n) captureLabel
      (Tau.capture (.singleton p) (.singleton p)).weaken)

def leftTail (p : Path n) : Ty n :=
  .capt .empty
    (.Pair (pureTop n) captureLabel
      (Tau.capture .empty (.singleton p)).weaken)

def rightTail (p : Path n) : Ty n :=
  sourceTail p

def mergedTail (p : Path n) : Ty n :=
  .capt .empty
    (.Pair (pureTop n) captureLabel
      (Tau.capture
        (.union .empty (.singleton p))
        (.singleton p)).weaken)

def sourceOuterShape (p : Path n) : Shape n :=
  .Pair (sourceTail p) valueLabel
    (.term (.capt (.singleton p.weaken) (sourceShape (n + 1))))

def leftOuterShape (p : Path n) : Shape n :=
  .Pair (leftTail p) valueLabel
    (.term (.capt (.singleton p.weaken) (leftViewShape (n + 1))))

def rightOuterShape (p : Path n) : Shape n :=
  .Pair (rightTail p) valueLabel
    (.term
      (.capt (.select (.var 0) captureLabel) (rightViewShape (n + 1))))

def mergedOuterShape (p : Path n) : Shape n :=
  .Pair (mergedTail p) valueLabel
    (.term
      (.capt
        (.union
          (.singleton p.weaken)
          (.select (.var 0) captureLabel))
        (.Inter (leftViewShape (n + 1)) (rightViewShape (n + 1)))))

def sourceOuter (p : Path n) : Ty n :=
  .capt .empty (sourceOuterShape p)

def outerIntersection (p : Path n) : Ty n :=
  .capt .empty (.Inter (leftOuterShape p) (rightOuterShape p))

def mergedOuter (p : Path n) : Ty n :=
  .capt .empty (mergedOuterShape p)

/-! ## Structural merge plans -/

def tailMergePlan {Gamma : Ctx n} {p : Path n} :
    Ty.Merge Gamma (leftTail p) (rightTail p) (mergedTail p) := by
  simpa [leftTail, rightTail, sourceTail, mergedTail] using
    (Ty.Merge.capt (Gamma := Gamma) CaptureSet.Join.same
      (Shape.Merge.pair Ty.Merge.same
        (Tau.Merge.capture CaptureSet.Join.union)))

def recursiveMergePlan {Gamma : Ctx n} {p : Path n} :
    Shape.Merge Gamma (leftOuterShape p) (rightOuterShape p)
      (mergedOuterShape p) := by
  simpa [leftOuterShape, rightOuterShape, mergedOuterShape] using
    (Shape.Merge.pair (tailMergePlan (Gamma := Gamma) (p := p))
      (Tau.Merge.term
        (Ty.Merge.capt CaptureSet.Join.union Shape.Merge.inter)))

def outerIntersectionToMerged {Gamma : Ctx n} {p : Path n} :
    Ty.Sub Gamma (outerIntersection p) (mergedOuter p) :=
  .capt .refl (.merge recursiveMergePlan)

/-! ## Closed allocation -/

def capability : Tm 0 :=
  .abs (pureTop 0) (.path (.var 0))

/-- The closure body refers to the previously allocated capability. -/
def capturedValue : Tm 1 :=
  .abs (pureTop 1) (.path (.var 1))

def captureMemberValue : Tm 2 :=
  .pair 1 captureLabel (.capture (.singleton (.var 1)))

def outerValue : Tm 3 :=
  .pair 0 valueLabel (.val 1)

def mergedAlias : Tm 4 :=
  .path (.var 0)

def body : Tm 5 :=
  .app ((Path.var 0).sel valueLabel) ((Path.var 0).sel valueLabel)

def term : Tm 0 :=
  .let capability
    (.let capturedValue
      (.let captureMemberValue
        (.let outerValue
          (.let mergedAlias body))))

private def context1 : Ctx 1 :=
  Ctx.nil.snoc (functionType 0)

private def context2 : Ctx 2 :=
  context1.snoc (capturedSource (.var 0))

private def context3 : Ctx 3 :=
  context2.snoc (sourceTail (.var 1))

private def context4 : Ctx 4 :=
  context3.snoc (outerIntersection (.var 2))

private def context5 : Ctx 5 :=
  context4.snoc (mergedOuter (.var 3))

/-! ## Common well-formed shapes -/

private def pureTopWf {Gamma : Ctx n} : Ty.Wf Gamma (pureTop n) :=
  .capt .empty .top

private def functionShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma (functionShape n) :=
  .fun pureTopWf pureTopWf

private def functionTypeWf {Gamma : Ctx n} :
    Ty.Wf Gamma (functionType n) :=
  .capt .empty functionShapeWf

private def sourceShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma (sourceShape n) :=
  .fun pureTopWf (by
    simpa [functionType, functionShape] using
      (functionTypeWf (Gamma := Gamma.snoc (pureTop n))))

private def leftViewShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma (leftViewShape n) :=
  .fun functionTypeWf (by
    simpa [functionType, functionShape] using
      (functionTypeWf (Gamma := Gamma.snoc (functionType n))))

private def rightViewShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma (rightViewShape n) :=
  functionShapeWf

private def intersectionShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma (.Inter (leftViewShape n) (rightViewShape n)) :=
  .inter leftViewShapeWf rightViewShapeWf

/-! ## Source paths and record well-formedness -/

private def capabilityPath1 :
    Path.Ty context1 (.var 0) (.term (functionType 1)) := by
  simpa [context1, Ctx.lookup, functionType, functionShape] using
    (Path.Ty.var : Path.Ty context1 (.var 0)
      (.term (Ctx.lookup context1 0)))

private def capabilityPath2 :
    Path.Ty context2 (.var 1) (.term (functionType 2)) := by
  simpa [context2, context1, Ctx.lookup, capturedSource, sourceShape,
    functionType, functionShape] using
    (Path.Ty.var : Path.Ty context2 (.var 1)
      (.term (Ctx.lookup context2 1)))

private def capabilityPath3 :
    Path.Ty context3 (.var 2) (.term (functionType 3)) := by
  simpa [context3, context2, context1, Ctx.lookup, sourceTail,
    capturedSource, sourceShape, functionType, functionShape] using
    (Path.Ty.var : Path.Ty context3 (.var 2)
      (.term (Ctx.lookup context3 2)))

private def capabilityPath4 :
    Path.Ty context4 (.var 3) (.term (functionType 4)) := by
  simpa [context4, context3, context2, context1, Ctx.lookup,
    outerIntersection, leftOuterShape, rightOuterShape, leftTail, rightTail,
    sourceTail, capturedSource, sourceShape, leftViewShape, rightViewShape,
    functionType, functionShape] using
    (Path.Ty.var : Path.Ty context4 (.var 3)
      (.term (Ctx.lookup context4 3)))

private def capabilityPath5 :
    Path.Ty context5 (.var 4) (.term (functionType 5)) := by
  simpa [context5, context4, context3, context2, context1, Ctx.lookup,
    mergedOuter, mergedOuterShape, mergedTail, capturedSource, sourceShape,
    leftViewShape, rightViewShape, functionType, functionShape] using
    (Path.Ty.var : Path.Ty context5 (.var 4)
      (.term (Ctx.lookup context5 4)))

private def sourceTailSelection
    {Gamma : Ctx n} {p path : Path n}
    (typing : Path.Ty Gamma path (.term (sourceTail p))) :
    Path.Ty Gamma (path.sel captureLabel)
      (.capture (.singleton p) (.singleton p)) := by
  simpa [sourceTail, Tau.weaken_open] using typing.sel_r

private def leftTailSelection
    {Gamma : Ctx n} {p path : Path n}
    (typing : Path.Ty Gamma path (.term (leftTail p))) :
    Path.Ty Gamma (path.sel captureLabel)
      (.capture .empty (.singleton p)) := by
  simpa [leftTail, Tau.weaken_open] using typing.sel_r

private def mergedTailSelection
    {Gamma : Ctx n} {p path : Path n}
    (typing : Path.Ty Gamma path (.term (mergedTail p))) :
    Path.Ty Gamma (path.sel captureLabel)
      (.capture (.union .empty (.singleton p)) (.singleton p)) := by
  simpa [mergedTail, Tau.weaken_open] using typing.sel_r

private def capturedSourceWf
    {Gamma : Ctx n} {p : Path n}
    (typing : Path.Ty Gamma p (.term (functionType n))) :
    Ty.Wf Gamma (capturedSource p) :=
  .capt (.singleton typing) sourceShapeWf

private def sourceTailWf2 :
    Ty.Wf context2 (sourceTail (.var 1)) := by
  have c : Path.Ty (context2.snoc (pureTop 2)) (.var 2)
      (.term (functionType 3)) := by
    simpa [context2, context1, Ctx.lookup, capturedSource, sourceShape,
      functionType, functionShape] using
      (Path.Ty.var : Path.Ty (context2.snoc (pureTop 2)) (.var 2)
        (.term (Ctx.lookup (context2.snoc (pureTop 2)) 2)))
  exact .capt .empty
    (.pair pureTopWf (.capture (.singleton c) (.singleton c) .refl))

private def sourceTailWf3 :
    Ty.Wf context3 (sourceTail (.var 2)) := by
  have c : Path.Ty (context3.snoc (pureTop 3)) (.var 3)
      (.term (functionType 4)) := by
    simpa [context3, context2, context1, Ctx.lookup, sourceTail,
      capturedSource, sourceShape, functionType, functionShape] using
      (Path.Ty.var : Path.Ty (context3.snoc (pureTop 3)) (.var 3)
        (.term (Ctx.lookup (context3.snoc (pureTop 3)) 3)))
  exact .capt .empty
    (.pair pureTopWf (.capture (.singleton c) (.singleton c) .refl))

private def leftTailWf3 :
    Ty.Wf context3 (leftTail (.var 2)) := by
  have c : Path.Ty (context3.snoc (pureTop 3)) (.var 3)
      (.term (functionType 4)) := by
    simpa [context3, context2, context1, Ctx.lookup, sourceTail,
      capturedSource, sourceShape, functionType, functionShape] using
      (Path.Ty.var : Path.Ty (context3.snoc (pureTop 3)) (.var 3)
        (.term (Ctx.lookup (context3.snoc (pureTop 3)) 3)))
  exact .capt .empty
    (.pair pureTopWf (.capture .empty (.singleton c) .empty))

private def rightTailWf3 :
    Ty.Wf context3 (rightTail (.var 2)) := by
  simpa [rightTail] using sourceTailWf3

private def mergedTailWf4 :
    Ty.Wf context4 (mergedTail (.var 3)) := by
  have c : Path.Ty (context4.snoc (pureTop 4)) (.var 4)
      (.term (functionType 5)) := by
    simpa [context4, context3, context2, context1, Ctx.lookup,
      outerIntersection, leftOuterShape, rightOuterShape, leftTail, rightTail,
      sourceTail, capturedSource, sourceShape, leftViewShape, rightViewShape,
      functionType, functionShape] using
      (Path.Ty.var : Path.Ty (context4.snoc (pureTop 4)) (.var 4)
        (.term (Ctx.lookup (context4.snoc (pureTop 4)) 4)))
  exact .capt .empty
    (.pair pureTopWf
      (.capture (.union .empty (.singleton c)) (.singleton c)
        (.union_elim .empty .refl)))

private def sourceOuterWf3 :
    Ty.Wf context3 (sourceOuter (.var 2)) := by
  have c : Path.Ty (context3.snoc (sourceTail (.var 2))) (.var 3)
      (.term (functionType 4)) := by
    simpa [context3, context2, context1, Ctx.lookup, sourceTail,
      capturedSource, sourceShape, functionType, functionShape] using
      (Path.Ty.var :
        Path.Ty (context3.snoc (sourceTail (.var 2))) (.var 3)
          (.term (Ctx.lookup (context3.snoc (sourceTail (.var 2))) 3)))
  exact .capt .empty
    (.pair sourceTailWf3
      (.term (.capt (.singleton c) sourceShapeWf)))

private def leftOuterWf3 :
    Shape.Wf context3 (leftOuterShape (.var 2)) := by
  have c : Path.Ty (context3.snoc (leftTail (.var 2))) (.var 3)
      (.term (functionType 4)) := by
    simpa [context3, context2, context1, Ctx.lookup, sourceTail,
      capturedSource, sourceShape, functionType, functionShape] using
      (Path.Ty.var :
        Path.Ty (context3.snoc (leftTail (.var 2))) (.var 3)
          (.term (Ctx.lookup (context3.snoc (leftTail (.var 2))) 3)))
  exact .pair leftTailWf3
    (.term (.capt (.singleton c) leftViewShapeWf))

private def rightOuterWf3 :
    Shape.Wf context3 (rightOuterShape (.var 2)) := by
  have selection :
      Path.Ty (context3.snoc (rightTail (.var 2)))
        ((Path.var 0).sel captureLabel)
        (.capture (.singleton (.var 3)) (.singleton (.var 3))) := by
    simpa [rightTail] using
      sourceTailSelection
        (Path.Ty.var :
          Path.Ty (context3.snoc (rightTail (.var 2))) (.var 0)
            (.term (Ctx.lookup
              (context3.snoc (rightTail (.var 2))) 0)))
  exact .pair rightTailWf3
    (.term (.capt (.select selection .refl) rightViewShapeWf))

private def outerIntersectionWf3 :
    Ty.Wf context3 (outerIntersection (.var 2)) :=
  .capt .empty (.inter leftOuterWf3 rightOuterWf3)

private def mergedOuterWf4 :
    Ty.Wf context4 (mergedOuter (.var 3)) := by
  have c : Path.Ty (context4.snoc (mergedTail (.var 3))) (.var 4)
      (.term (functionType 5)) := by
    simpa [context4, context3, context2, context1, Ctx.lookup,
      outerIntersection, leftOuterShape, rightOuterShape, leftTail, rightTail,
      sourceTail, capturedSource, sourceShape, leftViewShape, rightViewShape,
      functionType, functionShape] using
      (Path.Ty.var :
        Path.Ty (context4.snoc (mergedTail (.var 3))) (.var 4)
          (.term (Ctx.lookup (context4.snoc (mergedTail (.var 3))) 4)))
  have selection :
      Path.Ty (context4.snoc (mergedTail (.var 3)))
        ((Path.var 0).sel captureLabel)
        (.capture
          (.union .empty (.singleton (.var 4)))
          (.singleton (.var 4))) :=
    mergedTailSelection
      (Path.Ty.var :
        Path.Ty (context4.snoc (mergedTail (.var 3))) (.var 0)
          (.term (Ctx.lookup (context4.snoc (mergedTail (.var 3))) 0)))
  exact .capt .empty
    (.pair mergedTailWf4
      (.term
        (.capt
          (.union (.singleton c)
            (.select selection (.union_elim .empty .refl)))
          intersectionShapeWf)))

/-! ## Source view construction -/

private def sourceTailToLeft3 :
    Ty.Sub context3 (sourceTail (.var 2)) (leftTail (.var 2)) :=
  .capt .refl
    (.pair .refl (.capture .empty .refl .refl))

private def sourceOuterShapeToLeft3 :
    Shape.Sub context3 (sourceOuterShape (.var 2))
      (leftOuterShape (.var 2)) :=
  .pair sourceTailToLeft3
    (.term (.capt .refl sourceToLeft))

private def sourceOuterShapeToRight3 :
    Shape.Sub context3 (sourceOuterShape (.var 2))
      (rightOuterShape (.var 2)) := by
  apply Shape.Sub.pair .refl
  apply Tau.Sub.term
  apply Ty.Sub.capt
  · exact .select_lower (sourceTailSelection .var) .refl
  · exact sourceToRight

private def sourceOuterToIntersection3 :
    Ty.Sub context3 (sourceOuter (.var 2))
      (outerIntersection (.var 2)) :=
  .capt .refl (.inter sourceOuterShapeToLeft3 sourceOuterShapeToRight3)

/-! ## Typing the closed allocations -/

private def capabilityBodyTyping :
    Tm.Ty (Ctx.nil.snoc (pureTop 0)) (.path (.var 0))
      (pureTop 1) (.union .empty (.singleton (.var 0))) :=
  .sub
    (.path .var)
    (.capt (.path .var) .top)
    .union_right
    pureTopWf
    (.union .empty (.singleton .var))

private def capabilityTyping :
    Tm.Ty Ctx.nil capability (functionType 0) .empty :=
  .abs capabilityBodyTyping pureTopWf .empty

private def capturedBodyContext : Ctx 2 :=
  context1.snoc (pureTop 1)

private def capturedBodyCapabilityPath :
    Path.Ty capturedBodyContext (.var 1)
      (.term (functionType 1).weaken) := by
  simpa [capturedBodyContext, context1, Ctx.lookup, functionType,
    functionShape] using
    (Path.Ty.var : Path.Ty capturedBodyContext (.var 1)
      (.term (Ctx.lookup capturedBodyContext 1)))

private def capturedBodyArgumentPath :
    Path.Ty capturedBodyContext (.var 0) (.term (pureTop 2)) := by
  simpa [capturedBodyContext, Ctx.lookup] using
    (Path.Ty.var : Path.Ty capturedBodyContext (.var 0)
      (.term (Ctx.lookup capturedBodyContext 0)))

private def capturedBodyTyping :
    Tm.Ty capturedBodyContext (.path (.var 1))
      (functionType 1).weaken
      (.union (.singleton (.var 1)) (.singleton (.var 0))) :=
  .sub
    (.path capturedBodyCapabilityPath)
    (.capt (.path capturedBodyCapabilityPath)
      (.singleton_widen capturedBodyCapabilityPath))
    .union_left
    (by
      simpa [functionType, functionShape] using
        (functionTypeWf (Gamma := capturedBodyContext)))
    (.union (.singleton capturedBodyCapabilityPath)
      (.singleton capturedBodyArgumentPath))

private def capturedValueTyping :
    Tm.Ty context1 capturedValue (capturedSource (.var 0)) .empty := by
  have body' :
      Tm.Ty (context1.snoc (pureTop 1)) (.path (.var 1))
        (functionType 1).weaken
        (.union (CaptureSet.singleton (Path.var 0)).weaken
          (.singleton (.var 0))) := by
    simpa [capturedBodyContext, CaptureSet.weaken, CaptureSet.rename,
      Path.rename] using capturedBodyTyping
  simpa [capturedValue, capturedSource, sourceShape] using
    (Tm.Ty.abs body' pureTopWf
      (CaptureSet.Wf.singleton capabilityPath1))

private def capturedValuePath2 :
    Path.Ty context2 (.var 0)
      (.term (capturedSource (.var 1))) := by
  simpa [context2, context1, Ctx.lookup, capturedSource, sourceShape,
    functionType, functionShape] using
    (Path.Ty.var : Path.Ty context2 (.var 0)
      (.term (Ctx.lookup context2 0)))

private def captureMemberExactToSource :
    Ty.Sub context2
      (.capt (.singleton (.var 1))
        (.Pair
          (.capt (.singleton (.var 1)) (.Single (.var 1)))
          captureLabel
          (Tau.capture
            (.singleton (.var 1))
            (.singleton (.var 1))).weaken))
      (sourceTail (.var 1)) :=
  .capt
    (.path capabilityPath2)
    (.pair
      (.capt (.path capabilityPath2) .top)
      .refl)

private def captureMemberValueTyping :
    Tm.Ty context2 captureMemberValue (sourceTail (.var 1)) .empty :=
  .sub
    (.capture_pair (.singleton capabilityPath2))
    captureMemberExactToSource
    .refl
    sourceTailWf2
    .empty

private def capturedValuePath3 :
    Path.Ty context3 (.var 1)
      (.term (capturedSource (.var 2))) := by
  simpa [context3, context2, context1, Ctx.lookup, sourceTail,
    capturedSource, sourceShape, functionType, functionShape] using
    (Path.Ty.var : Path.Ty context3 (.var 1)
      (.term (Ctx.lookup context3 1)))

private def sourceTailPath3 :
    Path.Ty context3 (.var 0)
      (.term (sourceTail (.var 2))) := by
  simpa [context3, context2, context1, Ctx.lookup, sourceTail,
    capturedSource, sourceShape, functionType, functionShape] using
    (Path.Ty.var : Path.Ty context3 (.var 0)
      (.term (Ctx.lookup context3 0)))

private def outerMemberContext : Ctx 4 :=
  context3.snoc
    (.capt (.singleton (.var 0)) (.Single (.var 0)))

private def outerMemberValuePath :
    Path.Ty outerMemberContext (.var 2)
      (.term (capturedSource (.var 3))) := by
  simpa [outerMemberContext, context3, context2, context1, Ctx.lookup,
    sourceTail, capturedSource, sourceShape, functionType, functionShape] using
    (Path.Ty.var : Path.Ty outerMemberContext (.var 2)
      (.term (Ctx.lookup outerMemberContext 2)))

private def outerExactToSource :
    Ty.Sub context3
      (.capt
        (.union (.singleton (.var 0)) (.singleton (.var 1)))
        (.Pair
          (.capt (.singleton (.var 0)) (.Single (.var 0)))
          valueLabel
          (.term
            (.capt
              (.singleton (Path.var 1).weaken)
              (.Single (Path.var 1).weaken)))))
      (sourceOuter (.var 2)) := by
  apply Ty.Sub.capt
  · exact .union_elim
      (.path sourceTailPath3)
      (.trans (.path capturedValuePath3) (.path capabilityPath3))
  · apply Shape.Sub.pair
    · exact .capt
        (.path sourceTailPath3)
        (.singleton_widen sourceTailPath3)
    · exact .term
        (.capt
          (.path outerMemberValuePath)
          (.singleton_widen outerMemberValuePath))

private def outerValueSourceTyping :
    Tm.Ty context3 outerValue (sourceOuter (.var 2)) .empty :=
  .sub .pair outerExactToSource .refl sourceOuterWf3 .empty

private def outerValueIntersectionTyping :
    Tm.Ty context3 outerValue (outerIntersection (.var 2)) .empty :=
  .sub outerValueSourceTyping sourceOuterToIntersection3 .refl
    outerIntersectionWf3 .empty

private def outerIntersectionPath4 :
    Path.Ty context4 (.var 0)
      (.term (outerIntersection (.var 3))) := by
  simpa [context4, context3, context2, context1, Ctx.lookup,
    outerIntersection, leftOuterShape, rightOuterShape, leftTail, rightTail,
    sourceTail, capturedSource, sourceShape, leftViewShape, rightViewShape,
    functionType, functionShape] using
    (Path.Ty.var : Path.Ty context4 (.var 0)
      (.term (Ctx.lookup context4 0)))

private def mergedAliasTyping :
    Tm.Ty context4 mergedAlias (mergedOuter (.var 3)) .empty :=
  .sub
    (.path outerIntersectionPath4)
    (.trans
      (.capt (.path outerIntersectionPath4)
        (.singleton_widen outerIntersectionPath4))
      outerIntersectionToMerged)
    (.path outerIntersectionPath4)
    mergedOuterWf4
    .empty

/-! ## The observable merged capture contract -/

def mergedMemberCapture : CaptureSet 5 :=
  .union
    (.singleton (.var 4))
    (.select (Path.var 0).fst captureLabel)

private def mergedOuterPath5 :
    Path.Ty context5 (.var 0)
      (.term (mergedOuter (.var 4))) := by
  simpa [context5, context4, context3, context2, context1, Ctx.lookup,
    mergedOuter, mergedOuterShape, mergedTail, capturedSource, sourceShape,
    leftViewShape, rightViewShape, functionType, functionShape] using
    (Path.Ty.var : Path.Ty context5 (.var 0)
      (.term (Ctx.lookup context5 0)))

/-- Precise selection exposes the union of two distinct nonempty capture
contracts: the ambient capability and the abstract member of the merged
record tail. -/
def merged_member_path_typing :
    Path.Ty context5 ((Path.var 0).sel valueLabel)
      (.term
        (.capt mergedMemberCapture
          (.Inter (leftViewShape 5) (rightViewShape 5)))) := by
  simpa [mergedOuter, mergedOuterShape, mergedMemberCapture, Tau.open,
    Ty.open, Tau.subst, Ty.subst, CaptureSet.subst, Shape.subst,
    Path.subst, PathSubst.openAt] using mergedOuterPath5.sel_r

private def mergedCaptureSelectionTyping :
    Path.Ty context5 ((Path.var 0).fst.sel captureLabel)
      (.capture
        (.union .empty (.singleton (.var 4)))
        (.singleton (.var 4))) :=
  mergedTailSelection mergedOuterPath5.fst

private def mergedCaptureBounds :
    CaptureSet.Sub context5
      (.union .empty (.singleton (.var 4)))
      (.singleton (.var 4)) :=
  .union_elim .empty .refl

private def mergedMemberCaptureWf :
    CaptureSet.Wf context5 mergedMemberCapture :=
  .union
    (.singleton capabilityPath5)
    (.select mergedCaptureSelectionTyping mergedCaptureBounds)

private def mergedMemberTypeWf :
    Ty.Wf context5
      (.capt mergedMemberCapture
        (.Inter (leftViewShape 5) (rightViewShape 5))) :=
  .capt mergedMemberCaptureWf intersectionShapeWf

private def mergedSelectionUseToEmpty :
    CaptureSet.Sub context5
      (.singleton ((Path.var 0).sel valueLabel)) .empty :=
  .trans
    (.sel_root merged_member_path_typing)
    (.path mergedOuterPath5)

/-- The selected value carries the merged nonempty capture contract, while
the act of evaluating its path has empty use because the containing record is
pure. -/
def merged_member_typing :
    Tm.Ty context5 (.path ((Path.var 0).sel valueLabel))
      (.capt mergedMemberCapture
        (.Inter (leftViewShape 5) (rightViewShape 5)))
      .empty :=
  .sub
    (.path merged_member_path_typing)
    (.capt
      (.path merged_member_path_typing)
      (.singleton_widen merged_member_path_typing))
    mergedSelectionUseToEmpty
    mergedMemberTypeWf
    .empty

private def mergedCaptureToEmpty :
    CaptureSet.Sub context5 mergedMemberCapture .empty :=
  .union_elim
    (.path capabilityPath5)
    (.trans
      (.select_upper mergedCaptureSelectionTyping mergedCaptureBounds)
      (.path capabilityPath5))

private def functionMemberTyping :
    Tm.Ty context5 (.path ((Path.var 0).sel valueLabel))
      (.capt mergedMemberCapture (leftViewShape 5)) .empty :=
  .sub merged_member_typing
    (.capt .refl .inter_left)
    .refl
    (.capt mergedMemberCaptureWf leftViewShapeWf)
    .empty

private def argumentMemberTyping :
    Tm.Ty context5 (.path ((Path.var 0).sel valueLabel))
      (rightView 5) .empty :=
  .sub merged_member_typing
    (.capt mergedCaptureToEmpty .inter_right)
    .refl
    rightViewWf
    .empty

private def bodyTyping :
    Tm.Ty context5 body (functionType 5) .empty := by
  apply Tm.Ty.sub
  · simpa [body, leftViewShape, rightView, rightViewShape,
      functionType, functionShape, Ty.weaken_open] using
      Tm.Ty.app functionMemberTyping argumentMemberTyping
  · exact .refl
  · exact .union_elim .empty .empty
  · exact functionTypeWf
  · exact .empty

def term_typing :
    Tm.Ty Ctx.nil term (functionType 0) .empty := by
  unfold term
  exact .let capabilityTyping
    (.let capturedValueTyping
      (.let captureMemberValueTyping
        (.let outerValueIntersectionTyping
          (.let mergedAliasTyping bodyTyping functionTypeWf .empty)
          functionTypeWf .empty)
        functionTypeWf .empty)
      functionTypeWf .empty)
    functionTypeWf .empty

theorem term_type_safety
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial term) target) :
    State.Progress target :=
  term_typing.closed_type_safety steps

end

end LambdaPCCI.RecursiveRecordMergeRegression
