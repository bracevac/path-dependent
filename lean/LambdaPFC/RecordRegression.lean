import LambdaPFC.SemanticSafety

/-!
A closed regression for right-nested records and path-dependent types:

```text
I   = Top -> Top
r1  = { A = I }
r2  = { r1; x = implementation }  with r2.x : r2.A by subsumption
use = fun (f : r2.A) => f implementation
r3  = { r2; use : r2.A -> Top }
in r3.use r3.x
```

The annotation on `use` is literally `r2.A`.  Since `x` is the outer member
of `r2`, forming that annotation requires lookup to skip `x`; it cannot be
justified by the former immediate-member-only well-formedness rule.
-/

namespace LambdaPFC.RecordRegression

noncomputable section

def typeLabel : Name := 0
def valueLabel : Name := 1
def useLabel : Name := 2

private theorem type_ne_value : typeLabel ≠ valueLabel := by decide
private theorem type_ne_use : typeLabel ≠ useLabel := by decide
private theorem value_ne_use : valueLabel ≠ useLabel := by decide

def implementationType : Ty n :=
  .Fun .Top .Top

def firstRecord : Ty n :=
  .Pair implementationType typeLabel
    (Tau.intv implementationType implementationType).weaken

def secondRecord : Ty n :=
  .Pair firstRecord valueLabel
    (.ty (.TSel (.var 0) typeLabel))

def thirdRecord : Ty n :=
  .Pair secondRecord useLabel
    (.ty (.Fun (.TSel (.var 0) typeLabel) .Top))

/-! ## Lookup and well-formedness through the record spine -/

def firstRecord_type
    (typing : Path.Ty Gamma path (.ty firstRecord)) :
    Path.Ty Gamma (path.sel typeLabel)
      (.intv implementationType implementationType) := by
  simpa [firstRecord, Tau.weaken_open] using typing.sel_r

/-- Lookup of `A` in `r2` skips its outer `x` member. -/
def secondRecord_type
    (typing : Path.Ty Gamma path (.ty secondRecord)) :
    Path.Ty Gamma (path.sel typeLabel)
      (.intv implementationType implementationType) :=
  typing.sel_l (firstRecord_type typing.fst) type_ne_value

/-- Lookup of `A` in `r3` skips both `use` and `x`. -/
def thirdRecord_type
    (typing : Path.Ty Gamma path (.ty thirdRecord)) :
    Path.Ty Gamma (path.sel typeLabel)
      (.intv implementationType implementationType) :=
  typing.sel_l (secondRecord_type typing.fst) type_ne_use

def implementationTypeWf : Tau.Wf Gamma (.ty implementationType) :=
  .fun .top .top

private def firstRecordWf : Tau.Wf Gamma (.ty firstRecord) := by
  simpa [firstRecord, implementationType, Tau.weaken, Ty.weaken, Tau.rename,
    Ty.rename] using
    (Tau.Wf.pair (Γ := Gamma) implementationTypeWf
      (Tau.Wf.bounds_wf implementationTypeWf implementationTypeWf
        Tau.Sub.refl))

private def secondRecordWf : Tau.Wf Gamma (.ty secondRecord) := by
  apply Tau.Wf.pair firstRecordWf
  apply Tau.Wf.sel
  apply firstRecord_type
  simpa [Ctx.lookup, firstRecord] using
    (Path.Ty.var : Path.Ty (Gamma.snoc firstRecord) (.var 0)
      (.ty (Ctx.lookup (Gamma.snoc firstRecord) 0)))
  exact .refl

/-- The new `WF-Select` premise derives direct `r2.A` through the nested
lookup, without changing the type to `r2.fst.A`. -/
def nested_selection_wf
    (typing : Path.Ty Gamma path (.ty secondRecord)) :
    Tau.Wf Gamma (.ty (.TSel path typeLabel)) :=
  .sel (secondRecord_type typing) .refl

private def thirdRecordWf : Tau.Wf Gamma (.ty thirdRecord) := by
  apply Tau.Wf.pair secondRecordWf
  apply Tau.Wf.fun
  · apply nested_selection_wf
    simpa [Ctx.lookup, secondRecord] using
      (Path.Ty.var : Path.Ty (Gamma.snoc secondRecord) (.var 0)
        (.ty (Ctx.lookup (Gamma.snoc secondRecord) 0)))
  · exact .top

/-! ## Closed program -/

def implementation : Tm 0 :=
  .abs .Top (.path (.var 0))

def firstValue : Tm 1 :=
  .pair 0 typeLabel (.type implementationType)

def secondValue : Tm 2 :=
  .pair 0 valueLabel (.val 1)

/-- Variable 0 is `r2`, so the source annotation is exactly `r2.A`. -/
def useValue : Tm 3 :=
  .abs (.TSel (.var 0) typeLabel)
    (.app (.var 0) (.var 3))

def thirdValue : Tm 4 :=
  .pair 1 useLabel (.val 0)

def body : Tm 5 :=
  .app ((Path.var 0).sel useLabel) ((Path.var 0).sel valueLabel)

def term : Tm 0 :=
  .let implementation
    (.let firstValue
      (.let secondValue
        (.let useValue
          (.let thirdValue body))))

/-! ## Source typing -/

private def context1 : Ctx 1 :=
  Ctx.nil.snoc implementationType

private def context2 : Ctx 2 :=
  context1.snoc firstRecord

private def context3 : Ctx 3 :=
  context2.snoc secondRecord

private def useType : Ty 3 :=
  .Fun (.TSel (.var 0) typeLabel) .Top

private def context4 : Ctx 4 :=
  context3.snoc useType

private def context5 : Ctx 5 :=
  context4.snoc thirdRecord

private def implementationTyping :
    Tm.Ty Ctx.nil implementation implementationType :=
  .abs
    (.sub (.path .var) (.widen .var) .top)
    .top

private def firstValueTyping :
    Tm.Ty context1 firstValue firstRecord := by
  apply Tm.Ty.sub (Tm.Ty.tpair implementationTypeWf)
  · apply Tau.Sub.pair
    · exact .widen .var
    · exact .refl
  · exact firstRecordWf

/- The intermediate type names the allocated `r1`; the final type changes
that reference to the pair binder after the first component has been widened. -/
private def secondIntermediate : Ty 2 :=
  .Pair firstRecord valueLabel
    (.ty (.TSel (.var 1) typeLabel))

private def secondExactToIntermediate :
    Tau.Sub context2
      (.ty (.Pair (.Single (.var 0)) valueLabel
        (.ty (.Single (Path.var 1).weaken))))
      (.ty secondIntermediate) := by
  apply Tau.Sub.pair
  · exact .widen .var
  · exact .trans
      (.widen .var)
      (.sel_lo (firstRecord_type .var) .refl)

private def secondIntermediateToRecord :
    Tau.Sub context2 (.ty secondIntermediate) (.ty secondRecord) := by
  apply Tau.Sub.pair .refl
  exact .trans
    (.sel_hi (firstRecord_type .var) .refl)
    (.sel_lo (firstRecord_type .var) .refl)

private def secondValueTyping :
    Tm.Ty context2 secondValue secondRecord :=
  .sub
    .pair
    (.trans secondExactToIntermediate secondIntermediateToRecord)
    secondRecordWf

/-- The concrete nested lookup used in the lambda annotation. -/
def r2_type_selection_typing :
    Path.Ty context3 ((Path.var 0).sel typeLabel)
      (.intv implementationType implementationType) := by
  apply secondRecord_type
  simpa [context3, context2, context1, Ctx.lookup, secondRecord] using
    (Path.Ty.var : Path.Ty context3 (.var 0)
      (.ty (Ctx.lookup context3 0)))

/-- This exact proof was impossible with the old `Tau.Wf.sel` rule. -/
def r2_type_selection_wf :
    Tau.Wf context3 (.ty (.TSel (.var 0) typeLabel)) :=
  .sel r2_type_selection_typing .refl

private def useBodyContext : Ctx 4 :=
  context3.snoc (.TSel (.var 0) typeLabel)

private def selectedParameterTyping :
    Tm.Ty useBodyContext (.path (.var 0)) implementationType := by
  apply Tm.Ty.sub (Tm.Ty.path Path.Ty.var)
  · exact .trans
      (.widen .var)
      (.sel_hi (secondRecord_type .var) .refl)
  · exact implementationTypeWf

private def useArgumentTyping :
    Tm.Ty useBodyContext (.path (.var 3)) .Top :=
  .sub (.path .var) .top .top

private def useValueTyping :
    Tm.Ty context3 useValue useType :=
  .abs
    (.app selectedParameterTyping useArgumentTyping)
    r2_type_selection_wf

/- `thirdIntermediate` retains the allocated `r2` in the `use` signature;
the next step relates it to the first-component binder of `thirdRecord`. -/
private def thirdIntermediate : Ty 4 :=
  .Pair secondRecord useLabel
    (.ty (.Fun (.TSel (.var 2) typeLabel) .Top))

private def thirdExactToIntermediate :
    Tau.Sub context4
      (.ty (.Pair (.Single (.var 1)) useLabel
        (.ty (.Single (Path.var 0).weaken))))
      (.ty thirdIntermediate) := by
  apply Tau.Sub.pair
  · exact .widen .var
  · exact .widen .var

private def thirdIntermediateToRecord :
    Tau.Sub context4 (.ty thirdIntermediate) (.ty thirdRecord) := by
  apply Tau.Sub.pair .refl
  apply Tau.Sub.fun
  · exact .trans
      (.sel_hi (secondRecord_type .var) .refl)
      (.sel_lo (secondRecord_type .var) .refl)
  · exact .refl

private def thirdValueTyping :
    Tm.Ty context4 thirdValue thirdRecord :=
  .sub
    .pair
    (.trans thirdExactToIntermediate thirdIntermediateToRecord)
    thirdRecordWf

/-- `r3.use` expects the direct selection `r3.fst.A` (that is, `r2.A`). -/
def use_selection_typing :
    Path.Ty context5 ((Path.var 0).sel useLabel)
      (.ty (.Fun (.TSel (Path.var 0).fst typeLabel) .Top)) := by
  simpa [thirdRecord, Tau.open, Ty.open, Tau.subst, Ty.subst,
    Path.subst, PathSubst.openAt] using
    (Path.Ty.sel_r (Path.Ty.var :
      Path.Ty context5 (.var 0) (.ty (Ctx.lookup context5 0))))

private def r3FstTyping :
    Path.Ty context5 (Path.var 0).fst (.ty secondRecord) := by
  exact Path.Ty.fst Path.Ty.var

private def r3FstFstTyping :
    Path.Ty context5 (Path.var 0).fst.fst (.ty firstRecord) :=
  Path.Ty.fst r3FstTyping

/-- `r3.x` is found by skipping the outer `use` member. -/
def value_selection_typing :
    Path.Ty context5 ((Path.var 0).sel valueLabel)
      (.ty (.TSel (Path.var 0).fst.fst typeLabel)) := by
  apply Path.Ty.sel_l
  · exact Path.Ty.var
  · exact Path.Ty.sel_r r3FstTyping
  · exact value_ne_use

private def bodyFunctionTyping :
    Tm.Ty context5 (.path ((Path.var 0).sel useLabel))
      (.Fun (.TSel (Path.var 0).fst typeLabel) .Top) :=
  .sub
    (.path use_selection_typing)
    (.widen use_selection_typing)
    (.fun (nested_selection_wf r3FstTyping) .top)

/-- Exact bounds bridge the stored inner `r1.A` to the direct receiver
selection `r3.fst.A`; no annotation is rewritten to `receiver.fst.A`. -/
def value_term_typing :
    Tm.Ty context5 (.path ((Path.var 0).sel valueLabel))
      (.TSel (Path.var 0).fst typeLabel) :=
  .sub
    (.path value_selection_typing)
    (.trans
      (.widen value_selection_typing)
      (.trans
        (.sel_hi (firstRecord_type r3FstFstTyping) .refl)
        (.sel_lo (secondRecord_type r3FstTyping) .refl)))
    (nested_selection_wf r3FstTyping)

private def bodyTyping : Tm.Ty context5 body .Top :=
  .app bodyFunctionTyping value_term_typing

def term_typing : Tm.Ty Ctx.nil term .Top :=
  .let implementationTyping .top
    (.let firstValueTyping .top
      (.let secondValueTyping .top
        (.let useValueTyping .top
          (.let thirdValueTyping .top bodyTyping))))

theorem term_type_safety
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial term) target) :
    State.Progress target :=
  term_typing.closed_type_safety steps

end

end LambdaPFC.RecordRegression
