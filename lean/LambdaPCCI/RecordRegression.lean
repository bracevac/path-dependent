import LambdaPCCI.CaptureSafety

/-!
A capture-aware mirror of the closed right-nested-record regression in
`LambdaPFCI.RecordRegression`:

```text
I   = Top -> Top
r1  = { A = I }
r2  = { r1; x = implementation }  with r2.x : r2.A by subsumption
use = fun (f : r2.A) => f implementation
r3  = { r2; use : r2.A -> Top }
in r3.use r3.x
```

The annotation on `use` is literally `r2.A`.  All exposed capturing types
have the empty capture set; the term nevertheless exercises the capture-aware
typing and safety developments.
-/

namespace LambdaPCCI.RecordRegression

noncomputable section

def typeLabel : Name := 0
def valueLabel : Name := 1
def useLabel : Name := 2

private theorem type_ne_value : typeLabel ≠ valueLabel := by decide
private theorem type_ne_use : typeLabel ≠ useLabel := by decide
private theorem value_ne_use : valueLabel ≠ useLabel := by decide

def pureTop (n : Nat) : Ty n :=
  .capt .empty .Top

def implementationShape (n : Nat) : Shape n :=
  .Fun (pureTop n) (pureTop (n + 1))

def implementationType (n : Nat) : Ty n :=
  .capt .empty (implementationShape n)

def firstRecord (n : Nat) : Ty n :=
  .capt .empty
    (.Pair (implementationType n) typeLabel
      (.type (implementationShape n).weaken
        (implementationShape n).weaken))

def secondRecord (n : Nat) : Ty n :=
  .capt .empty
    (.Pair (firstRecord n) valueLabel
      (.term (.capt .empty (.TSel (.var 0) typeLabel))))

def thirdRecord (n : Nat) : Ty n :=
  .capt .empty
    (.Pair (secondRecord n) useLabel
      (.term
        (.capt .empty
          (.Fun
            (.capt .empty (.TSel (.var 0) typeLabel))
            (pureTop (n + 2))))))

/-! ## Lookup and well-formedness through the record spine -/

def firstRecord_type
    {Gamma : Ctx n} {path : Path n}
    (typing : Path.Ty Gamma path (.term (firstRecord n))) :
    Path.Ty Gamma (path.sel typeLabel)
      (.type (implementationShape n) (implementationShape n)) := by
  simpa [firstRecord, Tau.weaken_open] using typing.sel_r

/-- Lookup of `A` in `r2` skips its outer `x` member. -/
def secondRecord_type
    {Gamma : Ctx n} {path : Path n}
    (typing : Path.Ty Gamma path (.term (secondRecord n))) :
    Path.Ty Gamma (path.sel typeLabel)
      (.type (implementationShape n) (implementationShape n)) :=
  typing.sel_l (firstRecord_type typing.fst) type_ne_value

/-- Lookup of `A` in `r3` skips both `use` and `x`. -/
def thirdRecord_type
    {Gamma : Ctx n} {path : Path n}
    (typing : Path.Ty Gamma path (.term (thirdRecord n))) :
    Path.Ty Gamma (path.sel typeLabel)
      (.type (implementationShape n) (implementationShape n)) :=
  typing.sel_l (secondRecord_type typing.fst) type_ne_use

private def pureTopWf {Gamma : Ctx n} :
    Ty.Wf Gamma (pureTop n) :=
  .capt .empty .top

private def implementationShapeWf {Gamma : Ctx n} :
    Shape.Wf Gamma (implementationShape n) :=
  .fun pureTopWf pureTopWf

def implementationTypeWf {Gamma : Ctx n} :
    Ty.Wf Gamma (implementationType n) :=
  .capt .empty implementationShapeWf

private def firstRecordWf {Gamma : Ctx n} :
    Ty.Wf Gamma (firstRecord n) := by
  apply Ty.Wf.capt .empty
  apply Shape.Wf.pair implementationTypeWf
  apply Tau.Wf.type
  · simpa [implementationShape] using
      (implementationShapeWf (Gamma := Gamma.snoc (implementationType n)))
  · simpa [implementationShape] using
      (implementationShapeWf (Gamma := Gamma.snoc (implementationType n)))
  · exact .refl

private def secondRecordWf {Gamma : Ctx n} :
    Ty.Wf Gamma (secondRecord n) := by
  apply Ty.Wf.capt .empty
  apply Shape.Wf.pair firstRecordWf
  apply Tau.Wf.term
  apply Ty.Wf.capt .empty
  apply Shape.Wf.select
  · apply firstRecord_type
    simpa [Ctx.lookup, firstRecord] using
      (Path.Ty.var : Path.Ty (Gamma.snoc (firstRecord n)) (.var 0)
        (.term (Ctx.lookup (Gamma.snoc (firstRecord n)) 0)))
  · exact .refl

/-- The generalized `WF-Select` premise derives direct `r2.A` from nested lookup
through the record spine, without rewriting it to `r2.fst.A`. -/
def nested_selection_wf
    {Gamma : Ctx n} {path : Path n}
    (typing : Path.Ty Gamma path (.term (secondRecord n))) :
    Ty.Wf Gamma (.capt .empty (.TSel path typeLabel)) :=
  .capt .empty (.select (secondRecord_type typing) .refl)

private def thirdRecordWf {Gamma : Ctx n} :
    Ty.Wf Gamma (thirdRecord n) := by
  apply Ty.Wf.capt .empty
  apply Shape.Wf.pair secondRecordWf
  apply Tau.Wf.term
  apply Ty.Wf.capt .empty
  apply Shape.Wf.fun
  · apply nested_selection_wf
    simpa [Ctx.lookup, secondRecord] using
      (Path.Ty.var : Path.Ty (Gamma.snoc (secondRecord n)) (.var 0)
        (.term (Ctx.lookup (Gamma.snoc (secondRecord n)) 0)))
  · exact pureTopWf

/-! ## Closed program -/

def implementation : Tm 0 :=
  .abs (pureTop 0) (.path (.var 0))

def firstValue : Tm 1 :=
  .pair 0 typeLabel (.type (implementationShape 1))

def secondValue : Tm 2 :=
  .pair 0 valueLabel (.val 1)

/-- Variable 0 is `r2`, so the source annotation is exactly `r2.A`. -/
def useValue : Tm 3 :=
  .abs (.capt .empty (.TSel (.var 0) typeLabel))
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
  Ctx.nil.snoc (implementationType 0)

private def context2 : Ctx 2 :=
  context1.snoc (firstRecord 1)

private def context3 : Ctx 3 :=
  context2.snoc (secondRecord 2)

private def useType : Ty 3 :=
  .capt .empty
    (.Fun
      (.capt .empty (.TSel (.var 0) typeLabel))
      (pureTop 4))

private def context4 : Ctx 4 :=
  context3.snoc useType

private def context5 : Ctx 5 :=
  context4.snoc (thirdRecord 4)

private def implementationBodyTyping :
    Tm.Ty (Ctx.nil.snoc (pureTop 0))
      (.path (.var 0)) (pureTop 1)
      (.union .empty (.singleton (.var 0))) :=
  .sub
    (.path .var)
    (.capt (.path .var) .top)
    .union_right
    pureTopWf
    (.union .empty (.singleton .var))

private def implementationTyping :
    Tm.Ty Ctx.nil implementation (implementationType 0) .empty :=
  .abs implementationBodyTyping pureTopWf .empty

private def firstValueTyping :
    Tm.Ty context1 firstValue (firstRecord 1) .empty := by
  apply Tm.Ty.sub (Tm.Ty.type_pair implementationShapeWf)
  · apply Ty.Sub.capt (.path .var)
    apply Shape.Sub.pair
    · exact .capt (.path .var) (.singleton_widen .var)
    · exact .refl
  · exact .refl
  · exact firstRecordWf
  · exact .empty

/- The intermediate type names the allocated `r1`; the final type changes
that reference to the pair binder after the first component has been widened. -/
private def secondIntermediate : Ty 2 :=
  .capt .empty
    (.Pair (firstRecord 2) valueLabel
      (.term (.capt .empty (.TSel (.var 1) typeLabel))))

private def secondExactToIntermediate :
    Ty.Sub context2
      (.capt
        (.union (.singleton (.var 0)) (.singleton (.var 1)))
        (.Pair
          (.capt (.singleton (.var 0)) (.Single (.var 0)))
          valueLabel
          (.term
            (.capt
              (.singleton (Path.var 1).weaken)
              (.Single (Path.var 1).weaken)))))
      secondIntermediate := by
  apply Ty.Sub.capt (.union_elim (.path .var) (.path .var))
  apply Shape.Sub.pair
  · exact .capt (.path .var) (.singleton_widen .var)
  · apply Tau.Sub.term
    apply Ty.Sub.trans
    · exact .capt (.path .var) (.singleton_widen .var)
    · exact .capt .refl
        (.select_lower (firstRecord_type (.var (x := 1))) .refl)

private def secondIntermediateToRecord :
    Ty.Sub context2 secondIntermediate (secondRecord 2) := by
  apply Ty.Sub.capt .refl
  apply Shape.Sub.pair .refl
  apply Tau.Sub.term
  apply Ty.Sub.capt .refl
  exact .trans
    (.select_upper (firstRecord_type (.var (x := 1))) .refl)
    (.select_lower (firstRecord_type (.var (x := 0))) .refl)

private def secondValueTyping :
    Tm.Ty context2 secondValue (secondRecord 2) .empty :=
  .sub
    .pair
    (.trans secondExactToIntermediate secondIntermediateToRecord)
    .refl
    secondRecordWf
    .empty

/-- The concrete nested lookup used in the lambda annotation. -/
def r2_type_selection_typing :
    Path.Ty context3 ((Path.var 0).sel typeLabel)
      (.type (implementationShape 3) (implementationShape 3)) := by
  apply secondRecord_type
  simpa [context3, context2, context1, Ctx.lookup, secondRecord] using
    (Path.Ty.var : Path.Ty context3 (.var 0)
      (.term (Ctx.lookup context3 0)))

/-- This exact direct-selection proof relies on generalized selection
well-formedness rather than an immediate-member-only premise. -/
def r2_type_selection_wf :
    Ty.Wf context3 (.capt .empty (.TSel (.var 0) typeLabel)) :=
  .capt .empty (.select r2_type_selection_typing .refl)

private def useBodyContext : Ctx 4 :=
  context3.snoc (.capt .empty (.TSel (.var 0) typeLabel))

private def selectedParameterTyping :
    Tm.Ty useBodyContext (.path (.var 0))
      (implementationType 4) (.singleton (.var 0)) := by
  apply Tm.Ty.sub (Tm.Ty.path Path.Ty.var)
  · apply Ty.Sub.capt (.path .var)
    exact .trans
      (.singleton_widen .var)
      (.select_upper (secondRecord_type (.var (x := 1))) .refl)
  · exact .refl
  · exact implementationTypeWf
  · exact .singleton .var

private def useArgumentTyping :
    Tm.Ty useBodyContext (.path (.var 3)) (pureTop 4) .empty :=
  .sub
    (.path .var)
    (.capt (.path .var) .top)
    (.path .var)
    pureTopWf
    .empty

private def useBodyTyping :
    Tm.Ty useBodyContext
      (.app (.var 0) (.var 3)) (pureTop 4)
      (.union .empty (.singleton (.var 0))) :=
  .sub
    (.app selectedParameterTyping useArgumentTyping)
    .refl
    (.union_elim .union_right .empty)
    pureTopWf
    (.union .empty (.singleton .var))

private def useValueTyping :
    Tm.Ty context3 useValue useType .empty :=
  .abs useBodyTyping r2_type_selection_wf .empty

/- `thirdIntermediate` retains the allocated `r2` in the `use` signature;
the next step relates it to the first-component binder of `thirdRecord`. -/
private def thirdIntermediate : Ty 4 :=
  .capt .empty
    (.Pair (secondRecord 4) useLabel
      (.term
        (.capt .empty
          (.Fun
            (.capt .empty (.TSel (.var 2) typeLabel))
            (pureTop 6)))))

private def thirdExactToIntermediate :
    Ty.Sub context4
      (.capt
        (.union (.singleton (.var 1)) (.singleton (.var 0)))
        (.Pair
          (.capt (.singleton (.var 1)) (.Single (.var 1)))
          useLabel
          (.term
            (.capt
              (.singleton (Path.var 0).weaken)
              (.Single (Path.var 0).weaken)))))
      thirdIntermediate := by
  apply Ty.Sub.capt (.union_elim (.path .var) (.path .var))
  apply Shape.Sub.pair
  · exact .capt (.path .var) (.singleton_widen .var)
  · exact .term (.capt (.path .var) (.singleton_widen .var))

private def thirdIntermediateToRecord :
    Ty.Sub context4 thirdIntermediate (thirdRecord 4) := by
  apply Ty.Sub.capt .refl
  apply Shape.Sub.pair .refl
  apply Tau.Sub.term
  apply Ty.Sub.capt .refl
  apply Shape.Sub.fun
  · apply Ty.Sub.capt .refl
    exact .trans
      (.select_upper (secondRecord_type (.var (x := 0))) .refl)
      (.select_lower (secondRecord_type (.var (x := 2))) .refl)
  · exact .refl

private def thirdValueTyping :
    Tm.Ty context4 thirdValue (thirdRecord 4) .empty :=
  .sub
    .pair
    (.trans thirdExactToIntermediate thirdIntermediateToRecord)
    .refl
    thirdRecordWf
    .empty

/-- `r3.use` expects the direct selection `r3.fst.A` (that is, `r2.A`). -/
def use_selection_typing :
    Path.Ty context5 ((Path.var 0).sel useLabel)
      (.term
        (.capt .empty
          (.Fun
            (.capt .empty (.TSel (Path.var 0).fst typeLabel))
            (pureTop 6)))) := by
  simpa [thirdRecord, Tau.open, Ty.open, Shape.open, Tau.subst, Ty.subst,
    Shape.subst, CaptureSet.subst, Path.subst, PathSubst.openAt] using
    (Path.Ty.sel_r (Path.Ty.var :
      Path.Ty context5 (.var 0) (.term (Ctx.lookup context5 0))))

private def r3FstTyping :
    Path.Ty context5 (Path.var 0).fst (.term (secondRecord 5)) := by
  exact Path.Ty.fst Path.Ty.var

private def r3FstFstTyping :
    Path.Ty context5 (Path.var 0).fst.fst (.term (firstRecord 5)) :=
  Path.Ty.fst r3FstTyping

/-- `r3.x` is found by skipping the outer `use` member. -/
def value_selection_typing :
    Path.Ty context5 ((Path.var 0).sel valueLabel)
      (.term
        (.capt .empty
          (.TSel (Path.var 0).fst.fst typeLabel))) := by
  apply Path.Ty.sel_l
  · exact Path.Ty.var
  · exact Path.Ty.sel_r r3FstTyping
  · exact value_ne_use

private def useSelectionToEmpty :
    CaptureSet.Sub context5
      (.singleton ((Path.var 0).sel useLabel)) .empty :=
  .trans
    (.sel_root use_selection_typing)
    (.path (Path.Ty.var :
      Path.Ty context5 (.var 0) (.term (Ctx.lookup context5 0))))

private def valueSelectionToEmpty :
    CaptureSet.Sub context5
      (.singleton ((Path.var 0).sel valueLabel)) .empty :=
  .trans
    (.sel_root value_selection_typing)
    (.path (Path.Ty.var :
      Path.Ty context5 (.var 0) (.term (Ctx.lookup context5 0))))

private def bodyFunctionTyping :
    Tm.Ty context5 (.path ((Path.var 0).sel useLabel))
      (.capt .empty
        (.Fun
          (.capt .empty (.TSel (Path.var 0).fst typeLabel))
          (pureTop 6)))
      .empty :=
  .sub
    (.path use_selection_typing)
    (.capt useSelectionToEmpty (.singleton_widen use_selection_typing))
    useSelectionToEmpty
    (.capt .empty (.fun (nested_selection_wf r3FstTyping) pureTopWf))
    .empty

/-- Exact bounds bridge the stored inner `r1.A` to the direct receiver
selection `r3.fst.A`; no annotation is rewritten to `receiver.fst.A`. -/
def value_term_typing :
    Tm.Ty context5 (.path ((Path.var 0).sel valueLabel))
      (.capt .empty (.TSel (Path.var 0).fst typeLabel)) .empty :=
  .sub
    (.path value_selection_typing)
    (.capt valueSelectionToEmpty
      (.trans
        (.singleton_widen value_selection_typing)
        (.trans
          (.select_upper (firstRecord_type r3FstFstTyping) .refl)
          (.select_lower (secondRecord_type r3FstTyping) .refl))))
    valueSelectionToEmpty
    (nested_selection_wf r3FstTyping)
    .empty

private def bodyTyping :
    Tm.Ty context5 body (pureTop 5) .empty :=
  .sub
    (.app bodyFunctionTyping value_term_typing)
    .refl
    (.union_elim .empty .empty)
    pureTopWf
    .empty

def term_typing :
    Tm.Ty Ctx.nil term (pureTop 0) .empty := by
  unfold term
  exact .let implementationTyping
    (.let firstValueTyping
      (.let secondValueTyping
        (.let useValueTyping
          (.let thirdValueTyping bodyTyping pureTopWf .empty)
          pureTopWf .empty)
        pureTopWf .empty)
      pureTopWf .empty)
    pureTopWf .empty

theorem term_type_safety
    {n : Nat} {target : State n}
    (steps : State.Steps (State.initial term) target) :
    State.Progress target :=
  term_typing.closed_type_safety steps

end

end LambdaPCCI.RecordRegression
