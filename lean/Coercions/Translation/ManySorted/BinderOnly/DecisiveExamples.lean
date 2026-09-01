import Coercions.Translation.ManySorted.BinderOnly.TermElaboration
import Coercions.Translation.ManySorted.BinderOnly.LayoutExamples

/-!
# Bad-interval static abstractions

These regressions put the two characteristic inconsistent intervals under
actual source static abstractions.  The type example is closed; the capture
example deliberately retains one ambient capability so its body has a real
runtime dependency.  Both bodies may use the hypothetical interval assumptions,
and the generated abstractions are accepted by the independent target checker.
Elimination remains confined: the corresponding target theory has no ambient
model in the recursion-free evidence fragment.
-/

namespace DOTCaptureToManySortedFC.BinderOnly.DecisiveExamples

open DOTCapture.BinderOnly
open DOTCaptureToManySortedFC.BinderOnly.LayoutExamples

private theorem context_lower_recursionFree
    {scope : Sig} {context : Ctx scope} {sort : StaticSort}
    {reference : StaticRef sort scope} {endpoint : StaticExpr sort scope}
    (bound : HasLower context reference endpoint) :
    ((contextBoundCompiler context).lower bound).evidence.recursionFree =
      true := by
  cases reference with
  | bound index =>
      cases bound with
      | bound found => cases sort <;> rfl

private theorem context_upper_recursionFree
    {scope : Sig} {context : Ctx scope} {sort : StaticSort}
    {reference : StaticRef sort scope} {endpoint : StaticExpr sort scope}
    (bound : HasUpper context reference endpoint) :
    ((contextBoundCompiler context).upper bound).evidence.recursionFree =
      true := by
  cases reference with
  | bound index =>
      cases bound with
      | bound found => cases sort <;> rfl

private theorem compile_inclusion_recursionFree
    {scope : Sig} {context : Ctx scope} {sort : StaticSort}
    {source target : StaticExpr sort scope}
    (bounds : BoundCompiler context)
    (lowerRecursionFree :
      ∀ {sort} {reference : StaticRef sort scope}
        {endpoint : StaticExpr sort scope}
        (bound : HasLower context reference endpoint),
        (bounds.lower bound).evidence.recursionFree = true)
    (upperRecursionFree :
      ∀ {sort} {reference : StaticRef sort scope}
        {endpoint : StaticExpr sort scope}
        (bound : HasUpper context reference endpoint),
        (bounds.upper bound).evidence.recursionFree = true)
    (inclusion : Includes context source target) :
    (compileIncludes bounds inclusion).evidence.recursionFree = true := by
  induction inclusion <;>
    simp_all [compileIncludes, ManySortedFC.Evidence.recursionFree]
  all_goals constructor <;> assumption

private theorem compiled_inclusion_recursionFree
    {scope : Sig} {context : Ctx scope} {sort : StaticSort}
    {source target : StaticExpr sort scope}
    (inclusion : Includes context source target) :
    (compileIncludesTotal inclusion).evidence.recursionFree = true :=
  compile_inclusion_recursionFree (contextBoundCompiler context)
    context_lower_recursionFree context_upper_recursionFree inclusion

/-! ## Type bad bounds -/

/-- Under `Top ≤ A ≤ Bottom`, even `One` may be viewed as `Bottom`. -/
def oneIncludesBottom : TypeIncludes badTypeContext .one .bot :=
  .trans (.typeTop (type := .one))
    DOTCapture.BinderOnly.BadBoundsExamples.topIncludesBottom

/-- A static abstraction whose body uses the inconsistent interval. -/
def badTypeFunction : Value [] :=
  .staticLam badTypeInterval .unit

def badTypeFunctionTyping :
    Value.HasType Ctx.nil badTypeFunction
      (.capturing .empty (.forallI badTypeInterval .bot)) :=
  .staticLam (.adapt .unit (.cast oneIncludesBottom)) .refl

def compiledBadTypeFunction := compileValue badTypeFunctionTyping

theorem bad_type_function_checker_accepts :
    ManySortedFC.Tm.synth ManySortedFC.Ctx.nil
        compiledBadTypeFunction.term =
      some (.empty,
        translateTy Ctx.nil
          (.capturing .empty (.forallI badTypeInterval .bot))) := by
  rfl

/-- The body can use bad bounds, but no recursion-free closed target caller
can supply the model required by static application. -/
theorem bad_type_function_has_no_closed_static_argument
    (model : ManySortedFC.Theory.Model ManySortedFC.Ctx.nil
      (translateInterval Ctx.nil badTypeInterval))
    (modelRecursionFree : model.RecursionFree) : False :=
  bad_type_interval_has_no_closed_target_model model modelRecursionFree

/-- No source witness can realize the interval needed to call the function.
Translating any alleged realization would construct the impossible target
model above. -/
theorem bad_type_function_has_no_source_static_argument
    (witness : StaticExpr .type [])
    (satisfaction : Interval.SatisfiedBy Ctx.nil witness badTypeInterval) :
    False := by
  let compiled := compileModelTotal satisfaction
  let model : ManySortedFC.Theory.Model ManySortedFC.Ctx.nil
      (translateInterval Ctx.nil badTypeInterval) :=
    { symbols := TargetIntervalModel.symbols (translateExpr Ctx.nil witness)
      evidence := compiled.evidence
      satisfies := compiled.satisfies }
  apply bad_type_function_has_no_closed_static_argument model
  unfold ManySortedFC.Theory.Model.RecursionFree
  change compiled.evidence.recursionFree = true
  cases satisfaction with
  | between lower upper =>
      change
        ((compileIncludesTotal lower).evidence.recursionFree &&
          ((compileIncludesTotal upper).evidence.recursionFree && true)) =
            true
      rw [compiled_inclusion_recursionFree lower,
        compiled_inclusion_recursionFree upper]
      rfl

/-! ## Capture bad bounds -/

abbrev CaptureBodyScope : Sig :=
  CapabilitySourceScope ▹ .static .capture ▹ .term

/-- The outer capability after the static-capture and ordinary binders. -/
def capturedOuterVariable : BVar CaptureBodyScope .term :=
  .there (.there .here)

/-- The returned runtime closure really mentions the ambient capability. -/
def badCaptureBody : Value (CapabilitySourceScope ▹ .static .capture) :=
  .lam .one .one (.ret (.var capturedOuterVariable))

def badCaptureBodyRawTyping :
    Value.HasType badCaptureContext badCaptureBody
      (.capturing
        (.singleton (.var (.there .here)))
        (.arr .one .one)) :=
  .lam (.ret .var) .captureEmpty

/-- The impossible capture interval retags the genuine closure from `{x}` to
`{}` only inside the hypothetical static binder. -/
def badCaptureBodyTyping :
    Value.HasType badCaptureContext badCaptureBody
      (.capturing .empty (.arr .one .one)) :=
  .adapt badCaptureBodyRawTyping
    (.captured
      DOTCapture.BinderOnly.BadBoundsExamples.singletonIncludesEmpty
      .identity)

def badCaptureFunction : Value CapabilitySourceScope :=
  .staticLam badCaptureInterval badCaptureBody

def badCaptureFunctionTyping :
    Value.HasType capabilitySourceContext badCaptureFunction
      (.capturing .empty
        (.forallI badCaptureInterval
          (.capturing .empty (.arr .one .one)))) :=
  .staticLam badCaptureBodyTyping .refl

def compiledBadCaptureFunction := compileValue badCaptureFunctionTyping

theorem bad_capture_function_checker_accepts :
    ManySortedFC.Tm.synth
        (translateContext capabilitySourceContext)
        compiledBadCaptureFunction.term =
      some (.empty,
        translateTy capabilitySourceContext
          (.capturing .empty
            (.forallI badCaptureInterval
              (.capturing .empty (.arr .one .one))))) := by
  rfl

/-- As for type bad bounds, no target model can eliminate the abstraction. -/
theorem bad_capture_function_has_no_static_argument
    (model : ManySortedFC.Theory.Model
      (translateContext capabilitySourceContext)
      (translateInterval capabilitySourceContext badCaptureInterval)) : False :=
  bad_capture_interval_has_no_target_model model

/-- The capture abstraction likewise has no source-level static argument in
its ambient term context. -/
theorem bad_capture_function_has_no_source_static_argument
    (witness : StaticExpr .capture CapabilitySourceScope)
    (satisfaction : Interval.SatisfiedBy capabilitySourceContext witness
      badCaptureInterval) : False := by
  let compiled := compileModelTotal satisfaction
  exact bad_capture_function_has_no_static_argument
    { symbols := TargetIntervalModel.symbols
        (translateExpr capabilitySourceContext witness)
      evidence := compiled.evidence
      satisfies := compiled.satisfies }

end DOTCaptureToManySortedFC.BinderOnly.DecisiveExamples
