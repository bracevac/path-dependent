import Coercions.Translation.ManySorted.BinderOnly.ModelElaboration

/-!
# Ambient model-elaboration examples

Concrete first-order witnesses discharge the names-first substitution
invariant by computation.  These examples exercise realizable type/capture
intervals and the zero-evidence unbounded capture case.
-/

namespace DOTCaptureToManySortedFC.BinderOnly.ModelExamples

def exactOneInterval : DOTCapture.BinderOnly.Interval .type [] :=
  .exact (.type .one)

def exactOneInstantiation :
    Instantiation DOTCapture.BinderOnly.Ctx.nil (.type .one)
      exactOneInterval :=
  .between rfl rfl

def exactOneSourceModel :
    DOTCapture.BinderOnly.Interval.SatisfiedBy
      DOTCapture.BinderOnly.Ctx.nil (.type .one) exactOneInterval :=
  .between .refl .refl

def compiledExactOneModel :
    CompiledModel DOTCapture.BinderOnly.Ctx.nil (.type .one)
      exactOneInterval :=
  compileModel emptyBoundCompiler exactOneSourceModel exactOneInstantiation

@[simp]
theorem exact_one_model_evidence_shape :
    compiledExactOneModel.evidence =
      .cons (.inclusionRefl (.type .one))
        (.cons (.inclusionRefl (.type .one)) .nil) := rfl

/-- An asymmetric realizable interval makes the lower/upper certificate order
observable: `Bottom <= One` is stored before `One <= Top`. -/
def wideOneInterval : DOTCapture.BinderOnly.Interval .type [] :=
  .bounds (.some (.type .bot)) (.some (.type .top))

def wideOneInstantiation :
    Instantiation DOTCapture.BinderOnly.Ctx.nil (.type .one)
      wideOneInterval :=
  .between rfl rfl

def wideOneSourceModel :
    DOTCapture.BinderOnly.Interval.SatisfiedBy
      DOTCapture.BinderOnly.Ctx.nil (.type .one) wideOneInterval :=
  .between .typeBottom .typeTop

def compiledWideOneModel :
    CompiledModel DOTCapture.BinderOnly.Ctx.nil (.type .one)
      wideOneInterval :=
  compileModel emptyBoundCompiler wideOneSourceModel wideOneInstantiation

@[simp]
theorem wide_one_model_distinguishes_bound_order :
    compiledWideOneModel.evidence =
      .cons (.typeBottom .one) (.cons (.typeTop .one) .nil) := rfl

/-- Lower-only and upper-only intervals each allocate exactly one certificate. -/
def lowerOneInterval : DOTCapture.BinderOnly.Interval .type [] :=
  .bounds (.some (.type .bot)) .none

def compiledLowerOneModel :
    CompiledModel DOTCapture.BinderOnly.Ctx.nil (.type .one)
      lowerOneInterval :=
  compileModel emptyBoundCompiler (.lower .typeBottom) (.lower rfl)

@[simp]
theorem lower_one_model_evidence_shape :
    compiledLowerOneModel.evidence = .cons (.typeBottom .one) .nil := rfl

def upperOneInterval : DOTCapture.BinderOnly.Interval .type [] :=
  .bounds .none (.some (.type .top))

def compiledUpperOneModel :
    CompiledModel DOTCapture.BinderOnly.Ctx.nil (.type .one)
      upperOneInterval :=
  compileModel emptyBoundCompiler (.upper .typeTop) (.upper rfl)

@[simp]
theorem upper_one_model_evidence_shape :
    compiledUpperOneModel.evidence = .cons (.typeTop .one) .nil := rfl

def exactEmptyCaptureInterval :
    DOTCapture.BinderOnly.Interval .capture [] :=
  .exact (.capture .empty)

def exactEmptyCaptureInstantiation :
    Instantiation DOTCapture.BinderOnly.Ctx.nil (.capture .empty)
      exactEmptyCaptureInterval :=
  .between rfl rfl

def exactEmptyCaptureSourceModel :
    DOTCapture.BinderOnly.Interval.SatisfiedBy
      DOTCapture.BinderOnly.Ctx.nil (.capture .empty)
      exactEmptyCaptureInterval :=
  .between .refl .refl

def compiledExactEmptyCaptureModel :
    CompiledModel DOTCapture.BinderOnly.Ctx.nil (.capture .empty)
      exactEmptyCaptureInterval :=
  compileModel emptyBoundCompiler exactEmptyCaptureSourceModel
    exactEmptyCaptureInstantiation

def unboundedCaptureInterval :
    DOTCapture.BinderOnly.Interval .capture [] :=
  .unbounded

def unboundedCaptureSourceModel :
    DOTCapture.BinderOnly.Interval.SatisfiedBy
      DOTCapture.BinderOnly.Ctx.nil (.capture .empty)
      unboundedCaptureInterval :=
  .unbounded

def unboundedCaptureInstantiation :
    Instantiation DOTCapture.BinderOnly.Ctx.nil (.capture .empty)
      unboundedCaptureInterval :=
  .unbounded

def compiledUnboundedCaptureModel :
    CompiledModel DOTCapture.BinderOnly.Ctx.nil (.capture .empty)
      unboundedCaptureInterval :=
  compileModel emptyBoundCompiler unboundedCaptureSourceModel
    unboundedCaptureInstantiation

@[simp]
theorem unbounded_capture_model_has_no_evidence :
    compiledUnboundedCaptureModel.evidence = .nil := rfl

end DOTCaptureToManySortedFC.BinderOnly.ModelExamples
