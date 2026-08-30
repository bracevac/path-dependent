import Coercions.Translation.ManySorted.BinderOnly.ModelElaboration

/-!
# Ambient model-elaboration examples

These examples exercise total model compilation for realizable type/capture
intervals and the zero-evidence unbounded capture case.
-/

namespace DOTCaptureToManySortedFC.BinderOnly.ModelExamples

def exactOneInterval : DOTCapture.BinderOnly.Interval .type [] :=
  .exact (.type .one)

def exactOneInstantiation :
    Instantiation DOTCapture.BinderOnly.Ctx.nil (.type .one)
      exactOneInterval :=
  canonicalInstantiation DOTCapture.BinderOnly.Ctx.nil (.type .one)
    exactOneInterval

def exactOneSourceModel :
    DOTCapture.BinderOnly.Interval.SatisfiedBy
      DOTCapture.BinderOnly.Ctx.nil (.type .one) exactOneInterval :=
  .between .refl .refl

def compiledExactOneModel :
    CompiledModel DOTCapture.BinderOnly.Ctx.nil (.type .one)
      exactOneInterval :=
  compileModelTotal emptyBoundCompiler exactOneSourceModel

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
  canonicalInstantiation DOTCapture.BinderOnly.Ctx.nil (.type .one)
    wideOneInterval

def wideOneSourceModel :
    DOTCapture.BinderOnly.Interval.SatisfiedBy
      DOTCapture.BinderOnly.Ctx.nil (.type .one) wideOneInterval :=
  .between .typeBottom .typeTop

def compiledWideOneModel :
    CompiledModel DOTCapture.BinderOnly.Ctx.nil (.type .one)
      wideOneInterval :=
  compileModelTotal emptyBoundCompiler wideOneSourceModel

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
  compileModelTotal emptyBoundCompiler (.lower .typeBottom)

@[simp]
theorem lower_one_model_evidence_shape :
    compiledLowerOneModel.evidence = .cons (.typeBottom .one) .nil := rfl

def upperOneInterval : DOTCapture.BinderOnly.Interval .type [] :=
  .bounds .none (.some (.type .top))

def compiledUpperOneModel :
    CompiledModel DOTCapture.BinderOnly.Ctx.nil (.type .one)
      upperOneInterval :=
  compileModelTotal emptyBoundCompiler (.upper .typeTop)

@[simp]
theorem upper_one_model_evidence_shape :
    compiledUpperOneModel.evidence = .cons (.typeTop .one) .nil := rfl

def exactEmptyCaptureInterval :
    DOTCapture.BinderOnly.Interval .capture [] :=
  .exact (.capture .empty)

def exactEmptyCaptureInstantiation :
    Instantiation DOTCapture.BinderOnly.Ctx.nil (.capture .empty)
      exactEmptyCaptureInterval :=
  canonicalInstantiation DOTCapture.BinderOnly.Ctx.nil (.capture .empty)
    exactEmptyCaptureInterval

def exactEmptyCaptureSourceModel :
    DOTCapture.BinderOnly.Interval.SatisfiedBy
      DOTCapture.BinderOnly.Ctx.nil (.capture .empty)
      exactEmptyCaptureInterval :=
  .between .refl .refl

def compiledExactEmptyCaptureModel :
    CompiledModel DOTCapture.BinderOnly.Ctx.nil (.capture .empty)
      exactEmptyCaptureInterval :=
  compileModelTotal emptyBoundCompiler exactEmptyCaptureSourceModel

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
  canonicalInstantiation DOTCapture.BinderOnly.Ctx.nil (.capture .empty)
    unboundedCaptureInterval

def compiledUnboundedCaptureModel :
    CompiledModel DOTCapture.BinderOnly.Ctx.nil (.capture .empty)
      unboundedCaptureInterval :=
  compileModelTotal emptyBoundCompiler unboundedCaptureSourceModel

@[simp]
theorem unbounded_capture_model_has_no_evidence :
    compiledUnboundedCaptureModel.evidence = .nil := rfl

end DOTCaptureToManySortedFC.BinderOnly.ModelExamples
