import Coercions.DOT.Captures.BinderOnly.StaticJudgments
import Coercions.ManySortedFC.ModelConsistency
import Coercions.Translation.ManySorted.BinderOnly.Layout

/-!
# Regressions for the binder-only DOT-capture layout

These examples connect source true intervals to the target's confinement
theorems.  Bad bounds are available after a binder is opened, but the
corresponding closed packages have no model.  An unbounded capture binder,
on the other hand, allocates a name and no upper-evidence coordinate.
-/

namespace DOTCaptureToManySortedFC.BinderOnly.LayoutExamples

/-! ## Bad type bounds -/

def badTypeInterval : DOTCapture.BinderOnly.Interval .type [] :=
  .bounds (.some (.type .top)) (.some (.type .bot))

@[simp]
theorem bad_type_theory_is_the_target_bad_interval :
    translateInterval DOTCapture.BinderOnly.Ctx.nil badTypeInterval =
      ManySortedFC.StaticExamples.impossibleTypeInterval := rfl

/-- The source admits the interval hypothetically, but translating it does
not manufacture a closed realization. -/
theorem bad_type_interval_has_no_closed_target_model
    (model : ManySortedFC.Theory.Model
      (translateContext (DOTCapture.BinderOnly.Ctx.nil : DOTCapture.BinderOnly.Ctx []))
      (translateInterval DOTCapture.BinderOnly.Ctx.nil badTypeInterval)) : False :=
  ManySortedFC.no_closed_model_of_impossible_type_interval model

def badTypeContext : DOTCapture.BinderOnly.Ctx ([] ▹ .static .type) :=
  DOTCapture.BinderOnly.Ctx.nil.extendStatic badTypeInterval

@[simp]
theorem bad_type_name_uses_the_shared_slot :
    translateTy badTypeContext (.ref (.bound .here)) =
      ManySortedFC.Ty.tvar (.there (.there .here)) := rfl

/-! ## Bad capture bounds -/

abbrev CapabilitySourceScope : DOTCapture.BinderOnly.Sig := ([] : DOTCapture.BinderOnly.Sig) ▹ .term

def capabilitySourceContext : DOTCapture.BinderOnly.Ctx CapabilitySourceScope :=
  DOTCapture.BinderOnly.Ctx.nil.extendTerm .one

def badCaptureInterval : DOTCapture.BinderOnly.Interval .capture CapabilitySourceScope :=
  .bounds
    (.some (.capture (.singleton (.var .here))))
    (.some (.capture .empty))

@[simp]
theorem capability_context_translates_exactly :
    translateContext capabilitySourceContext =
      ManySortedFC.StaticExamples.capabilityContext := rfl

@[simp]
theorem bad_capture_theory_is_the_target_bad_interval :
    translateInterval capabilitySourceContext badCaptureInterval =
      ManySortedFC.StaticExamples.impossibleCaptureInterval := rfl

/-- As at the type sort, local contradictory assumptions remain usable while
no ambient model can construct the corresponding package. -/
theorem bad_capture_interval_has_no_target_model
    (model : ManySortedFC.Theory.Model
      (translateContext capabilitySourceContext)
      (translateInterval capabilitySourceContext badCaptureInterval)) :
    False :=
  ManySortedFC.no_model_of_impossible_capture_interval model

def badCaptureContext :
    DOTCapture.BinderOnly.Ctx (CapabilitySourceScope ▹ .static .capture) :=
  capabilitySourceContext.extendStatic badCaptureInterval

@[simp]
theorem bad_capture_name_uses_the_shared_slot :
    translateCapture badCaptureContext (.ref (.bound .here)) =
      ManySortedFC.Capture.cvar (.there (.there .here)) := rfl

@[simp]
theorem capability_path_survives_static_expansion :
    translatePath badCaptureContext (.var (.there .here)) =
      (.there (.there (.there .here)) :
        ManySortedFC.BVar (sig badCaptureContext) .term) := rfl

/-! ## Omitted capture upper bound -/

def unboundedCaptureInterval : DOTCapture.BinderOnly.Interval .capture [] :=
  .unbounded

def unboundedCaptureContext : DOTCapture.BinderOnly.Ctx ([] ▹ .static .capture) :=
  DOTCapture.BinderOnly.Ctx.nil.extendStatic unboundedCaptureInterval

@[simp]
theorem unbounded_capture_has_no_relations :
    intervalRelations unboundedCaptureInterval = [] := rfl

@[simp]
theorem unbounded_capture_has_no_upper_slot :
    (staticSlot unboundedCaptureContext
      (.here : DOTCapture.BinderOnly.BVar ([] ▹ .static .capture) (.static .capture))).upper =
      none := rfl

@[simp]
theorem unbounded_capture_theory_is_target_unbounded :
    translateInterval DOTCapture.BinderOnly.Ctx.nil unboundedCaptureInterval =
      ManySortedFC.StaticExamples.unboundedCaptureTheory := rfl

end DOTCaptureToManySortedFC.BinderOnly.LayoutExamples
