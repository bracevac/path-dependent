import DotToFCsub.OperationalCorrespondence
import DotFC.Source.Examples

/-!
# End-to-end DOT-to-FCsub regressions

These examples cross the complete checked bridge boundary: source
certificates elaborate to selection-free standalone FCsub, the executable
kernel validates the generated certificates, and erasure commutes with the
source runtime image.
-/

namespace DotToFCsub.Examples

open FCsub
open Elaboration

def A : DotFC.Source.Name := DotFC.Source.Examples.A

/-! ## Direct slots and syntax-shape regressions -/

def badContext : DotFC.Source.Ctx ([] ▹ .term) :=
  DotFC.Source.Ctx.nil.snoc (.member A .top .bot)

def badHandle :
    DotFC.Source.Handle badContext
      (.here : DotFC.BVar ([] ▹ .term) .term) A .top .bot :=
  .direct .here

def badLower : DotFC.Source.Sub badContext .top (.sel .here A) :=
  .lower badHandle

def badUpper : DotFC.Source.Sub badContext (.sel .here A) .bot :=
  .upper badHandle

theorem direct_lower_uses_canonical_slot :
    sub? badLower = some (.var MemberEncoding.lower) := by
  native_decide

theorem direct_upper_uses_canonical_slot :
    sub? badUpper = some (.var MemberEncoding.upper) := by
  native_decide

def exactObject :
    DotFC.Source.HasTy DotFC.Source.Ctx.nil (.obj A .bot)
      (.member A .bot .bot) :=
  .obj .bot

def exactTarget : FCsub.Tm [] :=
  .newtype .bot
    (MemberEncoding.pack .bot .bot (.tvar (.there .here))
      (.eqToLe (.symm (.var .here)))
      (.eqToLe (.var .here)) .unit)

theorem exact_object_is_private_newtype :
    term? exactObject = some exactTarget := by
  native_decide

def exactMemberWf :
    DotFC.Source.Wf DotFC.Source.Ctx.nil (.member A .bot .bot) :=
  .member .bot .bot

def memberLet :
    DotFC.Source.HasTy DotFC.Source.Ctx.nil
      (.let' (.obj A .bot) (.var .here)) (.member A .bot .bot) :=
  .let' exactObject (.var .here) exactMemberWf

def memberLetBody : FCsub.Tm (MemberEncoding.Payload []) :=
  MemberEncoding.pack .bot .bot (.tvar MemberEncoding.name)
    (.var MemberEncoding.lower) (.var MemberEncoding.upper)
    (.var MemberEncoding.payload)

def memberLetTarget : FCsub.Tm [] :=
  MemberEncoding.open .bot .bot exactTarget memberLetBody

theorem member_let_opens_exactly_once :
    term? memberLet = some memberLetTarget := by
  native_decide

def memberInterface : DotFC.Source.Ty [] := .member A .bot .top

def memberInterfaceWf :
    DotFC.Source.Wf DotFC.Source.Ctx.nil memberInterface :=
  .member .bot .top

def memberAllSub :
    DotFC.Source.Sub DotFC.Source.Ctx.nil
      (.all memberInterface (.top : DotFC.Source.Ty ([] ▹ .term)))
      (.all memberInterface (.top : DotFC.Source.Ty ([] ▹ .term))) :=
  .all (.refl memberInterfaceWf) .id (.refl .top)
    (.all memberInterfaceWf .top) (.all memberInterfaceWf .top)

def memberAllEvidence : FCsub.LeCo [] :=
  MemberEncoding.forallEvidence
    (.refl (MemberEncoding.telescope .bot .top))
    .top .top (.refl .top)

theorem member_function_subtyping_is_constrained :
    sub? memberAllSub = some memberAllEvidence := by
  native_decide

def plainAllSub :
    DotFC.Source.Sub DotFC.Source.Ctx.nil
      (.all .top (.top : DotFC.Source.Ty ([] ▹ .term)))
      (.all .top (.top : DotFC.Source.Ty ([] ▹ .term))) :=
  .all (.refl .top) .id (.refl .top)
    (.all .top .top) (.all .top .top)

theorem plain_function_subtyping_is_arrow :
    sub? plainAllSub = some (.arr (.refl .top) (.refl .top)) := by
  native_decide

/-! ## Checked canonical constrained application -/

def memberFunctionSource : DotFC.Source.Ty [] :=
  .all memberInterface (.top : DotFC.Source.Ty ([] ▹ .term))

def memberFunctionSourceWf :
    DotFC.Source.Wf DotFC.Source.Ctx.nil memberFunctionSource :=
  .all memberInterfaceWf .top

def memberFunctionTarget : FCsub.Ty [] :=
  MemberEncoding.forallType .bot .top .top

def abstractAppContext : DotFC.Source.Ctx (([] ▹ .term) ▹ .term) :=
  (DotFC.Source.Ctx.nil.snoc memberFunctionSource).snoc
    (.member A (.bot : DotFC.Source.Ty ([] ▹ .term)) .top)

def abstractAppDomain : DotFC.Source.Ty (([] ▹ .term) ▹ .term) :=
  .member A .bot .top

def abstractAppCodomain :
    DotFC.Source.Ty ((([] ▹ .term) ▹ .term) ▹ .term) :=
  .top

def abstractFunctionLookup :
    DotFC.Source.Lookup abstractAppContext (.there .here)
      (.all abstractAppDomain abstractAppCodomain) :=
  .there .here

def abstractArgumentLookup :
    DotFC.Source.Lookup abstractAppContext .here abstractAppDomain :=
  .here

def abstractMemberApp :
    DotFC.Source.HasTy abstractAppContext
      (.app (.there .here) .here)
      (.top : DotFC.Source.Ty (([] ▹ .term) ▹ .term)) :=
  @DotFC.Source.HasTy.app _ abstractAppContext (.there .here) .here
    abstractAppDomain abstractAppCodomain
    (.var abstractFunctionLookup) (.var abstractArgumentLookup) .top

def abstractAppTargetContext :
    FCsub.Ctx (MemberEncoding.Payload ([] ▹ .term)) :=
  (FCsub.Ctx.nil.extendTerm memberFunctionTarget).extendPayload
    (MemberEncoding.telescope .bot .top) .one

def abstractMemberAppTarget :
    FCsub.Tm (MemberEncoding.Payload ([] ▹ .term)) :=
  MemberEncoding.app .bot .top
    (.var (.there (.there (.there (.there .here)))))
    (.tvar MemberEncoding.name) (.var MemberEncoding.lower)
    (.var MemberEncoding.upper) (.var MemberEncoding.payload)

theorem abstract_member_app_uses_canonical_static_application :
    term? abstractMemberApp = some abstractMemberAppTarget := by
  native_decide

theorem abstract_member_app_is_checked : BReady abstractMemberApp := by
  refine ⟨abstractAppTargetContext, .top, abstractMemberAppTarget,
    ?_, ?_, abstract_member_app_uses_canonical_static_application, ?_⟩
  · rfl
  · rfl
  · native_decide

theorem exact_object_is_checked : BReady exactObject := by
  refine ⟨FCsub.Ctx.nil, MemberEncoding.existsType .bot .bot,
    exactTarget, ?_, ?_, exact_object_is_private_newtype, ?_⟩
  · rfl
  · rfl
  · native_decide

theorem member_let_is_checked : BReady memberLet := by
  refine ⟨FCsub.Ctx.nil, MemberEncoding.existsType .bot .bot,
    memberLetTarget, ?_, ?_, member_let_opens_exactly_once, ?_⟩
  · rfl
  · rfl
  · native_decide

/-- The source member let takes one ordinary erased zeta step. -/
theorem member_let_source_step :
    DotFC.Source.Runtime.Step
      (DotFC.Source.Tm.let' (.obj A .bot) (.var .here)).erase
      (.obj : DotFC.Source.Runtime.Tm []) := by
  exact .zeta .obj

/-- The checked Stage-B compilation maps that source step to exactly one
FCsub runtime step; all generated names and bound evidence remain static. -/
theorem member_let_runtime_correspondence :
    FCsub.Runtime.Step memberLetTarget.erase
      (.unit : FCsub.Runtime.Tm []) := by
  obtain ⟨target, compilation, step⟩ :=
    member_let_is_checked.sourceStep member_let_source_step
  have targetEq : target = memberLetTarget :=
    TermTranslates.functional compilation member_let_opens_exactly_once
  subst target
  simpa [RuntimeEmbedding.embed, RuntimeEmbedding.embedWith] using step

/-! ## Stable-root interface adaptation -/

def noncanonicalAppContext : DotFC.Source.Ctx (([] ▹ .term) ▹ .term) :=
  (DotFC.Source.Ctx.nil.snoc memberFunctionSource).snoc
    (.member A (.bot : DotFC.Source.Ty ([] ▹ .term)) .bot)

def noncanonicalFunctionLookup :
    DotFC.Source.Lookup noncanonicalAppContext (.there .here)
      (.all abstractAppDomain abstractAppCodomain) :=
  .there .here

def noncanonicalExactDomain :
    DotFC.Source.Ty (([] ▹ .term) ▹ .term) :=
  .member A .bot .bot

def noncanonicalArgumentLookup :
    DotFC.Source.Lookup noncanonicalAppContext .here
      noncanonicalExactDomain :=
  .here

def noncanonicalArgumentView :
    DotFC.Source.Sub noncanonicalAppContext noncanonicalExactDomain
      abstractAppDomain :=
  .member (.refl .bot) (.top .bot)

def noncanonicalArgumentTyping :
    DotFC.Source.HasTy noncanonicalAppContext (.var .here)
      abstractAppDomain :=
  .sub (.var noncanonicalArgumentLookup) noncanonicalArgumentView
    (.member .bot .top)

def noncanonicalMemberApp :
    DotFC.Source.HasTy noncanonicalAppContext
      (.app (.there .here) .here)
      (.top : DotFC.Source.Ty (([] ▹ .term) ▹ .term)) :=
  @DotFC.Source.HasTy.app _ noncanonicalAppContext (.there .here) .here
    abstractAppDomain abstractAppCodomain
    (.var noncanonicalFunctionLookup) noncanonicalArgumentTyping .top

def noncanonicalAppTargetContext :
    FCsub.Ctx (MemberEncoding.Payload ([] ▹ .term)) :=
  (FCsub.Ctx.nil.extendTerm memberFunctionTarget).extendPayload
    (MemberEncoding.telescope .bot .bot) .one

def noncanonicalMemberAppTarget :
    FCsub.Tm (MemberEncoding.Payload ([] ▹ .term)) :=
  MemberEncoding.app .bot .top
    (.var (.there (.there (.there (.there .here)))))
    (.tvar MemberEncoding.name)
    (.trans (.refl .bot) (.var MemberEncoding.lower))
    (.trans (.var MemberEncoding.upper) (.top .bot))
    (.var MemberEncoding.payload)

theorem noncanonical_member_app_adapts_root_evidence :
    term? noncanonicalMemberApp = some noncanonicalMemberAppTarget := by
  native_decide

theorem noncanonical_context_translation :
    SourceContext.Translates noncanonicalAppContext
      noncanonicalAppTargetContext := rfl

theorem noncanonical_member_app_checker_accepts :
    FCsub.synthTm noncanonicalAppTargetContext noncanonicalMemberAppTarget =
      some .top := by
  native_decide

theorem noncanonical_member_app_ready : BReady noncanonicalMemberApp := by
  exact ⟨noncanonicalAppTargetContext, .top, noncanonicalMemberAppTarget,
    noncanonical_context_translation, rfl,
    noncanonical_member_app_adapts_root_evidence,
    noncanonical_member_app_checker_accepts⟩

/-! ## Bad bounds retain directed evidence provenance -/

def badBoundsTargetContext : FCsub.Ctx (MemberEncoding.Payload []) :=
  FCsub.Ctx.nil.extendPayload (MemberEncoding.telescope .top .bot) .one

def badBoundsEvidence : FCsub.LeCo (MemberEncoding.Payload []) :=
  .trans (.var MemberEncoding.lower) (.var MemberEncoding.upper)

theorem bad_bounds_compile_to_lower_then_upper :
    sub? DotFC.Source.Examples.badBounds = some badBoundsEvidence := by
  native_decide

theorem bad_bounds_checker_keeps_endpoints :
    FCsub.synthLe badBoundsTargetContext badBoundsEvidence =
      some ((.top : FCsub.Ty (MemberEncoding.Payload [])), .bot) := by
  native_decide

theorem bad_bounds_ready :
    SubReady DotFC.Source.Examples.badBounds := by
  refine ⟨badBoundsTargetContext, .top, .bot, badBoundsEvidence,
    ?_, ?_, ?_, bad_bounds_compile_to_lower_then_upper,
    bad_bounds_checker_keeps_endpoints⟩
  · rfl
  · rfl
  · rfl

theorem bad_bounds_preserved :
    Nonempty (FCsub.LeCo.HasType badBoundsTargetContext badBoundsEvidence
      .top .bot) :=
  FCsub.synthLe_sound bad_bounds_checker_keeps_endpoints

/-! ## Exact construction exported behind independently justified bounds -/

def exactPrivateTarget : FCsub.Tm [] := exactTarget

def exactToAbstractAdaptation :
    FCsub.TelMor [] MemberEncoding.names MemberEncoding.constraints
      MemberEncoding.names MemberEncoding.constraints :=
  MemberEncoding.varianceMorphism
    (sourceLower := .bot) (sourceUpper := .bot)
    (targetLower := .bot) (targetUpper := .top)
    (.refl .bot) (.top .bot)

def exactToAbstractEvidence : FCsub.LeCo [] :=
  MemberEncoding.existsEvidence exactToAbstractAdaptation

def abstractObjectTarget : FCsub.Tm [] :=
  .cast exactPrivateTarget exactToAbstractEvidence

def abstractObjectType : FCsub.Ty [] :=
  MemberEncoding.existsType .bot .top

theorem abstract_object_compiles_with_independent_bounds :
    term? DotFC.Source.Examples.abstractObjectTyping =
      some abstractObjectTarget := by
  native_decide

theorem abstract_object_checker_accepts :
    FCsub.synthTm FCsub.Ctx.nil abstractObjectTarget =
      some abstractObjectType := by
  native_decide

theorem abstract_object_ready :
    BReady DotFC.Source.Examples.abstractObjectTyping := by
  refine ⟨FCsub.Ctx.nil, abstractObjectType, abstractObjectTarget,
    ?_, ?_, abstract_object_compiles_with_independent_bounds,
    abstract_object_checker_accepts⟩
  · rfl
  · rfl

theorem abstract_object_preserved :
    Nonempty (FCsub.Tm.HasType FCsub.Ctx.nil abstractObjectTarget
      abstractObjectType) :=
  FCsub.synthTm_sound abstract_object_checker_accepts

theorem abstract_object_erasure_preserved :
    abstractObjectTarget.erase =
      sourceRuntime DotFC.Source.Examples.abstractObjectTyping :=
  term_erasure DotFC.Source.Examples.abstractObjectTyping
    abstract_object_compiles_with_independent_bounds

theorem abstract_object_erases_to_unit :
    abstractObjectTarget.erase =
      (FCsub.Runtime.Tm.unit : FCsub.Runtime.Tm []) := by
  native_decide

/-! ## A genuinely dependent constrained function -/

def dependentFunctionTarget : FCsub.Tm [] :=
  MemberEncoding.lam .bot .top
    (.lam .bot
      (.cast (.var .here) (.var (.there MemberEncoding.lower))))

def dependentFunctionTargetType : FCsub.Ty [] :=
  MemberEncoding.forallType .bot .top
    (.arr .bot (.tvar (.there MemberEncoding.name)))

theorem dependent_selection_becomes_bound_name :
    Layout.translateTy?
      (DotFC.Explicit.Ctx.ofSource
        (DotFC.Source.Ctx.nil.snoc
          DotFC.Source.Examples.dependentDomain))
      (.all .bot (.sel (.there .here) A)) =
      some (.arr .bot (.tvar (.there MemberEncoding.name))) := by
  native_decide

theorem dependent_function_compiles :
    term? DotFC.Source.Examples.dependentFunctionTyping =
      some dependentFunctionTarget := by
  native_decide

theorem dependent_function_checker_accepts :
    FCsub.synthTm FCsub.Ctx.nil dependentFunctionTarget =
      some dependentFunctionTargetType := by
  native_decide

theorem dependent_function_ready :
    BReady DotFC.Source.Examples.dependentFunctionTyping := by
  refine ⟨FCsub.Ctx.nil, dependentFunctionTargetType,
    dependentFunctionTarget, ?_, ?_, dependent_function_compiles,
    dependent_function_checker_accepts⟩
  · rfl
  · rfl

theorem dependent_function_preserved :
    Nonempty (FCsub.Tm.HasType FCsub.Ctx.nil dependentFunctionTarget
      dependentFunctionTargetType) :=
  FCsub.synthTm_sound dependent_function_checker_accepts

theorem dependent_function_erasure_preserved :
    dependentFunctionTarget.erase =
      sourceRuntime DotFC.Source.Examples.dependentFunctionTyping :=
  term_erasure DotFC.Source.Examples.dependentFunctionTyping
    dependent_function_compiles

theorem dependent_function_erases_to_two_lambdas :
    dependentFunctionTarget.erase =
      (.lam (.lam (.var .here)) : FCsub.Runtime.Tm []) := by
  native_decide

/-! ### Canonical application of the dependent constrained function -/

def dependentApplicationContext :
    DotFC.Source.Ctx (([] ▹ .term) ▹ .term) :=
  (DotFC.Source.Ctx.nil.snoc
    DotFC.Source.Examples.dependentFunctionType).snoc
      (.member A (.bot : DotFC.Source.Ty ([] ▹ .term)) .top)

def dependentApplicationDomain :
    DotFC.Source.Ty (([] ▹ .term) ▹ .term) :=
  .member A .bot .top

def dependentApplicationCodomain :
    DotFC.Source.Ty ((([] ▹ .term) ▹ .term) ▹ .term) :=
  .all .bot (.sel (.there .here) A)

def dependentApplicationResult :
    DotFC.Source.Ty (([] ▹ .term) ▹ .term) :=
  .all .bot (.sel (.there .here) A)

def dependentFunctionLookup :
    DotFC.Source.Lookup dependentApplicationContext (.there .here)
      (.all dependentApplicationDomain dependentApplicationCodomain) :=
  .there .here

def dependentArgumentLookup :
    DotFC.Source.Lookup dependentApplicationContext .here
      dependentApplicationDomain :=
  .here

def dependentResultHandle :
    DotFC.Source.Handle
      (dependentApplicationContext.snoc
        (.bot : DotFC.Source.Ty (([] ▹ .term) ▹ .term)))
      (.there .here) A .bot .top :=
  .direct (.there .here)

def dependentApplicationResultWf :
    DotFC.Source.Wf dependentApplicationContext dependentApplicationResult :=
  .all .bot (.sel dependentResultHandle)

def dependentCanonicalApplication :
    DotFC.Source.HasTy dependentApplicationContext
      (.app (.there .here) .here) dependentApplicationResult := by
  exact @DotFC.Source.HasTy.app _ dependentApplicationContext
    (.there .here) .here dependentApplicationDomain
    dependentApplicationCodomain (.var dependentFunctionLookup)
    (.var dependentArgumentLookup) dependentApplicationResultWf

def dependentApplicationTargetContext :
    FCsub.Ctx (MemberEncoding.Payload ([] ▹ .term)) :=
  (FCsub.Ctx.nil.extendTerm dependentFunctionTargetType).extendPayload
    (MemberEncoding.telescope .bot .top) .one

def dependentApplicationTarget :
    FCsub.Tm (MemberEncoding.Payload ([] ▹ .term)) :=
  MemberEncoding.app .bot .top
    (.var (.there (.there (.there (.there .here)))))
    (.tvar MemberEncoding.name) (.var MemberEncoding.lower)
    (.var MemberEncoding.upper) (.var MemberEncoding.payload)

def dependentApplicationTargetType :
    FCsub.Ty (MemberEncoding.Payload ([] ▹ .term)) :=
  .arr .bot (.tvar (.there MemberEncoding.name))

theorem dependent_application_compiles_with_canonical_slot :
    term? dependentCanonicalApplication =
      some dependentApplicationTarget := by
  native_decide

theorem dependent_application_checker_accepts :
    FCsub.synthTm dependentApplicationTargetContext
      dependentApplicationTarget =
      some dependentApplicationTargetType := by
  native_decide

theorem dependent_application_result_translates :
    Layout.Translates
      (DotFC.Explicit.Ctx.ofSource dependentApplicationContext)
      dependentApplicationResult dependentApplicationTargetType := by
  unfold Layout.Translates
  native_decide

theorem dependent_application_ready :
    BReady dependentCanonicalApplication := by
  refine ⟨dependentApplicationTargetContext,
    dependentApplicationTargetType, dependentApplicationTarget,
    ?_, dependent_application_result_translates,
    dependent_application_compiles_with_canonical_slot,
    dependent_application_checker_accepts⟩
  rfl

theorem dependent_application_preserved :
    Nonempty (FCsub.Tm.HasType dependentApplicationTargetContext
      dependentApplicationTarget dependentApplicationTargetType) :=
  FCsub.synthTm_sound dependent_application_checker_accepts

theorem dependent_application_erasure_preserved :
    dependentApplicationTarget.erase =
      sourceRuntime dependentCanonicalApplication :=
  term_erasure dependentCanonicalApplication
    dependent_application_compiles_with_canonical_slot

theorem dependent_application_erases_to_runtime_app :
    dependentApplicationTarget.erase =
      (.app (.var (.there (.there (.there (.there .here)))))
        (.var .here) :
        FCsub.Runtime.Tm (MemberEncoding.Payload ([] ▹ .term))) := by
  native_decide

end DotToFCsub.Examples
