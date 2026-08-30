import Coercions.Translation.ManySorted.Acyclic.TermTranslation
import Coercions.Translation.ManySorted.Acyclic.ValueTranslationErasure
import Coercions.Translation.ManySorted.Acyclic.SourceErasure
import Coercions.Translation.ManySorted.Acyclic.ComputationalRuntime

/-!
# Erasure of certified acyclic term translation

Returns reuse value translation, primitive `x.v` selection reads the
receiver's separated payload, applications preserve both operands, plain
lets remain runtime lets, and object lets erase target `open` to one runtime
let.  Capture-use annotations erase.  Successful compilation therefore
preserves the independently defined captured-DOT runtime term exactly.  This
is exact erasure preservation into the shared runtime, not a claim of an
independent source small-step semantics or a full source-to-target simulation.
-/

namespace DOTCaptureToManySortedFC.Acyclic.TermTranslationErasure

namespace Source

export DOTCapture.Acyclic (Scope Var Path Ctx Term Capture Ty)

namespace Term
export DOTCapture.Acyclic.Term (HasType)
end Term

end Source

namespace Translation

export DOTCaptureToManySortedFC.Acyclic.ValueTranslation
  (CompiledTerm compileTerm?)

export DOTCaptureToManySortedFC.Acyclic.TermTranslation
  (compileUse? compileSelect)

end Translation

namespace Runtime

export DOTCaptureToManySortedFC.Acyclic.RuntimeContext (Ready)

end Runtime

/-! ## Erasure of individual generated rules -/

/-- One successful capture-use rule adds only a target `Tm.use`, which is
runtime-transparent. -/
private theorem compileUse?_erase
    {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context}
    {sourceTerm : Source.Term scope}
    {sourceUse targetUse : Source.Capture scope}
    {sourceType : Source.Ty scope}
    (inner : Translation.CompiledTerm ready sourceTerm sourceUse sourceType)
    (inclusion : DOTCapture.Acyclic.CaptureIncludes
      context sourceUse targetUse)
    {compiled : Translation.CompiledTerm
      ready sourceTerm targetUse sourceType}
    (success : Translation.compileUse? inner inclusion = some compiled) :
    compiled.term.erase = inner.term.erase := by
  obtain ⟨evidence, termEquation⟩ :=
    TermTranslation.compileUse?_term inner inclusion success
  rw [termEquation]
  rfl

/-! ## Derivation-directed compiler erasure -/

private theorem compileTerm?_erase
    {scope : Source.Scope} {context : Source.Ctx scope}
    (ready : Runtime.Ready context)
    {sourceTerm : Source.Term scope} {sourceUse : Source.Capture scope}
    {sourceType : Source.Ty scope}
    (typing : Source.Term.HasType
      context sourceTerm sourceUse sourceType) :
    ∀ (compiled : Translation.CompiledTerm
      ready sourceTerm sourceUse sourceType),
      Translation.compileTerm? ready typing = some compiled →
        compiled.term.erase =
          SourceErasure.eraseTerm context sourceTerm := by
  exact ValueTranslationErasure.compileTerm_eraseCore typing ready

/-- Every successful certified captured-DOT term compilation commutes
exactly with canonical runtime erasure. -/
theorem compileTerm_erase
    {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context}
    {sourceTerm : Source.Term scope} {sourceUse : Source.Capture scope}
    {sourceType : Source.Ty scope}
    {typing : Source.Term.HasType
      context sourceTerm sourceUse sourceType}
    {compiled : Translation.CompiledTerm
      ready sourceTerm sourceUse sourceType}
    (success : Translation.compileTerm? ready typing = some compiled) :
    compiled.term.erase = SourceErasure.eraseTerm context sourceTerm :=
  compileTerm?_erase ready typing compiled success

/-- Option-level form: failed translation stays failed, while every
successful result maps to the direct source runtime term. -/
theorem compileTerm?_map_erase
    {scope : Source.Scope} {context : Source.Ctx scope}
    (ready : Runtime.Ready context)
    {sourceTerm : Source.Term scope} {sourceUse : Source.Capture scope}
    {sourceType : Source.Ty scope}
    (typing : Source.Term.HasType
      context sourceTerm sourceUse sourceType) :
    (Translation.compileTerm? ready typing).map
        (fun compiled => compiled.term.erase) =
      (Translation.compileTerm? ready typing).map
        (fun _ => SourceErasure.eraseTerm context sourceTerm) := by
  generalize resultEquation :
    Translation.compileTerm? ready typing = result
  cases result with
  | none => rfl
  | some compiled =>
      simp only [Option.map_some]
      exact congrArg some (compileTerm_erase resultEquation)

/-! ## Operational correspondence through exact erasure -/

/-- A compiled term takes exactly the runtime steps taken by the direct
source erasure.  This is transport along exact compiler erasure, not a
second source semantics with unrelated transitions. -/
theorem compileTerm_step_iff
    {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context}
    {sourceTerm : Source.Term scope} {sourceUse : Source.Capture scope}
    {sourceType : Source.Ty scope}
    {typing : Source.Term.HasType
      context sourceTerm sourceUse sourceType}
    {compiled : Translation.CompiledTerm
      ready sourceTerm sourceUse sourceType}
    (success : Translation.compileTerm? ready typing = some compiled)
    {next : ManySortedFC.Runtime.Tm (Layout.sig context).termCount} :
    ManySortedFC.Runtime.Step compiled.term.erase next ↔
      ManySortedFC.Runtime.Step
        (SourceErasure.eraseTerm context sourceTerm) next := by
  rw [compileTerm_erase success]

/-- The same exact transport holds for any finite runtime reduction trace. -/
theorem compileTerm_steps_iff
    {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context}
    {sourceTerm : Source.Term scope} {sourceUse : Source.Capture scope}
    {sourceType : Source.Ty scope}
    {typing : Source.Term.HasType
      context sourceTerm sourceUse sourceType}
    {compiled : Translation.CompiledTerm
      ready sourceTerm sourceUse sourceType}
    (success : Translation.compileTerm? ready typing = some compiled)
    {result : ManySortedFC.Runtime.Tm (Layout.sig context).termCount} :
    ManySortedFC.Runtime.Steps compiled.term.erase result ↔
      ManySortedFC.Runtime.Steps
        (SourceErasure.eraseTerm context sourceTerm) result := by
  rw [compileTerm_erase success]

private theorem option_map_constant_of_isSome {alpha beta : Type}
    (option : Option alpha) (constant : beta)
    (present : option.isSome = true) :
    option.map (fun _ => constant) = some constant := by
  cases option <;> simp_all

private theorem option_eq_some_get {alpha : Type} (option : Option alpha)
    (present : option.isSome = true) :
    option = some (option.get present) := by
  cases option <;> simp_all

/-! ## Runtime-variable regressions -/

namespace Regression

namespace TermRegression

export DOTCaptureToManySortedFC.Acyclic.TermTranslation.Regression
  (exactPrimitiveTyping exact_primitive_compiles exactNestedUseTyping
    exact_nested_use_compiles)

end TermRegression

namespace ExposureRegression

export DOTCaptureToManySortedFC.Acyclic.ExposureTranslation.Regression
  (OlderPlainSourceContext olderPlainReceiver olderPlainExposure)

end ExposureRegression

/-- Primitive `x.v` selection is observably non-unit: it erases to the
separated payload variable of the open receiver. -/
theorem exact_open_selection_erases_to_payload_variable :
    (Translation.compileTerm? RuntimeContext.exactObjectReady
      TermRegression.exactPrimitiveTyping).map
        (fun compiled => compiled.term.erase) =
      some (.var (Layout.termVar StaticTranslation.exactSourceContext
        (.here : Source.Var 1)).toTermIndex) := by
  calc
    _ = (Translation.compileTerm? RuntimeContext.exactObjectReady
          TermRegression.exactPrimitiveTyping).map (fun _ =>
            SourceErasure.eraseTerm StaticTranslation.exactSourceContext
              (.select StaticTranslation.exactReceiver .v)) :=
      compileTerm?_map_erase RuntimeContext.exactObjectReady
        TermRegression.exactPrimitiveTyping
    _ = _ := by
      rw [option_map_constant_of_isSome _ _
        TermRegression.exact_primitive_compiles]
      rfl

/-- Target evidence/use nodes are runtime-transparent even when two source
capture widenings surround the selected payload read. -/
theorem nested_uses_erase_to_payload_variable :
    (Translation.compileTerm? RuntimeContext.exactObjectReady
      TermRegression.exactNestedUseTyping).map
        (fun compiled => compiled.term.erase) =
      some (.var (Layout.termVar StaticTranslation.exactSourceContext
        (.here : Source.Var 1)).toTermIndex) := by
  calc
    _ = (Translation.compileTerm? RuntimeContext.exactObjectReady
          TermRegression.exactNestedUseTyping).map (fun _ =>
            SourceErasure.eraseTerm StaticTranslation.exactSourceContext
              (.select StaticTranslation.exactReceiver .v)) :=
      compileTerm?_map_erase RuntimeContext.exactObjectReady
        TermRegression.exactNestedUseTyping
    _ = _ := by
      rw [option_map_constant_of_isSome _ _
        TermRegression.exact_nested_use_compiles]
      rfl

/-- Selection through an older open receiver still erases to that receiver's
renamed payload coordinate after a newer ordinary binding is added. -/
def olderOpenPrimitiveTyping : Source.Term.HasType
    ExposureRegression.OlderPlainSourceContext
    (.select ExposureRegression.olderPlainReceiver .v)
    (.singleton ExposureRegression.olderPlainReceiver)
    ExposureRegression.olderPlainReceiver.valueMemberType :=
  .select ExposureRegression.olderPlainExposure

theorem older_open_selection_compiles :
    (Translation.compileTerm? RuntimeContext.olderObjectReady
      olderOpenPrimitiveTyping).isSome = true := by
  rfl

theorem older_open_selection_erases_to_payload_variable :
    (Translation.compileTerm? RuntimeContext.olderObjectReady
      olderOpenPrimitiveTyping).map
        (fun compiled => compiled.term.erase) =
      some (.var (Layout.termVar
        ExposureRegression.OlderPlainSourceContext
        (.there (.here : Source.Var 1))).toTermIndex) := by
  calc
    _ = (Translation.compileTerm? RuntimeContext.olderObjectReady
          olderOpenPrimitiveTyping).map (fun _ =>
            SourceErasure.eraseTerm
              ExposureRegression.OlderPlainSourceContext
              (.select ExposureRegression.olderPlainReceiver .v)) :=
      compileTerm?_map_erase RuntimeContext.olderObjectReady
        olderOpenPrimitiveTyping
    _ = _ := by
      rw [option_map_constant_of_isSome _ _
        older_open_selection_compiles]
      rfl

/-! ### Closed higher-order programs -/

namespace ComputationalRegression

export DOTCaptureToManySortedFC.Acyclic.TermTranslation.ComputationalRegression
  (emptyReady returnSelectedTyping applySelectedTyping
    returnSelected_compiles applySelected_compiles
    returnSelectedCompiled applySelectedCompiled)

theorem returnSelected_compile_success :
    Translation.compileTerm? emptyReady returnSelectedTyping =
      some returnSelectedCompiled := by
  simpa [returnSelectedCompiled] using
    option_eq_some_get
      (Translation.compileTerm? emptyReady returnSelectedTyping)
      returnSelected_compiles

theorem applySelected_compile_success :
    Translation.compileTerm? emptyReady applySelectedTyping =
      some applySelectedCompiled := by
  simpa [applySelectedCompiled] using
    option_eq_some_get
      (Translation.compileTerm? emptyReady applySelectedTyping)
      applySelected_compiles

/-- The generated target retains the complete two-let program and identity
payload after erasure. -/
theorem returnSelected_compiled_erases_exactly :
    returnSelectedCompiled.term.erase =
      ComputationalRuntime.returnSelectedRuntime := by
  calc
    _ = SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
          DOTCapture.Acyclic.ComputationalExamples.returnSelected :=
      compileTerm_erase returnSelected_compile_success
    _ = _ := ComputationalRuntime.returnSelected_erases_exactly

/-- The generated application likewise retains both lets and the payload
application after erasure. -/
theorem applySelected_compiled_erases_exactly :
    applySelectedCompiled.term.erase =
      ComputationalRuntime.applySelectedRuntime := by
  calc
    _ = SourceErasure.eraseTerm DOTCapture.Acyclic.Ctx.nil
          DOTCapture.Acyclic.ComputationalExamples.applySelected :=
      compileTerm_erase applySelected_compile_success
    _ = _ := ComputationalRuntime.applySelected_erases_exactly

/-- Exact compiler erasure transports the source runtime's two zeta steps:
the compiled program returns the identity function, not unit. -/
theorem returnSelected_compiled_steps_to_identity :
    ManySortedFC.Runtime.Steps returnSelectedCompiled.term.erase
      ComputationalRuntime.identity := by
  apply (compileTerm_steps_iff returnSelected_compile_success).2
  simpa only [ComputationalRuntime.returnSelected_erases_exactly] using
    ComputationalRuntime.returnSelected_steps_to_identity

/-- Exact compiler erasure transports the two zeta steps and final beta step
of the selected-function application. -/
theorem applySelected_compiled_steps_to_unit :
    ManySortedFC.Runtime.Steps applySelectedCompiled.term.erase .unit := by
  apply (compileTerm_steps_iff applySelected_compile_success).2
  simpa only [ComputationalRuntime.applySelected_erases_exactly] using
    ComputationalRuntime.applySelected_steps_to_unit

/-- A direct syntactic guard against the former unit-producing stub. -/
theorem returnSelected_compiled_erasure_is_not_unit :
    returnSelectedCompiled.term.erase ≠
      (.unit : ManySortedFC.Runtime.Tm 0) := by
  rw [returnSelected_compiled_erases_exactly]
  intro equality
  cases equality

/-- The value reached by the return program is itself observably non-unit. -/
theorem returnSelected_compiled_result_is_not_unit :
    ComputationalRuntime.identity ≠
      (.unit : ManySortedFC.Runtime.Tm 0) :=
  ComputationalRuntime.identity_is_not_unit

end ComputationalRegression

end Regression

end DOTCaptureToManySortedFC.Acyclic.TermTranslationErasure
