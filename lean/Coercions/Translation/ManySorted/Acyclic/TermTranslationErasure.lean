import Coercions.Translation.ManySorted.Acyclic.TermTranslation
import Coercions.Translation.ManySorted.Acyclic.ValueTranslationErasure
import Coercions.Translation.ManySorted.Acyclic.SourceErasure

/-!
# Erasure of certified acyclic term translation

Returns reuse value translation, primitive `x.v` selection is a read of the
receiver's separated payload variable, and every source/target capture-use
annotation erases.  Successful compilation therefore preserves the direct
captured-DOT runtime term exactly.
-/

namespace DOTCaptureToManySortedFC.Acyclic.TermTranslationErasure

namespace Source

export DOTCapture.Acyclic (Scope Var Path Ctx Term Capture Ty)

namespace Term
export DOTCapture.Acyclic.Term (HasType)
end Term

end Source

namespace Translation

export DOTCaptureToManySortedFC.Acyclic.TermTranslation
  (CompiledTerm compileTerm? compileUse? compileSelect)

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
  induction typing with
  | ret valueTyping =>
      intro compiled success
      change Option.map _
        (ValueTranslation.compileValue? ready valueTyping) =
          some compiled at success
      generalize valueEquation :
        ValueTranslation.compileValue? ready valueTyping = valueResult
      cases valueResult with
      | none => simp [valueEquation] at success
      | some valueCompiled =>
          rw [valueEquation] at success
          cases Option.some.inj success
          exact ValueTranslationErasure.compileValue_erase valueEquation
  | select exposes =>
      intro compiled success
      change some (TermTranslation.compileSelect ready exposes) =
        some compiled at success
      cases Option.some.inj success
      let selected := SelectionTranslation.compile ready.translated exposes
      simpa [TermTranslation.compileSelect, selected] using
        SourceErasure.generatedSelection_erase selected.resolved
  | use termTyping inclusion induction =>
      intro compiled success
      change Option.bind
        (TermTranslation.compileTerm? ready termTyping)
        (fun inner => TermTranslation.compileUse? inner inclusion) =
          some compiled at success
      generalize innerEquation :
        TermTranslation.compileTerm? ready termTyping = innerResult
      cases innerResult with
      | none => simp [innerEquation] at success
      | some inner =>
          rw [innerEquation] at success
          have outerErase := compileUse?_erase inner inclusion success
          exact outerErase.trans (induction inner innerEquation)

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

private theorem option_map_constant_of_isSome {alpha beta : Type}
    (option : Option alpha) (constant : beta)
    (present : option.isSome = true) :
    option.map (fun _ => constant) = some constant := by
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

end Regression

end DOTCaptureToManySortedFC.Acyclic.TermTranslationErasure
