import Coercions.Translation.ManySorted.Acyclic.ValueTranslation
import Coercions.Translation.ManySorted.Acyclic.SourceErasure

/-!
# Erasure of certified acyclic value translation

The acyclic object convention is representation-transparent at runtime.
Capture retagging erases, existential packaging erases to its payload, and an
already-open object receiver is repackaged only in static syntax.  Therefore
every successful value compilation has exactly the direct source erasure.
-/

namespace DOTCaptureToManySortedFC.Acyclic.ValueTranslationErasure

namespace Source

export DOTCapture.Acyclic (Scope Ctx Value Ty)

namespace Value
export DOTCapture.Acyclic.Value (HasType)
end Value

end Source

namespace Translation

export DOTCaptureToManySortedFC.Acyclic.ValueTranslation
  (CompiledValue compileValue?)

end Translation

namespace Runtime

export DOTCaptureToManySortedFC.Acyclic.RuntimeContext (Ready)

end Runtime

/-! ## Compiler erasure -/

private theorem compileValue?_erase
    {scope : Source.Scope} {context : Source.Ctx scope}
    (ready : Runtime.Ready context)
    {value : Source.Value scope} {type : Source.Ty scope}
    (typing : Source.Value.HasType context value type) :
    ∀ (compiled : Translation.CompiledValue ready value type),
      Translation.compileValue? ready typing = some compiled →
        compiled.term.erase =
          SourceErasure.eraseValue context value := by
  induction typing with
  | var =>
      rename_i name
      intro compiled success
      unfold ValueTranslation.compileValue? at success
      generalize resolutionEquation :
        RuntimeContext.resolveVariable ready name = resolution at success
      cases resolution with
      | plain facts =>
          simp only at success
          cases Option.some.inj success
          cases facts with
          | mk targetType notObject typeTranslated targetLookup =>
              cases targetType <;>
                change ManySortedFC.Runtime.Tm.var
                    (Layout.termVar context name).toTermIndex =
                  ManySortedFC.Runtime.Tm.var
                    (Layout.termVar context name).toTermIndex <;>
                rfl
      | object facts =>
          simp only at success
          cases Option.some.inj success
          change ManySortedFC.Runtime.Tm.var
              facts.resolved.slot.payload.toTermIndex =
            ManySortedFC.Runtime.Tm.var
              (Layout.termVar context name).toTermIndex
          rw [facts.resolved.payloadIsPath]
          rfl
  | unit =>
      intro compiled success
      unfold ValueTranslation.compileValue? at success
      cases Option.some.inj success
      rfl
  | object typeLower typeUpper captureLower captureUpper payloadTyping
      payloadShape payloadCapture induction =>
      intro compiled success
      unfold ValueTranslation.compileValue? at success
      simp only [SourceErasure.eraseValue]
      split at success <;> try simp_all
      split at success <;> try simp_all
      split at success <;> try simp_all
      generalize payloadEquation :
        Translation.compileValue? ready payloadTyping = payloadResult
          at success
      cases payloadResult with
      | none => simp at success
      | some payloadCompiled =>
          simp only [Option.bind] at success
          split at success <;> try simp_all
          split at success <;> try simp_all
          split at success <;> try simp_all
          split at success <;> try simp_all
          split at success <;> try simp_all
          split at success <;> try simp_all
          cases success
          simpa [ObjectEncoding.pack, ObjectEncoding.retagPayload,
            ManySortedFC.Tm.erase, ManySortedFC.Tm.eraseWith,
            ManySortedFC.Adapter.erase] using
            induction

/-- Successful certified value translation commutes exactly with canonical
source and target erasure. -/
theorem compileValue_erase
    {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context}
    {value : Source.Value scope} {type : Source.Ty scope}
    {typing : Source.Value.HasType context value type}
    {compiled : Translation.CompiledValue ready value type}
    (success : Translation.compileValue? ready typing = some compiled) :
    compiled.term.erase = SourceErasure.eraseValue context value :=
  compileValue?_erase ready typing compiled success

/-- Option-level form: failure is preserved, while every successful result
maps to the one direct source runtime term. -/
theorem compileValue?_map_erase
    {scope : Source.Scope} {context : Source.Ctx scope}
    (ready : Runtime.Ready context)
    {value : Source.Value scope} {type : Source.Ty scope}
    (typing : Source.Value.HasType context value type) :
    (Translation.compileValue? ready typing).map
        (fun compiled => compiled.term.erase) =
      (Translation.compileValue? ready typing).map
        (fun _ => SourceErasure.eraseValue context value) := by
  generalize resultEquation :
    Translation.compileValue? ready typing = result
  cases result with
  | none => rfl
  | some compiled =>
      simp only [Option.map_some]
      exact congrArg some (compileValue_erase resultEquation)

private theorem option_map_constant_of_isSome {alpha beta : Type}
    (option : Option alpha) (constant : beta)
    (present : option.isSome = true) :
    option.map (fun _ => constant) = some constant := by
  cases option <;> simp_all

/-! ## Decisive regressions -/

namespace Regression

namespace ValueRegression

export DOTCaptureToManySortedFC.Acyclic.ValueTranslation.Regression
  (exactObjectCompiled? exact_object_compiles_to_exact_type
    returnedObjectCompiled? returnedObjectTyping
    returned_object_variable_compiles)

end ValueRegression

namespace SourceExamples

export DOTCapture.Acyclic.Examples (exactObject exactObjectTyping)

end SourceExamples

theorem exact_object_compiler_succeeds :
    ValueRegression.exactObjectCompiled?.isSome = true := by
  have translatedType :=
    ValueRegression.exact_object_compiles_to_exact_type
  generalize resultEquation :
    ValueRegression.exactObjectCompiled? = result
      at translatedType ⊢
  cases result <;> simp_all

/-- The exact `A = One`, `C = ∅` package has no runtime wrapper and
therefore erases to its unit payload. -/
theorem exact_object_erases_to_payload :
    ValueRegression.exactObjectCompiled?.map
        (fun compiled => compiled.term.erase) =
      some ManySortedFC.Runtime.Tm.unit := by
  calc
    _ = ValueRegression.exactObjectCompiled?.map (fun _ =>
          SourceErasure.eraseValue
            (DOTCapture.Acyclic.Ctx.nil : Source.Ctx 0)
            SourceExamples.exactObject) :=
      compileValue?_map_erase RuntimeContext.nil
        SourceExamples.exactObjectTyping
    _ = _ := by
      rw [option_map_constant_of_isSome _ _
        exact_object_compiler_succeeds]
      rfl

/-- Returning an already-open object repackages it only statically.  The
target package and retag adapter both erase, leaving the runtime variable of
the receiver's separated payload. -/
theorem returned_object_erases_to_runtime_variable :
    ValueRegression.returnedObjectCompiled?.map
        (fun compiled => compiled.term.erase) =
      some (.var (Layout.termVar
        StaticTranslation.exactSourceContext
        (.here : DOTCapture.Acyclic.Var 1)).toTermIndex) := by
  calc
    _ = ValueRegression.returnedObjectCompiled?.map (fun _ =>
          SourceErasure.eraseValue StaticTranslation.exactSourceContext
            (.var (.here : DOTCapture.Acyclic.Var 1))) :=
      compileValue?_map_erase RuntimeContext.exactObjectReady
        ValueRegression.returnedObjectTyping
    _ = _ := by
      rw [option_map_constant_of_isSome _ _
        ValueRegression.returned_object_variable_compiles]
      rfl

end Regression

end DOTCaptureToManySortedFC.Acyclic.ValueTranslationErasure
