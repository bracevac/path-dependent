import Coercions.Translation.ManySorted.Acyclic.ValueTranslation
import Coercions.Translation.ManySorted.Acyclic.SourceErasure

/-!
# Erasure of certified acyclic value translation

The acyclic object convention is representation-transparent at runtime.
Capture retagging, logical adaptation, and existential packaging erase,
while source lambdas retain their full compiled bodies.  The mutual proof
also covers application, plain sequencing, and object opening, so every
successful value/MNF compilation has exactly the independent source erasure.

This is the closed, acyclic, value-MNF captured-DOT compiler case-study core's
positive `{A,C,v}` fragment: variable-only paths and plain lambda parameters.
It does not claim intersections, recursive self types, or object-parameter
universal/negative translation.
-/

namespace DOTCaptureToManySortedFC.Acyclic.ValueTranslationErasure

namespace Source

export DOTCapture.Acyclic (Scope Ctx Value Term Capture Ty)

namespace Value
export DOTCapture.Acyclic.Value (HasType)
end Value

namespace Term
export DOTCapture.Acyclic.Term (HasType)
end Term

end Source

namespace Translation

export DOTCaptureToManySortedFC.Acyclic.ValueTranslation
  (CompiledValue CompiledTerm compileValue? compileTerm?)

end Translation

namespace Runtime

export DOTCaptureToManySortedFC.Acyclic.RuntimeContext (Ready)

end Runtime

/-! ## Compiler erasure -/

private theorem plainSig {scope : Source.Scope}
    (context : Source.Ctx scope) (type : Source.Ty scope)
    (plain : type.IsPlain) :
    Layout.sig (context.extendTerm type) =
      (Layout.sig context) ▹ .term := by
  cases type with
  | top | bot | one | ref | arr => rfl
  | object =>
      simp [DOTCapture.Acyclic.Ty.IsPlain,
        DOTCapture.Acyclic.Ty.objectSignature?,
        DOTCapture.Acyclic.Ty.stripCapture] at plain
  | capturing captures shape =>
      cases shape with
      | object =>
          simp [DOTCapture.Acyclic.Ty.IsPlain,
            DOTCapture.Acyclic.Ty.objectSignature?,
            DOTCapture.Acyclic.Ty.stripCapture] at plain
      | top | bot | one | ref | arr | capturing => rfl

/-- A plain source binding and its one target term binder induce the same
runtime lifting.  `HEq` accounts for the fact that the source classifier,
rather than the target signature index, establishes the scope equality. -/
private theorem compiledRenaming_extendPlain {scope : Source.Scope}
    (context : Source.Ctx scope) (type : Source.Ty scope)
    (plain : type.IsPlain) :
    HEq (SourceErasure.compiledRenaming (context.extendTerm type))
      (SourceErasure.compiledRenaming context).lift := by
  cases type with
  | top => apply heq_of_eq; funext index; cases index <;> rfl
  | bot => apply heq_of_eq; funext index; cases index <;> rfl
  | one => apply heq_of_eq; funext index; cases index <;> rfl
  | ref => apply heq_of_eq; funext index; cases index <;> rfl
  | arr => apply heq_of_eq; funext index; cases index <;> rfl
  | object =>
      simp [DOTCapture.Acyclic.Ty.IsPlain,
        DOTCapture.Acyclic.Ty.objectSignature?,
        DOTCapture.Acyclic.Ty.stripCapture] at plain
  | capturing captures shape =>
      cases shape with
      | object =>
          simp [DOTCapture.Acyclic.Ty.IsPlain,
            DOTCapture.Acyclic.Ty.objectSignature?,
            DOTCapture.Acyclic.Ty.stripCapture] at plain
      | top | bot | one | ref | arr | capturing =>
          apply heq_of_eq
          funext index
          cases index <;> rfl

/-- A canonical object expansion adds many static target binders but exactly
the same single runtime payload coordinate as its source binding. -/
private theorem compiledRenaming_extendObject {scope : Source.Scope}
    (context : Source.Ctx scope)
    (signature : DOTCapture.Acyclic.ObjectSig scope) :
    SourceErasure.compiledRenaming
        (context.extendTerm (.capturing signature.captureUpper
          (.object signature))) =
      (SourceErasure.compiledRenaming context).lift := by
  funext index
  cases index with
  | here => rfl
  | there older => rfl

/-- Canonical target erasure below the fixed object telescope is the same
as erasing with the telescope lift used by `Tm.open`. -/
private theorem payloadRenamingIdentity (scope : ManySortedFC.Sig) :
    (ManySortedFC.Erasure.Renaming.identity scope).liftPayload
        ObjectEncoding.symbols ObjectEncoding.relations =
      ManySortedFC.Erasure.Renaming.identity
        (ObjectEncoding.PayloadScope scope) := by
  funext index
  cases index with
  | here => rfl
  | there index =>
      cases index with
      | there index =>
        cases index with
        | there index =>
          cases index with
          | there index =>
            cases index with
            | there index =>
              cases index with
              | there index =>
                cases index with
                | there index => rfl

private theorem payloadEraseCanonical (scope : ManySortedFC.Sig)
    (body : ManySortedFC.Tm (ObjectEncoding.PayloadScope scope)) :
    body.eraseWith
        ((ManySortedFC.Erasure.Renaming.identity scope).liftPayload
          ObjectEncoding.symbols ObjectEncoding.relations) =
      body.erase := by
  unfold ManySortedFC.Tm.erase
  rw [payloadRenamingIdentity]
  rfl

private def ValueErases {scope : Source.Scope}
    {context : Source.Ctx scope} {value : Source.Value scope}
    {type : Source.Ty scope}
    (typing : Source.Value.HasType context value type) : Prop :=
  ∀ (ready : Runtime.Ready context)
    (compiled : Translation.CompiledValue ready value type),
    Translation.compileValue? ready typing = some compiled →
      compiled.term.erase = SourceErasure.eraseValue context value

private def TermErases {scope : Source.Scope}
    {context : Source.Ctx scope} {term : Source.Term scope}
    {use : Source.Capture scope} {type : Source.Ty scope}
    (typing : Source.Term.HasType context term use type) : Prop :=
  ∀ (ready : Runtime.Ready context)
    (compiled : Translation.CompiledTerm ready term use type),
    Translation.compileTerm? ready typing = some compiled →
      compiled.term.erase = SourceErasure.eraseTerm context term

/-- The mutual value/MNF compiler commutes with the independently defined
source erasure for every typing rule. -/
theorem compileTerm_eraseCore {scope : Source.Scope}
    {context : Source.Ctx scope} {term : Source.Term scope}
    {use : Source.Capture scope} {type : Source.Ty scope}
    (typing : Source.Term.HasType context term use type) :
    TermErases typing := by
  change TermErases typing
  apply DOTCapture.Acyclic.Term.HasType.rec
    (motive_1 := fun _ _ _ typing => ValueErases typing)
    (motive_2 := fun _ _ _ _ typing => TermErases typing)
  case var =>
    intro scope context name
    unfold ValueErases
    intro ready compiled success
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
  case unit =>
    intro scope context
    unfold ValueErases
    intro ready compiled success
    unfold ValueTranslation.compileValue? at success
    cases Option.some.inj success
    rfl
  case lam =>
    intro scope context domain codomain body bodyUse closure domainPlain
      bodyTyping captures induction
    unfold TermErases at induction
    unfold ValueErases
    intro ready compiled success
    obtain ⟨bodyReady, bodyCompiled, erasedBody, bodyEquation,
      bodyErasure, compiledErasure⟩ :=
      ValueTranslation.compileValue?_lam_erase ready domainPlain bodyTyping
        captures success
    rw [compiledErasure]
    cases domain with
    | object signature =>
        simp [DOTCapture.Acyclic.Ty.IsPlain,
          DOTCapture.Acyclic.Ty.objectSignature?,
          DOTCapture.Acyclic.Ty.stripCapture] at domainPlain
    | capturing retained shape =>
        cases shape with
        | object signature =>
            simp [DOTCapture.Acyclic.Ty.IsPlain,
              DOTCapture.Acyclic.Ty.objectSignature?,
              DOTCapture.Acyclic.Ty.stripCapture] at domainPlain
        | top | bot | one | ref | arr | capturing =>
            congr 1
            rw [← eq_of_heq bodyErasure,
              induction bodyReady bodyCompiled bodyEquation]
            unfold SourceErasure.eraseTerm
            congr 1
            funext index
            cases index <;> rfl
    | top | bot | one | ref | arr =>
        congr 1
        rw [← eq_of_heq bodyErasure,
          induction bodyReady bodyCompiled bodyEquation]
        unfold SourceErasure.eraseTerm
        congr 1
        funext index
        cases index <;> rfl
  case object =>
    intro scope context signature typeWitness captureWitness payload
      payloadType typeLower typeUpper captureLower captureUpper payloadTyping
      payloadShape payloadCapture induction
    unfold ValueErases at induction ⊢
    intro ready compiled success
    unfold ValueTranslation.compileValue? at success
    simp only [SourceErasure.eraseValue]
    split at success <;> try simp_all
    split at success <;> try simp_all
    split at success <;> try simp_all
    generalize payloadEquation :
      ValueTranslation.compileValue? ready payloadTyping = payloadResult
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
          induction ready payloadCompiled payloadEquation
  case adapt =>
    intro scope context value source target valueTyping inclusion induction
    unfold ValueErases at induction ⊢
    intro ready compiled success
    obtain ⟨valueCompiled, evidence, valueEquation, termEquation⟩ :=
      ValueTranslation.compileValue?_adapt_term ready valueTyping inclusion
        success
    rw [termEquation]
    simpa [ManySortedFC.Tm.erase, ManySortedFC.Tm.eraseWith,
      ManySortedFC.Adapter.erase] using
      induction ready valueCompiled valueEquation
  case ret =>
    intro scope context value type valueTyping induction
    unfold ValueErases at induction
    unfold TermErases
    intro ready compiled success
    unfold ValueTranslation.compileTerm? at success
    generalize valueEquation :
      ValueTranslation.compileValue? ready valueTyping = valueResult at success
    cases valueResult with
    | none => simp at success
    | some valueCompiled =>
        cases success
        exact induction ready valueCompiled valueEquation
  case select =>
    intro scope context receiver signature exposes
    unfold TermErases
    intro ready compiled success
    unfold ValueTranslation.compileTerm? at success
    cases Option.some.inj success
    let selected := SelectionTranslation.compile ready.translated exposes
    change (SelectionTranslation.term selected.resolved).erase = _
    simpa [selected] using
      SourceErasure.generatedSelection_erase selected.resolved
  case app =>
    intro scope context function argument functionType domain codomain
      functionTyping functionShape domainPlain argumentTyping functionInduction
      argumentInduction
    unfold ValueErases at functionInduction argumentInduction
    unfold TermErases
    intro ready compiled success
    unfold ValueTranslation.compileTerm? at success
    split at success <;> try contradiction
    generalize functionEquation :
      ValueTranslation.compileValue? ready functionTyping = functionResult
        at success
    cases functionResult with
    | none => simp at success
    | some functionCompiled =>
        generalize argumentEquation :
          ValueTranslation.compileValue? ready argumentTyping = argumentResult
            at success
        cases argumentResult with
        | none => simp at success
        | some argumentCompiled =>
            cases success
            simp only [ManySortedFC.Tm.erase_app,
              SourceErasure.eraseTerm_app]
            rw [functionInduction ready functionCompiled functionEquation,
              argumentInduction ready argumentCompiled argumentEquation]
  case letPlain =>
    intro scope context result bound rhs body rhsUse bodyUse bodyOuterUse
      boundPlain rhsTyping bodyTyping discharge rhsInduction bodyInduction
    unfold TermErases at rhsInduction bodyInduction ⊢
    intro ready compiled success
    obtain ⟨rhsCompiled, bodyReady, bodyCompiled, erasedBody, rhsEquation,
      bodyEquation, bodyErasure, compiledErasure⟩ :=
      ValueTranslation.compileTerm?_letPlain_erase ready boundPlain
        rhsTyping bodyTyping discharge success
    rw [compiledErasure, rhsInduction ready rhsCompiled rhsEquation]
    cases bound with
    | object signature =>
        simp [DOTCapture.Acyclic.Ty.IsPlain,
          DOTCapture.Acyclic.Ty.objectSignature?,
          DOTCapture.Acyclic.Ty.stripCapture] at boundPlain
    | capturing retained shape =>
        cases shape with
        | object signature =>
            simp [DOTCapture.Acyclic.Ty.IsPlain,
              DOTCapture.Acyclic.Ty.objectSignature?,
              DOTCapture.Acyclic.Ty.stripCapture] at boundPlain
        | top | bot | one | ref | arr | capturing =>
            congr 1
            rw [← eq_of_heq bodyErasure,
              bodyInduction bodyReady bodyCompiled bodyEquation]
            unfold SourceErasure.eraseTerm
            congr 1
            funext index
            cases index <;> rfl
    | top | bot | one | ref | arr =>
        congr 1
        rw [← eq_of_heq bodyErasure,
          bodyInduction bodyReady bodyCompiled bodyEquation]
        unfold SourceErasure.eraseTerm
        congr 1
        funext index
        cases index <;> rfl
  case letObject =>
    intro scope context signature result rhs body bodyUse bodyOuterUse
      rhsTyping bodyTyping discharge rhsInduction bodyInduction
    unfold ValueErases at rhsInduction
    unfold TermErases at bodyInduction ⊢
    intro ready compiled success
    obtain ⟨rhsCompiled, bodyReady, bodyCompiled, erasedBody, rhsEquation,
      bodyEquation, bodyErasure, compiledErasure⟩ :=
      ValueTranslation.compileTerm?_letObject_erase ready rhsTyping
        bodyTyping discharge success
    rw [compiledErasure, rhsInduction ready rhsCompiled rhsEquation]
    congr 1
    rw [← eq_of_heq bodyErasure,
      bodyInduction bodyReady bodyCompiled bodyEquation]
    unfold SourceErasure.eraseTerm
    congr 1
    funext index
    cases index <;> rfl
  case use =>
    intro scope context term sourceUse targetUse type termTyping inclusion
      induction
    unfold TermErases at induction ⊢
    intro ready compiled success
    obtain ⟨inner, evidence, innerEquation, termEquation⟩ :=
      ValueTranslation.compileTerm?_use_term ready termTyping inclusion success
    rw [termEquation]
    exact induction ready inner innerEquation

private theorem compileValue?_erase
    {scope : Source.Scope} {context : Source.Ctx scope}
    (ready : Runtime.Ready context)
    {value : Source.Value scope} {type : Source.Ty scope}
    (typing : Source.Value.HasType context value type) :
    ∀ (compiled : Translation.CompiledValue ready value type),
      Translation.compileValue? ready typing = some compiled →
        compiled.term.erase = SourceErasure.eraseValue context value := by
  intro compiled success
  let compiledTerm : Translation.CompiledTerm ready (.ret value) .empty type :=
    { sourceTyping := .ret typing
      targetUse := .empty
      targetType := compiled.targetType
      useTranslated := rfl
      typeTranslated := compiled.typeTranslated
      term := compiled.term
      typing := compiled.typing }
  have termSuccess : Translation.compileTerm? ready (.ret typing) =
      some compiledTerm := by
    unfold ValueTranslation.compileTerm?
    rw [success]
    rfl
  exact compileTerm_eraseCore (.ret typing) ready compiledTerm termSuccess

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
