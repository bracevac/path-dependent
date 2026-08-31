import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.Compiler
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.SourceErasure
import Coercions.Translation.ManySorted.Acyclic.ValueTranslationErasure

/-! # Exact erasure of the direct general-expression compiler -/

namespace DOTCaptureToManySortedFC.Acyclic.GeneralExpression.CompilerErasure

namespace Source
export DOTCapture.Acyclic.GeneralExpression (Scope Ctx Value Term Capture Ty)
export DOTCapture.Acyclic (ExposesObject)
namespace Value
export DOTCapture.Acyclic.GeneralExpression.Value (HasType)
end Value
namespace Term
export DOTCapture.Acyclic.GeneralExpression.Term (HasType)
end Term
end Source

namespace Translation
export DOTCaptureToManySortedFC.Acyclic.GeneralExpression.Compiler
  (CompiledValue CompiledTerm CompiledObjectSignature
    CompiledObjectArgument CompiledObjectFunction compileValue? compileTerm?
    compileObjectFunction? compilePolarizedValue?
    compilePolarizedObjectArgument? compilePolarizedTerm?)
end Translation

namespace Runtime
export DOTCaptureToManySortedFC.Acyclic.RuntimeContext (Ready)
end Runtime

private def ValueErases {scope : Source.Scope} {context : Source.Ctx scope}
    {value : Source.Value scope} {type : Source.Ty scope}
    (typing : Source.Value.HasType context value type) : Prop :=
  ∀ (ready : Runtime.Ready context)
    (compiled : Translation.CompiledValue ready value type),
    Translation.compileValue? ready typing = some compiled →
      compiled.term.erase = SourceErasure.eraseValue context value

private def TermErases {scope : Source.Scope} {context : Source.Ctx scope}
    {term : Source.Term scope} {use : Source.Capture scope}
    {type : Source.Ty scope}
    (typing : Source.Term.HasType context term use type) : Prop :=
  ∀ (ready : Runtime.Ready context)
    (compiled : Translation.CompiledTerm ready term use type),
    Translation.compileTerm? ready typing = some compiled →
      compiled.term.erase = SourceErasure.eraseTerm context term

private def ObjectArgumentErases {scope : Source.Scope}
    {context : Source.Ctx scope} {argument : Source.Term scope}
    {signature : DOTCapture.Acyclic.ObjectSig scope}
    (_ : DOTCapture.Acyclic.GeneralExpression.ObjectArgument.HasType context
      argument signature) : Prop := True

private def ObjectFunctionErases {scope : Source.Scope}
    {context : Source.Ctx scope} {function : Source.Term scope}
    {use : Source.Capture scope}
    {signature : DOTCapture.Acyclic.ObjectSig scope} {codomain : Source.Ty scope}
    {closure : Source.Capture scope}
    (_ : DOTCapture.Acyclic.GeneralExpression.ObjectFunction.HasType context
      function use signature codomain closure) : Prop := True

private def PolarizedValueErases {scope : Source.Scope}
    {context : Source.Ctx scope} {value : Source.Value scope}
    {type : Source.Ty scope}
    (typing : Source.Value.HasType context value type) : Prop :=
  ∀ (ready : Runtime.Ready context)
    (compiled : Translation.CompiledValue ready value type),
    Translation.compilePolarizedValue? ready typing = some compiled →
      compiled.term.erase = SourceErasure.eraseValue context value

private def PolarizedObjectArgumentErases {scope : Source.Scope}
    {context : Source.Ctx scope} {argument : Source.Term scope}
    {signature : DOTCapture.Acyclic.ObjectSig scope}
    (typing : DOTCapture.Acyclic.GeneralExpression.ObjectArgument.HasType
      context argument signature) : Prop :=
  ∀ (ready : Runtime.Ready context)
    (interface : Translation.CompiledObjectSignature context signature)
    (compiled : Translation.CompiledObjectArgument ready interface argument),
    Translation.compilePolarizedObjectArgument? ready interface typing =
        some compiled →
      compiled.target.payload.erase =
        SourceErasure.eraseTerm context argument

private def PolarizedObjectFunctionErases {scope : Source.Scope}
    {context : Source.Ctx scope} {function : Source.Term scope}
    {use : Source.Capture scope}
    {signature : DOTCapture.Acyclic.ObjectSig scope}
    {codomain : Source.Ty scope} {closure : Source.Capture scope}
    (typing : DOTCapture.Acyclic.GeneralExpression.ObjectFunction.HasType
      context function use signature codomain closure) : Prop :=
  ∀ (ready : Runtime.Ready context)
    (interface : Translation.CompiledObjectSignature context signature)
    (compiled : Translation.CompiledObjectFunction ready interface function
      use codomain closure),
    Translation.compileObjectFunction? ready interface typing = some compiled →
      compiled.term.erase = SourceErasure.eraseTerm context function

private def PolarizedTermErases {scope : Source.Scope}
    {context : Source.Ctx scope} {term : Source.Term scope}
    {use : Source.Capture scope} {type : Source.Ty scope}
    (typing : Source.Term.HasType context term use type) : Prop :=
  ∀ (ready : Runtime.Ready context)
    (compiled : Translation.CompiledTerm ready term use type),
    Translation.compilePolarizedTerm? ready typing = some compiled →
      compiled.term.erase = SourceErasure.eraseTerm context term

theorem compileTerm_eraseCore {scope : Source.Scope}
    {context : Source.Ctx scope} {term : Source.Term scope}
    {use : Source.Capture scope} {type : Source.Ty scope}
    (typing : Source.Term.HasType context term use type) :
    TermErases typing := by
  change TermErases typing
  apply DOTCapture.Acyclic.GeneralExpression.Term.HasType.rec
    (motive_1 := fun _ _ _ typing => ValueErases typing)
    (motive_2 := fun _ _ _ typing => ObjectArgumentErases typing)
    (motive_3 := fun _ _ _ _ _ _ typing => ObjectFunctionErases typing)
    (motive_4 := fun _ _ _ _ typing => TermErases typing)
  all_goals
    simp only [ValueErases, TermErases, ObjectArgumentErases,
      ObjectFunctionErases]
    intros
  case var scope context name ready compiled success =>
    obtain ⟨core, h, termEq⟩ :=
      Compiler.compileValue?_var_result ready name success
    rw [termEq]
    exact DOTCaptureToManySortedFC.Acyclic.ValueTranslationErasure.compileValue_erase h
  case unit =>
    unfold Compiler.compileValue? at *
    cases Option.some.inj ‹_›
    rfl
  case lam scope context domain codomain body bodyUse closure domainPlain
      bodyTyping captures ih ready compiled success =>
    obtain ⟨dt, ct, cl, hd, hc, hcl, bodyCompiled, bodyEq, finishEq⟩ :=
      Compiler.compileValue?_lam_result ready domainPlain bodyTyping captures
        success
    obtain ⟨eb, heb, heq⟩ := Compiler.finishLambda?_erase domainPlain captures
      hd hc hcl bodyCompiled finishEq
    rw [heq]
    cases domain with
    | object => contradiction
    | capturing retained shape =>
        cases shape with
        | object => contradiction
        | top | bot | one | ref | arr | capturing =>
            congr 1
            rw [← eq_of_heq heb, ih _ bodyCompiled bodyEq]
            unfold SourceErasure.eraseTerm
            congr 1
            funext index
            cases index <;> rfl
    | top | bot | one | ref | arr =>
        congr 1
        rw [← eq_of_heq heb, ih _ bodyCompiled bodyEq]
        unfold SourceErasure.eraseTerm
        congr 1
        funext index
        cases index <;> rfl
  case objectLam scope context signature codomain body bodyUse closure
      bodyTyping captures bodyIH ready compiled success =>
    unfold Compiler.compileValue? at success
    contradiction
  case object scope context signature tw cw payload payloadType tl tu cl cu
      payloadTyping ps pc ih ready compiled success =>
    obtain ⟨payloadCompiled, hp, he⟩ :=
      Compiler.compileValue?_object_erase ready tl tu cl cu payloadTyping ps pc
        success
    rw [he, ih ready payloadCompiled hp]
    exact SourceErasure.eraseValue_object context signature tw cw payload
  case adapt scope context value source target vt inc ih ready compiled success =>
    obtain ⟨inner, evidence, innerEq, termEq⟩ :=
      Compiler.compileValue?_adapt_term ready vt inc success
    rw [termEq]
    simpa [ManySortedFC.Tm.erase, ManySortedFC.Tm.eraseWith,
      ManySortedFC.Adapter.erase] using ih ready inner innerEq
  case literal => trivial
  case stable => trivial
  case returned => trivial
  case letPlain => trivial
  case use => trivial
  case ret scope context value type vt ih ready compiled success =>
    unfold Compiler.compileTerm? at success
    generalize hv : Compiler.compileValue? ready vt = rv at success
    cases rv with
    | none => simp at success
    | some cv => cases success; exact ih ready cv hv
  case select scope context receiver signature exposes ready compiled success =>
    unfold Compiler.compileTerm? at success
    cases Option.some.inj success
    exact SourceErasure.generatedSelection_erase
      (SelectionTranslation.compile ready.translated exposes).resolved
  case app scope context f a fu au ft d c fty shape aty fih aih ready compiled success =>
    obtain ⟨fc, ac, hf, ha, termEq⟩ :=
      Compiler.compileTerm?_app_term ready fty shape aty success
    rw [termEq, ManySortedFC.Tm.erase_app, SourceErasure.eraseTerm_app,
      fih ready fc hf, aih ready ac ha]
  case objectApp =>
    simp [Compiler.compileTerm?] at *
  case letPlain scope context result bound rhs body ru bu bou plain rt bt dis
      rih bih ready compiled success =>
    obtain ⟨rtarget, cout, hr, hc, rc, bc, rhsEq, bodyEq, finishEq⟩ :=
      Compiler.compileTerm?_letPlain_result ready plain rt bt dis success
    obtain ⟨eb, heb, heq⟩ := Compiler.finishPlainLet?_erase plain dis hr hc rc bc finishEq
    rw [heq, rih ready rc rhsEq]
    cases bound with
    | object => contradiction
    | capturing retained shape =>
        cases shape with
        | object => contradiction
        | top | bot | one | ref | arr | capturing =>
            congr 1
            rw [← eq_of_heq heb, bih _ bc bodyEq]
            unfold SourceErasure.eraseTerm
            congr 1
            funext index
            cases index <;> rfl
    | top | bot | one | ref | arr =>
        congr 1
        rw [← eq_of_heq heb, bih _ bc bodyEq]
        unfold SourceErasure.eraseTerm
        congr 1
        funext index
        cases index <;> rfl
  case letObject scope context sig result rhs ru body bu bou rt bt dis rih bih
      ready compiled success =>
    obtain ⟨bounds, rtarget, cout, hs, hr, hc, rc, bc, rhsEq, bodyEq,
      finishEq⟩ := Compiler.compileTerm?_letObject_result ready rt bt dis success
    obtain ⟨eb, heb, heq⟩ := Compiler.finishObjectLet?_erase dis hs hr hc rc bc finishEq
    rw [heq, rih ready rc rhsEq]
    congr 1
    cases heb
    rw [bih _ bc bodyEq]
    unfold SourceErasure.eraseTerm
    congr 1
    funext index
    cases index <;> rfl
  case use scope context term su tu type tt inc ih ready compiled success =>
    obtain ⟨inner, evidence, innerEq, termEq⟩ :=
      Compiler.compileTerm?_use_term ready tt inc success
    rw [termEq]
    exact ih ready inner innerEq

private theorem compileValue?_erase {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {value : Source.Value scope} {type : Source.Ty scope}
    (typing : Source.Value.HasType context value type) :
    ∀ compiled, Translation.compileValue? ready typing = some compiled →
      compiled.term.erase = SourceErasure.eraseValue context value := by
  intro compiled success
  let ct : Translation.CompiledTerm ready (.ret value) .empty type :=
    { sourceTyping := .ret typing, targetUse := .empty
      targetType := compiled.targetType, useTranslated := rfl
      typeTranslated := compiled.typeTranslated, term := compiled.term
      typing := compiled.typing }
  apply compileTerm_eraseCore (.ret typing) ready ct
  unfold Compiler.compileTerm?
  rw [success]
  rfl

theorem compileValue_erase {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context} {value : Source.Value scope}
    {type : Source.Ty scope} {typing : Source.Value.HasType context value type}
    {compiled : Translation.CompiledValue ready value type}
    (success : Translation.compileValue? ready typing = some compiled) :
    compiled.term.erase = SourceErasure.eraseValue context value :=
  compileValue?_erase ready typing compiled success

theorem compileTerm_erase {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context} {term : Source.Term scope}
    {use : Source.Capture scope} {type : Source.Ty scope}
    {typing : Source.Term.HasType context term use type}
    {compiled : Translation.CompiledTerm ready term use type}
    (success : Translation.compileTerm? ready typing = some compiled) :
    compiled.term.erase = SourceErasure.eraseTerm context term :=
  compileTerm_eraseCore typing ready compiled success

private theorem objectConsumer_erase {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {signature : DOTCapture.Acyclic.ObjectSig scope}
    {interface : Translation.CompiledObjectSignature context signature}
    {codomain : Source.Ty scope} {body : Source.Term (scope + 1)}
    {bodyUse : Source.Capture (scope + 1)} {closure : Source.Capture scope}
    (compiled : Compiler.CompiledObjectConsumer ready interface codomain body
      bodyUse closure) :
    compiled.term.erase = .lam compiled.bodyCompiled.term.erase := by
  simp [Compiler.CompiledObjectConsumer.term,
    DOTCaptureToManySortedFC.Acyclic.NegativeObjectInterface.abstract,
    ManySortedFC.Tm.erase, ManySortedFC.Tm.eraseWith]
  congr 2
  funext index
  cases index with
  | here => rfl
  | there older =>
      cases older with
      | there older =>
          cases older with
          | there older =>
              cases older with
              | there older =>
                  cases older with
                  | there older =>
                      cases older with
                      | there older =>
                          cases older with
                          | there older => rfl

private theorem objectApplication_erase {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {signature : DOTCapture.Acyclic.ObjectSig scope}
    {interface : Translation.CompiledObjectSignature context signature}
    {function argument : Source.Term scope}
    {functionUse : Source.Capture scope} {codomain : Source.Ty scope}
    {closure : Source.Capture scope}
    (functionCompiled : Translation.CompiledObjectFunction ready interface
      function functionUse codomain closure)
    (argumentCompiled : Translation.CompiledObjectArgument ready interface
      argument) :
    (Compiler.compileObjectApplication functionCompiled argumentCompiled).term.erase =
      .app functionCompiled.term.erase argumentCompiled.target.payload.erase := by
  rfl

set_option maxHeartbeats 8000000 in
theorem compilePolarizedTerm_eraseCore {scope : Source.Scope}
    {context : Source.Ctx scope} {term : Source.Term scope}
    {use : Source.Capture scope} {type : Source.Ty scope}
    (typing : Source.Term.HasType context term use type) :
    PolarizedTermErases typing := by
  change PolarizedTermErases typing
  apply DOTCapture.Acyclic.GeneralExpression.Term.HasType.rec
    (motive_1 := fun _ _ _ typing => PolarizedValueErases typing)
    (motive_2 := fun _ _ _ typing => PolarizedObjectArgumentErases typing)
    (motive_3 := fun _ _ _ _ _ _ typing =>
      PolarizedObjectFunctionErases typing)
    (motive_4 := fun _ _ _ _ typing => PolarizedTermErases typing)
  all_goals
    simp only [PolarizedValueErases, PolarizedObjectArgumentErases,
      PolarizedObjectFunctionErases, PolarizedTermErases]
    intros
  case var scope context name ready compiled success =>
    obtain ⟨core, coreEquation, termEquation⟩ :=
      Compiler.compilePolarizedValue?_var_result ready name success
    rw [termEquation]
    exact DOTCaptureToManySortedFC.Acyclic.ValueTranslationErasure.compileValue_erase
      coreEquation
  case unit scope context ready compiled success =>
    unfold Compiler.compilePolarizedValue? Compiler.compileValue? at success
    cases Option.some.inj success
    rfl
  case lam scope context domain codomain body bodyUse closure domainPlain
      bodyTyping captures bodyIH ready compiled success =>
    obtain ⟨domainTarget, codomainTarget, closureTarget, domainTranslated,
      codomainTranslated, closureTranslated, bodyCompiled, bodyEquation,
      finishEquation⟩ := Compiler.compilePolarizedValue?_lam_result ready
        domainPlain bodyTyping captures success
    obtain ⟨erasedBody, bodyErases, compiledErases⟩ :=
      Compiler.finishLambda?_erase domainPlain captures domainTranslated
        codomainTranslated closureTranslated bodyCompiled finishEquation
    rw [compiledErases]
    cases domain with
    | object => contradiction
    | capturing retained shape =>
        cases shape with
        | object => contradiction
        | top | bot | one | ref | arr | capturing =>
            congr 1
            rw [← eq_of_heq bodyErases,
              bodyIH _ bodyCompiled bodyEquation]
            unfold SourceErasure.eraseTerm
            congr 1
            funext index
            cases index <;> rfl
    | top | bot | one | ref | arr =>
        congr 1
        rw [← eq_of_heq bodyErases,
          bodyIH _ bodyCompiled bodyEquation]
        unfold SourceErasure.eraseTerm
        congr 1
        funext index
        cases index <;> rfl
  case objectLam scope context signature codomain body bodyUse closure
      bodyTyping captures bodyIH ready compiled success =>
    simp [Compiler.compilePolarizedValue?, Compiler.compileValue?] at success
  case object scope context signature typeWitness captureWitness payload
      payloadType typeLower typeUpper captureLower captureUpper payloadTyping
      payloadShape payloadCapture payloadIH ready compiled success =>
    unfold Compiler.compilePolarizedValue? at success
    split at success <;> try contradiction
    split at success <;> try contradiction
    split at success <;> try contradiction
    generalize payloadEquation :
      Compiler.compilePolarizedValue? ready payloadTyping = payloadResult
        at success
    cases payloadResult with
    | none => simp at success
    | some payloadCompiled =>
        simp only [Bind.bind, Option.bind] at success
        split at success <;> try contradiction
        simp only at success
        split at success <;> try contradiction
        simp only at success
        split at success <;> try contradiction
        simp only at success
        split at success <;> try contradiction
        simp only at success
        split at success <;> try contradiction
        simp only at success
        split at success <;> try contradiction
        simp only at success
        cases success
        simpa [ObjectEncoding.pack, ObjectEncoding.retagPayload,
          ManySortedFC.Tm.erase, ManySortedFC.Tm.eraseWith,
          ManySortedFC.Adapter.erase] using
          payloadIH ready payloadCompiled payloadEquation
  case adapt scope context value source target valueTyping inclusion valueIH
      ready compiled success =>
    obtain ⟨inner, evidence, innerEquation, termEquation⟩ :=
      Compiler.compilePolarizedValue?_adapt_term ready valueTyping inclusion
        success
    rw [termEquation]
    simpa [ManySortedFC.Tm.erase, ManySortedFC.Tm.eraseWith,
      ManySortedFC.Adapter.erase] using
      valueIH ready inner innerEquation
  case literal scope context available expected typeWitness captureWitness
      payload payloadType typeLower typeUpper captureLower captureUpper
      payloadTyping payloadShape payloadCapture adaptation payloadIH ready
      interface compiled success =>
    unfold Compiler.compilePolarizedObjectArgument? at success
    split at success <;> try contradiction
    split at success <;> try contradiction
    split at success <;> try contradiction
    generalize payloadEquation :
      Compiler.compilePolarizedValue? ready payloadTyping = payloadResult
        at success
    cases payloadResult with
    | none => simp at success
    | some payloadCompiled =>
        simp only [Bind.bind, Option.bind] at success
        split at success <;> try contradiction
        simp only at success
        split at success <;> try contradiction
        simp only at success
        split at success <;> try contradiction
        simp only at success
        split at success <;> try contradiction
        simp only at success
        split at success <;> try contradiction
        simp only at success
        split at success <;> try contradiction
        simp only at success
        split at success <;> try contradiction
        simp only at success
        split at success <;> try contradiction
        simp only at success
        split at success <;> try contradiction
        simp only at success
        split at success <;> try contradiction
        simp only at success
        cases success
        simpa [ObjectEncoding.retagPayload, ManySortedFC.Tm.erase,
          ManySortedFC.Tm.eraseWith, ManySortedFC.Adapter.erase] using
          payloadIH ready payloadCompiled payloadEquation
  case stable scope context name available expected canonical adaptation ready
      interface compiled success =>
    unfold Compiler.compilePolarizedObjectArgument? at success
    simpa using Compiler.compileStableObjectArgument?_erase ready interface
      canonical adaptation success
  case returned scope context signature codomain body bodyUse closure
      bodyTyping captures bodyIH ready interface compiled success =>
    obtain ⟨bodyCompiled, consumer, bodyEquation, termEquation,
      consumerBodyEquation⟩ :=
      Compiler.compileObjectFunction?_returned_result ready interface
        bodyTyping captures success
    rw [termEquation, objectConsumer_erase, consumerBodyEquation]
    congr 1
    have bodyErases := bodyIH _ bodyCompiled bodyEquation
    have bodyErasesHEq : HEq bodyCompiled.term.erase
        (SourceErasure.eraseTerm
          (context.extendTerm signature.formedType) body) :=
      heq_of_eq bodyErases
    have sourceAlignment : HEq
        (SourceErasure.eraseTerm
          (context.extendTerm signature.formedType) body)
        (DOTCapture.Acyclic.GeneralExpression.Erasure.eraseTermWith
          (SourceErasure.compiledRenaming context).lift body) := by
      unfold SourceErasure.eraseTerm
      apply heq_of_eq
      congr 1
      funext index
      cases index <;> rfl
    exact eq_of_heq (bodyErasesHEq.trans sourceAlignment)
  case letPlain scope context signature codomain bound closure rhs body rhsUse
      bodyUse bodyOuterUse boundPlain rhsTyping bodyTyping discharge rhsIH
      bodyIH ready interface compiled success =>
    obtain ⟨rhsCompiled, bodyInterface, bodyBounds, bodyCompiled,
      rhsEquation, bodyEquation, finishEquation⟩ :=
      Compiler.compileObjectFunction?_letPlain_result ready interface
        boundPlain rhsTyping bodyTyping discharge success
    obtain ⟨erasedBody, bodyErases, compiledErases⟩ :=
      Compiler.finishObjectFunctionLet?_erase ready interface boundPlain
        rhsTyping bodyTyping discharge rhsCompiled bodyInterface bodyBounds
        bodyCompiled finishEquation
    rw [compiledErases, rhsIH ready rhsCompiled rhsEquation]
    cases bound with
    | object => contradiction
    | capturing retained shape =>
        cases shape with
        | object => contradiction
        | top | bot | one | ref | arr | capturing =>
            congr 1
            rw [← eq_of_heq bodyErases,
              bodyIH _ _ bodyCompiled bodyEquation]
            unfold SourceErasure.eraseTerm
            congr 1
            funext index
            cases index <;> rfl
    | top | bot | one | ref | arr =>
        congr 1
        rw [← eq_of_heq bodyErases,
          bodyIH _ _ bodyCompiled bodyEquation]
        unfold SourceErasure.eraseTerm
        congr 1
        funext index
        cases index <;> rfl
  case use scope context function sourceUse targetUse signature codomain
      closure functionTyping inclusion functionIH ready interface compiled
      success =>
    unfold Compiler.compileObjectFunction? at success
    generalize innerEquation :
      Compiler.compileObjectFunction? ready interface functionTyping =
        innerResult at success
    cases innerResult with
    | none => simp at success
    | some inner =>
        split at success <;> try contradiction
        simp only [Bind.bind, Option.bind] at success
        split at success <;> try contradiction
        cases success
        simpa [ManySortedFC.Tm.erase, ManySortedFC.Tm.eraseWith] using
          functionIH ready interface inner innerEquation
  case ret scope context value type valueTyping valueIH ready compiled success =>
    unfold Compiler.compilePolarizedTerm? at success
    generalize valueEquation :
      Compiler.compilePolarizedValue? ready valueTyping = valueResult at success
    cases valueResult with
    | none => simp at success
    | some valueCompiled =>
        cases success
        exact valueIH ready valueCompiled valueEquation
  case select scope context receiver signature exposes ready compiled success =>
    unfold Compiler.compilePolarizedTerm? at success
    cases Option.some.inj success
    exact SourceErasure.generatedSelection_erase
      (SelectionTranslation.compile ready.translated exposes).resolved
  case app scope context function argument functionUse argumentUse functionType
      domain codomain functionTyping functionShape argumentTyping functionIH
      argumentIH ready compiled success =>
    unfold Compiler.compilePolarizedTerm? at success
    split at success <;> try contradiction
    generalize functionEquation :
      Compiler.compilePolarizedTerm? ready functionTyping = functionResult
        at success
    cases functionResult with
    | none => simp at success
    | some functionCompiled =>
        generalize argumentEquation :
          Compiler.compilePolarizedTerm? ready argumentTyping = argumentResult
            at success
        cases argumentResult with
        | none => simp at success
        | some argumentCompiled =>
            cases success
            rw [ManySortedFC.Tm.erase_app, SourceErasure.eraseTerm_app,
              functionIH ready functionCompiled functionEquation,
              argumentIH ready argumentCompiled argumentEquation]
  case objectApp scope context function argument functionUse closure codomain
      signature functionTyping argumentTyping functionIH argumentIH ready
      compiled success =>
    obtain ⟨interface, functionCompiled, argumentCompiled,
      interfaceEquation, functionEquation, argumentEquation, termEquation⟩ :=
      Compiler.compilePolarizedTerm?_objectApp_result ready functionTyping
        argumentTyping success
    rw [termEquation, objectApplication_erase,
      functionIH ready interface functionCompiled functionEquation,
      argumentIH ready interface argumentCompiled argumentEquation]
    rfl
  case letPlain scope context result bound rhs body rhsUse bodyUse bodyOuterUse
      boundPlain rhsTyping bodyTyping discharge rhsIH bodyIH ready compiled
      success =>
    obtain ⟨resultTarget, bodyOuterTarget, resultTranslated,
      bodyOuterTranslated, rhsCompiled, bodyCompiled, rhsEquation,
      bodyEquation, finishEquation⟩ :=
      Compiler.compilePolarizedTerm?_letPlain_result ready boundPlain
        rhsTyping bodyTyping discharge success
    obtain ⟨erasedBody, bodyErases, compiledErases⟩ :=
      Compiler.finishPlainLet?_erase boundPlain discharge resultTranslated
        bodyOuterTranslated rhsCompiled bodyCompiled finishEquation
    rw [compiledErases, rhsIH ready rhsCompiled rhsEquation]
    cases bound with
    | object => contradiction
    | capturing retained shape =>
        cases shape with
        | object => contradiction
        | top | bot | one | ref | arr | capturing =>
                congr 1
                rw [← eq_of_heq bodyErases,
                  bodyIH _ bodyCompiled bodyEquation]
                unfold SourceErasure.eraseTerm
                congr 1
                funext index
                cases index <;> rfl
    | top | bot | one | ref | arr =>
        congr 1
        rw [← eq_of_heq bodyErases,
          bodyIH _ bodyCompiled bodyEquation]
        unfold SourceErasure.eraseTerm
        congr 1
        funext index
        cases index <;> rfl
  case letObject scope context signature result rhs rhsUse body bodyUse
      bodyOuterUse rhsTyping bodyTyping discharge rhsIH bodyIH ready compiled
      success =>
    obtain ⟨bounds, resultTarget, bodyOuterTarget, signatureTranslated,
      resultTranslated, bodyOuterTranslated, rhsCompiled, bodyCompiled,
      rhsEquation, bodyEquation, finishEquation⟩ :=
      Compiler.compilePolarizedTerm?_letObject_result ready rhsTyping
        bodyTyping discharge success
    obtain ⟨erasedBody, bodyErases, compiledErases⟩ :=
      Compiler.finishObjectLet?_erase discharge signatureTranslated
        resultTranslated bodyOuterTranslated rhsCompiled bodyCompiled
        finishEquation
    rw [compiledErases, rhsIH ready rhsCompiled rhsEquation]
    congr 1
    cases bodyErases
    rw [bodyIH _ bodyCompiled bodyEquation]
    unfold SourceErasure.eraseTerm
    congr 1
    funext index
    cases index <;> rfl
  case use scope context term sourceUse targetUse type termTyping inclusion
      termIH ready compiled success =>
    obtain ⟨inner, evidence, innerEquation, termEquation⟩ :=
      Compiler.compilePolarizedTerm?_use_term ready termTyping inclusion success
    rw [termEquation]
    exact termIH ready inner innerEquation

private theorem compilePolarizedValue?_erase {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {value : Source.Value scope} {type : Source.Ty scope}
    (typing : Source.Value.HasType context value type) :
    ∀ compiled,
      Translation.compilePolarizedValue? ready typing = some compiled →
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
  apply compilePolarizedTerm_eraseCore (.ret typing) ready compiledTerm
  unfold Compiler.compilePolarizedTerm?
  rw [success]
  rfl

theorem compilePolarizedValue_erase {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {value : Source.Value scope} {type : Source.Ty scope}
    {typing : Source.Value.HasType context value type}
    {compiled : Translation.CompiledValue ready value type}
    (success : Translation.compilePolarizedValue? ready typing =
      some compiled) :
    compiled.term.erase = SourceErasure.eraseValue context value :=
  compilePolarizedValue?_erase ready typing compiled success

theorem compilePolarizedTerm_erase {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {term : Source.Term scope} {use : Source.Capture scope}
    {type : Source.Ty scope}
    {typing : Source.Term.HasType context term use type}
    {compiled : Translation.CompiledTerm ready term use type}
    (success : Translation.compilePolarizedTerm? ready typing =
      some compiled) :
    compiled.term.erase = SourceErasure.eraseTerm context term :=
  compilePolarizedTerm_eraseCore typing ready compiled success

theorem compilePolarizedTerm?_map_erase {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {term : Source.Term scope} {use : Source.Capture scope}
    {type : Source.Ty scope}
    (typing : Source.Term.HasType context term use type) :
    (Translation.compilePolarizedTerm? ready typing).map
        (fun compiled => compiled.term.erase) =
      (Translation.compilePolarizedTerm? ready typing).map
        (fun _ => SourceErasure.eraseTerm context term) := by
  generalize success : Translation.compilePolarizedTerm? ready typing = result
  cases result with
  | none => rfl
  | some compiled =>
      exact congrArg some (compilePolarizedTerm_erase success)

theorem compilePolarizedTerm_step_iff {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {term : Source.Term scope} {use : Source.Capture scope}
    {type : Source.Ty scope}
    {typing : Source.Term.HasType context term use type}
    {compiled : Translation.CompiledTerm ready term use type}
    (success : Translation.compilePolarizedTerm? ready typing =
      some compiled) {next} :
    ManySortedFC.Runtime.Step compiled.term.erase next ↔
      ManySortedFC.Runtime.Step (SourceErasure.eraseTerm context term) next := by
  rw [compilePolarizedTerm_erase success]

theorem compilePolarizedTerm_steps_iff {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Runtime.Ready context}
    {term : Source.Term scope} {use : Source.Capture scope}
    {type : Source.Ty scope}
    {typing : Source.Term.HasType context term use type}
    {compiled : Translation.CompiledTerm ready term use type}
    (success : Translation.compilePolarizedTerm? ready typing =
      some compiled) {result} :
    ManySortedFC.Runtime.Steps compiled.term.erase result ↔
      ManySortedFC.Runtime.Steps
        (SourceErasure.eraseTerm context term) result := by
  rw [compilePolarizedTerm_erase success]

theorem compileTerm?_map_erase {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Runtime.Ready context)
    {term : Source.Term scope} {use : Source.Capture scope}
    {type : Source.Ty scope} (typing : Source.Term.HasType context term use type) :
    (Translation.compileTerm? ready typing).map (fun c => c.term.erase) =
      (Translation.compileTerm? ready typing).map
        (fun _ => SourceErasure.eraseTerm context term) := by
  generalize h : Translation.compileTerm? ready typing = r
  cases r with
  | none => rfl
  | some c => exact congrArg some (compileTerm_erase h)

theorem compileTerm_step_iff {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context} {term : Source.Term scope}
    {use : Source.Capture scope} {type : Source.Ty scope}
    {typing : Source.Term.HasType context term use type}
    {compiled : Translation.CompiledTerm ready term use type}
    (success : Translation.compileTerm? ready typing = some compiled) {next} :
    ManySortedFC.Runtime.Step compiled.term.erase next ↔
      ManySortedFC.Runtime.Step (SourceErasure.eraseTerm context term) next := by
  rw [compileTerm_erase success]

theorem compileTerm_steps_iff {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context} {term : Source.Term scope}
    {use : Source.Capture scope} {type : Source.Ty scope}
    {typing : Source.Term.HasType context term use type}
    {compiled : Translation.CompiledTerm ready term use type}
    (success : Translation.compileTerm? ready typing = some compiled) {result} :
    ManySortedFC.Runtime.Steps compiled.term.erase result ↔
      ManySortedFC.Runtime.Steps (SourceErasure.eraseTerm context term) result := by
  rw [compileTerm_erase success]

end DOTCaptureToManySortedFC.Acyclic.GeneralExpression.CompilerErasure
