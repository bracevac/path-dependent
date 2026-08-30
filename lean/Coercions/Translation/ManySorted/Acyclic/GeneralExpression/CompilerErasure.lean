import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.Compiler
import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.SourceErasure
import Coercions.Translation.ManySorted.Acyclic.ValueTranslationErasure

/-! # Exact erasure of the direct general-expression compiler -/

namespace DOTCaptureToManySortedFC.Acyclic.GeneralExpression.CompilerErasure

namespace Source
export DOTCapture.Acyclic.GeneralExpression (Scope Ctx Value Term Capture Ty)
namespace Value
export DOTCapture.Acyclic.GeneralExpression.Value (HasType)
end Value
namespace Term
export DOTCapture.Acyclic.GeneralExpression.Term (HasType)
end Term
end Source

namespace Translation
export DOTCaptureToManySortedFC.Acyclic.GeneralExpression.Compiler
  (CompiledValue CompiledTerm compileValue? compileTerm?)
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

theorem compileTerm_eraseCore {scope : Source.Scope}
    {context : Source.Ctx scope} {term : Source.Term scope}
    {use : Source.Capture scope} {type : Source.Ty scope}
    (typing : Source.Term.HasType context term use type) :
    TermErases typing := by
  change TermErases typing
  apply DOTCapture.Acyclic.GeneralExpression.Term.HasType.rec
    (motive_1 := fun _ _ _ typing => ValueErases typing)
    (motive_2 := fun _ _ _ _ typing => TermErases typing)
  all_goals
    simp only [ValueErases, TermErases]
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
