import Coercions.ManySortedFC.TermTyping
import Coercions.ManySortedFC.TheoryModelChecker

/-!
# Structural checker for annotated many-sorted FC terms

The checker follows the annotated term syntax and synthesizes one exact type.
Every independently synthesized type is compared by decidable equality; no
subtyping, subcapturing, constraint solving, or adapter search is performed.
Logical certificates, structural adapters, and local-theory models are
delegated to their proof-producing structural checkers. Adapter application
additionally checks the ANF value boundary needed by its eta erasure.
-/

namespace ManySortedFC
namespace Tm

/-- A successful value check together with its declarative witness. -/
structure ValueChecked {scope : Sig} (term : Tm scope) : Type where
  typing : IsValue term

/-- Check the call-by-value side condition used by static abstraction.

Static abstractions and packages disappear or expose their payload at runtime,
so their contained term must itself already be a value. -/
def checkValue {scope : Sig} : (term : Tm scope) ->
    Option (ValueChecked term)
  | .var _ => some ⟨.var⟩
  | .unit => some ⟨.unit⟩
  | .lam _ _ _ => some ⟨.lam⟩
  | .app _ _ => none
  | .let' _ _ _ => none
  | .adapt term _ => do
      let checked ← checkValue term
      pure ⟨.adapt checked.typing⟩
  | .slam _ body => do
      let checked ← checkValue body
      pure ⟨.slam checked.typing⟩
  | .sapp _ _ _ _ => none
  | .pack _ _ _ _ payload => do
      let checked ← checkValue payload
      pure ⟨.pack checked.typing⟩
  | .«open» _ _ _ _ _ => none

/-- The exact type synthesized for an annotated term, together with its
declarative typing derivation. -/
structure Checked {scope : Sig} (context : Ctx scope) (term : Tm scope) where
  type : Ty scope
  typing : HasType context term type

/-- Structurally synthesize the exact type of an annotated term. -/
def check {scope : Sig} (context : Ctx scope) :
    (term : Tm scope) -> Option (Checked context term)
  | .var index =>
      some ⟨(context.lookup index).termType, .var index⟩

  | .unit =>
      some ⟨.one, .unit⟩

  | .lam domain codomain body => do
      let bodyChecked ← check (context.extendTerm domain) body
      if bodyMatches : bodyChecked.type = codomain.weaken then
        let bodyTyping : HasType (context.extendTerm domain) body
            codomain.weaken := by
          simpa [bodyMatches] using bodyChecked.typing
        pure ⟨.arr domain codomain, .lam bodyTyping⟩
      else
        none

  | .app function argument => do
      let functionChecked ← check context function
      match functionType : functionChecked.type with
      | .arr domain codomain => do
          let argumentChecked ← check context argument
          if argumentMatches : argumentChecked.type = domain then
            let functionTyping : HasType context function
                (.arr domain codomain) := by
              simpa [functionType] using functionChecked.typing
            let argumentTyping : HasType context argument domain := by
              simpa [argumentMatches] using argumentChecked.typing
            pure ⟨codomain, .app functionTyping argumentTyping⟩
          else
            none
      | _ => none

  | .let' result rhs body => do
      let rhsChecked ← check context rhs
      let bodyChecked ← check
        (context.extendTerm rhsChecked.type) body
      if bodyMatches : bodyChecked.type = result.weaken then
        let bodyTyping : HasType (context.extendTerm rhsChecked.type) body
            result.weaken := by
          simpa [bodyMatches] using bodyChecked.typing
        pure ⟨result, .let' rhsChecked.typing bodyTyping⟩
      else
        none

  | .adapt term adapter => do
      let termValue ← checkValue term
      let termChecked ← check context term
      let adapterChecked ← Adapter.check context adapter
      if sourceMatches : termChecked.type = adapterChecked.source then
        let adapterTyping : Adapter.HasType context adapter termChecked.type
            adapterChecked.target := by
          simpa [sourceMatches] using adapterChecked.typing
        pure ⟨adapterChecked.target,
          .adapt termValue.typing termChecked.typing adapterTyping⟩
      else
        none

  | .slam theory body => do
      let bodyValue ← checkValue body
      let bodyChecked ← check (context.extendTheory theory) body
      pure ⟨.forallT theory bodyChecked.type,
        .slam bodyValue.typing bodyChecked.typing⟩

  | @Tm.sapp _ symbols relations theory function symbolArguments
      evidenceArguments => do
      let functionChecked ← check context function
      match functionType : functionChecked.type with
      | @Ty.forallT _ actualSymbols actualRelations actualTheory bodyType =>
          let actual : Σ symbols, Σ relations,
              Theory scope symbols relations :=
            ⟨actualSymbols, actualRelations, actualTheory⟩
          let expected : Σ symbols, Σ relations,
              Theory scope symbols relations :=
            ⟨symbols, relations, theory⟩
          if interfaceMatches : actual = expected then
            by
              dsimp [actual, expected] at interfaceMatches
              cases interfaceMatches
              exact do
                let functionTyping : HasType context function
                    (.forallT theory bodyType) := by
                  simpa [functionType] using functionChecked.typing
                let satisfaction ← Theory.checkSatisfaction context
                  symbolArguments theory evidenceArguments
                pure ⟨bodyType.instantiateStatic symbolArguments,
                  .sapp functionTyping satisfaction⟩
          else
            none
      | _ => none

  | .pack theory payloadType symbolArguments evidenceArguments payload => do
      let satisfaction ← Theory.checkSatisfaction context
        symbolArguments theory evidenceArguments
      let payloadChecked ← check context payload
      let expectedPayload := payloadType.instantiateStatic symbolArguments
      if payloadMatches : payloadChecked.type = expectedPayload then
        let payloadTyping : HasType context payload expectedPayload := by
          simpa [payloadMatches] using payloadChecked.typing
        pure ⟨.existsT theory payloadType,
          .pack satisfaction payloadTyping⟩
      else
        none

  | @Tm.«open» _ symbols relations theory payloadType result package body =>
      do
        let packageChecked ← check context package
        let expectedPackage : Ty scope := .existsT theory payloadType
        if packageMatches : packageChecked.type = expectedPackage then
          let packageTyping : HasType context package expectedPackage := by
            simpa [packageMatches] using packageChecked.typing
          let bodyChecked ← check
            ((context.extendTheory theory).extendTerm payloadType) body
          let expectedBody :=
            (result.rename (Rename.weakenStatic symbols relations)).weaken
          if bodyMatches : bodyChecked.type = expectedBody then
            let bodyTyping : HasType
                ((context.extendTheory theory).extendTerm payloadType) body
                expectedBody := by
              simpa [bodyMatches] using bodyChecked.typing
            pure ⟨result, .«open» packageTyping bodyTyping⟩
          else
            none
        else
          none

/-- The type-only public projection of the proof-producing checker. -/
def synth {scope : Sig} (context : Ctx scope) (term : Tm scope) :
    Option (Ty scope) :=
  (check context term).map Checked.type

/-- Every successful checker result carries its declarative typing proof. -/
theorem check_sound {scope : Sig} {context : Ctx scope} {term : Tm scope}
    {checked : Checked context term}
    (_accepted : check context term = some checked) :
    Nonempty (HasType context term checked.type) :=
  ⟨checked.typing⟩

end Tm
end ManySortedFC
