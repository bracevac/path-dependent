import Coercions.ManySortedFC.TermTyping
import Coercions.ManySortedFC.TheoryModelChecker

/-!
# Structural checker for capture-predictive many-sorted FC terms

The checker follows the annotated term syntax and synthesizes both the exact
returned type and an upper bound on capabilities used immediately.  Every
independently synthesized type, capture, and certificate endpoint is compared
by decidable equality.  Logical certificates, structural adapters, and local
theory models are delegated to their proof-producing structural checkers.

Applications, static applications, existential opening, and adaptation have
explicit ANF value boundaries.  This makes their capture equations local:
invocation charges retained outer captures, while sequencing combines the
right-hand side prediction with the discharged body prediction.
-/

namespace ManySortedFC
namespace Tm

/-- A successful value check together with its declarative witness. -/
structure ValueChecked {scope : Sig} (term : Tm scope) : Type where
  typing : IsValue term

/-- Check the call-by-value side conditions used by the ANF typing rules.

Static abstractions and packages disappear or expose their payload at runtime,
so their contained term must itself already be a value.  Capture-use widening
is not a value constructor: it remains an explicit computation annotation. -/
def checkValue {scope : Sig} : (term : Tm scope) ->
    Option (ValueChecked term)
  | .var _ => some ⟨.var⟩
  | .unit => some ⟨.unit⟩
  | .lam _ _ _ _ _ => some ⟨.lam⟩
  | .app _ _ => none
  | .let' _ _ _ _ _ => none
  | .adapt term _ => do
      let checked ← checkValue term
      pure ⟨.adapt checked.typing⟩
  | .slam _ _ body _ => do
      let checked ← checkValue body
      pure ⟨.slam checked.typing⟩
  | .sapp _ _ _ _ => none
  | .pack _ _ _ _ _ payload _ => do
      let checked ← checkValue payload
      pure ⟨.pack checked.typing⟩
  | .«open» _ _ _ _ _ _ _ => none
  | .use _ _ => none

/-- The capture and type synthesized for an annotated term, together with its
declarative typing derivation. -/
structure Checked {scope : Sig} (context : Ctx scope) (term : Tm scope) where
  use : Capture scope
  type : Ty scope
  typing : HasType context term use type

/-- Check one certificate against exact capture-inclusion endpoints. -/
def checkCaptureInclusion {scope : Sig} (context : Ctx scope)
    (evidence : Evidence (.inclusion .capture) scope)
  (source target : Capture scope) :
    Option (Evidence.Proves context evidence
      (.inclusion (.capture source) (.capture target))) := do
  let checked ← Evidence.check context evidence
  let ⟨proposition, typing⟩ := checked
  match proposition with
  | .inclusion (.capture actualSource) (.capture actualTarget) =>
      if sourceMatches : actualSource = source then
        if targetMatches : actualTarget = target then
          let typing : Evidence.Proves context evidence
              (.inclusion (.capture source) (.capture target)) := by
            simpa [sourceMatches, targetMatches] using typing
          pure typing
        else
          none
      else
        none

/-- Structurally synthesize the exact capture prediction and returned type. -/
def check {scope : Sig} (context : Ctx scope) :
    (term : Tm scope) -> Option (Checked context term)
  | .var index =>
      some ⟨.empty, Ty.precise index (context.lookup index).termType,
        .var index⟩

  | .unit =>
      some ⟨.empty, .one, .unit⟩

  | .lam domain codomain closure body captures => do
      let bodyContext := context.extendTerm domain
      let bodyChecked ← check bodyContext body
      if bodyMatches : bodyChecked.type = codomain.weaken then
        let bodyTyping : HasType bodyContext body bodyChecked.use
            codomain.weaken := by
          simpa [bodyMatches] using bodyChecked.typing
        let capturesTyping ← checkCaptureInclusion bodyContext captures
          bodyChecked.use (.union closure.weaken (.singleton .here))
        pure ⟨.empty, .capturing closure (.arr domain codomain),
          .lam bodyTyping capturesTyping⟩
      else
        none

  | .app function argument => do
      let functionValue ← checkValue function
      let argumentValue ← checkValue argument
      let functionChecked ← check context function
      if functionPure : functionChecked.use = .empty then
        let functionTyping : HasType context function .empty
            functionChecked.type := by
          simpa [functionPure] using functionChecked.typing
        match functionShape : functionChecked.type.stripCapture with
        | .arr domain codomain => do
            let argumentChecked ← check context argument
            if argumentPure : argumentChecked.use = .empty then
              if argumentMatches : argumentChecked.type = domain then
                let argumentTyping : HasType context argument .empty
                    domain := by
                  simpa [argumentPure, argumentMatches] using
                    argumentChecked.typing
                pure ⟨
                  .union functionChecked.type.outerCapture
                    domain.outerCapture,
                  codomain,
                  .app functionValue.typing argumentValue.typing
                    functionTyping functionShape argumentTyping⟩
              else
                none
            else
              none
        | _ => none
      else
        none

  | .let' result bodyOuterUse rhs body discharge => do
      let rhsChecked ← check context rhs
      let bodyContext := context.extendTerm rhsChecked.type
      let bodyChecked ← check bodyContext body
      if bodyMatches : bodyChecked.type = result.weaken then
        let bodyTyping : HasType bodyContext body bodyChecked.use
            result.weaken := by
          simpa [bodyMatches] using bodyChecked.typing
        let dischargeTyping ← checkCaptureInclusion bodyContext discharge
          bodyChecked.use bodyOuterUse.weaken
        pure ⟨.union rhsChecked.use bodyOuterUse, result,
          .let' rhsChecked.typing bodyTyping dischargeTyping⟩
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
        pure ⟨termChecked.use, adapterChecked.target,
          .adapt termValue.typing termChecked.typing adapterTyping⟩
      else
        none

  | @Tm.slam _ symbols relations theory closure body captures => do
      let bodyValue ← checkValue body
      let bodyContext := context.extendTheory theory
      let bodyChecked ← check bodyContext body
      if bodyPure : bodyChecked.use = .empty then
        let bodyTyping : HasType bodyContext body .empty
            bodyChecked.type := by
          simpa [bodyPure] using bodyChecked.typing
        let capturesTyping ← checkCaptureInclusion bodyContext captures
          bodyChecked.type.outerCapture
          (closure.rename (Rename.weakenStatic symbols relations))
        pure ⟨.empty,
          .capturing closure (.forallT theory bodyChecked.type),
          .slam bodyValue.typing bodyTyping capturesTyping⟩
      else
        none

  | @Tm.sapp _ symbols relations theory function symbolArguments
      evidenceArguments => do
      let functionValue ← checkValue function
      let functionChecked ← check context function
      if functionPure : functionChecked.use = .empty then
        let functionTyping : HasType context function .empty
            functionChecked.type := by
          simpa [functionPure] using functionChecked.typing
        match functionShape : functionChecked.type.stripCapture with
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
                  let satisfaction ← Theory.checkSatisfaction context
                    symbolArguments theory evidenceArguments
                  pure ⟨functionChecked.type.outerCapture,
                    bodyType.instantiateStatic symbolArguments,
                    .sapp functionValue.typing functionTyping functionShape
                      satisfaction⟩
            else
              none
        | _ => none
      else
        none

  | .pack theory payloadType closure symbolArguments evidenceArguments
      payload captures => do
      let satisfaction ← Theory.checkSatisfaction context
        symbolArguments theory evidenceArguments
      let payloadValue ← checkValue payload
      let payloadChecked ← check context payload
      let expectedPayload := payloadType.instantiateStatic symbolArguments
      if payloadPure : payloadChecked.use = .empty then
        if payloadMatches : payloadChecked.type = expectedPayload then
          let payloadTyping : HasType context payload .empty
              expectedPayload := by
            simpa [payloadPure, payloadMatches] using payloadChecked.typing
          let capturesTyping ← checkCaptureInclusion context captures
            expectedPayload.outerCapture closure
          pure ⟨.empty, .capturing closure (.existsT theory payloadType),
            .pack satisfaction payloadValue.typing payloadTyping
              capturesTyping⟩
        else
          none
      else
        none

  | @Tm.«open» _ symbols relations theory payloadType result bodyOuterUse
      package body discharge => do
      let packageValue ← checkValue package
      let packageChecked ← check context package
      if packagePure : packageChecked.use = .empty then
        let packageTyping : HasType context package .empty
            packageChecked.type := by
          simpa [packagePure] using packageChecked.typing
        let expectedPackage : Ty scope := .existsT theory payloadType
        if packageMatches : packageChecked.type.stripCapture =
            expectedPackage then
          let bodyContext :=
            (context.extendTheory theory).extendTerm payloadType
          let bodyChecked ← check bodyContext body
          let expectedBody :=
            (result.rename (Rename.weakenStatic symbols relations)).weaken
          if bodyMatches : bodyChecked.type = expectedBody then
            let bodyTyping : HasType bodyContext body bodyChecked.use
                expectedBody := by
              simpa [bodyMatches] using bodyChecked.typing
            let weakenedOuter :=
              (bodyOuterUse.rename
                (Rename.weakenStatic symbols relations)).weaken
            let dischargeBound :=
              Capture.union weakenedOuter (.singleton .here)
            let dischargeTyping ← checkCaptureInclusion bodyContext
              discharge bodyChecked.use dischargeBound
            pure ⟨.union packageChecked.type.outerCapture bodyOuterUse,
              result,
              .«open» packageValue.typing packageTyping packageMatches
                bodyTyping dischargeTyping⟩
          else
            none
        else
          none
      else
        none

  | .use term inclusion => do
      let termChecked ← check context term
      let inclusionChecked ← Evidence.check context inclusion
      let ⟨proposition, typing⟩ := inclusionChecked
      match proposition with
      | .inclusion (.capture actualSource) (.capture targetUse) =>
          if sourceMatches : actualSource = termChecked.use then
            let inclusionTyping : Evidence.Proves context inclusion
                (.inclusion (.capture termChecked.use)
                  (.capture targetUse)) := by
              simpa [sourceMatches] using typing
            pure ⟨targetUse, termChecked.type,
              .use termChecked.typing inclusionTyping⟩
          else
            none

/-- Public projection of both synthesized indices. -/
def synth {scope : Sig} (context : Ctx scope) (term : Tm scope) :
    Option (Capture scope × Ty scope) :=
  (check context term).map fun checked => (checked.use, checked.type)

/-- Compatibility projection for clients interested only in the returned
type.  Capture-sensitive clients should use `synth`. -/
def synthType {scope : Sig} (context : Ctx scope) (term : Tm scope) :
    Option (Ty scope) :=
  (check context term).map Checked.type

/-- Every successful checker result carries its declarative typing proof. -/
theorem check_sound {scope : Sig} {context : Ctx scope} {term : Tm scope}
    {checked : Checked context term}
    (_accepted : check context term = some checked) :
    Nonempty (HasType context term checked.use checked.type) :=
  ⟨checked.typing⟩

end Tm
end ManySortedFC
