import Coercions.Translation.ManySorted.CheckedFrontend.Evidence

/-!
# Syntax-directed checked elaboration

The checker synthesizes the source use and type of every raw node and returns
the corresponding intrinsic `DOTCapture.ModalIntersections` derivation.
Annotations are compared literally.  Logical premises are accepted only when
their supplied first-order certificates check.
-/

namespace DOTCaptureToManySortedFC.CheckedFrontend

open DOTCapture.ModalIntersections

/-- Front-end errors distinguish syntax/type mismatches, bad certificates,
and forms outside the executable fragment. -/
inductive Error : Type where
  | unsupported (feature : UnsupportedFeature)
  | typeMismatch
  | expectedFunction
  | expectedUniversal
  | expectedExistential
  | nonPlainBinder
  | invalidInclusion
  | invalidInterval
  | invalidAdapter
  | invalidModeCoverage
  | invalidSeparationCoverage
deriving DecidableEq, Repr

/-- A raw value elaborated to cumulative source syntax and source typing. -/
structure CheckedValue {scope : Source.Sig}
    (environment : Source.TypingEnv scope) where
  value : DOTCapture.ModalIntersections.Value scope
  type : Source.Ty scope
  typing : DOTCapture.ModalIntersections.Value.HasType environment value type

/-- A raw computation elaborated to cumulative source syntax and source
typing, including its synthesized immediate-use capture. -/
structure CheckedTerm {scope : Source.Sig}
    (environment : Source.TypingEnv scope) where
  term : DOTCapture.ModalIntersections.Term scope
  use : Source.Capture scope
  type : Source.Ty scope
  typing : DOTCapture.ModalIntersections.Term.HasType environment term use type

private def requireOption {alpha : Type} (error : Error) :
    Option alpha -> Except Error alpha
  | some value => .ok value
  | none => .error error

/-- Decide the source language's syntactic non-object binder condition. -/
private def checkPlain {scope : Source.Sig} (type : Source.Ty scope) :
    Option (PLift (Plain type)) :=
  match stripped : type.stripCapture with
  | .object _ => none
  | .top => some ⟨by unfold Plain; rw [stripped]; trivial⟩
  | .bot => some ⟨by unfold Plain; rw [stripped]; trivial⟩
  | .one => some ⟨by unfold Plain; rw [stripped]; trivial⟩
  | .ref _ => some ⟨by unfold Plain; rw [stripped]; trivial⟩
  | .arr _ _ => some ⟨by unfold Plain; rw [stripped]; trivial⟩
  | .objectArrow _ _ => some ⟨by unfold Plain; rw [stripped]; trivial⟩
  | .capturing _ _ => some ⟨by unfold Plain; rw [stripped]; trivial⟩
  | .forallI _ _ => some ⟨by unfold Plain; rw [stripped]; trivial⟩
  | .existsI _ _ => some ⟨by unfold Plain; rw [stripped]; trivial⟩
  | .modal _ _ => some ⟨by unfold Plain; rw [stripped]; trivial⟩

mutual

/-- Elaborate one raw value. -/
def checkValue {scope : Source.Sig} (environment : Source.TypingEnv scope) :
    RawValue scope -> Except Error (CheckedValue environment)
  | .var name =>
      .ok {
        value := .var name
        type := environment.bindings.lookupTerm name
        typing := .declaredVar }
  | .unit =>
      .ok { value := .unit, type := .one, typing := .unit }
  | .lam domain codomain closure captures body => do
      let domainPlain <- requireOption .nonPlainBinder (checkPlain domain)
      let bodyChecked <- checkTerm (environment.extendTerm domain) body
      let expectedBodyType := codomain.weaken (kind := .term)
      if bodyTypeMatches : bodyChecked.type = expectedBodyType then
        let expectedUse : Source.Capture (scope ▹ .term) :=
          .union (closure.weaken (kind := .term))
            (.singleton (.var .here))
        let captureProof <- requireOption .invalidInclusion
          (Evidence.check (environment.extendTerm domain).bindings
            (.capture bodyChecked.use) (.capture expectedUse) captures)
        let bodyTyping : DOTCapture.ModalIntersections.Term.HasType
            (environment.extendTerm domain) bodyChecked.term bodyChecked.use
            expectedBodyType := bodyTypeMatches ▸ bodyChecked.typing
        .ok {
          value := .lam domain codomain bodyChecked.term
          type := .capturing closure (.arr domain codomain)
          typing := .lam domainPlain.down bodyTyping captureProof }
      else
        .error .typeMismatch
  | @RawValue.staticLam _ sort interval closure captures body => do
      let bodyChecked <- checkValue (environment.extendStatic interval) body
      let expectedCapture := closure.weaken (kind := .static sort)
      let captureProof <- requireOption .invalidInclusion
        (Evidence.check (environment.extendStatic interval).bindings
          (.capture bodyChecked.type.outerCapture)
          (.capture expectedCapture) captures)
      .ok {
        value := .staticLam interval bodyChecked.value
        type := .capturing closure (.forallI interval bodyChecked.type)
        typing := .staticLam bodyChecked.typing captureProof }
  | @RawValue.pack _ _sort interval payloadType witness closure satisfaction
      captures payload => do
      let satisfactionProof <- requireOption .invalidInterval
        (Evidence.checkInterval environment.bindings witness interval
          satisfaction)
      let payloadChecked <- checkValue environment payload
      let expectedPayloadType := payloadType.instantiateStatic witness
      if payloadTypeMatches : payloadChecked.type = expectedPayloadType then
        let payloadTyping : DOTCapture.ModalIntersections.Value.HasType
            environment payloadChecked.value expectedPayloadType :=
          payloadTypeMatches ▸ payloadChecked.typing
        let captureProof <- requireOption .invalidInclusion
          (Evidence.check environment.bindings
            (.capture expectedPayloadType.outerCapture) (.capture closure)
            captures)
        .ok {
          value := .pack interval payloadType witness payloadChecked.value
          type := .capturing closure (.existsI interval payloadType)
          typing := .pack satisfactionProof payloadTyping captureProof }
      else
        .error .typeMismatch
  | .lock requirements result closure captures body => do
      let bodyChecked <- checkTerm (environment.push requirements) body
      if bodyTypeMatches : bodyChecked.type = result then
        let bodyTyping : DOTCapture.ModalIntersections.Term.HasType
            (environment.push requirements) bodyChecked.term bodyChecked.use
            result := bodyTypeMatches ▸ bodyChecked.typing
        let captureProof <- requireOption .invalidInclusion
          (Evidence.check environment.bindings (.capture bodyChecked.use)
            (.capture closure) captures)
        .ok {
          value := .lock requirements result closure bodyChecked.term
          type := .capturing closure (.modal requirements result)
          typing := .lock bodyTyping captureProof }
      else
        .error .typeMismatch
  | .adapt target adapter value => do
      let valueChecked <- checkValue environment value
      let adapterProof <- requireOption .invalidAdapter
        (Evidence.checkAdapter environment valueChecked.type target adapter)
      .ok {
        value := valueChecked.value
        type := target
        typing := .adapt valueChecked.typing adapterProof }
  | .unsupported feature => .error (.unsupported feature)

/-- Elaborate one raw computation. -/
def checkTerm {scope : Source.Sig} (environment : Source.TypingEnv scope) :
    RawTerm scope -> Except Error (CheckedTerm environment)
  | .ret value => do
      let valueChecked <- checkValue environment value
      .ok {
        term := .ret valueChecked.value
        use := .empty
        type := valueChecked.type
        typing := .ret valueChecked.typing }
  | .app function argument => do
      let functionChecked <- checkTerm environment function
      let argumentChecked <- checkTerm environment argument
      match functionShape : functionChecked.type.stripCapture with
      | .arr domain codomain =>
          if argumentTypeMatches : argumentChecked.type = domain then
            let domainPlain <- requireOption .nonPlainBinder (checkPlain domain)
            let argumentTyping : DOTCapture.ModalIntersections.Term.HasType
                environment argumentChecked.term argumentChecked.use domain :=
              argumentTypeMatches ▸ argumentChecked.typing
            .ok {
              term := .app functionChecked.term argumentChecked.term
              use := functionChecked.use.seq
                (argumentChecked.use.seq
                  (.union functionChecked.type.outerCapture
                    domain.outerCapture))
              type := codomain
              typing := .app functionChecked.typing functionShape domainPlain.down
                argumentTyping }
          else
            .error .typeMismatch
      | _ => .error .expectedFunction
  | .letPlain bound result bodyOuterUse discharge rhs body => do
      let boundPlain <- requireOption .nonPlainBinder (checkPlain bound)
      let rhsChecked <- checkTerm environment rhs
      if rhsTypeMatches : rhsChecked.type = bound then
        let rhsTyping : DOTCapture.ModalIntersections.Term.HasType environment
            rhsChecked.term rhsChecked.use bound :=
          rhsTypeMatches ▸ rhsChecked.typing
        let bodyChecked <- checkTerm (environment.extendTerm bound) body
        let expectedBodyType := result.weaken (kind := .term)
        if bodyTypeMatches : bodyChecked.type = expectedBodyType then
          let expectedBodyUse := bodyOuterUse.weaken (kind := .term)
          let dischargeProof <- requireOption .invalidInclusion
            (Evidence.check (environment.extendTerm bound).bindings
              (.capture bodyChecked.use) (.capture expectedBodyUse) discharge)
          let bodyTyping : DOTCapture.ModalIntersections.Term.HasType
              (environment.extendTerm bound) bodyChecked.term bodyChecked.use
              expectedBodyType := bodyTypeMatches ▸ bodyChecked.typing
          .ok {
            term := .let' result rhsChecked.term bodyChecked.term
            use := .union rhsChecked.use bodyOuterUse
            type := result
            typing := .letPlain boundPlain.down rhsTyping bodyTyping
              dischargeProof }
        else
          .error .typeMismatch
      else
        .error .typeMismatch
  | @RawTerm.staticApp _ _sort interval bodyType argument satisfaction
      function => do
      let functionChecked <- checkTerm environment function
      let expectedShape : Source.Ty scope := .forallI interval bodyType
      if functionShape : functionChecked.type.stripCapture = expectedShape then
        let satisfactionProof <- requireOption .invalidInterval
          (Evidence.checkInterval environment.bindings argument interval
            satisfaction)
        .ok {
          term := .staticApp interval functionChecked.term argument
          use := functionChecked.use.seq functionChecked.type.outerCapture
          type := bodyType.instantiateStatic argument
          typing := .staticApp functionChecked.typing functionShape
            satisfactionProof }
      else
        .error .expectedUniversal
  | @RawTerm.openPackage _ sort interval payloadType result bodyOuterUse
      discharge package body => do
      let packageChecked <- checkTerm environment package
      let expectedShape : Source.Ty scope := .existsI interval payloadType
      if packageShape : packageChecked.type.stripCapture = expectedShape then
        let bodyEnvironment := environment.extendPayload interval payloadType
        let bodyChecked <- checkTerm bodyEnvironment body
        let expectedBodyType :=
          (result.weaken (kind := .static sort)).weaken (kind := .term)
        if bodyTypeMatches : bodyChecked.type = expectedBodyType then
          let expectedBodyUse : Source.Capture (Source.PayloadScope scope sort) :=
            .union
              ((bodyOuterUse.weaken (kind := .static sort)).weaken
                (kind := .term))
              (.singleton (.var .here))
          let dischargeProof <- requireOption .invalidInclusion
            (Evidence.check bodyEnvironment.bindings
              (.capture bodyChecked.use) (.capture expectedBodyUse) discharge)
          let bodyTyping : DOTCapture.ModalIntersections.Term.HasType
              bodyEnvironment bodyChecked.term bodyChecked.use
              expectedBodyType := bodyTypeMatches ▸ bodyChecked.typing
          .ok {
            term := .«open» interval payloadType result packageChecked.term
              bodyChecked.term
            use := packageChecked.use.seq
              (.union packageChecked.type.outerCapture bodyOuterUse)
            type := result
            typing := .«open» packageChecked.typing packageShape bodyTyping
              dischargeProof }
        else
          .error .typeMismatch
      else
        .error .expectedExistential
  | .unlock requirements result modesCovered separationsCovered scrutinee => do
      let scrutineeChecked <- checkTerm environment scrutinee
      let expectedShape : Source.Ty scope := .modal requirements result
      if scrutineeShape : scrutineeChecked.type.stripCapture = expectedShape then
        match requirementShape : requirements with
        | .mk separation modeContext =>
            let modeProof <- requireOption .invalidModeCoverage
              (Evidence.checkModeCoverage environment.bindings
                environment.locks modeContext modesCovered)
            let separationProof <- requireOption .invalidSeparationCoverage
              (Evidence.checkSeparationCoverage environment.bindings
                environment.locks separation separationsCovered)
            let satisfactionAtShape : Satisfies environment.bindings
                environment.locks (.mk separation modeContext) :=
              .mk modeProof separationProof
            let satisfaction : Satisfies environment.bindings
                environment.locks requirements :=
              requirementShape.symm ▸ satisfactionAtShape
            .ok {
              term := .unlock requirements scrutineeChecked.term
              use := scrutineeChecked.use.seq
                scrutineeChecked.type.outerCapture
              type := result
              typing := .unlock scrutineeChecked.typing scrutineeShape
                satisfaction }
      else
        .error .typeMismatch
  | .use targetUse evidence term => do
      let termChecked <- checkTerm environment term
      let proof <- requireOption .invalidInclusion
        (Evidence.check environment.bindings (.capture termChecked.use)
          (.capture targetUse) evidence)
      .ok {
        term := termChecked.term
        use := targetUse
        type := termChecked.type
        typing := .use termChecked.typing proof }
  | .unsupported feature => .error (.unsupported feature)

end

/-- Successful value checking contains a source typing derivation. -/
def CheckedValue.sound {scope : Source.Sig}
    {environment : Source.TypingEnv scope}
    (checked : CheckedValue environment) :
    DOTCapture.ModalIntersections.Value.HasType environment checked.value
      checked.type :=
  checked.typing

/-- Successful term checking contains a source typing derivation. -/
def CheckedTerm.sound {scope : Source.Sig}
    {environment : Source.TypingEnv scope}
    (checked : CheckedTerm environment) :
    DOTCapture.ModalIntersections.Term.HasType environment checked.term
      checked.use checked.type :=
  checked.typing

/-- Structural elaboration is deterministic, including the returned proof
term: two successful equations for the same checker call have equal output. -/
theorem checkTerm_deterministic {scope : Source.Sig}
    (environment : Source.TypingEnv scope) (raw : RawTerm scope)
    (first second : CheckedTerm environment)
    (firstAccepted : checkTerm environment raw = .ok first)
    (secondAccepted : checkTerm environment raw = .ok second) :
    first = second := by
  rw [firstAccepted] at secondAccepted
  exact Except.ok.inj secondAccepted

end DOTCaptureToManySortedFC.CheckedFrontend
