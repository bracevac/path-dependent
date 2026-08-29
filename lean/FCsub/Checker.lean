import FCsub.Typing

/-!
# Executable structural checker for FCsub

The checker validates fully annotated target syntax.  It never searches for
subtyping evidence: every directed step and every telescope adaptation must
already occur in the input certificate.
-/

namespace FCsub

abbrev Endpoints (scope : Sig) := Ty scope × Ty scope

structure EqChecked {scope : Sig} (context : Ctx scope)
    (evidence : EqCo scope) where
  source : Ty scope
  target : Ty scope
  typing : EqCo.HasType context evidence source target

structure LeChecked {scope : Sig} (context : Ctx scope)
    (evidence : LeCo scope) where
  source : Ty scope
  target : Ty scope
  typing : LeCo.HasType context evidence source target

structure MorChecked {scope : Sig} (context : Ctx scope)
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints) where
  source : Telescope scope sourceNames sourceConstraints
  target : Telescope scope targetNames targetConstraints
  typing : TelMor.HasType context morphism source target

structure TmChecked {scope : Sig} (context : Ctx scope)
    (term : Tm scope) where
  type : Ty scope
  typing : Tm.HasType context term type

structure ValueChecked {scope : Sig} (term : Tm scope) : Type where
  typing : Tm.IsValue term

/-- A successful `Option` computation together with its defining equation.
Factoring this dependent match out keeps all nonescape branches uniform. -/
structure OptionChecked {α : Type} (value : Option α) where
  output : α
  equation : value = some output

def checkSomeCore {α : Type} (value : Option α) :
    Option (OptionChecked value) :=
  match value with
  | none => none
  | some output => some ⟨output, rfl⟩

def checkEqCore {scope : Sig} (context : Ctx scope)
    (evidence : EqCo scope) : Option (EqChecked context evidence) :=
  match evidence with
  | .var index =>
      match binding : context.lookup index with
      | .equality left right =>
          some ⟨left, right, EqCo.HasType.var binding⟩
  | .refl type => some ⟨type, type, .refl type⟩
  | .symm inner => do
      let checked ← checkEqCore context inner
      pure ⟨checked.target, checked.source, .symm checked.typing⟩
  | .trans first second => do
      let firstChecked ← checkEqCore context first
      let secondChecked ← checkEqCore context second
      if middle : firstChecked.target = secondChecked.source then
        let secondTyping : EqCo.HasType context second firstChecked.target
            secondChecked.target := by
          simpa [middle] using secondChecked.typing
        pure ⟨firstChecked.source, secondChecked.target,
          .trans firstChecked.typing secondTyping⟩
      else
        none
  | .unfoldRec bodies index =>
      if guarded : bodies.headGuarded then
        some ⟨.recProj bodies index, bodies.unfoldAt index,
          EqCo.HasType.unfoldRec guarded⟩
      else
        none

mutual

def checkLeCore {scope : Sig} (context : Ctx scope)
    (evidence : LeCo scope) : Option (LeChecked context evidence) :=
  match evidence with
  | .var index =>
      match binding : context.lookup index with
      | .inclusion source target =>
          some ⟨source, target, LeCo.HasType.var binding⟩
  | .refl type => some ⟨type, type, .refl type⟩
  | .trans first second => do
      let firstChecked ← checkLeCore context first
      let secondChecked ← checkLeCore context second
      if middle : firstChecked.target = secondChecked.source then
        let secondTyping : LeCo.HasType context second firstChecked.target
            secondChecked.target := by
          simpa [middle] using secondChecked.typing
        pure ⟨firstChecked.source, secondChecked.target,
          .trans firstChecked.typing secondTyping⟩
      else
        none
  | .top source => some ⟨source, .top, .top source⟩
  | .bot target => some ⟨.bot, target, .bot target⟩
  | .eqToLe equality => do
      let checked ← checkEqCore context equality
      pure ⟨checked.source, checked.target, .eqToLe checked.typing⟩
  | .arr domain codomain => do
      let domainChecked ← checkLeCore context domain
      let codomainChecked ←
        checkLeCore (context.extendTerm domainChecked.source) codomain
      pure ⟨.arr domainChecked.target codomainChecked.source,
        .arr domainChecked.source codomainChecked.target,
        .arr domainChecked.typing codomainChecked.typing⟩
  | .existsT adaptation sourcePayload targetPayload payload => do
      let adaptationChecked ← checkMorCore context adaptation
      let payloadChecked ← checkLeCore
        (context.extendTelescope adaptationChecked.source) payload
      if sourceMatches : payloadChecked.source = sourcePayload then
        if targetMatches : payloadChecked.target = adaptation.pull targetPayload then
          let payloadTyping : LeCo.HasType
              (context.extendTelescope adaptationChecked.source) payload
              sourcePayload (adaptation.pull targetPayload) := by
            simpa [sourceMatches, targetMatches] using payloadChecked.typing
          pure ⟨.existsT adaptationChecked.source sourcePayload,
            .existsT adaptationChecked.target targetPayload,
            .existsT adaptationChecked.typing payloadTyping⟩
        else none
      else none
  | .forallT adaptation sourceBody targetBody body => do
      let adaptationChecked ← checkMorCore context adaptation
      let bodyChecked ← checkLeCore
        (context.extendTelescope adaptationChecked.source) body
      if sourceMatches : bodyChecked.source = adaptation.pull sourceBody then
        if targetMatches : bodyChecked.target = targetBody then
          let bodyTyping : LeCo.HasType
              (context.extendTelescope adaptationChecked.source) body
              (adaptation.pull sourceBody) targetBody := by
            simpa [sourceMatches, targetMatches] using bodyChecked.typing
          pure ⟨.forallT adaptationChecked.target sourceBody,
            .forallT adaptationChecked.source targetBody,
            .forallT adaptationChecked.typing bodyTyping⟩
        else none
      else none

def checkArgsCore {scope : Sig} (context : Ctx scope)
    {names constraints : Nat}
    (telescope : Telescope scope names constraints)
    (witnesses : TypeArgs scope names) (arguments : LeArgs scope constraints) :
    Option (LeArgs.HasType context telescope witnesses arguments) :=
  match telescope, arguments with
  | .nil, .nil => some .nil
  | .snoc initial (.inclusion lower upper), .snoc previous evidence => do
      let previousTyping ← checkArgsCore context initial witnesses previous
      let evidenceChecked ← checkLeCore context evidence
      if sourceMatches : evidenceChecked.source =
          lower.instantiateNames witnesses then
        if targetMatches : evidenceChecked.target =
            upper.instantiateNames witnesses then
          let evidenceTyping : LeCo.HasType context evidence
              (lower.instantiateNames witnesses)
              (upper.instantiateNames witnesses) := by
            simpa [sourceMatches, targetMatches] using evidenceChecked.typing
          pure (.snoc previousTyping evidenceTyping)
        else none
      else none

def checkMorCore {scope : Sig} (context : Ctx scope)
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints) : Option (MorChecked context morphism) :=
  match morphism with
  | .refl telescope => some ⟨telescope, telescope, .refl telescope⟩
  | .map source target names evidence => do
      let argumentsTyping ← checkArgsCore
        (context.extendTelescope source)
        (target.rename
          (Rename.weakenStatic sourceNames sourceConstraints))
        names evidence
      pure ⟨source, target, .map argumentsTyping⟩
  | .trans first second => do
      let firstChecked ← checkMorCore context first
      let secondChecked ← checkMorCore context second
      if middle : firstChecked.target = secondChecked.source then
        let secondTyping : TelMor.HasType context second firstChecked.target
            secondChecked.target := by
          simpa [middle] using secondChecked.typing
        pure ⟨firstChecked.source, secondChecked.target,
          .trans firstChecked.typing secondTyping⟩
      else none

end


def checkValueCore {scope : Sig} : (term : Tm scope) →
    Option (ValueChecked term)
  | .unit => some ⟨.unit⟩
  | .var _ => none
  | .lam _ _ => some ⟨.lam⟩
  | .app _ _ => none
  | .let' _ _ => none
  | .cast term _ => do
      let value ← checkValueCore term
      pure ⟨.cast value.typing⟩
  | .pack _ _ _ _ payload => do
      let value ← checkValueCore payload
      pure ⟨.pack value.typing⟩
  | .«open» _ _ _ _ => none
  | .slam _ body => do
      let value ← checkValueCore body
      pure ⟨.slam value.typing⟩
  | .sapp _ _ _ _ => none
  | .newtype _ _ => none
  | .foldRec _ _ term => do
      let value ← checkValueCore term
      pure ⟨Tm.IsValue.foldRec value.typing⟩
  | .unfoldRec _ _ _ => none

def checkTmCore {scope : Sig} (context : Ctx scope)
    (term : Tm scope) : Option (TmChecked context term) :=
  match term with
  | .unit => some ⟨.one, .unit⟩
  | .var index =>
      match binding : context.lookup index with
      | .term type => some ⟨type, Tm.HasType.var binding⟩
  | .lam domain body => do
      let bodyChecked ← checkTmCore (context.extendTerm domain) body
      pure ⟨.arr domain bodyChecked.type, .lam bodyChecked.typing⟩
  | .app function argument => do
      let functionChecked ← checkTmCore context function
      match functionType : functionChecked.type with
      | .arr domain codomain => do
          let argumentChecked ← checkTmCore context argument
          if sameDomain : argumentChecked.type = domain then
            let nonescape ← checkSomeCore codomain.strengthenTerm
            let functionTyping : Tm.HasType context function
                (.arr domain codomain) := by
              simpa [functionType] using functionChecked.typing
            let argumentTyping : Tm.HasType context argument domain := by
              simpa [sameDomain] using argumentChecked.typing
            pure ⟨nonescape.output,
              .app functionTyping argumentTyping nonescape.equation⟩
          else none
      | _ => none
  | .let' rhs body => do
      let rhsChecked ← checkTmCore context rhs
      let bodyChecked ← checkTmCore
        (context.extendTerm rhsChecked.type) body
      let nonescape ← checkSomeCore bodyChecked.type.strengthenTerm
      pure ⟨nonescape.output,
        .let' rhsChecked.typing bodyChecked.typing nonescape.equation⟩
  | .cast inner evidence => do
      let termChecked ← checkTmCore context inner
      let evidenceChecked ← checkLeCore context evidence
      if sameSource : termChecked.type = evidenceChecked.source then
        let evidenceTyping : LeCo.HasType context evidence termChecked.type
            evidenceChecked.target := by
          simpa [sameSource] using evidenceChecked.typing
        pure ⟨evidenceChecked.target,
          .cast termChecked.typing evidenceTyping⟩
      else none
  | .pack telescope payloadType witnesses evidence payload => do
      let argumentsTyping ←
        checkArgsCore context telescope witnesses evidence
      let payloadChecked ← checkTmCore context payload
      let expected := payloadType.instantiateStatic witnesses
      if samePayload : payloadChecked.type = expected then
        let payloadTyping : Tm.HasType context payload expected := by
          simpa [samePayload] using payloadChecked.typing
        pure ⟨.existsT telescope payloadType,
          .pack argumentsTyping payloadTyping⟩
      else none
  | .«open» telescope payloadType package body => do
      let packageChecked ← checkTmCore context package
      if packageType : packageChecked.type = .existsT telescope payloadType then
        let packageTyping : Tm.HasType context package
            (.existsT telescope payloadType) := by
          simpa [packageType] using packageChecked.typing
        let bodyChecked ← checkTmCore
          (context.extendPayload telescope payloadType) body
        let nonescape ← checkSomeCore bodyChecked.type.strengthenPayload
        pure ⟨nonescape.output,
          .openT packageTyping bodyChecked.typing nonescape.equation⟩
      else none
  | .slam telescope body => do
      let bodyValue ← checkValueCore body
      let bodyChecked ← checkTmCore (context.extendTelescope telescope) body
      pure ⟨.forallT telescope bodyChecked.type,
        .slam bodyValue.typing bodyChecked.typing⟩
  | @Tm.sapp _ names constraints telescope function witnesses evidence => do
      let functionChecked ← checkTmCore context function
      match functionType : functionChecked.type with
      | @Ty.forallT _ actualNames actualConstraints actualTelescope bodyType =>
          let actual : Σ n, Σ c, Telescope scope n c :=
            ⟨actualNames, actualConstraints, actualTelescope⟩
          let expected : Σ n, Σ c, Telescope scope n c :=
            ⟨names, constraints, telescope⟩
          if same : actual = expected then
            by
              dsimp [actual, expected] at same
              cases same
              exact do
                let functionTyping : Tm.HasType context function
                    (.forallT telescope bodyType) := by
                  simpa [functionType] using functionChecked.typing
                let argumentsTyping ←
                  checkArgsCore context telescope witnesses evidence
                pure ⟨bodyType.instantiateStatic witnesses,
                  .sapp functionTyping argumentsTyping⟩
          else none
      | _ => none
  | .newtype witness body => do
      let bodyChecked ← checkTmCore (context.extendNewtype witness) body
      let nonescape ← checkSomeCore bodyChecked.type.strengthenNewtype
      pure ⟨nonescape.output,
        .newtype bodyChecked.typing nonescape.equation⟩
  | .foldRec bodies index inner =>
      if guarded : bodies.headGuarded then do
        let innerChecked ← checkTmCore context inner
        if sameType : innerChecked.type = bodies.unfoldAt index then
          let innerTyping : Tm.HasType context inner (bodies.unfoldAt index) := by
            simpa [sameType] using innerChecked.typing
          pure ⟨.recProj bodies index, .foldRec guarded innerTyping⟩
        else
          none
      else
        none
  | .unfoldRec bodies index inner =>
      if guarded : bodies.headGuarded then do
        let innerChecked ← checkTmCore context inner
        if sameType : innerChecked.type = .recProj bodies index then
          let innerTyping : Tm.HasType context inner (.recProj bodies index) := by
            simpa [sameType] using innerChecked.typing
          pure ⟨bodies.unfoldAt index, .unfoldRec guarded innerTyping⟩
        else
          none
      else
        none

/-! ## Public executable interface -/

def synthEq {scope : Sig} (context : Ctx scope) (evidence : EqCo scope) :
    Option (Endpoints scope) :=
  (checkEqCore context evidence).map fun checked =>
    (checked.source, checked.target)

def synthLe {scope : Sig} (context : Ctx scope) (evidence : LeCo scope) :
    Option (Endpoints scope) :=
  (checkLeCore context evidence).map fun checked =>
    (checked.source, checked.target)

def checkArgs {scope : Sig} (context : Ctx scope)
    {names constraints : Nat} (telescope : Telescope scope names constraints)
    (witnesses : TypeArgs scope names) (arguments : LeArgs scope constraints) :
    Bool :=
  (checkArgsCore context telescope witnesses arguments).isSome

def synthMor {scope : Sig} (context : Ctx scope)
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints) :
    Option (Telescope scope sourceNames sourceConstraints ×
      Telescope scope targetNames targetConstraints) :=
  (checkMorCore context morphism).map fun checked =>
    (checked.source, checked.target)

def synthTm {scope : Sig} (context : Ctx scope) (term : Tm scope) :
    Option (Ty scope) :=
  (checkTmCore context term).map TmChecked.type

/-! Expected-endpoint interfaces.  These are Boolean wrappers around the
proof-producing synthesis kernels, so callers never need to compare dependent
checker records themselves. -/

def checkEquality {scope : Sig} (context : Ctx scope) (evidence : EqCo scope)
    (source target : Ty scope) : Bool :=
  synthEq context evidence == some (source, target)

def checkEvidence {scope : Sig} (context : Ctx scope) (evidence : LeCo scope)
    (source target : Ty scope) : Bool :=
  synthLe context evidence == some (source, target)

def checkMorphism {scope : Sig} (context : Ctx scope)
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints)
    (source : Telescope scope sourceNames sourceConstraints)
    (target : Telescope scope targetNames targetConstraints) : Bool :=
  synthMor context morphism == some (source, target)

def checkTerm {scope : Sig} (context : Ctx scope) (term : Tm scope)
    (type : Ty scope) : Bool :=
  synthTm context term == some type

/-! ## Soundness -/

theorem synthEq_sound {scope : Sig} {context : Ctx scope}
    {evidence : EqCo scope} {source target : Ty scope}
    (checked : synthEq context evidence = some (source, target)) :
    Nonempty (EqCo.HasType context evidence source target) := by
  unfold synthEq at checked
  cases equation : checkEqCore context evidence with
  | none => simp [equation] at checked
  | some value =>
      rw [equation] at checked
      cases value with
      | mk actualSource actualTarget typing =>
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at checked
          obtain ⟨rfl, rfl⟩ := checked
          exact ⟨typing⟩

theorem synthLe_sound {scope : Sig} {context : Ctx scope}
    {evidence : LeCo scope} {source target : Ty scope}
    (checked : synthLe context evidence = some (source, target)) :
    Nonempty (LeCo.HasType context evidence source target) := by
  unfold synthLe at checked
  cases equation : checkLeCore context evidence with
  | none => simp [equation] at checked
  | some value =>
      rw [equation] at checked
      cases value with
      | mk actualSource actualTarget typing =>
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at checked
          obtain ⟨rfl, rfl⟩ := checked
          exact ⟨typing⟩

theorem checkArgs_sound {scope : Sig} {context : Ctx scope}
    {names constraints : Nat}
    {telescope : Telescope scope names constraints}
    {witnesses : TypeArgs scope names} {arguments : LeArgs scope constraints}
    (checked : checkArgs context telescope witnesses arguments = true) :
    Nonempty (LeArgs.HasType context telescope witnesses arguments) := by
  unfold checkArgs at checked
  cases equation : checkArgsCore context telescope witnesses arguments with
  | none => simp [equation] at checked
  | some typing => exact ⟨typing⟩

theorem synthMor_sound {scope : Sig} {context : Ctx scope}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    {morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints}
    {source : Telescope scope sourceNames sourceConstraints}
    {target : Telescope scope targetNames targetConstraints}
    (checked : synthMor context morphism = some (source, target)) :
    Nonempty (TelMor.HasType context morphism source target) := by
  unfold synthMor at checked
  cases equation : checkMorCore context morphism with
  | none => simp [equation] at checked
  | some value =>
      rw [equation] at checked
      cases value with
      | mk actualSource actualTarget typing =>
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at checked
          obtain ⟨rfl, rfl⟩ := checked
          exact ⟨typing⟩

theorem synthTm_sound {scope : Sig} {context : Ctx scope}
    {term : Tm scope} {type : Ty scope}
    (checked : synthTm context term = some type) :
    Nonempty (Tm.HasType context term type) := by
  unfold synthTm at checked
  cases equation : checkTmCore context term with
  | none => simp [equation] at checked
  | some value =>
      rw [equation] at checked
      cases value with
      | mk actualType typing =>
          simp only [Option.map_some, Option.some.injEq] at checked
          cases checked
          exact ⟨typing⟩

theorem checkEquality_sound {scope : Sig} {context : Ctx scope}
    {evidence : EqCo scope} {source target : Ty scope}
    (checked : checkEquality context evidence source target = true) :
    Nonempty (EqCo.HasType context evidence source target) := by
  apply synthEq_sound
  simpa [checkEquality] using checked

theorem checkEvidence_sound {scope : Sig} {context : Ctx scope}
    {evidence : LeCo scope} {source target : Ty scope}
    (checked : checkEvidence context evidence source target = true) :
    Nonempty (LeCo.HasType context evidence source target) := by
  apply synthLe_sound
  simpa [checkEvidence] using checked

theorem checkMorphism_sound {scope : Sig} {context : Ctx scope}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    {morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints}
    {source : Telescope scope sourceNames sourceConstraints}
    {target : Telescope scope targetNames targetConstraints}
    (checked : checkMorphism context morphism source target = true) :
    Nonempty (TelMor.HasType context morphism source target) := by
  apply synthMor_sound
  simpa [checkMorphism] using checked

theorem checkTerm_sound {scope : Sig} {context : Ctx scope}
    {term : Tm scope} {type : Ty scope}
    (checked : checkTerm context term type = true) :
    Nonempty (Tm.HasType context term type) := by
  apply synthTm_sound
  simpa [checkTerm] using checked

end FCsub
