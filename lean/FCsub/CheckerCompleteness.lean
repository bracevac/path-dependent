import FCsub.Checker

/-!
# Completeness of the executable FCsub checker

This module is deliberately separate from `FCsub.Checker`: the executable
kernel and its soundness proof do not depend on the larger declarative-to-
algorithmic induction below.
-/

namespace FCsub

/-! ## Equality evidence -/

private theorem checkEqCore_complete {scope : Sig} {context : Ctx scope}
    {evidence : EqCo scope} {source target : Ty scope}
    (typing : EqCo.HasType context evidence source target) :
    ∃ checked, checkEqCore context evidence = some checked ∧
      checked.source = source ∧ checked.target = target := by
  induction typing with
  | var binding =>
      unfold checkEqCore
      split
      next actualLeft actualRight lookupEq =>
        have same : Binding.equality actualLeft actualRight =
            Binding.equality _ _ := lookupEq.symm.trans binding
        cases same
        exact ⟨_, rfl, rfl, rfl⟩
  | refl type => exact ⟨⟨type, type, .refl type⟩, rfl, rfl, rfl⟩
  | symm _ induction =>
      obtain ⟨checked, core, sourceEq, targetEq⟩ := induction
      simp [checkEqCore, core, sourceEq, targetEq]
  | trans _ _ firstInduction secondInduction =>
      obtain ⟨firstChecked, firstCore, firstSource, firstTarget⟩ :=
        firstInduction
      obtain ⟨secondChecked, secondCore, secondSource, secondTarget⟩ :=
        secondInduction
      simp [checkEqCore, firstCore, secondCore, firstSource, firstTarget,
        secondSource, secondTarget]

/-! ## Directed evidence, argument lists, and telescope morphisms

These are a structural mutual recursion over the mutually inductive typing
derivations.  Each call consumes an immediate premise derivation; no raw-term
size metric or well-founded proof is involved.
-/

private abbrev LeCoreComplete {scope : Sig} (context : Ctx scope)
    (evidence : LeCo scope) (source target : Ty scope)
    (_typing : LeCo.HasType context evidence source target) : Prop :=
  ∃ checked, checkLeCore context evidence = some checked ∧
    checked.source = source ∧ checked.target = target

private abbrev ArgsCoreComplete {scope : Sig} (context : Ctx scope)
    {names constraints : Nat} (telescope : Telescope scope names constraints)
    (witnesses : TypeArgs scope names) (arguments : LeArgs scope constraints)
    (_typing : LeArgs.HasType context telescope witnesses arguments) : Prop :=
  ∃ checked, checkArgsCore context telescope witnesses arguments = some checked

private abbrev MorCoreComplete {scope : Sig} (context : Ctx scope)
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints)
    (source : Telescope scope sourceNames sourceConstraints)
    (target : Telescope scope targetNames targetConstraints)
    (_typing : TelMor.HasType context morphism source target) : Prop :=
  ∃ checked, checkMorCore context morphism = some checked ∧
    checked.source = source ∧ checked.target = target

private theorem checkLeCore_complete {scope : Sig} {context : Ctx scope}
    {evidence : LeCo scope} {source target : Ty scope}
    (typing : LeCo.HasType context evidence source target) :
    ∃ checked, checkLeCore context evidence = some checked ∧
      checked.source = source ∧ checked.target = target := by
  exact LeCo.HasType.rec
    (motive_1 := fun {scope} context evidence source target typing =>
      LeCoreComplete context evidence source target typing)
    (motive_2 := fun {scope} context {names constraints} telescope witnesses
        arguments typing =>
      ArgsCoreComplete context telescope witnesses arguments typing)
    (motive_3 := fun {scope} context
        {sourceNames sourceConstraints targetNames targetConstraints}
        morphism source target typing =>
      MorCoreComplete context morphism source target typing)
    (var := by
      intro _ context _ _ _ binding
      unfold LeCoreComplete
      unfold checkLeCore
      split
      next actualSource actualTarget lookupEq =>
        have same : Binding.inclusion actualSource actualTarget =
            Binding.inclusion _ _ := lookupEq.symm.trans binding
        cases same
        exact ⟨_, rfl, rfl, rfl⟩)
    (refl := by
      intro _ _ type
      exact ⟨⟨type, type, .refl type⟩, rfl, rfl, rfl⟩)
    (trans := by
      intro _ _ _ _ _ _ _ _ _ firstInduction secondInduction
      obtain ⟨firstChecked, firstCore, firstSource, firstTarget⟩ :=
        firstInduction
      obtain ⟨secondChecked, secondCore, secondSource, secondTarget⟩ :=
        secondInduction
      simp [LeCoreComplete, checkLeCore, firstCore, secondCore, firstSource, firstTarget,
        secondSource, secondTarget])
    (top := by
      intro _ _ source
      exact ⟨⟨source, .top, .top source⟩, rfl, rfl, rfl⟩)
    (bot := by
      intro _ _ target
      exact ⟨⟨.bot, target, .bot target⟩, rfl, rfl, rfl⟩)
    (eqToLe := by
      intro _ _ _ _ _ equalityTyping
      obtain ⟨checked, core, sourceEq, targetEq⟩ :=
        checkEqCore_complete equalityTyping
      simp [LeCoreComplete, checkLeCore, core, sourceEq, targetEq])
    (arr := by
      intro _ _ _ _ _ _ _ _ _ _ domainInduction codomainInduction
      obtain ⟨domainChecked, domainCore, domainSource, domainTarget⟩ :=
        domainInduction
      obtain ⟨codomainChecked, codomainCore, codomainSource,
        codomainTarget⟩ := codomainInduction
      rcases domainChecked with ⟨actualDomainSource, actualDomainTarget,
        actualDomainTyping⟩
      dsimp at domainCore domainSource domainTarget
      subst actualDomainSource
      subst actualDomainTarget
      rcases codomainChecked with ⟨actualCodomainSource,
        actualCodomainTarget, actualCodomainTyping⟩
      dsimp at codomainCore codomainSource codomainTarget
      subst actualCodomainSource
      subst actualCodomainTarget
      simp [LeCoreComplete, checkLeCore, domainCore, codomainCore])
    (existsT := by
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ adaptationInduction
        payloadInduction
      obtain ⟨adaptationChecked, adaptationCore, adaptationSource,
        adaptationTarget⟩ := adaptationInduction
      obtain ⟨payloadChecked, payloadCore, payloadSource, payloadTarget⟩ :=
        payloadInduction
      rcases adaptationChecked with ⟨actualSourceTelescope,
        actualTargetTelescope, actualAdaptationTyping⟩
      dsimp at adaptationCore adaptationSource adaptationTarget
      subst actualSourceTelescope
      subst actualTargetTelescope
      rcases payloadChecked with ⟨actualPayloadSource, actualPayloadTarget,
        actualPayloadTyping⟩
      dsimp at payloadCore payloadSource payloadTarget
      subst actualPayloadSource
      subst actualPayloadTarget
      simp [LeCoreComplete, checkLeCore, adaptationCore, payloadCore])
    (forallT := by
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ adaptationInduction
        bodyInduction
      obtain ⟨adaptationChecked, adaptationCore, adaptationSource,
        adaptationTarget⟩ := adaptationInduction
      obtain ⟨bodyChecked, bodyCore, bodySource, bodyTarget⟩ :=
        bodyInduction
      rcases adaptationChecked with ⟨actualTargetTelescope,
        actualSourceTelescope, actualAdaptationTyping⟩
      dsimp at adaptationCore adaptationSource adaptationTarget
      subst actualTargetTelescope
      subst actualSourceTelescope
      rcases bodyChecked with ⟨actualBodySource, actualBodyTarget,
        actualBodyTyping⟩
      dsimp at bodyCore bodySource bodyTarget
      subst actualBodySource
      subst actualBodyTarget
      simp [LeCoreComplete, checkLeCore, adaptationCore, bodyCore])
    (nil := by
      intro _ _ _ _
      exact ⟨_, rfl⟩)
    (snoc := by
      intro _ _ _ _ _ _ _ _ _ _ _ _ initialInduction evidenceInduction
      obtain ⟨initialChecked, initialCore⟩ := initialInduction
      obtain ⟨evidenceChecked, evidenceCore, evidenceSource,
        evidenceTarget⟩ := evidenceInduction
      simp [ArgsCoreComplete, checkArgsCore, initialCore, evidenceCore, evidenceSource,
        evidenceTarget])
    (by
      intro _ _ _ _ telescope
      exact ⟨⟨telescope, telescope, .refl telescope⟩, rfl, rfl, rfl⟩)
    (by
      intro _ _ _ _ _ _ _ _ _ _ _ argumentsInduction
      obtain ⟨argumentsChecked, argumentsCore⟩ := argumentsInduction
      simp [MorCoreComplete, checkMorCore, argumentsCore])
    (by
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ firstInduction
        secondInduction
      obtain ⟨firstChecked, firstCore, firstSource, firstTarget⟩ :=
        firstInduction
      obtain ⟨secondChecked, secondCore, secondSource, secondTarget⟩ :=
        secondInduction
      simp [MorCoreComplete, checkMorCore, firstCore, secondCore, firstSource, firstTarget,
        secondSource, secondTarget])
    typing

private theorem checkArgsCore_complete {scope : Sig} {context : Ctx scope}
    {names constraints : Nat}
    {telescope : Telescope scope names constraints}
    {witnesses : TypeArgs scope names} {arguments : LeArgs scope constraints}
    (typing : LeArgs.HasType context telescope witnesses arguments) :
    ∃ checked, checkArgsCore context telescope witnesses arguments =
      some checked := by
  induction constraints with
  | zero =>
      cases typing
      exact ⟨_, rfl⟩
  | succ constraints induction =>
      cases typing with
      | snoc initialTyping evidenceTyping =>
          obtain ⟨initialChecked, initialCore⟩ := induction initialTyping
          obtain ⟨evidenceChecked, evidenceCore, evidenceSource,
            evidenceTarget⟩ := checkLeCore_complete evidenceTyping
          simp [checkArgsCore, initialCore, evidenceCore, evidenceSource,
            evidenceTarget]

private theorem checkMorCore_complete {scope : Sig} {context : Ctx scope}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    {morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints}
    {source : Telescope scope sourceNames sourceConstraints}
    {target : Telescope scope targetNames targetConstraints}
    (typing : TelMor.HasType context morphism source target) :
    ∃ checked, checkMorCore context morphism = some checked ∧
      checked.source = source ∧ checked.target = target := by
  exact TelMor.HasType.rec
    (motive_1 := fun {_} _ _ _ _ _ => True)
    (motive_2 := fun {_} _ {_ _} _ _ _ _ => True)
    (motive_3 := fun {scope} context
        {sourceNames sourceConstraints targetNames targetConstraints}
        morphism source target typing =>
      MorCoreComplete context morphism source target typing)
    (var := by intros; trivial)
    (refl := by intros; trivial)
    (trans := by intros; trivial)
    (top := by intros; trivial)
    (bot := by intros; trivial)
    (eqToLe := by intros; trivial)
    (arr := by intros; trivial)
    (existsT := by intros; trivial)
    (forallT := by intros; trivial)
    (nil := by intros; trivial)
    (snoc := by intros; trivial)
    (by
      intro _ _ _ _ telescope
      exact ⟨⟨telescope, telescope, .refl telescope⟩, rfl, rfl, rfl⟩)
    (by
      intro _ _ _ _ _ _ _ _ _ _ argumentsTyping _
      obtain ⟨argumentsChecked, argumentsCore⟩ :=
        checkArgsCore_complete argumentsTyping
      simp [MorCoreComplete, checkMorCore, argumentsCore])
    (by
      intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ firstInduction
        secondInduction
      obtain ⟨firstChecked, firstCore, firstSource, firstTarget⟩ :=
        firstInduction
      obtain ⟨secondChecked, secondCore, secondSource, secondTarget⟩ :=
        secondInduction
      simp [MorCoreComplete, checkMorCore, firstCore, secondCore, firstSource,
        firstTarget, secondSource, secondTarget])
    typing

/-! ## Values and terms -/

private theorem checkSomeCore_complete {α : Type} {value : Option α}
    {result : α} (equation : value = some result) :
    ∃ checked, checkSomeCore value = some checked ∧
      checked.output = result := by
  cases value with
  | none => simp at equation
  | some actual =>
      have same : actual = result := Option.some.inj equation
      cases same
      exact ⟨⟨result, rfl⟩, rfl, rfl⟩

private theorem checkValueCore_complete {scope : Sig} {term : Tm scope}
    (value : Tm.IsValue term) :
    ∃ checked, checkValueCore term = some checked := by
  induction value with
  | unit => exact ⟨_, rfl⟩
  | lam => exact ⟨_, rfl⟩
  | cast _ induction =>
      obtain ⟨checked, core⟩ := induction
      exact ⟨⟨.cast checked.typing⟩, by simp [checkValueCore, core]⟩
  | pack _ induction =>
      obtain ⟨checked, core⟩ := induction
      exact ⟨⟨.pack checked.typing⟩, by simp [checkValueCore, core]⟩
  | slam _ induction =>
      obtain ⟨checked, core⟩ := induction
      exact ⟨⟨.slam checked.typing⟩, by simp [checkValueCore, core]⟩

private theorem checkTmCore_complete {scope : Sig} {context : Ctx scope}
    {term : Tm scope} {type : Ty scope}
    (typing : Tm.HasType context term type) :
    ∃ checked, checkTmCore context term = some checked ∧
      checked.type = type := by
  induction typing with
  | unit => exact ⟨⟨.one, .unit⟩, rfl, rfl⟩
  | var binding =>
      unfold checkTmCore
      split
      next actualType lookupEq =>
        have same : Binding.term actualType = Binding.term _ :=
          lookupEq.symm.trans binding
        cases same
        exact ⟨_, rfl, rfl⟩
  | lam bodyTyping bodyInduction =>
      obtain ⟨bodyChecked, bodyCore, bodyType⟩ := bodyInduction
      simp [checkTmCore, bodyCore, bodyType]
  | app functionTyping argumentTyping resultEquation functionInduction
      argumentInduction =>
      obtain ⟨functionChecked, functionCore, functionType⟩ :=
        functionInduction
      obtain ⟨argumentChecked, argumentCore, argumentType⟩ :=
        argumentInduction
      rcases functionChecked with ⟨actualFunctionType, actualFunctionTyping⟩
      dsimp at functionCore functionType
      subst actualFunctionType
      rcases argumentChecked with ⟨actualArgumentType, actualArgumentTyping⟩
      dsimp at argumentCore argumentType
      subst actualArgumentType
      obtain ⟨nonescapeChecked, nonescapeCore, nonescapeOutput⟩ :=
        checkSomeCore_complete resultEquation
      rcases nonescapeChecked with ⟨actualResult, actualNonescape⟩
      dsimp at nonescapeCore nonescapeOutput
      subst actualResult
      simp [checkTmCore, functionCore, argumentCore, nonescapeCore]
  | let' rhsTyping bodyTyping resultEquation rhsInduction bodyInduction =>
      obtain ⟨rhsChecked, rhsCore, rhsType⟩ := rhsInduction
      obtain ⟨bodyChecked, bodyCore, bodyType⟩ := bodyInduction
      rcases rhsChecked with ⟨actualRhsType, actualRhsTyping⟩
      dsimp at rhsCore rhsType
      subst actualRhsType
      rcases bodyChecked with ⟨actualBodyType, actualBodyTyping⟩
      dsimp at bodyCore bodyType
      subst actualBodyType
      obtain ⟨nonescapeChecked, nonescapeCore, nonescapeOutput⟩ :=
        checkSomeCore_complete resultEquation
      rcases nonescapeChecked with ⟨actualResult, actualNonescape⟩
      dsimp at nonescapeCore nonescapeOutput
      subst actualResult
      simp [checkTmCore, rhsCore, bodyCore, nonescapeCore]
  | cast termTyping evidenceTyping termInduction =>
      obtain ⟨termChecked, termCore, termType⟩ := termInduction
      obtain ⟨evidenceChecked, evidenceCore, evidenceSource,
        evidenceTarget⟩ := checkLeCore_complete evidenceTyping
      simp [checkTmCore, termCore, termType, evidenceCore, evidenceSource,
        evidenceTarget]
  | pack argumentsTyping payloadTyping payloadInduction =>
      obtain ⟨argumentsChecked, argumentsCore⟩ :=
        checkArgsCore_complete argumentsTyping
      obtain ⟨payloadChecked, payloadCore, payloadType⟩ := payloadInduction
      simp [checkTmCore, argumentsCore, payloadCore, payloadType]
  | openT packageTyping bodyTyping resultEquation packageInduction
      bodyInduction =>
      obtain ⟨packageChecked, packageCore, packageType⟩ := packageInduction
      obtain ⟨bodyChecked, bodyCore, bodyType⟩ := bodyInduction
      rcases packageChecked with ⟨actualPackageType, actualPackageTyping⟩
      dsimp at packageCore packageType
      subst actualPackageType
      rcases bodyChecked with ⟨actualBodyType, actualBodyTyping⟩
      dsimp at bodyCore bodyType
      subst actualBodyType
      obtain ⟨nonescapeChecked, nonescapeCore, nonescapeOutput⟩ :=
        checkSomeCore_complete resultEquation
      rcases nonescapeChecked with ⟨actualResult, actualNonescape⟩
      dsimp at nonescapeCore nonescapeOutput
      subst actualResult
      simp [checkTmCore, packageCore, bodyCore, nonescapeCore]
  | slam bodyValue bodyTyping bodyInduction =>
      obtain ⟨valueChecked, valueCore⟩ := checkValueCore_complete bodyValue
      obtain ⟨bodyChecked, bodyCore, bodyType⟩ := bodyInduction
      simp [checkTmCore, valueCore, bodyCore, bodyType]
  | sapp functionTyping argumentsTyping functionInduction =>
      obtain ⟨functionChecked, functionCore, functionType⟩ :=
        functionInduction
      obtain ⟨argumentsChecked, argumentsCore⟩ :=
        checkArgsCore_complete argumentsTyping
      rcases functionChecked with ⟨actualFunctionType, actualFunctionTyping⟩
      dsimp at functionCore functionType
      subst actualFunctionType
      simp [checkTmCore, functionCore, argumentsCore]
  | newtype bodyTyping resultEquation bodyInduction =>
      obtain ⟨bodyChecked, bodyCore, bodyType⟩ := bodyInduction
      rcases bodyChecked with ⟨actualBodyType, actualBodyTyping⟩
      dsimp at bodyCore bodyType
      subst actualBodyType
      obtain ⟨nonescapeChecked, nonescapeCore, nonescapeOutput⟩ :=
        checkSomeCore_complete resultEquation
      rcases nonescapeChecked with ⟨actualResult, actualNonescape⟩
      dsimp at nonescapeCore nonescapeOutput
      subst actualResult
      simp [checkTmCore, bodyCore, nonescapeCore]

/-! ## Public completeness -/

theorem synthEq_complete {scope : Sig} {context : Ctx scope}
    {evidence : EqCo scope} {source target : Ty scope}
    (typing : EqCo.HasType context evidence source target) :
    synthEq context evidence = some (source, target) := by
  obtain ⟨checked, core, sourceEq, targetEq⟩ :=
    checkEqCore_complete typing
  simp [synthEq, core, sourceEq, targetEq]

theorem synthLe_complete {scope : Sig} {context : Ctx scope}
    {evidence : LeCo scope} {source target : Ty scope}
    (typing : LeCo.HasType context evidence source target) :
    synthLe context evidence = some (source, target) := by
  obtain ⟨checked, core, sourceEq, targetEq⟩ :=
    checkLeCore_complete typing
  simp [synthLe, core, sourceEq, targetEq]

theorem checkArgs_complete {scope : Sig} {context : Ctx scope}
    {names constraints : Nat}
    {telescope : Telescope scope names constraints}
    {witnesses : TypeArgs scope names} {arguments : LeArgs scope constraints}
    (typing : LeArgs.HasType context telescope witnesses arguments) :
    checkArgs context telescope witnesses arguments = true := by
  obtain ⟨checked, core⟩ := checkArgsCore_complete typing
  simp [checkArgs, core]

theorem synthMor_complete {scope : Sig} {context : Ctx scope}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    {morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints}
    {source : Telescope scope sourceNames sourceConstraints}
    {target : Telescope scope targetNames targetConstraints}
    (typing : TelMor.HasType context morphism source target) :
    synthMor context morphism = some (source, target) := by
  obtain ⟨checked, core, sourceEq, targetEq⟩ :=
    checkMorCore_complete typing
  simp [synthMor, core, sourceEq, targetEq]

theorem synthTm_complete {scope : Sig} {context : Ctx scope}
    {term : Tm scope} {type : Ty scope}
    (typing : Tm.HasType context term type) :
    synthTm context term = some type := by
  obtain ⟨checked, core, typeEq⟩ := checkTmCore_complete typing
  simp [synthTm, core, typeEq]

/-! ## Literal `Bool` acceptance contracts -/

theorem checkEquality_iff {scope : Sig} {context : Ctx scope}
    {evidence : EqCo scope} {source target : Ty scope} :
    checkEquality context evidence source target = true ↔
      Nonempty (EqCo.HasType context evidence source target) := by
  constructor
  · exact checkEquality_sound
  · rintro ⟨typing⟩
    simp [checkEquality, synthEq_complete typing]

theorem checkEvidence_iff {scope : Sig} {context : Ctx scope}
    {evidence : LeCo scope} {source target : Ty scope} :
    checkEvidence context evidence source target = true ↔
      Nonempty (LeCo.HasType context evidence source target) := by
  constructor
  · exact checkEvidence_sound
  · rintro ⟨typing⟩
    simp [checkEvidence, synthLe_complete typing]

theorem checkArgs_iff {scope : Sig} {context : Ctx scope}
    {names constraints : Nat}
    {telescope : Telescope scope names constraints}
    {witnesses : TypeArgs scope names} {arguments : LeArgs scope constraints} :
    checkArgs context telescope witnesses arguments = true ↔
      Nonempty (LeArgs.HasType context telescope witnesses arguments) := by
  constructor
  · exact checkArgs_sound
  · rintro ⟨typing⟩
    exact checkArgs_complete typing

theorem checkMorphism_iff {scope : Sig} {context : Ctx scope}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    {morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints}
    {source : Telescope scope sourceNames sourceConstraints}
    {target : Telescope scope targetNames targetConstraints} :
    checkMorphism context morphism source target = true ↔
      Nonempty (TelMor.HasType context morphism source target) := by
  constructor
  · exact checkMorphism_sound
  · rintro ⟨typing⟩
    simp [checkMorphism, synthMor_complete typing]

theorem checkTerm_iff {scope : Sig} {context : Ctx scope}
    {term : Tm scope} {type : Ty scope} :
    checkTerm context term type = true ↔
      Nonempty (Tm.HasType context term type) := by
  constructor
  · exact checkTerm_sound
  · rintro ⟨typing⟩
    simp [checkTerm, synthTm_complete typing]

end FCsub
