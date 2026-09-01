import Coercions.ManySortedFC.TermChecker

/-!
# Completeness of the many-sorted FC term checker

Every declarative term typing derivation is reflected by the independent
structural checker at exactly the same immediate-use and result-type indices.
The auxiliary completeness arguments cover evidence, adapters, and theory
models used at annotated term boundaries.
-/

namespace ManySortedFC

namespace Evidence

private theorem check_complete_projection {scope : Sig}
    {context : Ctx scope} {relation : Relation}
    {evidence : Evidence relation scope}
    {proposition : Proposition relation scope}
    (typing : Proves context evidence proposition) :
    (check context evidence).map Checked.proposition = some proposition := by
  induction typing with
  | var binding =>
      simp only [check]
      split <;> simp_all
  | equalityRefl => rfl
  | equalitySymm typing ih =>
      obtain ⟨checked, checkedEq, propEq⟩ := Option.map_eq_some_iff.mp ih
      cases checked with
      | mk checkedProp checkedTyping =>
        dsimp at propEq
        subst checkedProp
        simp [check, checkedEq]
  | equalityTrans first second firstIH secondIH =>
      obtain ⟨firstChecked, firstEq, firstPropEq⟩ :=
        Option.map_eq_some_iff.mp firstIH
      obtain ⟨secondChecked, secondEq, secondPropEq⟩ :=
        Option.map_eq_some_iff.mp secondIH
      cases firstChecked with
      | mk firstProp firstTyping =>
        cases secondChecked with
        | mk secondProp secondTyping =>
          dsimp at firstPropEq secondPropEq
          subst firstProp
          subst secondProp
          simp [check, firstEq, secondEq]
  | equalityArrow domain codomain domainIH codomainIH =>
      obtain ⟨domainChecked, domainEq, domainPropEq⟩ :=
        Option.map_eq_some_iff.mp domainIH
      obtain ⟨codomainChecked, codomainEq, codomainPropEq⟩ :=
        Option.map_eq_some_iff.mp codomainIH
      cases domainChecked with
      | mk domainProp domainTyping =>
        cases codomainChecked with
        | mk codomainProp codomainTyping =>
          dsimp at domainPropEq codomainPropEq
          subst domainProp
          subst codomainProp
          simp [check, domainEq, codomainEq]
  | equalityCapturing captures shape capturesIH shapeIH =>
      obtain ⟨capturesChecked, capturesEq, capturesPropEq⟩ :=
        Option.map_eq_some_iff.mp capturesIH
      obtain ⟨shapeChecked, shapeEq, shapePropEq⟩ :=
        Option.map_eq_some_iff.mp shapeIH
      cases capturesChecked with
      | mk capturesProp capturesTyping =>
        cases shapeChecked with
        | mk shapeProp shapeTyping =>
          dsimp at capturesPropEq shapePropEq
          subst capturesProp
          subst shapeProp
          simp [check, capturesEq, shapeEq]
  | equalityCaptureUnion left right leftIH rightIH =>
      obtain ⟨leftChecked, leftEq, leftPropEq⟩ :=
        Option.map_eq_some_iff.mp leftIH
      obtain ⟨rightChecked, rightEq, rightPropEq⟩ :=
        Option.map_eq_some_iff.mp rightIH
      cases leftChecked with
      | mk leftProp leftTyping =>
        cases rightChecked with
        | mk rightProp rightTyping =>
          dsimp at leftPropEq rightPropEq
          subst leftProp
          subst rightProp
          simp [check, leftEq, rightEq]
  | equalityCaptureReadOnly capture ih =>
      obtain ⟨checked, checkedEq, propEq⟩ := Option.map_eq_some_iff.mp ih
      cases checked with
      | mk checkedProp checkedTyping =>
        dsimp at propEq
        subst checkedProp
        simp [check, checkedEq]
  | inclusionRefl => rfl
  | inclusionTrans first second firstIH secondIH =>
      obtain ⟨firstChecked, firstEq, firstPropEq⟩ :=
        Option.map_eq_some_iff.mp firstIH
      obtain ⟨secondChecked, secondEq, secondPropEq⟩ :=
        Option.map_eq_some_iff.mp secondIH
      cases firstChecked with
      | mk firstProp firstTyping =>
        cases secondChecked with
        | mk secondProp secondTyping =>
          dsimp at firstPropEq secondPropEq
          subst firstProp
          subst secondProp
          simp [check, firstEq, secondEq]
  | equalityToInclusion typing ih =>
      obtain ⟨checked, checkedEq, propEq⟩ := Option.map_eq_some_iff.mp ih
      cases checked with
      | mk checkedProp checkedTyping =>
        dsimp at propEq
        subst checkedProp
        simp [check, checkedEq]
  | typeTop => rfl
  | typeBottom => rfl
  | typeArrow domain codomain domainIH codomainIH =>
      obtain ⟨domainChecked, domainEq, domainPropEq⟩ :=
        Option.map_eq_some_iff.mp domainIH
      obtain ⟨codomainChecked, codomainEq, codomainPropEq⟩ :=
        Option.map_eq_some_iff.mp codomainIH
      cases domainChecked with
      | mk domainProp domainTyping =>
        cases codomainChecked with
        | mk codomainProp codomainTyping =>
          dsimp at domainPropEq codomainPropEq
          subst domainProp
          subst codomainProp
          simp [check, domainEq, codomainEq]
  | typeCapturing captures shape capturesIH shapeIH =>
      obtain ⟨capturesChecked, capturesEq, capturesPropEq⟩ :=
        Option.map_eq_some_iff.mp capturesIH
      obtain ⟨shapeChecked, shapeEq, shapePropEq⟩ :=
        Option.map_eq_some_iff.mp shapeIH
      cases capturesChecked with
      | mk capturesProp capturesTyping =>
        cases shapeChecked with
        | mk shapeProp shapeTyping =>
          dsimp at capturesPropEq shapePropEq
          subst capturesProp
          subst shapeProp
          simp [check, capturesEq, shapeEq]
  | captureEmpty => rfl
  | captureUnionLeft => rfl
  | captureUnionRight => rfl
  | captureUnionElim left right leftIH rightIH =>
      obtain ⟨leftChecked, leftEq, leftPropEq⟩ :=
        Option.map_eq_some_iff.mp leftIH
      obtain ⟨rightChecked, rightEq, rightPropEq⟩ :=
        Option.map_eq_some_iff.mp rightIH
      cases leftChecked with
      | mk leftProp leftTyping =>
        cases rightChecked with
        | mk rightProp rightTyping =>
          dsimp at leftPropEq rightPropEq
          subst leftProp
          subst rightProp
          simp [check, leftEq, rightEq]
  | captureVariable binding =>
      simp only [check]
      split <;> simp_all
  | captureReadOnly => rfl
  | captureReadOnlyMono subcapture ih =>
      obtain ⟨checked, checkedEq, propEq⟩ := Option.map_eq_some_iff.mp ih
      cases checked with
      | mk checkedProp checkedTyping =>
        dsimp at propEq
        subst checkedProp
        simp [check, checkedEq]
  | modeEmpty => rfl
  | modeUnion left right leftIH rightIH =>
      obtain ⟨leftChecked, leftEq, leftPropEq⟩ :=
        Option.map_eq_some_iff.mp leftIH
      obtain ⟨rightChecked, rightEq, rightPropEq⟩ :=
        Option.map_eq_some_iff.mp rightIH
      cases leftChecked with
      | mk leftProp leftTyping =>
        cases rightChecked with
        | mk rightProp rightTyping =>
          dsimp at leftPropEq rightPropEq
          subst leftProp
          subst rightProp
          simp [check, leftEq, rightEq]
  | modeSubcapture subcapture upperMode subcaptureIH modeIH =>
      obtain ⟨subcaptureChecked, subcaptureEq, subcapturePropEq⟩ :=
        Option.map_eq_some_iff.mp subcaptureIH
      obtain ⟨modeChecked, modeEq, modePropEq⟩ :=
        Option.map_eq_some_iff.mp modeIH
      cases subcaptureChecked with
      | mk subcaptureProp subcaptureTyping =>
        cases modeChecked with
        | mk modeProp modeTyping =>
          dsimp at subcapturePropEq modePropEq
          subst subcaptureProp
          subst modeProp
          simp [check, subcaptureEq, modeEq]
  | modeWritable => rfl
  | modeReadOnly => rfl
  | separateSymm evidence ih =>
      obtain ⟨checked, checkedEq, propEq⟩ := Option.map_eq_some_iff.mp ih
      cases checked with
      | mk checkedProp checkedTyping =>
        dsimp at propEq
        subst checkedProp
        simp [check, checkedEq]
  | separateUnion left right leftIH rightIH =>
      obtain ⟨leftChecked, leftEq, leftPropEq⟩ :=
        Option.map_eq_some_iff.mp leftIH
      obtain ⟨rightChecked, rightEq, rightPropEq⟩ :=
        Option.map_eq_some_iff.mp rightIH
      cases leftChecked with
      | mk leftProp leftTyping =>
        cases rightChecked with
        | mk rightProp rightTyping =>
          dsimp at leftPropEq rightPropEq
          subst leftProp
          subst rightProp
          simp [check, leftEq, rightEq]
  | separateEmpty => rfl
  | separateReadOnly left right leftIH rightIH =>
      obtain ⟨leftChecked, leftEq, leftPropEq⟩ :=
        Option.map_eq_some_iff.mp leftIH
      obtain ⟨rightChecked, rightEq, rightPropEq⟩ :=
        Option.map_eq_some_iff.mp rightIH
      cases leftChecked with
      | mk leftProp leftTyping =>
        cases rightChecked with
        | mk rightProp rightTyping =>
          dsimp at leftPropEq rightPropEq
          subst leftProp
          subst rightProp
          simp [check, leftEq, rightEq]
  | separateSubcapture subcapture separation subcaptureIH separationIH =>
      obtain ⟨subcaptureChecked, subcaptureEq, subcapturePropEq⟩ :=
        Option.map_eq_some_iff.mp subcaptureIH
      obtain ⟨separationChecked, separationEq, separationPropEq⟩ :=
        Option.map_eq_some_iff.mp separationIH
      cases subcaptureChecked with
      | mk subcaptureProp subcaptureTyping =>
        cases separationChecked with
        | mk separationProp separationTyping =>
          dsimp at subcapturePropEq separationPropEq
          subst subcaptureProp
          subst separationProp
          simp [check, subcaptureEq, separationEq]
  | separateOfDisjoint disjoint ih =>
      obtain ⟨checked, checkedEq, propEq⟩ := Option.map_eq_some_iff.mp ih
      cases checked with
      | mk checkedProp checkedTyping =>
        dsimp at propEq
        subst checkedProp
        simp [check, checkedEq]
  | disjointSymm evidence ih =>
      obtain ⟨checked, checkedEq, propEq⟩ := Option.map_eq_some_iff.mp ih
      cases checked with
      | mk checkedProp checkedTyping =>
        dsimp at propEq
        subst checkedProp
        simp [check, checkedEq]
  | disjointUnion left right leftIH rightIH =>
      obtain ⟨leftChecked, leftEq, leftPropEq⟩ :=
        Option.map_eq_some_iff.mp leftIH
      obtain ⟨rightChecked, rightEq, rightPropEq⟩ :=
        Option.map_eq_some_iff.mp rightIH
      cases leftChecked with
      | mk leftProp leftTyping =>
        cases rightChecked with
        | mk rightProp rightTyping =>
          dsimp at leftPropEq rightPropEq
          subst leftProp
          subst rightProp
          simp [check, leftEq, rightEq]
  | disjointEmpty => rfl
  | disjointEquality equality disjoint equalityIH disjointIH =>
      obtain ⟨equalityChecked, equalityEq, equalityPropEq⟩ :=
        Option.map_eq_some_iff.mp equalityIH
      obtain ⟨disjointChecked, disjointEq, disjointPropEq⟩ :=
        Option.map_eq_some_iff.mp disjointIH
      cases equalityChecked with
      | mk equalityProp equalityTyping =>
        cases disjointChecked with
        | mk disjointProp disjointTyping =>
          dsimp at equalityPropEq disjointPropEq
          subst equalityProp
          subst disjointProp
          simp [check, equalityEq, disjointEq]

end Evidence

namespace TheoryMorphism

private theorem checkValidates_complete {scope : Sig}
    {symbols : List StaticSort} {allRelations relations : List Relation}
    {context : Ctx (StaticScope scope symbols allRelations)}
    {target : Theory scope symbols relations}
    {evidence : EvidenceArgs
      (StaticScope scope symbols allRelations) relations}
    (typing : Validates context target evidence) :
    ∃ checked, checkValidates context target evidence = some checked := by
  induction typing with
  | nil => exact ⟨.nil, rfl⟩
  | cons head tail tailIH =>
      have headIH := Evidence.check_complete_projection head
      obtain ⟨headChecked, headEq, headPropositionEq⟩ :=
        Option.map_eq_some_iff.mp headIH
      obtain ⟨tailChecked, tailEq⟩ := tailIH
      cases headChecked with
      | mk headProposition headCheckedTyping =>
          dsimp at headPropositionEq
          subst headProposition
          simp [checkValidates, headEq, tailEq]

private theorem check_complete {scope : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    {context : Ctx scope}
    {source target : Theory scope symbols relations}
    {morphism : TheoryMorphism source target}
    (typing : HasType context morphism) :
    ∃ checked, check context morphism = some checked :=
  checkValidates_complete typing

end TheoryMorphism

namespace ModalTheoryMap

private theorem satisfaction_complete {scope : Sig}
    {context : Ctx scope}
    {symbols : List StaticSort} {arguments : SymbolArgs scope symbols}
    {relations : List Relation} {theory : Theory scope symbols relations}
    {evidence : EvidenceArgs scope relations}
    (typing : Theory.SatisfiedBy context arguments theory evidence) :
    ∃ checked,
      Theory.checkSatisfaction context arguments theory evidence =
        some checked := by
  induction typing with
  | nil => exact ⟨.nil, rfl⟩
  | cons head tail tailIH =>
      have headIH := Evidence.check_complete_projection head
      obtain ⟨headChecked, headEq, headPropositionEq⟩ :=
        Option.map_eq_some_iff.mp headIH
      obtain ⟨tailChecked, tailEq⟩ := tailIH
      cases headChecked with
      | mk headProposition headCheckedTyping =>
          dsimp at headPropositionEq
          subst headProposition
          simp [Theory.checkSatisfaction, headEq, tailEq]

private theorem check_complete {scope : Sig}
    {requiredSeparationCount availableSeparationCount : Nat}
    {requiredModes availableModes : List CaptureMode}
    {context : Ctx scope}
    {available : ModalContext availableSeparationCount availableModes scope}
    {required : ModalContext requiredSeparationCount requiredModes scope}
    {mapping : ModalTheoryMap scope availableSeparationCount availableModes
      requiredSeparationCount requiredModes}
    (typing : HasType context available required mapping) :
    ∃ checked, check context available required mapping = some checked := by
  unfold HasType at typing
  unfold check TheoryMap.check
  exact satisfaction_complete typing

end ModalTheoryMap

namespace Adapter

private theorem check_complete_projection {scope : Sig}
    {context : Ctx scope} {adapter : Adapter scope}
    {source target : Ty scope}
    (typing : HasType context adapter source target) :
    synth context adapter = some (source, target) := by
  induction typing with
  | identity => rfl
  | cast evidenceTyping =>
      have evidenceIH := Evidence.check_complete_projection evidenceTyping
      obtain ⟨evidenceChecked, evidenceEq, propositionEq⟩ :=
        Option.map_eq_some_iff.mp evidenceIH
      cases evidenceChecked with
      | mk proposition checkedTyping =>
        dsimp at propositionEq
        subst proposition
        simp [synth, check, evidenceEq]
  | retagCapture capturesTyping shapeTyping =>
      have capturesIH := Evidence.check_complete_projection capturesTyping
      have shapeIH := Evidence.check_complete_projection shapeTyping
      obtain ⟨capturesChecked, capturesEq, capturesPropEq⟩ :=
        Option.map_eq_some_iff.mp capturesIH
      obtain ⟨shapeChecked, shapeEq, shapePropEq⟩ :=
        Option.map_eq_some_iff.mp shapeIH
      cases capturesChecked with
      | mk capturesProp checkedCapturesTyping =>
        cases shapeChecked with
        | mk shapeProp checkedShapeTyping =>
          dsimp at capturesPropEq shapePropEq
          subst capturesProp
          subst shapeProp
          simp [synth, check, capturesEq, shapeEq]
  | forgetEmptyCapture => rfl
  | captured capturesTyping shapeTyping shapeIH =>
      have capturesIH := Evidence.check_complete_projection capturesTyping
      obtain ⟨capturesChecked, capturesEq, capturesPropEq⟩ :=
        Option.map_eq_some_iff.mp capturesIH
      obtain ⟨shapeChecked, shapeEq, shapeEndpointsEq⟩ :=
        Option.map_eq_some_iff.mp shapeIH
      cases capturesChecked with
      | mk capturesProp checkedCapturesTyping =>
        cases shapeChecked with
        | mk shapeSource shapeTarget checkedShapeTyping =>
          dsimp at capturesPropEq shapeEndpointsEq
          subst capturesProp
          cases Prod.mk.inj shapeEndpointsEq with
          | intro shapeSourceEq shapeTargetEq =>
            subst shapeSource
            subst shapeTarget
            simp [synth, check, capturesEq, shapeEq]
  | compose firstTyping secondTyping firstIH secondIH =>
      obtain ⟨firstChecked, firstEq, endpointsEq⟩ :=
        Option.map_eq_some_iff.mp firstIH
      obtain ⟨secondChecked, secondEq, secondEndpointsEq⟩ :=
        Option.map_eq_some_iff.mp secondIH
      cases firstChecked with
      | mk firstSource firstTarget firstCheckedTyping =>
        cases secondChecked with
        | mk secondSource secondTarget secondCheckedTyping =>
          dsimp at endpointsEq secondEndpointsEq
          cases Prod.mk.inj endpointsEq with
          | intro firstSourceEq firstTargetEq =>
            cases Prod.mk.inj secondEndpointsEq with
            | intro secondSourceEq secondTargetEq =>
              subst firstSource
              subst firstTarget
              subst secondSource
              subst secondTarget
              simp [synth, check, firstEq, secondEq]
  | function domainTyping codomainTyping domainIH codomainIH =>
      obtain ⟨domainChecked, domainEq, domainEndpointsEq⟩ :=
        Option.map_eq_some_iff.mp domainIH
      obtain ⟨codomainChecked, codomainEq, codomainEndpointsEq⟩ :=
        Option.map_eq_some_iff.mp codomainIH
      cases domainChecked with
      | mk domainSource domainTarget checkedDomainTyping =>
        cases codomainChecked with
        | mk codomainSource codomainTarget checkedCodomainTyping =>
          dsimp at domainEndpointsEq codomainEndpointsEq
          cases Prod.mk.inj domainEndpointsEq with
          | intro domainSourceEq domainTargetEq =>
            cases Prod.mk.inj codomainEndpointsEq with
            | intro codomainSourceEq codomainTargetEq =>
              subst domainSource
              subst domainTarget
              subst codomainSource
              subst codomainTarget
              simp [synth, check, domainEq, codomainEq]
  | modal requirementsTyping resultTyping resultIH =>
      obtain ⟨checkedRequirements, requirementsEq⟩ :=
        ModalTheoryMap.check_complete requirementsTyping
      obtain ⟨resultChecked, resultEq, endpointsEq⟩ :=
        Option.map_eq_some_iff.mp resultIH
      cases resultChecked with
      | mk resultSource resultTarget checkedResultTyping =>
          dsimp at endpointsEq
          cases Prod.mk.inj endpointsEq with
          | intro resultSourceEq resultTargetEq =>
            subst resultSource
            subst resultTarget
            simp [synth, check, requirementsEq, resultEq]
  | forallT bodyTyping bodyIH =>
      obtain ⟨bodyChecked, bodyEq, endpointsEq⟩ :=
        Option.map_eq_some_iff.mp bodyIH
      cases bodyChecked with
      | mk bodySource bodyTarget checkedBodyTyping =>
        dsimp at endpointsEq
        cases Prod.mk.inj endpointsEq with
        | intro bodySourceEq bodyTargetEq =>
          subst bodySource
          subst bodyTarget
          simp [synth, check, bodyEq]
  | existsT payloadTyping payloadIH =>
      obtain ⟨payloadChecked, payloadEq, endpointsEq⟩ :=
        Option.map_eq_some_iff.mp payloadIH
      cases payloadChecked with
      | mk payloadSource payloadTarget checkedPayloadTyping =>
        dsimp at endpointsEq
        cases Prod.mk.inj endpointsEq with
        | intro payloadSourceEq payloadTargetEq =>
          subst payloadSource
          subst payloadTarget
          simp [synth, check, payloadEq]
  | forallMorphism constraintsTyping bodyTyping bodyIH =>
      obtain ⟨checkedConstraints, constraintsEq⟩ :=
        TheoryMorphism.check_complete constraintsTyping
      obtain ⟨bodyChecked, bodyEq, endpointsEq⟩ :=
        Option.map_eq_some_iff.mp bodyIH
      cases bodyChecked with
      | mk bodySource bodyTarget checkedBodyTyping =>
        dsimp at endpointsEq
        cases Prod.mk.inj endpointsEq with
        | intro bodySourceEq bodyTargetEq =>
          subst bodySource
          subst bodyTarget
          simp [synth, check, constraintsEq, bodyEq]
  | existsMorphism constraintsTyping payloadTyping payloadIH =>
      obtain ⟨checkedConstraints, constraintsEq⟩ :=
        TheoryMorphism.check_complete constraintsTyping
      obtain ⟨payloadChecked, payloadEq, endpointsEq⟩ :=
        Option.map_eq_some_iff.mp payloadIH
      cases payloadChecked with
      | mk payloadSource payloadTarget checkedPayloadTyping =>
        dsimp at endpointsEq
        cases Prod.mk.inj endpointsEq with
        | intro payloadSourceEq payloadTargetEq =>
          subst payloadSource
          subst payloadTarget
          simp [synth, check, constraintsEq, payloadEq]

end Adapter

namespace Theory

private theorem checkSatisfaction_complete {scope : Sig}
    {context : Ctx scope}
    {symbols : List StaticSort} {arguments : SymbolArgs scope symbols}
    {relations : List Relation} {theory : Theory scope symbols relations}
    {evidence : EvidenceArgs scope relations}
    (satisfaction : SatisfiedBy context arguments theory evidence) :
    ∃ checked,
      checkSatisfaction context arguments theory evidence = some checked := by
  induction satisfaction with
  | nil => exact ⟨.nil, rfl⟩
  | cons head tail tailIH =>
      have headIH := Evidence.check_complete_projection head
      obtain ⟨headChecked, headEq, headPropEq⟩ :=
        Option.map_eq_some_iff.mp headIH
      obtain ⟨tailChecked, tailEq⟩ := tailIH
      cases headChecked with
      | mk headProposition headCheckedTyping =>
        dsimp at headPropEq
        subst headProposition
        simp [checkSatisfaction, headEq, tailEq]

end Theory

namespace Tm

private theorem evidence_check_complete {scope : Sig}
    {context : Ctx scope} {relation : Relation}
    {evidence : Evidence relation scope}
    {proposition : Proposition relation scope}
    (typing : Evidence.Proves context evidence proposition) :
    ∃ checkedTyping,
      Evidence.check context evidence =
        some ⟨proposition, checkedTyping⟩ := by
  have projected := Evidence.check_complete_projection typing
  obtain ⟨checked, checkedEq, propositionEq⟩ :=
    Option.map_eq_some_iff.mp projected
  cases checked with
  | mk checkedProposition checkedTyping =>
    dsimp at propositionEq
    subst checkedProposition
    exact ⟨checkedTyping, checkedEq⟩

private theorem checkValue_complete {scope : Sig} {term : Tm scope}
    (value : IsValue term) :
    ∃ checked, checkValue term = some checked := by
  induction value with
  | var => exact ⟨⟨.var⟩, rfl⟩
  | unit => exact ⟨⟨.unit⟩, rfl⟩
  | lam => exact ⟨⟨.lam⟩, rfl⟩
  | adapt termValue termIH =>
      obtain ⟨termChecked, termEq⟩ := termIH
      exact ⟨⟨.adapt termChecked.typing⟩, by simp [checkValue, termEq]⟩
  | lock => exact ⟨⟨.lock⟩, rfl⟩
  | slam bodyValue bodyIH =>
      obtain ⟨bodyChecked, bodyEq⟩ := bodyIH
      exact ⟨⟨.slam bodyChecked.typing⟩, by simp [checkValue, bodyEq]⟩
  | pack payloadValue payloadIH =>
      obtain ⟨payloadChecked, payloadEq⟩ := payloadIH
      exact ⟨⟨.pack payloadChecked.typing⟩,
        by simp [checkValue, payloadEq]⟩

private theorem checkCaptureInclusion_complete {scope : Sig}
    {context : Ctx scope}
    {evidence : Evidence (.inclusion .capture) scope}
    {source target : Capture scope}
    (typing : Evidence.Proves context evidence
      (.inclusion (.capture source) (.capture target))) :
    ∃ checked,
      checkCaptureInclusion context evidence source target = some checked := by
  have evidenceIH := Evidence.check_complete_projection typing
  obtain ⟨evidenceChecked, evidenceEq, propositionEq⟩ :=
    Option.map_eq_some_iff.mp evidenceIH
  cases evidenceChecked with
  | mk proposition checkedTyping =>
    dsimp at propositionEq
    subst proposition
    simp [checkCaptureInclusion, evidenceEq]

private theorem adapter_check_complete {scope : Sig} {context : Ctx scope}
    {adapter : Adapter scope} {source target : Ty scope}
    (typing : Adapter.HasType context adapter source target) :
    ∃ checkedTyping,
      Adapter.check context adapter =
        some ⟨source, target, checkedTyping⟩ := by
  have projected := Adapter.check_complete_projection typing
  unfold Adapter.synth at projected
  obtain ⟨checked, checkedEq, endpointsEq⟩ :=
    Option.map_eq_some_iff.mp projected
  cases checked with
  | mk checkedSource checkedTarget checkedTyping =>
    dsimp at endpointsEq
    cases Prod.mk.inj endpointsEq with
    | intro sourceEq targetEq =>
      subst checkedSource
      subst checkedTarget
      exact ⟨checkedTyping, checkedEq⟩

private theorem check_complete_of_synth {scope : Sig}
    {context : Ctx scope} {term : Tm scope}
    {use : Capture scope} {type : Ty scope}
    (accepted : synth context term = some (use, type)) :
    ∃ checkedTyping,
      check context term = some ⟨use, type, checkedTyping⟩ := by
  unfold synth at accepted
  obtain ⟨checked, checkedEq, indicesEq⟩ :=
    Option.map_eq_some_iff.mp accepted
  cases checked with
  | mk checkedUse checkedType checkedTyping =>
    dsimp at indicesEq
    cases Prod.mk.inj indicesEq with
    | intro useEq typeEq =>
      subst checkedUse
      subst checkedType
      exact ⟨checkedTyping, checkedEq⟩

/-- Every declaratively typed annotated target term is accepted by the
independent structural checker at exactly the same capture and type indices. -/
theorem synth_complete {scope : Sig} {context : Ctx scope}
    {term : Tm scope} {use : Capture scope} {type : Ty scope}
    (typing : HasType context term use type) :
    synth context term = some (use, type) := by
  induction typing with
  | var => rfl
  | unit => rfl
  | lam bodyTyping capturesTyping bodyIH =>
      obtain ⟨checkedBodyTyping, bodyEq⟩ :=
        check_complete_of_synth bodyIH
      obtain ⟨checkedCapturesTyping, capturesEq⟩ :=
        checkCaptureInclusion_complete capturesTyping
      simp [synth, check, bodyEq, capturesEq]
  | app functionTyping functionShape argumentTyping functionIH argumentIH =>
      obtain ⟨checkedFunctionTyping, functionEq⟩ :=
        check_complete_of_synth functionIH
      obtain ⟨checkedArgumentTyping, argumentEq⟩ :=
        check_complete_of_synth argumentIH
      simp [synth, check, functionEq, argumentEq]
      split <;> simp_all
  | let' rhsTyping bodyTyping dischargeTyping rhsIH bodyIH =>
      obtain ⟨checkedRhsTyping, rhsEq⟩ :=
        check_complete_of_synth rhsIH
      obtain ⟨checkedBodyTyping, bodyEq⟩ :=
        check_complete_of_synth bodyIH
      obtain ⟨checkedDischargeTyping, dischargeEq⟩ :=
        checkCaptureInclusion_complete dischargeTyping
      simp [synth, check, rhsEq, bodyEq, dischargeEq]
  | adapt termValue termTyping adapterTyping termIH =>
      obtain ⟨checkedTermValue, termValueEq⟩ :=
        checkValue_complete termValue
      obtain ⟨checkedTermTyping, termEq⟩ :=
        check_complete_of_synth termIH
      obtain ⟨checkedAdapterTyping, adapterEq⟩ :=
        adapter_check_complete adapterTyping
      simp [synth, check, termValueEq, termEq, adapterEq]
  | lock bodyTyping capturesTyping bodyIH =>
      obtain ⟨checkedBodyTyping, bodyEq⟩ :=
        check_complete_of_synth bodyIH
      obtain ⟨checkedCapturesTyping, capturesEq⟩ :=
        checkCaptureInclusion_complete capturesTyping
      simp [synth, check, bodyEq, capturesEq]
  | unlock termTyping termShape satisfaction termIH =>
      obtain ⟨checkedTermTyping, termEq⟩ :=
        check_complete_of_synth termIH
      obtain ⟨checkedSatisfaction, satisfactionEq⟩ :=
        Theory.checkSatisfaction_complete satisfaction
      rename_i _ _ _ _ _ _ _ _ termType _
      cases termType with
      | top => simp [Ty.stripCapture] at termShape
      | bot => simp [Ty.stripCapture] at termShape
      | one => simp [Ty.stripCapture] at termShape
      | tvar => simp [Ty.stripCapture] at termShape
      | arr => simp [Ty.stripCapture] at termShape
      | forallT => simp [Ty.stripCapture] at termShape
      | existsT => simp [Ty.stripCapture] at termShape
      | capturing captures shape =>
          change shape = Ty.modal _ _ at termShape
          subst shape
          simp [synth, check, Ty.stripCapture, Ty.outerCapture,
            termEq, satisfactionEq]
      | modal actualRequirements actualResult =>
          simp [Ty.stripCapture] at termShape
          rcases termShape with ⟨rfl, rfl, requirementsEq, resultEq⟩
          cases requirementsEq
          cases resultEq
          simp [synth, check, Ty.stripCapture, Ty.outerCapture,
            termEq, satisfactionEq]
  | slam bodyValue bodyTyping capturesTyping bodyIH =>
      obtain ⟨checkedBodyValue, bodyValueEq⟩ :=
        checkValue_complete bodyValue
      obtain ⟨checkedBodyTyping, bodyEq⟩ :=
        check_complete_of_synth bodyIH
      obtain ⟨checkedCapturesTyping, capturesEq⟩ :=
        checkCaptureInclusion_complete capturesTyping
      simp [synth, check, bodyValueEq, bodyEq, capturesEq]
  | sapp functionTyping functionShape satisfaction functionIH =>
      obtain ⟨checkedFunctionTyping, functionEq⟩ :=
        check_complete_of_synth functionIH
      obtain ⟨checkedSatisfaction, satisfactionEq⟩ :=
        Theory.checkSatisfaction_complete satisfaction
      rename_i _ _ _ _ _ functionType _ _ _ _
      cases functionType with
      | top => simp [Ty.stripCapture] at functionShape
      | bot => simp [Ty.stripCapture] at functionShape
      | one => simp [Ty.stripCapture] at functionShape
      | tvar => simp [Ty.stripCapture] at functionShape
      | arr => simp [Ty.stripCapture] at functionShape
      | modal => simp [Ty.stripCapture] at functionShape
      | existsT => simp [Ty.stripCapture] at functionShape
      | capturing captures shape =>
          change shape = Ty.forallT _ _ at functionShape
          subst shape
          simp [synth, check, Ty.stripCapture, Ty.outerCapture,
            functionEq, satisfactionEq]
      | forallT actualTheory actualBody =>
          simp [Ty.stripCapture] at functionShape
          rcases functionShape with ⟨rfl, rfl, theoryEq, bodyEq⟩
          cases theoryEq
          cases bodyEq
          simp [synth, check, Ty.stripCapture, Ty.outerCapture,
            functionEq, satisfactionEq]
  | pack satisfaction payloadValue payloadTyping capturesTyping payloadIH =>
      obtain ⟨checkedSatisfaction, satisfactionEq⟩ :=
        Theory.checkSatisfaction_complete satisfaction
      obtain ⟨checkedPayloadValue, payloadValueEq⟩ :=
        checkValue_complete payloadValue
      obtain ⟨checkedPayloadTyping, payloadEq⟩ :=
        check_complete_of_synth payloadIH
      obtain ⟨checkedCapturesTyping, capturesEq⟩ :=
        checkCaptureInclusion_complete capturesTyping
      simp [synth, check, satisfactionEq, payloadValueEq, payloadEq,
        capturesEq]
  | «open» packageTyping packageShape bodyTyping dischargeTyping packageIH
      bodyIH =>
      obtain ⟨checkedPackageTyping, packageEq⟩ :=
        check_complete_of_synth packageIH
      obtain ⟨checkedBodyTyping, bodyEq⟩ :=
        check_complete_of_synth bodyIH
      obtain ⟨checkedDischargeTyping, dischargeEq⟩ :=
        checkCaptureInclusion_complete dischargeTyping
      simp [synth, check, packageEq, packageShape, bodyEq, dischargeEq]
  | use termTyping inclusionTyping termIH =>
      obtain ⟨checkedTermTyping, termEq⟩ :=
        check_complete_of_synth termIH
      obtain ⟨checkedInclusionTyping, inclusionEq⟩ :=
        evidence_check_complete inclusionTyping
      simp [synth, check, termEq, inclusionEq]

end Tm

end ManySortedFC
