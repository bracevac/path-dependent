import Coercions.Translation.ManySorted.Acyclic.ValueTranslation
import Coercions.Translation.ManySorted.Acyclic.SelectionTranslation
import Coercions.Translation.ManySorted.Acyclic.EvidenceTranslation
import Coercions.DOT.Captures.Acyclic.ComputationalExamples

/-!
# Acyclic value-MNF captured-DOT compilation

This module presents the **closed, acyclic, value-MNF captured-DOT compiler
case-study core**.  Its acceptance programs are closed; the underlying
compiler API also accepts an arbitrary executable `Ready` context.
Applications take values,
object-opening lets require a canonical object value RHS, and object bindings
compile through the many-sorted FC target's FCsub-style existential opening
(`ManySortedFC.Tm.open`).  The supported term rules are return, selection,
value-application, plain let, object-opening let, and explicit use widening;
the mutually compiled value rules are variable, unit, lambda, object package,
and logical adaptation.

Lambda domains must satisfy `Ty.IsPlain`.  Paths are variable-only and the
object case uses the fixed `{A,C,v}` member layout.  Recursive objects, full
DOT, general non-MNF terms, intersections, arbitrary labels or members,
dependent arrows, structural arrow adaptation, object-parameter universals,
and the negative/universal interface translation are outside this fragment.
The positive object slice is existential: a canonical package is eliminated
by target `Tm.open`, never by pretending its expanded telescope is one plain
term binder.
-/

/-! ## Independent target rechecking

Compiler results carry declarative target typings, but they remain ordinary
annotated many-sorted FC syntax.  Syntax-directed completeness below reflects
any such typing derivation back through the target's structural checker.
Consequently even proof-indexed, definitionally opaque compiler artifacts can
be rechecked independently at their exact capture and type indices.
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

end Evidence

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
  | app functionValue argumentValue functionTyping functionShape
      argumentTyping functionIH argumentIH =>
      obtain ⟨checkedFunctionValue, functionValueEq⟩ :=
        checkValue_complete functionValue
      obtain ⟨checkedArgumentValue, argumentValueEq⟩ :=
        checkValue_complete argumentValue
      obtain ⟨checkedFunctionTyping, functionEq⟩ :=
        check_complete_of_synth functionIH
      obtain ⟨checkedArgumentTyping, argumentEq⟩ :=
        check_complete_of_synth argumentIH
      simp [synth, check, functionValueEq, argumentValueEq, functionEq,
        argumentEq]
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
  | slam bodyValue bodyTyping capturesTyping bodyIH =>
      obtain ⟨checkedBodyValue, bodyValueEq⟩ :=
        checkValue_complete bodyValue
      obtain ⟨checkedBodyTyping, bodyEq⟩ :=
        check_complete_of_synth bodyIH
      obtain ⟨checkedCapturesTyping, capturesEq⟩ :=
        checkCaptureInclusion_complete capturesTyping
      simp [synth, check, bodyValueEq, bodyEq, capturesEq]
  | sapp functionValue functionTyping functionShape satisfaction functionIH =>
      obtain ⟨checkedFunctionValue, functionValueEq⟩ :=
        checkValue_complete functionValue
      obtain ⟨checkedFunctionTyping, functionEq⟩ :=
        check_complete_of_synth functionIH
      obtain ⟨checkedSatisfaction, satisfactionEq⟩ :=
        Theory.checkSatisfaction_complete satisfaction
      rename_i _ _ _ _ _ _ functionType _ _ _
      cases functionType with
      | top => simp [Ty.stripCapture] at functionShape
      | bot => simp [Ty.stripCapture] at functionShape
      | one => simp [Ty.stripCapture] at functionShape
      | tvar => simp [Ty.stripCapture] at functionShape
      | arr => simp [Ty.stripCapture] at functionShape
      | existsT => simp [Ty.stripCapture] at functionShape
      | capturing captures shape =>
          change shape = Ty.forallT _ _ at functionShape
          subst shape
          simp [synth, check, Ty.stripCapture, Ty.outerCapture,
            functionValueEq, functionEq, satisfactionEq]
      | forallT actualTheory actualBody =>
          simp [Ty.stripCapture] at functionShape
          rcases functionShape with ⟨rfl, rfl, theoryEq, bodyEq⟩
          cases theoryEq
          cases bodyEq
          simp [synth, check, Ty.stripCapture, Ty.outerCapture,
            functionValueEq, functionEq, satisfactionEq]
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
  | «open» packageValue packageTyping packageShape bodyTyping
      dischargeTyping packageIH bodyIH =>
      obtain ⟨checkedPackageValue, packageValueEq⟩ :=
        checkValue_complete packageValue
      obtain ⟨checkedPackageTyping, packageEq⟩ :=
        check_complete_of_synth packageIH
      obtain ⟨checkedBodyTyping, bodyEq⟩ :=
        check_complete_of_synth bodyIH
      obtain ⟨checkedDischargeTyping, dischargeEq⟩ :=
        checkCaptureInclusion_complete dischargeTyping
      simp [synth, check, packageValueEq, packageEq, packageShape, bodyEq,
        dischargeEq]
  | use termTyping inclusionTyping termIH =>
      obtain ⟨checkedTermTyping, termEq⟩ :=
        check_complete_of_synth termIH
      obtain ⟨checkedInclusionTyping, inclusionEq⟩ :=
        evidence_check_complete inclusionTyping
      simp [synth, check, termEq, inclusionEq]

end Tm

end ManySortedFC

namespace DOTCaptureToManySortedFC.Acyclic.TermTranslation

namespace Source

export DOTCapture.Acyclic
  (Scope Path Capture Ty StaticExpr Ctx Value Term ObjectSig ExposesObject
    CaptureIncludes)

namespace Path
export DOTCapture.Acyclic.Path (selectedType selectedCapture valueMemberType)
end Path

namespace Term
export DOTCapture.Acyclic.Term (HasType)
end Term

namespace Value
export DOTCapture.Acyclic.Value (HasType)
end Value

end Source

namespace Target

export ManySortedFC
  (Capture Ty StaticExpr Evidence Tm)

namespace Evidence
export ManySortedFC.Evidence (Proves)
end Evidence

namespace Tm
export ManySortedFC.Tm (HasType check synth)
end Tm

end Target

namespace Context

export DOTCaptureToManySortedFC.Acyclic.RuntimeContext
  (Ready)

end Context

namespace Static

export DOTCaptureToManySortedFC.Acyclic.StaticTranslation
  (translateCapture? translateTy? translateExpr?)

end Static

namespace Values

export DOTCaptureToManySortedFC.Acyclic.ValueTranslation
  (CompiledValue CompiledTerm compileValue? compileTerm? compileAdapt?
    finishLambda? finishPlainLet? finishObjectLet?)

end Values

namespace Selection

export DOTCaptureToManySortedFC.Acyclic.SelectionTranslation
  (Result selectedPayloadType term compile)

end Selection

namespace Logical

export DOTCaptureToManySortedFC.Acyclic.EvidenceTranslation
  (CompiledInclusion compileIncludes?)

end Logical

/-! ## Proof-carrying result -/

abbrev CompiledTerm {scope : Source.Scope} {context : Source.Ctx scope}
    (ready : Context.Ready context) (sourceTerm : Source.Term scope)
    (sourceUse : Source.Capture scope) (sourceType : Source.Ty scope) :=
  Values.CompiledTerm ready sourceTerm sourceUse sourceType

/-! ## Exact endpoint alignment -/

private theorem translateCaptureExpression {scope : Source.Scope}
    {context : Source.Ctx scope} {source : Source.Capture scope}
    {target : Target.Capture (Layout.sig context)}
    (translated : Static.translateCapture? context source = some target) :
    Static.translateExpr? context (.capture source) =
      some (.capture target) := by
  simp [Static.translateExpr?, translated]

private theorem ofTranslateCaptureExpression {scope : Source.Scope}
    {context : Source.Ctx scope} {source : Source.Capture scope}
    {target : Target.Capture (Layout.sig context)}
    (translated : Static.translateExpr? context (.capture source) =
      some (.capture target)) :
    Static.translateCapture? context source = some target := by
  unfold Static.translateExpr? at translated
  obtain ⟨found, foundTranslated, foundEquality⟩ :=
    Option.map_eq_some_iff.mp translated
  have equality : found = target := by
    injection foundEquality
  subst target
  exact foundTranslated

private theorem translatedExpression_unique {scope : Source.Scope}
    {context : Source.Ctx scope}
    {source : Source.StaticExpr .capture scope}
    {first second : Target.StaticExpr .capture (Layout.sig context)}
    (firstTranslated : Static.translateExpr? context source = some first)
    (secondTranslated : Static.translateExpr? context source = some second) :
    first = second :=
  StaticTranslation.TranslatesExpr.functional
    firstTranslated secondTranslated

/-! ## Individual source rules -/

/-- Primitive selection is total once its source exposure and translated
runtime context are available. -/
noncomputable def compileSelect {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Context.Ready context)
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (exposes : Source.ExposesObject context receiver signature) :
    CompiledTerm ready (.select receiver .v) (.singleton receiver)
      receiver.valueMemberType := by
  let selected := Selection.compile ready.translated exposes
  exact
    { sourceTyping := selected.sourceTyping
      targetUse := .singleton selected.resolved.slot.payload
      targetType := Selection.selectedPayloadType selected.resolved
      useTranslated := selected.useTranslated
      typeTranslated := selected.typeTranslated
      term := Selection.term selected.resolved
      typing := selected.targetTyping }

/-- The logical certificate and translated endpoint needed to add one target
`Tm.use`.  Separating this payload from the final `CompiledTerm` makes the
generated term constructor available through an ordinary `Option.map` law. -/
structure CompiledUse {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Context.Ready context}
    {sourceTerm : Source.Term scope}
    {sourceUse sourceTargetUse : Source.Capture scope}
    {sourceType : Source.Ty scope}
    (inner : CompiledTerm ready sourceTerm sourceUse sourceType)
    (inclusion : Source.CaptureIncludes context sourceUse sourceTargetUse) where
  targetUse : Target.Capture (Layout.sig context)
  useTranslated :
    Static.translateCapture? context sourceTargetUse = some targetUse
  evidence : Target.Evidence (.inclusion .capture) (Layout.sig context)
  evidenceTyping : Target.Evidence.Proves ready.target evidence
    (.inclusion (.capture inner.targetUse) (.capture targetUse))

/-- Compile the logical payload for one source capture-use rule.  Failure can
only come from translating or resolving one of the raw source endpoints. -/
noncomputable def compileUseEvidence? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Context.Ready context}
    {sourceTerm : Source.Term scope}
    {sourceUse targetUse : Source.Capture scope}
    {sourceType : Source.Ty scope}
    (inner : CompiledTerm ready sourceTerm sourceUse sourceType)
    (inclusion : Source.CaptureIncludes context sourceUse targetUse) :
    Option (CompiledUse inner inclusion) := by
  generalize compiledEquation :
    Logical.compileIncludes? ready.translated inclusion = compiledResult
  cases compiledResult with
  | none => exact none
  | some compiled =>
      rcases compiled with
        ⟨sourceTarget, targetTarget, sourceTranslated, targetTranslated,
          evidence, evidenceTyping⟩
      cases sourceTarget with
      | capture compiledSource =>
          cases targetTarget with
          | capture compiledTarget =>
              have expectedSource :=
                translateCaptureExpression inner.useTranslated
              have sourceEquality := translatedExpression_unique
                sourceTranslated expectedSource
              cases sourceEquality
              have targetUseTranslated :=
                ofTranslateCaptureExpression targetTranslated
              exact some
                { targetUse := compiledTarget
                  useTranslated := targetUseTranslated
                  evidence := evidence
                  evidenceTyping := evidenceTyping }

/-- Add exactly one target `Tm.use` for one source capture-use rule. -/
noncomputable def compileUse? {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Context.Ready context}
    {sourceTerm : Source.Term scope}
    {sourceUse targetUse : Source.Capture scope}
    {sourceType : Source.Ty scope}
    (inner : CompiledTerm ready sourceTerm sourceUse sourceType)
    (inclusion : Source.CaptureIncludes context sourceUse targetUse) :
    Option (CompiledTerm ready sourceTerm targetUse sourceType) :=
  (compileUseEvidence? inner inclusion).map fun compiled =>
    { sourceTyping := .use inner.sourceTyping inclusion
      targetUse := compiled.targetUse
      targetType := inner.targetType
      useTranslated := compiled.useTranslated
      typeTranslated := inner.typeTranslated
      term := .use inner.term compiled.evidence
      typing := .use inner.typing compiled.evidenceTyping }

/-- A successful source-use compilation adds exactly one target `Tm.use`
node.  This projection keeps downstream erasure proofs independent of the
dependent endpoint-alignment implementation above. -/
theorem compileUse?_term {scope : Source.Scope}
    {context : Source.Ctx scope} {ready : Context.Ready context}
    {sourceTerm : Source.Term scope}
    {sourceUse targetUse : Source.Capture scope}
    {sourceType : Source.Ty scope}
    (inner : CompiledTerm ready sourceTerm sourceUse sourceType)
    (inclusion : Source.CaptureIncludes context sourceUse targetUse)
    {compiled : CompiledTerm ready sourceTerm targetUse sourceType}
    (success : compileUse? inner inclusion = some compiled) :
    ∃ evidence, compiled.term = .use inner.term evidence := by
  unfold compileUse? at success
  obtain ⟨generated, generatedCompiled, generatedEquality⟩ :=
    Option.map_eq_some_iff.mp success
  cases generatedEquality
  exact ⟨generated.evidence, rfl⟩

/-! ## Derivation-directed compiler -/

/-- Translate captured-DOT term typing derivations without proof search.
Optional failure records partial static-annotation translation as well as the
endpoint and logical-evidence translation performed by value construction and
capture-use compilation. -/
noncomputable abbrev compileTerm? {scope : Source.Scope}
    {context : Source.Ctx scope} (ready : Context.Ready context)
    {sourceTerm : Source.Term scope} {sourceUse : Source.Capture scope}
    {sourceType : Source.Ty scope}
    (derivation : Source.Term.HasType context sourceTerm sourceUse sourceType) :
    Option (CompiledTerm ready sourceTerm sourceUse sourceType) :=
  Values.compileTerm? ready derivation

/-! ## Exact-object regressions -/

namespace Regression

namespace RuntimeRegression

export DOTCaptureToManySortedFC.Acyclic.RuntimeContext
  (nil exactObjectReady)

end RuntimeRegression

namespace ExposureRegression

export DOTCaptureToManySortedFC.Acyclic.ExposureTranslation.Regression
  (ExactSignature ExactSourceContext exactExposure)

end ExposureRegression

namespace SourceExamples

export DOTCapture.Acyclic.Examples
  (exactSignature exactObject exactObjectTyping)

end SourceExamples

abbrev exactReceiver := StaticTranslation.exactReceiver
abbrev exactSlot := Layout.newestReceiverSlot []

/-! ### Return-marker erasure -/

def unitReturnTyping : Source.Term.HasType (.nil : Source.Ctx 0)
    (.ret .unit) .empty .one :=
  .ret .unit

theorem unit_return_compiles :
    (compileTerm? RuntimeRegression.nil unitReturnTyping).isSome = true := by
  rfl

noncomputable def unitReturnResult :=
  (compileTerm? RuntimeRegression.nil unitReturnTyping).get
    unit_return_compiles

theorem unit_return_has_no_target_marker :
    unitReturnResult.term = (.unit : Target.Tm []) := by
  rfl

/-- Returning a formed captured-DOT object delegates to value compilation;
the source `ret` marker adds no wrapper around the generated package. -/
def exactObjectReturnTyping : Source.Term.HasType (.nil : Source.Ctx 0)
    (.ret SourceExamples.exactObject) .empty
    (.capturing .empty (.object SourceExamples.exactSignature)) :=
  .ret SourceExamples.exactObjectTyping

theorem exact_object_return_compiles :
    (compileTerm? RuntimeRegression.nil
      exactObjectReturnTyping).isSome = true := by
  rfl

noncomputable def exactObjectReturnResult :=
  (compileTerm? RuntimeRegression.nil exactObjectReturnTyping).get
    exact_object_return_compiles

theorem exact_object_return_has_exact_package_type :
    exactObjectReturnResult.targetUse =
        (.empty : Target.Capture []) ∧
      exactObjectReturnResult.targetType =
        ObjectEncoding.objectType ObjectEncoding.exactBounds := by
  constructor <;> rfl

theorem exact_object_return_checker_accepts :
    (Target.Tm.check RuntimeRegression.nil.target
      exactObjectReturnResult.term).isSome = true := by
  rfl

theorem exact_object_return_synthesizes_package_type :
    Target.Tm.synth RuntimeRegression.nil.target
        exactObjectReturnResult.term =
      some
        ((.empty : Target.Capture []),
          ObjectEncoding.objectType ObjectEncoding.exactBounds) := by
  rfl

/-! ### Genuine `x.A`, `x.C`, and `x.v` selection -/

def exactPrimitiveTyping : Source.Term.HasType
    ExposureRegression.ExactSourceContext
    (.select exactReceiver .v) (.singleton exactReceiver)
    exactReceiver.valueMemberType :=
  .select ExposureRegression.exactExposure

theorem exact_primitive_compiles :
    (compileTerm? RuntimeRegression.exactObjectReady
      exactPrimitiveTyping).isSome = true := by
  rfl

noncomputable def exactPrimitiveResult :=
  (compileTerm? RuntimeRegression.exactObjectReady
    exactPrimitiveTyping).get exact_primitive_compiles

/-- The primitive read charges the receiver payload root and returns exactly
`(x.A)^{x.C}` translated through the receiver's shared alpha/chi slot. -/
theorem exact_primitive_has_xA_xC_xv_indices :
    exactPrimitiveResult.targetUse =
        (.singleton exactSlot.payload : Target.Capture _) ∧
      exactPrimitiveResult.targetType =
        (.capturing (.cvar exactSlot.chi.name)
          (.tvar exactSlot.alpha.name) : Target.Ty _) := by
  constructor <;> rfl

theorem exact_primitive_checker_accepts :
    (Target.Tm.check RuntimeRegression.exactObjectReady.target
      exactPrimitiveResult.term).isSome = true := by
  rfl

theorem exact_primitive_synthesizes_xA_xC :
    Target.Tm.synth RuntimeRegression.exactObjectReady.target
        exactPrimitiveResult.term =
      some
        ((.singleton exactSlot.payload : Target.Capture _),
          (.capturing (.cvar exactSlot.chi.name)
            (.tvar exactSlot.alpha.name) : Target.Ty _)) := by
  rfl

/-! ### One source use becomes one additional target use -/

def exactSelectedUseTyping : Source.Term.HasType
    ExposureRegression.ExactSourceContext
    (.select exactReceiver .v) exactReceiver.selectedCapture
    exactReceiver.valueMemberType :=
  .use (.select ExposureRegression.exactExposure)
    ExposureRegression.exactExposure.payloadRoot

theorem exact_selected_use_compiles :
    (compileTerm? RuntimeRegression.exactObjectReady
      exactSelectedUseTyping).isSome = true := by
  rfl

noncomputable def exactSelectedUseResult :=
  (compileTerm? RuntimeRegression.exactObjectReady
    exactSelectedUseTyping).get exact_selected_use_compiles

noncomputable def exactSelection :=
  Selection.compile RuntimeRegression.exactObjectReady.translated
    ExposureRegression.exactExposure

theorem exact_selected_use_is_one_explicit_widening :
    exactSelectedUseResult.term =
      .use (Selection.term exactSelection.resolved)
        (.captureVariable exactSelection.resolved.slot.payload) := by
  rfl

theorem exact_selected_use_has_xA_xC_xv_indices :
    exactSelectedUseResult.targetUse =
        (.cvar exactSlot.chi.name : Target.Capture _) ∧
      exactSelectedUseResult.targetType =
        (.capturing (.cvar exactSlot.chi.name)
          (.tvar exactSlot.alpha.name) : Target.Ty _) := by
  constructor <;> rfl

theorem exact_selected_use_checker_accepts :
    (Target.Tm.check RuntimeRegression.exactObjectReady.target
      exactSelectedUseResult.term).isSome = true := by
  rfl

theorem exact_selected_use_synthesizes_xC :
    Target.Tm.synth RuntimeRegression.exactObjectReady.target
        exactSelectedUseResult.term =
      some
        ((.cvar exactSlot.chi.name : Target.Capture _),
          (.capturing (.cvar exactSlot.chi.name)
            (.tvar exactSlot.alpha.name) : Target.Ty _)) := by
  rfl

/-! A transitive source inclusion is retained inside the one new evidence
tree; it does not introduce one target term node per logical sub-proof. -/

def exactUpperUseTyping : Source.Term.HasType
    ExposureRegression.ExactSourceContext
    (.select exactReceiver .v)
    ExposureRegression.ExactSignature.weaken.captureUpper
    exactReceiver.valueMemberType :=
  .use (.select ExposureRegression.exactExposure)
    (.trans ExposureRegression.exactExposure.payloadRoot
      ExposureRegression.exactExposure.captureUpper)

theorem exact_upper_use_compiles :
    (compileTerm? RuntimeRegression.exactObjectReady
      exactUpperUseTyping).isSome = true := by
  rfl

noncomputable def exactUpperUseResult :=
  (compileTerm? RuntimeRegression.exactObjectReady
    exactUpperUseTyping).get exact_upper_use_compiles

theorem exact_upper_use_is_one_explicit_widening :
    exactUpperUseResult.term =
      .use (Selection.term exactSelection.resolved)
        (.inclusionTrans
          (.captureVariable exactSelection.resolved.slot.payload)
          (.var exactSelection.resolved.facts.captureUpper)) := by
  rfl

/-! Two nested source rules recurse to two additional term nodes.  This is
distinct from the prior regression, whose one source rule contains a
transitive logical certificate but still adds only one term node. -/

def exactNestedUseTyping : Source.Term.HasType
    ExposureRegression.ExactSourceContext
    (.select exactReceiver .v)
    ExposureRegression.ExactSignature.weaken.captureUpper
    exactReceiver.valueMemberType :=
  .use exactSelectedUseTyping ExposureRegression.exactExposure.captureUpper

theorem exact_nested_use_compiles :
    (compileTerm? RuntimeRegression.exactObjectReady
      exactNestedUseTyping).isSome = true := by
  rfl

noncomputable def exactNestedUseResult :=
  (compileTerm? RuntimeRegression.exactObjectReady
    exactNestedUseTyping).get exact_nested_use_compiles

theorem exact_nested_use_has_two_explicit_widenings :
    exactNestedUseResult.term =
      .use
        (.use (Selection.term exactSelection.resolved)
          (.captureVariable exactSelection.resolved.slot.payload))
        (.var exactSelection.resolved.facts.captureUpper) := by
  rfl

theorem exact_nested_use_synthesizes_empty :
    Target.Tm.synth RuntimeRegression.exactObjectReady.target
        exactNestedUseResult.term =
      some
        ((.empty : Target.Capture _),
          (.capturing (.cvar exactSlot.chi.name)
            (.tvar exactSlot.alpha.name) : Target.Ty _)) := by
  rfl

/-! ### Static footprint and independent checker rejection -/

/-- Every object opening allocates the two advertised abstract names,
`A` and `C`; the payload remains a separate term binder. -/
theorem object_signature_symbol_count_is_two :
    ObjectEncoding.symbols.length = 2 := by
  rfl

/-- The fixed object theory carries the lower and upper endpoint relation for
each of those two names. -/
theorem object_signature_relation_count_is_four :
    ObjectEncoding.relations.length = 4 :=
  ObjectEncoding.relation_count_is_four

/-- The value payload is one ordinary runtime binder, separate from both
abstract symbols and all four evidence binders. -/
theorem object_payload_binder_count_is_one :
    ObjectEncoding.payloadTerm (scope := []) =
      (.here : ManySortedFC.BVar (ObjectEncoding.PayloadScope []) .term) :=
  ObjectEncoding.payload_is_one_separate_term_binder

/-- Surface the central negative model test beside the compiler acceptance
suite: reflexive certificates at fabricated witnesses do not satisfy the
object's incompatible ambient bounds. -/
theorem fabricated_bad_object_model_is_rejected :
    (ManySortedFC.Theory.checkModel ObjectEncoding.badContext
      (ObjectEncoding.theory ObjectEncoding.badBounds)
      ObjectEncoding.fabricatedSymbols
      ObjectEncoding.fabricatedEvidence).isNone = true :=
  ObjectEncoding.fabricated_bad_model_is_rejected

/-- A small target-only value keeps the executable checker tests independent
of the proof-carrying source compiler. -/
def targetUnitIdentity : Target.Tm [] :=
  .lam .one .one .empty (.var .here)
    (.captureEmpty (.union .empty (.singleton .here)))

theorem target_unit_identity_checker_accepts :
    (Target.Tm.check ManySortedFC.Ctx.nil targetUnitIdentity).isSome = true := by
  rfl

theorem target_unit_identity_synthesizes_function :
    Target.Tm.synth ManySortedFC.Ctx.nil targetUnitIdentity =
      some (.empty, .capturing .empty (.arr .one .one)) := by
  rfl

/-- The application boundary rejects a function value where the identity's
`One` domain requires a unit value. -/
theorem wrong_argument_shape_is_rejected :
    Target.Tm.check ManySortedFC.Ctx.nil
      (.app targetUnitIdentity targetUnitIdentity) = none := by
  rfl

end Regression

/-! ## Closed computational regressions -/

namespace ComputationalRegression

/-! ### Runtime-spine metrics

These structural counts ignore types, captures, and logical certificates in
exactly the same way as erasure.  Object packages contribute the metrics of
their representation payload; each source let becomes one runtime let. -/

structure RuntimeStats where
  lets : Nat
  lambdas : Nat
  applications : Nat
deriving DecidableEq

namespace RuntimeStats

def zero : RuntimeStats := ⟨0, 0, 0⟩

def add (left right : RuntimeStats) : RuntimeStats :=
  ⟨left.lets + right.lets,
    left.lambdas + right.lambdas,
    left.applications + right.applications⟩

def oneLet (stats : RuntimeStats) : RuntimeStats :=
  ⟨stats.lets + 1, stats.lambdas, stats.applications⟩

def oneLambda (stats : RuntimeStats) : RuntimeStats :=
  ⟨stats.lets, stats.lambdas + 1, stats.applications⟩

def oneApplication (stats : RuntimeStats) : RuntimeStats :=
  ⟨stats.lets, stats.lambdas, stats.applications + 1⟩

end RuntimeStats

mutual

def valueRuntimeStats {scope : Source.Scope} :
    Source.Value scope → RuntimeStats
  | .var _ => .zero
  | .unit => .zero
  | .lam _ _ body => (termRuntimeStats body).oneLambda
  | .object _ _ _ payload => valueRuntimeStats payload

def termRuntimeStats {scope : Source.Scope} :
    Source.Term scope → RuntimeStats
  | .ret value => valueRuntimeStats value
  | .select _ _ => .zero
  | .app function argument =>
      ((valueRuntimeStats function).add
        (valueRuntimeStats argument)).oneApplication
  | .let' _ rhs body =>
      ((termRuntimeStats rhs).add (termRuntimeStats body)).oneLet

end

namespace Examples

export DOTCapture.Acyclic.ComputationalExamples
  (returnSelected applySelected closedUnaryType functionSignature
    functionObjectTyping selectedTypePlain selectedPure selectedFunctionTyping
    selectedApplication identityTyping identity functionObject unaryShape
    selectedApplicationRaw objectExposure olderObjectExposure receiver
    olderReceiver)

end Examples

abbrev emptyReady :=
  DOTCaptureToManySortedFC.Acyclic.RuntimeContext.nil

abbrev unaryShape : Source.Ty 0 := .arr .one .one
abbrev closedUnaryType : Source.Ty 0 := .capturing .empty unaryShape
abbrev identity : Source.Value 0 :=
  .lam .one .one (.ret (.var .here))
abbrev functionSignature : Source.ObjectSig 0 :=
  .bounds unaryShape unaryShape .empty .empty
abbrev functionObject : Source.Value 0 :=
  .object functionSignature unaryShape .empty identity
abbrev receiver : Source.Path 1 := .var .here

abbrev returnSelected : Source.Term 0 :=
  .let' closedUnaryType (.ret functionObject)
    (.let' closedUnaryType.weaken (.select receiver .v)
      (.ret (.var .here)))

abbrev applySelected : Source.Term 0 :=
  .let' .one (.ret functionObject)
    (.let' .one (.select receiver .v)
      (.app (.var .here) .unit))

abbrev regressionIdentityTyping : Source.Value.HasType (.nil : Source.Ctx 0)
    identity closedUnaryType :=
  .lam (Eq.refl none) (.ret .var) .captureEmpty

abbrev regressionFunctionObjectTyping : Source.Value.HasType
    (.nil : Source.Ctx 0) functionObject
    (.capturing .empty (.object functionSignature)) :=
  .object .refl .refl .refl .refl regressionIdentityTyping .refl .refl

abbrev regressionObjectContext : Source.Ctx 1 :=
    (.nil : Source.Ctx 0).extendTerm
    (.capturing .empty (.object functionSignature))

abbrev regressionObjectExposure : Source.ExposesObject
    regressionObjectContext receiver functionSignature.weaken :=
  .variable (Eq.refl _)

abbrev regressionSelectedPure : Source.Term.HasType regressionObjectContext
    (.select receiver .v) .empty receiver.valueMemberType :=
  .use regressionObjectExposure.valueMember
    regressionObjectExposure.captureUpper

abbrev regressionSelectedTypePlain : receiver.valueMemberType.IsPlain :=
  Eq.refl none

abbrev regressionSelectedContext : Source.Ctx 2 :=
  regressionObjectContext.extendTerm receiver.valueMemberType

abbrev regressionOlderExposure : Source.ExposesObject
    regressionSelectedContext (.var (.there .here))
      functionSignature.weaken.weaken :=
  .variable (Eq.refl _)

abbrev regressionSelectedFunctionTyping : Source.Value.HasType
    regressionSelectedContext (.var .here)
      closedUnaryType.weaken.weaken :=
  .adapt .var (.typeCapturing regressionOlderExposure.captureUpper
    regressionOlderExposure.typeUpper)

abbrev regressionSelectedApplication : Source.Term.HasType
    regressionSelectedContext (.app (.var .here) .unit) .empty .one :=
  .use (.app regressionSelectedFunctionTyping (Eq.refl _) .unit)
    (.captureUnionElim .captureEmpty .captureEmpty)

abbrev returnSelectedTyping : Source.Term.HasType (.nil : Source.Ctx 0)
    returnSelected .empty closedUnaryType :=
  .use
    (.letObject (signature := functionSignature)
      regressionFunctionObjectTyping
      (.use
        (.letPlain regressionSelectedTypePlain regressionSelectedPure
          (.ret regressionSelectedFunctionTyping) .captureEmpty)
        (.captureUnionElim .captureEmpty .captureEmpty))
      .captureEmpty)
    (.captureUnionElim .captureEmpty .captureEmpty)

abbrev applySelectedTyping : Source.Term.HasType (.nil : Source.Ctx 0)
    applySelected .empty .one :=
  .use
    (.letObject (signature := functionSignature)
      regressionFunctionObjectTyping
      (.use
        (.letPlain regressionSelectedTypePlain regressionSelectedPure
          regressionSelectedApplication .captureEmpty)
        (.captureUnionElim .captureEmpty .captureEmpty))
      .captureEmpty)
    (.captureUnionElim .captureEmpty .captureEmpty)

set_option maxHeartbeats 2000000 in
noncomputable abbrev returnSelected_compiles :
    (compileTerm? emptyReady returnSelectedTyping).isSome = true := by
  unfold compileTerm?
  unfold returnSelectedTyping returnSelected closedUnaryType
  unfold regressionFunctionObjectTyping regressionIdentityTyping
  unfold regressionSelectedPure regressionObjectExposure
  unfold regressionSelectedFunctionTyping regressionOlderExposure
  unfold functionObject identity functionSignature unaryShape receiver
  rfl

set_option maxHeartbeats 2000000 in
noncomputable abbrev applySelected_compiles :
    (compileTerm? emptyReady applySelectedTyping).isSome = true := by
  unfold compileTerm?
  unfold applySelectedTyping applySelected
  unfold regressionFunctionObjectTyping regressionIdentityTyping
  unfold regressionSelectedPure regressionObjectExposure
  unfold regressionSelectedApplication
  unfold regressionSelectedFunctionTyping regressionOlderExposure
  unfold functionObject identity functionSignature unaryShape receiver
  rfl

noncomputable abbrev returnSelectedCompiled :=
  (compileTerm? emptyReady returnSelectedTyping).get
    returnSelected_compiles

noncomputable abbrev applySelectedCompiled :=
  (compileTerm? emptyReady applySelectedTyping).get
    applySelected_compiles

theorem returnSelected_runtime_stats :
    termRuntimeStats returnSelected = ⟨2, 1, 0⟩ := by
  rfl

theorem applySelected_runtime_stats :
    termRuntimeStats applySelected = ⟨2, 1, 1⟩ := by
  rfl

theorem returnSelected_has_exact_target_indices :
    returnSelectedCompiled.targetUse = (.empty : Target.Capture []) ∧
    returnSelectedCompiled.targetType =
      (.capturing .empty (.arr .one .one) : Target.Ty []) := by
  constructor
  · apply Eq.symm
    apply Option.some.inj
    simpa [Static.translateCapture?] using
      returnSelectedCompiled.useTranslated
  · apply Eq.symm
    apply Option.some.inj
    simpa [closedUnaryType, unaryShape, Static.translateTy?,
      Static.translateCapture?] using returnSelectedCompiled.typeTranslated

theorem applySelected_has_exact_target_indices :
    applySelectedCompiled.targetUse = (.empty : Target.Capture []) ∧
    applySelectedCompiled.targetType = (.one : Target.Ty []) := by
  constructor
  · apply Eq.symm
    apply Option.some.inj
    simpa [Static.translateCapture?] using
      applySelectedCompiled.useTranslated
  · apply Eq.symm
    apply Option.some.inj
    simpa [Static.translateTy?] using applySelectedCompiled.typeTranslated

noncomputable def returnSelected_target_is_well_typed :
    Target.Tm.HasType emptyReady.target returnSelectedCompiled.term
      .empty (.capturing .empty (.arr .one .one)) := by
  simpa [returnSelected_has_exact_target_indices.1,
    returnSelected_has_exact_target_indices.2] using
      returnSelectedCompiled.typing

noncomputable def applySelected_target_is_well_typed :
    Target.Tm.HasType emptyReady.target applySelectedCompiled.term
      .empty .one := by
  simpa [applySelected_has_exact_target_indices.1,
    applySelected_has_exact_target_indices.2] using
      applySelectedCompiled.typing

theorem returnSelected_target_synthesizes_exact_indices :
    Target.Tm.synth emptyReady.target returnSelectedCompiled.term =
      some
        ((.empty : Target.Capture []),
          (.capturing .empty (.arr .one .one) : Target.Ty [])) :=
  ManySortedFC.Tm.synth_complete returnSelected_target_is_well_typed

theorem applySelected_target_synthesizes_exact_indices :
    Target.Tm.synth emptyReady.target applySelectedCompiled.term =
      some ((.empty : Target.Capture []), (.one : Target.Ty [])) :=
  ManySortedFC.Tm.synth_complete applySelected_target_is_well_typed

theorem returnSelected_target_checker_accepts :
    (Target.Tm.check emptyReady.target
      returnSelectedCompiled.term).isSome = true := by
  have accepted := congrArg Option.isSome
    returnSelected_target_synthesizes_exact_indices
  simpa [ManySortedFC.Tm.synth] using accepted

theorem applySelected_target_checker_accepts :
    (Target.Tm.check emptyReady.target
      applySelectedCompiled.term).isSome = true := by
  have accepted := congrArg Option.isSome
    applySelected_target_synthesizes_exact_indices
  simpa [ManySortedFC.Tm.synth] using accepted

/-- The compiled return program is genuinely a function computation, not the
placeholder unit term used by the superseded compiler sketch. -/
theorem returnSelected_target_is_not_unit :
    returnSelectedCompiled.term ≠ (.unit : Target.Tm []) := by
  intro termEquality
  have typing := returnSelected_target_is_well_typed
  rw [termEquality] at typing
  cases typing

end ComputationalRegression

end DOTCaptureToManySortedFC.Acyclic.TermTranslation
