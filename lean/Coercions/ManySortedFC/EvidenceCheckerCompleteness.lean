import Coercions.ManySortedFC.EvidenceChecker

/-!
# Completeness of the many-sorted evidence checker

Every declarative evidence derivation is reflected by the structural checker
at its exact intrinsically sorted proposition.
-/

namespace ManySortedFC
namespace Evidence

/-- Checking declaratively valid evidence recovers its exact proposition. -/
theorem check_complete_projection {scope : Sig}
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

/-- Exact proof-producing completeness, without projecting the proposition. -/
theorem check_complete {scope : Sig}
    {context : Ctx scope} {relation : Relation}
    {evidence : Evidence relation scope}
    {proposition : Proposition relation scope}
    (typing : Proves context evidence proposition) :
    ∃ checkedTyping,
      check context evidence = some ⟨proposition, checkedTyping⟩ := by
  obtain ⟨checked, checkedEq, propositionEq⟩ :=
    Option.map_eq_some_iff.mp (check_complete_projection typing)
  cases checked with
  | mk checkedProposition checkedTyping =>
      dsimp at propositionEq
      subst checkedProposition
      exact ⟨checkedTyping, checkedEq⟩

end Evidence
end ManySortedFC
