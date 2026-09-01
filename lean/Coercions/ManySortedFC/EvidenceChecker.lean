import Coercions.ManySortedFC.Evidence

/-!
# Structural checker for many-sorted logical evidence

The checker synthesizes the exact proposition proved by an explicit logical
certificate. It follows certificate syntax recursively and performs equality
tests only where independently synthesized endpoints must meet.

No branch invokes ambient subtyping, subcapturing, constraint solving, or a
structural adapter.  The classifier-projection branches recompute only the
decidable ground relations on closed classifier kinds.  A successful result
contains its declarative `Evidence.Proves` derivation by construction.
-/

namespace ManySortedFC.Evidence

/-- Structurally synthesize the proposition proved by a logical certificate. -/
def check {scope : Sig} (context : Ctx scope) :
    {relation : Relation} -> (evidence : Evidence relation scope) ->
      Option (Checked context evidence)
  | _, .var index =>
      match binding : context.lookup index with
      | .evidence proposition =>
          some ⟨proposition, .var binding⟩

  | _, .equalityRefl expression =>
      some ⟨.equality expression expression, .equalityRefl expression⟩
  | _, .equalitySymm inner => do
      let checked ← check context inner
      let ⟨proposition, typing⟩ := checked
      match proposition with
      | .equality left right =>
          pure ⟨.equality right left, .equalitySymm typing⟩
  | _, .equalityTrans first second => do
      let firstChecked ← check context first
      let secondChecked ← check context second
      let ⟨firstProposition, firstTyping⟩ := firstChecked
      let ⟨secondProposition, secondTyping⟩ := secondChecked
      match firstProposition, secondProposition with
      | .equality left firstMiddle, .equality secondMiddle right =>
          if middleMatches : firstMiddle = secondMiddle then
            let alignedSecondTyping : Proves context second
                (.equality firstMiddle right) := by
              simpa [middleMatches] using secondTyping
            pure ⟨.equality left right,
              .equalityTrans firstTyping alignedSecondTyping⟩
          else
            none
  | _, .unfoldRec bodies index =>
      if guarded : bodies.headGuarded then
        some ⟨
          .equality (.type (.recProj bodies index))
            (.type (bodies.unfoldAt index)),
          .unfoldRec guarded⟩
      else
        none
  | _, .equalityArrow domain codomain => do
      let domainChecked ← check context domain
      let codomainChecked ← check context codomain
      let ⟨domainProposition, domainTyping⟩ := domainChecked
      let ⟨codomainProposition, codomainTyping⟩ := codomainChecked
      match domainProposition, codomainProposition with
      | .equality (.type sourceDomain) (.type targetDomain),
          .equality (.type sourceCodomain) (.type targetCodomain) =>
          pure ⟨
            .equality (.type (.arr sourceDomain sourceCodomain))
              (.type (.arr targetDomain targetCodomain)),
            .equalityArrow domainTyping codomainTyping⟩
  | _, .equalityCapturing captures shape => do
      let capturesChecked ← check context captures
      let shapeChecked ← check context shape
      let ⟨capturesProposition, capturesTyping⟩ := capturesChecked
      let ⟨shapeProposition, shapeTyping⟩ := shapeChecked
      match capturesProposition, shapeProposition with
      | .equality (.capture sourceCapture) (.capture targetCapture),
          .equality (.type sourceShape) (.type targetShape) =>
          pure ⟨
            .equality (.type (.capturing sourceCapture sourceShape))
              (.type (.capturing targetCapture targetShape)),
            .equalityCapturing capturesTyping shapeTyping⟩
  | _, .equalityCaptureUnion left right => do
      let leftChecked ← check context left
      let rightChecked ← check context right
      let ⟨leftProposition, leftTyping⟩ := leftChecked
      let ⟨rightProposition, rightTyping⟩ := rightChecked
      match leftProposition, rightProposition with
      | .equality (.capture sourceLeft) (.capture targetLeft),
          .equality (.capture sourceRight) (.capture targetRight) =>
          pure ⟨
            .equality (.capture (.union sourceLeft sourceRight))
              (.capture (.union targetLeft targetRight)),
            .equalityCaptureUnion leftTyping rightTyping⟩
  | _, .equalityCaptureReadOnly capture => do
      let checked ← check context capture
      let ⟨proposition, typing⟩ := checked
      match proposition with
      | .equality (.capture source) (.capture target) =>
          pure ⟨
            .equality (.capture (.readOnly source))
              (.capture (.readOnly target)),
            .equalityCaptureReadOnly typing⟩
  | _, .classifierGroundEquality left right =>
      if equivalent : Classifier.Kind.Equivalent left right then
        some ⟨
          .equality (.classifier (.ground left))
            (.classifier (.ground right)),
          .classifierGroundEquality left right equivalent⟩
      else
        none
  | _, .equalityCaptureProjectScoped capture classifier => do
      let captureChecked ← check context capture
      let classifierChecked ← check context classifier
      let ⟨captureProposition, captureTyping⟩ := captureChecked
      let ⟨classifierProposition, classifierTyping⟩ := classifierChecked
      match captureProposition, classifierProposition with
      | .equality (.capture sourceCapture) (.capture targetCapture),
          .equality (.classifier sourceKind) (.classifier targetKind) =>
          pure ⟨
            .equality (.capture (.project sourceCapture sourceKind))
              (.capture (.project targetCapture targetKind)),
            .equalityCaptureProjectScoped captureTyping classifierTyping⟩
  | _, .equalityCaptureProject equality sourceKind targetKind => do
      let checked ← check context equality
      let ⟨proposition, typing⟩ := checked
      match proposition with
      | .equality (.capture source) (.capture target) =>
          if equivalent : Classifier.Kind.Equivalent sourceKind targetKind then
            pure ⟨
              .equality (.capture (.project source sourceKind))
                (.capture (.project target targetKind)),
              .equalityCaptureProject typing equivalent⟩
          else
            none
  | _, .equalityCaptureProjectTop capture =>
      some ⟨
        .equality
          (.capture (.project capture (.ground Classifier.Kind.top)))
          (.capture capture),
        .equalityCaptureProjectTop capture⟩
  | _, .equalityCaptureProjectCompose capture innerKind outerKind =>
      some ⟨
        .equality
          (.capture (.project (.project capture innerKind) outerKind))
          (.capture (.project capture (outerKind.intersect innerKind))),
        .equalityCaptureProjectCompose capture innerKind outerKind⟩
  | _, .equalityCaptureProjectEmpty capture kind =>
      if emptyKind : Classifier.Kind.IsEmpty kind then
        some ⟨
          .equality (.capture (.project capture kind)) (.capture .empty),
          .equalityCaptureProjectEmpty capture kind emptyKind⟩
      else
        none
  | _, .equalityCaptureProjectComplete membership => do
      let checked ← check context membership
      let ⟨proposition, typing⟩ := checked
      match proposition with
      | .captureHasKind capture kind =>
          pure ⟨
            .equality (.capture (.project capture kind)) (.capture capture),
            .equalityCaptureProjectComplete typing⟩

  | _, .inclusionRefl expression =>
      some ⟨.inclusion expression expression, .inclusionRefl expression⟩
  | _, .inclusionTrans first second => do
      let firstChecked ← check context first
      let secondChecked ← check context second
      let ⟨firstProposition, firstTyping⟩ := firstChecked
      let ⟨secondProposition, secondTyping⟩ := secondChecked
      match firstProposition, secondProposition with
      | .inclusion lower firstMiddle, .inclusion secondMiddle upper =>
          if middleMatches : firstMiddle = secondMiddle then
            let alignedSecondTyping : Proves context second
                (.inclusion firstMiddle upper) := by
              simpa [middleMatches] using secondTyping
            pure ⟨.inclusion lower upper,
              .inclusionTrans firstTyping alignedSecondTyping⟩
          else
            none
  | _, .equalityToInclusion equality => do
      let checked ← check context equality
      let ⟨proposition, typing⟩ := checked
      match proposition with
      | .equality left right =>
          pure ⟨.inclusion left right,
            .equalityToInclusion typing⟩

  | _, .typeTop source =>
      some ⟨.inclusion (.type source) (.type .top), .typeTop source⟩
  | _, .typeBottom target =>
      some ⟨.inclusion (.type .bot) (.type target), .typeBottom target⟩
  | _, .typeArrow domain codomain => do
      let domainChecked ← check context domain
      let codomainChecked ← check context codomain
      let ⟨domainProposition, domainTyping⟩ := domainChecked
      let ⟨codomainProposition, codomainTyping⟩ := codomainChecked
      match domainProposition, codomainProposition with
      | .inclusion (.type targetDomain) (.type sourceDomain),
          .inclusion (.type sourceCodomain) (.type targetCodomain) =>
          pure ⟨
            .inclusion (.type (.arr sourceDomain sourceCodomain))
              (.type (.arr targetDomain targetCodomain)),
            .typeArrow domainTyping codomainTyping⟩
  | _, .typeCapturing captures shape => do
      let capturesChecked ← check context captures
      let shapeChecked ← check context shape
      let ⟨capturesProposition, capturesTyping⟩ := capturesChecked
      let ⟨shapeProposition, shapeTyping⟩ := shapeChecked
      match capturesProposition, shapeProposition with
      | .inclusion (.capture sourceCapture) (.capture targetCapture),
          .inclusion (.type sourceShape) (.type targetShape) =>
          pure ⟨
            .inclusion (.type (.capturing sourceCapture sourceShape))
              (.type (.capturing targetCapture targetShape)),
            .typeCapturing capturesTyping shapeTyping⟩

  | _, .classifierGroundInclusion lower upper =>
      if included : Classifier.Kind.Subkind lower upper then
        some ⟨
          .inclusion (.classifier (.ground lower))
            (.classifier (.ground upper)),
          .classifierGroundInclusion lower upper included⟩
      else
        none
  | _, .classifierExclude kind allowedKind excludedKind allowed excluded => do
      let allowedChecked ← check context allowed
      let excludedChecked ← check context excluded
      let ⟨allowedProposition, allowedTyping⟩ := allowedChecked
      let ⟨excludedProposition, excludedTyping⟩ := excludedChecked
      if allowedMatches : allowedProposition =
          .inclusion (.classifier kind) (.classifier (.ground allowedKind)) then
        if excludedMatches : excludedProposition =
            .classifierDisjoint kind (.ground excludedKind) then
          let alignedAllowedTyping : Proves context allowed
              (.inclusion (.classifier kind)
                (.classifier (.ground allowedKind))) := by
            simpa [allowedMatches] using allowedTyping
          let alignedExcludedTyping : Proves context excluded
              (.classifierDisjoint kind (.ground excludedKind)) := by
            simpa [excludedMatches] using excludedTyping
          pure ⟨
            .inclusion (.classifier kind)
              (.classifier (.ground
                (Classifier.Kind.subtract allowedKind excludedKind))),
            .classifierExclude alignedAllowedTyping alignedExcludedTyping⟩
        else
          none
      else
        none

  | _, .captureEmpty target =>
      some ⟨.inclusion (.capture .empty) (.capture target),
        .captureEmpty target⟩
  | _, .captureUnionLeft left right =>
      some ⟨.inclusion (.capture left) (.capture (.union left right)),
        .captureUnionLeft left right⟩
  | _, .captureUnionRight left right =>
      some ⟨.inclusion (.capture right) (.capture (.union left right)),
        .captureUnionRight left right⟩
  | _, .captureUnionElim left right => do
      let leftChecked ← check context left
      let rightChecked ← check context right
      let ⟨leftProposition, leftTyping⟩ := leftChecked
      let ⟨rightProposition, rightTyping⟩ := rightChecked
      match leftProposition, rightProposition with
      | .inclusion (.capture leftCapture) (.capture leftTarget),
          .inclusion (.capture rightCapture) (.capture rightTarget) =>
          if targetMatches : leftTarget = rightTarget then
            let alignedRightTyping : Proves context right
                (.inclusion (.capture rightCapture)
                  (.capture leftTarget)) := by
              simpa [targetMatches] using rightTyping
            pure ⟨
              .inclusion (.capture (.union leftCapture rightCapture))
                (.capture leftTarget),
              .captureUnionElim leftTyping alignedRightTyping⟩
          else
            none
  | _, .captureVariable index =>
      match binding : context.lookup index with
      | .term (.capturing captures shape) =>
          some ⟨.inclusion (.capture (.singleton index))
              (.capture captures),
            .captureVariable binding⟩
      | .term _ => none
  | _, .captureReadOnly capture =>
      some ⟨.inclusion (.capture (.readOnly capture)) (.capture capture),
        .captureReadOnly capture⟩
  | _, .captureReadOnlyMono subcapture => do
      let checked ← check context subcapture
      let ⟨proposition, typing⟩ := checked
      match proposition with
      | .inclusion (.capture lower) (.capture upper) =>
          pure ⟨
            .inclusion (.capture (.readOnly lower))
              (.capture (.readOnly upper)),
            .captureReadOnlyMono typing⟩
  | _, .captureProjectSource capture kind =>
      some ⟨
        .inclusion (.capture (.project capture kind)) (.capture capture),
        .captureProjectSource capture kind⟩
  | _, .captureProjectSourceScoped capture kind =>
      some ⟨
        .inclusion (.capture (.project capture kind)) (.capture capture),
        .captureProjectSourceScoped capture kind⟩
  | _, .captureProjectMono subcapture sourceKind targetKind => do
      let checked ← check context subcapture
      let ⟨proposition, typing⟩ := checked
      match proposition with
      | .inclusion (.capture source) (.capture target) =>
          if kindSubtyping :
              Classifier.Kind.Subkind sourceKind targetKind then
            pure ⟨
              .inclusion (.capture (.project source sourceKind))
                (.capture (.project target targetKind)),
              .captureProjectMono typing kindSubtyping⟩
          else
            none
  | _, .captureProjectMonoScoped subcapture subclassifier => do
      let captureChecked ← check context subcapture
      let classifierChecked ← check context subclassifier
      let ⟨captureProposition, captureTyping⟩ := captureChecked
      let ⟨classifierProposition, classifierTyping⟩ := classifierChecked
      match captureProposition, classifierProposition with
      | .inclusion (.capture sourceCapture) (.capture targetCapture),
          .inclusion (.classifier sourceKind) (.classifier targetKind) =>
          pure ⟨
            .inclusion (.capture (.project sourceCapture sourceKind))
              (.capture (.project targetCapture targetKind)),
            .captureProjectMonoScoped captureTyping classifierTyping⟩
  | _, .captureProjectMerge capture leftKind rightKind =>
      some ⟨
        .inclusion (.capture (.project capture (leftKind ++ rightKind)))
          (.capture (.union (.project capture leftKind)
            (.project capture rightKind))),
        .captureProjectMerge capture leftKind rightKind⟩

  | _, .modeEmpty mode =>
      some ⟨.mode (mode := mode) .empty, .modeEmpty mode⟩
  | _, .modeUnion left right => do
      let leftChecked ← check context left
      let rightChecked ← check context right
      let ⟨leftProposition, leftTyping⟩ := leftChecked
      let ⟨rightProposition, rightTyping⟩ := rightChecked
      match leftProposition, rightProposition with
      | .mode leftCapture, .mode rightCapture =>
          pure ⟨.mode (.union leftCapture rightCapture),
            .modeUnion leftTyping rightTyping⟩
  | _, .modeSubcapture subcapture upperMode => do
      let subcaptureChecked ← check context subcapture
      let modeChecked ← check context upperMode
      let ⟨subcaptureProposition, subcaptureTyping⟩ := subcaptureChecked
      let ⟨modeProposition, modeTyping⟩ := modeChecked
      match subcaptureProposition, modeProposition with
      | .inclusion (.capture lower) (.capture inclusionUpper),
          .mode modeUpper =>
          if upperMatches : inclusionUpper = modeUpper then
            let alignedModeTyping : Proves context upperMode
                (.mode inclusionUpper) := by
              simpa [upperMatches] using modeTyping
            pure ⟨.mode lower,
              .modeSubcapture subcaptureTyping alignedModeTyping⟩
          else
            none
  | _, .modeWritable capture =>
      some ⟨.mode (mode := .writable) capture, .modeWritable capture⟩
  | _, .modeReadOnly capture =>
      some ⟨.mode (mode := .readOnly) (.readOnly capture),
        .modeReadOnly capture⟩

  | _, .separateSymm evidence => do
      let checked ← check context evidence
      let ⟨proposition, typing⟩ := checked
      match proposition with
      | .separate left right =>
          pure ⟨.separate right left, .separateSymm typing⟩
  | _, .separateUnion left right => do
      let leftChecked ← check context left
      let rightChecked ← check context right
      let ⟨leftProposition, leftTyping⟩ := leftChecked
      let ⟨rightProposition, rightTyping⟩ := rightChecked
      match leftProposition, rightProposition with
      | .separate leftCapture leftOther,
          .separate rightCapture rightOther =>
          if otherMatches : leftOther = rightOther then
            let alignedRightTyping : Proves context right
                (.separate rightCapture leftOther) := by
              simpa [otherMatches] using rightTyping
            pure ⟨.separate (.union leftCapture rightCapture) leftOther,
              .separateUnion leftTyping alignedRightTyping⟩
          else
            none
  | _, .separateEmpty capture =>
      some ⟨.separate .empty capture, .separateEmpty capture⟩
  | _, .separateReadOnly left right => do
      let leftChecked ← check context left
      let rightChecked ← check context right
      let ⟨leftProposition, leftTyping⟩ := leftChecked
      let ⟨rightProposition, rightTyping⟩ := rightChecked
      match leftProposition, rightProposition with
      | .mode leftCapture, .mode rightCapture =>
          pure ⟨.separate leftCapture rightCapture,
            .separateReadOnly leftTyping rightTyping⟩
  | _, .separateSubcapture subcapture separation => do
      let subcaptureChecked ← check context subcapture
      let separationChecked ← check context separation
      let ⟨subcaptureProposition, subcaptureTyping⟩ := subcaptureChecked
      let ⟨separationProposition, separationTyping⟩ := separationChecked
      match subcaptureProposition, separationProposition with
      | .inclusion (.capture lower) (.capture inclusionUpper),
          .separate separationUpper other =>
          if upperMatches : inclusionUpper = separationUpper then
            let alignedSeparationTyping : Proves context separation
                (.separate inclusionUpper other) := by
              simpa [upperMatches] using separationTyping
            pure ⟨.separate lower other,
              .separateSubcapture subcaptureTyping alignedSeparationTyping⟩
          else
            none
  | _, .separateOfDisjoint disjoint => do
      let checked ← check context disjoint
      let ⟨proposition, typing⟩ := checked
      match proposition with
      | .disjoint left right =>
          pure ⟨.separate left right, .separateOfDisjoint typing⟩

  | _, .disjointSymm evidence => do
      let checked ← check context evidence
      let ⟨proposition, typing⟩ := checked
      match proposition with
      | .disjoint left right =>
          pure ⟨.disjoint right left, .disjointSymm typing⟩
  | _, .disjointUnion left right => do
      let leftChecked ← check context left
      let rightChecked ← check context right
      let ⟨leftProposition, leftTyping⟩ := leftChecked
      let ⟨rightProposition, rightTyping⟩ := rightChecked
      match leftProposition, rightProposition with
      | .disjoint leftCapture leftOther,
          .disjoint rightCapture rightOther =>
          if otherMatches : leftOther = rightOther then
            let alignedRightTyping : Proves context right
                (.disjoint rightCapture leftOther) := by
              simpa [otherMatches] using rightTyping
            pure ⟨.disjoint (.union leftCapture rightCapture) leftOther,
              .disjointUnion leftTyping alignedRightTyping⟩
          else
            none
  | _, .disjointEmpty capture =>
      some ⟨.disjoint .empty capture, .disjointEmpty capture⟩
  | _, .disjointEquality equality disjoint => do
      let equalityChecked ← check context equality
      let disjointChecked ← check context disjoint
      let ⟨equalityProposition, equalityTyping⟩ := equalityChecked
      let ⟨disjointProposition, disjointTyping⟩ := disjointChecked
      match equalityProposition, disjointProposition with
      | .equality (.capture replacement) (.capture equalityOriginal),
          .disjoint disjointOriginal other =>
          if originalMatches : equalityOriginal = disjointOriginal then
            let alignedDisjointTyping : Proves context disjoint
                (.disjoint equalityOriginal other) := by
              simpa [originalMatches] using disjointTyping
            pure ⟨.disjoint replacement other,
              .disjointEquality equalityTyping alignedDisjointTyping⟩
          else
            none
  | _, .disjointCaptureProject leftCapture leftKind rightCapture rightKind =>
      if kindDisjoint : Classifier.Kind.Disjoint leftKind rightKind then
        some ⟨
          .disjoint (.project leftCapture leftKind)
            (.project rightCapture rightKind),
          .disjointCaptureProject leftCapture leftKind rightCapture rightKind
            kindDisjoint⟩
      else
        none
  | _, .classifierGroundDisjoint left right =>
      if disjoint : Classifier.Kind.Disjoint left right then
        some ⟨.classifierDisjoint (.ground left) (.ground right),
          .classifierGroundDisjoint left right disjoint⟩
      else
        none
  | _, .classifierDisjointSymm evidence => do
      let checked ← check context evidence
      let ⟨proposition, typing⟩ := checked
      match proposition with
      | .classifierDisjoint left right =>
          pure ⟨.classifierDisjoint right left,
            .classifierDisjointSymm typing⟩
  | _, .disjointCaptureProjectScoped leftCapture rightCapture classifiers => do
      let checked ← check context classifiers
      let ⟨proposition, typing⟩ := checked
      match proposition with
      | .classifierDisjoint leftKind rightKind =>
          pure ⟨
            .disjoint (.project leftCapture leftKind)
              (.project rightCapture rightKind),
            .disjointCaptureProjectScoped leftCapture rightCapture typing⟩
  | _, .captureHasKindEmpty kind =>
      some ⟨.captureHasKind .empty kind, .captureHasKindEmpty kind⟩
  | _, .captureHasKindUnion left right => do
      let leftChecked ← check context left
      let rightChecked ← check context right
      let ⟨leftProposition, leftTyping⟩ := leftChecked
      let ⟨rightProposition, rightTyping⟩ := rightChecked
      match leftProposition, rightProposition with
      | .captureHasKind leftCapture leftKind,
          .captureHasKind rightCapture rightKind =>
          if kindMatches : leftKind = rightKind then
            let alignedRightTyping : Proves context right
                (.captureHasKind rightCapture leftKind) := by
              simpa [kindMatches] using rightTyping
            pure ⟨.captureHasKind (.union leftCapture rightCapture) leftKind,
              .captureHasKindUnion leftTyping alignedRightTyping⟩
          else
            none
  | _, .captureHasKindProject capture kind =>
      some ⟨.captureHasKind (.project capture kind) kind,
        .captureHasKindProject capture kind⟩
  | _, .captureHasKindSubcapture subcapture upper => do
      let subcaptureChecked ← check context subcapture
      let upperChecked ← check context upper
      let ⟨subcaptureProposition, subcaptureTyping⟩ := subcaptureChecked
      let ⟨upperProposition, upperTyping⟩ := upperChecked
      match subcaptureProposition, upperProposition with
      | .inclusion (.capture lowerCapture) (.capture inclusionUpper),
          .captureHasKind membershipUpper kind =>
          if upperMatches : inclusionUpper = membershipUpper then
            let alignedUpperTyping : Proves context upper
                (.captureHasKind inclusionUpper kind) := by
              simpa [upperMatches] using upperTyping
            pure ⟨.captureHasKind lowerCapture kind,
              .captureHasKindSubcapture subcaptureTyping alignedUpperTyping⟩
          else
            none
  | _, .captureHasKindWiden membership subclassifier => do
      let membershipChecked ← check context membership
      let classifierChecked ← check context subclassifier
      let ⟨membershipProposition, membershipTyping⟩ := membershipChecked
      let ⟨classifierProposition, classifierTyping⟩ := classifierChecked
      match membershipProposition, classifierProposition with
      | .captureHasKind capture membershipKind,
          .inclusion (.classifier inclusionLower)
            (.classifier inclusionUpper) =>
          if lowerMatches : membershipKind = inclusionLower then
            let alignedClassifierTyping : Proves context subclassifier
                (.inclusion (.classifier membershipKind)
                  (.classifier inclusionUpper)) := by
              simpa [lowerMatches] using classifierTyping
            pure ⟨.captureHasKind capture inclusionUpper,
              .captureHasKindWiden membershipTyping alignedClassifierTyping⟩
          else
            none

/-- Soundness is carried by every successful checker result. -/
theorem check_sound {scope : Sig} {context : Ctx scope}
    {relation : Relation} {evidence : Evidence relation scope}
    {checked : Checked context evidence}
    (_accepted : check context evidence = some checked) :
    Nonempty (Proves context evidence checked.proposition) :=
  ⟨checked.typing⟩

namespace CaptureVariableExamples

/-- An explicitly captured term binding exposes its declared outer capture
to the structural evidence checker. -/
example :
    (check (Ctx.nil.extendTerm (.capturing .empty .one))
      (.captureVariable (.here : BVar ([] ▹ .term) .term))).map
        Checked.proposition =
      some (.inclusion
        (.capture (.singleton (.here : BVar ([] ▹ .term) .term)))
        (.capture .empty)) := by
  rfl

/-- A bare term binding remains a capture root; the checker cannot synthesize
the corresponding contraction to the accounting default `empty`. -/
example :
    check (Ctx.nil.extendTerm .one)
      (.captureVariable (.here : BVar ([] ▹ .term) .term)) = none := by
  rfl

end CaptureVariableExamples

end ManySortedFC.Evidence
