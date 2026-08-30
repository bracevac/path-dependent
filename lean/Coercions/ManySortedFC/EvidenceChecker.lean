import Coercions.ManySortedFC.Evidence

/-!
# Structural checker for many-sorted logical evidence

The checker synthesizes the exact proposition proved by an explicit logical
certificate. It follows certificate syntax recursively and performs equality
tests only where two independently synthesized endpoints must meet:
transitivity and capture-union elimination.

No branch invokes subtyping, subcapturing, constraint solving, or a structural
adapter. A successful result contains its declarative `Evidence.Proves`
derivation by construction.
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

/-- Soundness is carried by every successful checker result. -/
theorem check_sound {scope : Sig} {context : Ctx scope}
    {relation : Relation} {evidence : Evidence relation scope}
    {checked : Checked context evidence}
    (_accepted : check context evidence = some checked) :
    Nonempty (Proves context evidence checked.proposition) :=
  ⟨checked.typing⟩

end ManySortedFC.Evidence
