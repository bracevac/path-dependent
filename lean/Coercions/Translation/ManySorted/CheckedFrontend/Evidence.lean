import Coercions.Translation.ManySorted.CheckedFrontend.Source

/-!
# Structural checking of source certificates

The checker follows the supplied constructor tree exactly.  Transitivity has
an explicit middle expression, and structural rules recursively check their
premises.  Lexical-bound constructors name the exact static variable whose
declared endpoint is consulted.  The checker never searches a context for a
useful path or invents a bound.
-/

namespace DOTCaptureToManySortedFC.CheckedFrontend

namespace Evidence

open DOTCapture.ModalIntersections

/-- Check a first-order inclusion certificate against its claimed endpoints. -/
def check {scope : Source.Sig} (context : Ctx scope) :
    {sort : Source.StaticSort} ->
    (source target : Source.StaticExpr sort scope) ->
    Certificate scope sort ->
    Option (Includes context source target)
  | _, source, target, .refl =>
      if equal : source = target then
        some (equal ▸ .refl)
      else
        none
  | _, source, target, .trans middle first second => do
      let firstProof <- check context source middle first
      let secondProof <- check context middle target second
      pure (.trans firstProof secondProof)
  | _, source, target, .boundLower name =>
      match found : context.lookupStatic name with
      | .bounds (.some declaredLower) upper =>
          if sourceMatches : source = declaredLower then
            if targetMatches : target =
                DOTCapture.ModalIntersections.StaticExpr.bound name then
              by
                subst source
                subst target
                exact some (.lower (.bound found))
            else
              none
          else
            none
      | _ => none
  | _, source, target, .boundUpper name =>
      match found : context.lookupStatic name with
      | .bounds lower (.some declaredUpper) =>
          if sourceMatches : source =
              DOTCapture.ModalIntersections.StaticExpr.bound name then
            if targetMatches : target = declaredUpper then
              by
                subst source
                subst target
                exact some (.upper (.bound found))
            else
              none
          else
            none
      | _ => none
  | .type, source, target, .typeTop =>
      match source, target with
      | .type sourceType, .type .top => some .typeTop
      | _, _ => none
  | .type, source, target, .typeBottom =>
      match source, target with
      | .type .bot, .type targetType => some .typeBottom
      | _, _ => none
  | .type, source, target, .typeArrow domain codomain =>
      match source, target with
      | .type (.arr sourceDomain sourceCodomain),
          .type (.arr targetDomain targetCodomain) => do
          let domainProof <- check context (.type targetDomain)
            (.type sourceDomain) domain
          let codomainProof <- check context (.type sourceCodomain)
            (.type targetCodomain) codomain
          pure (.typeArrow domainProof codomainProof)
      | _, _ => none
  | .type, source, target, .typeCapturing captures shape =>
      match source, target with
      | .type (.capturing sourceCapture sourceShape),
          .type (.capturing targetCapture targetShape) => do
          let captureProof <- check context (.capture sourceCapture)
            (.capture targetCapture) captures
          let shapeProof <- check context (.type sourceShape)
            (.type targetShape) shape
          pure (.typeCapturing captureProof shapeProof)
      | _, _ => none
  | .capture, source, target, .captureEmpty =>
      match source, target with
      | .capture .empty, .capture targetCapture => some .captureEmpty
      | _, _ => none
  | .capture, source, target, .captureUnionLeft =>
      match source, target with
      | .capture left, .capture (.union targetLeft right) =>
          if equal : left = targetLeft then
            some (equal ▸ .captureUnionLeft)
          else
            none
      | _, _ => none
  | .capture, source, target, .captureUnionRight =>
      match source, target with
      | .capture right, .capture (.union left targetRight) =>
          if equal : right = targetRight then
            some (equal ▸ .captureUnionRight)
          else
            none
      | _, _ => none
  | .capture, source, target, .captureUnionElim left right =>
      match source, target with
      | .capture (.union sourceLeft sourceRight), .capture targetCapture => do
          let leftProof <- check context (.capture sourceLeft)
            (.capture targetCapture) left
          let rightProof <- check context (.capture sourceRight)
            (.capture targetCapture) right
          pure (.captureUnionElim leftProof rightProof)
      | _, _ => none
  | .capture, source, target, .captureReadOnly =>
      match source, target with
      | .capture (.readOnly sourceCapture), .capture targetCapture =>
          if equal : sourceCapture = targetCapture then
            some (equal ▸ .captureReadOnly)
          else
            none
      | _, _ => none
  | .capture, source, target, .captureReadOnlyMono inner =>
      match source, target with
      | .capture (.readOnly sourceCapture),
          .capture (.readOnly targetCapture) => do
          let proof <- check context (.capture sourceCapture)
            (.capture targetCapture) inner
          pure (.captureReadOnlyMono proof)
      | _, _ => none
  | .capture, source, target, .captureVariable certificateName =>
      match source, target with
      | .capture (.singleton (.var sourceName)), .capture targetCapture =>
          if nameMatches : sourceName = certificateName then
            match found : context.lookupTerm certificateName with
            | .capturing declaredCapture shape =>
                if captureMatches : declaredCapture = targetCapture then
                  by
                    subst sourceName
                    subst targetCapture
                    exact some (.captureVariable found)
                else
                  none
            | _ => none
          else
            none
      | _, _ => none

/-- Check the endpoint obligations selected by an interval's exact shape. -/
def checkInterval {scope : Source.Sig} (context : Ctx scope)
    {sort : Source.StaticSort} (witness : Source.StaticExpr sort scope)
    (interval : Source.Interval sort scope)
    (certificate : IntervalCertificate scope sort) :
    Option (Interval.SatisfiedBy context witness interval) :=
  match interval, certificate with
  | .bounds .none .none, .unbounded => some .unbounded
  | .bounds (.some lower) .none, .lower evidence => do
      let proof <- check context lower witness evidence
      pure (.lower proof)
  | .bounds .none (.some upper), .upper evidence => do
      let proof <- check context witness upper evidence
      pure (.upper proof)
  | .bounds (.some lower) (.some upper), .between lowerEvidence upperEvidence => do
      let lowerProof <- check context lower witness lowerEvidence
      let upperProof <- check context witness upper upperEvidence
      pure (.between lowerProof upperProof)
  | _, _ => none

/-- Check a structural adapter certificate without searching for subtyping. -/
def checkAdapter {scope : Source.Sig} (environment : Source.TypingEnv scope) :
    (source target : Source.Ty scope) -> AdapterCertificate scope ->
      Option (Adapts environment source target)
  | source, target, .identity =>
      if equal : source = target then
        some (equal ▸ .identity)
      else
        none
  | source, target, .cast certificate => do
      let proof <- check environment.bindings (.type source) (.type target)
        certificate
      pure (.cast proof)
  | source, target, .compose middle first second => do
      let firstProof <- checkAdapter environment source middle first
      let secondProof <- checkAdapter environment middle target second
      pure (.compose firstProof secondProof)
  | source, target, .function domain codomain =>
      match source, target with
      | .arr sourceDomain sourceCodomain, .arr targetDomain targetCodomain => do
          let domainProof <- checkAdapter environment targetDomain sourceDomain
            domain
          let codomainProof <- checkAdapter environment sourceCodomain
            targetCodomain codomain
          pure (.function domainProof codomainProof)
      | _, _ => none
  | source, target, .captured subcapture inner =>
      match source, target with
      | .capturing sourceCapture sourceShape,
          .capturing targetCapture targetShape => do
          let captureProof <- check environment.bindings
            (.capture sourceCapture) (.capture targetCapture) subcapture
          let innerProof <- checkAdapter environment sourceShape targetShape
            inner
          pure (.captured captureProof innerProof)
      | _, _ => none

/-! ## Modal certificate checking -/

/-- Check one structural access-mode certificate.  Lock-frame lookup has no
certificate constructor in this fragment. -/
def checkMode {scope : Source.Sig} (context : Ctx scope)
    (assumptions : ModalAssumptions scope) :
    (capture : Capture scope) -> (mode : CaptureMode) ->
      ModeCertificate scope -> Option (Mode context assumptions capture mode)
  | .empty, mode, .empty => some (.empty mode)
  | .union left right, mode, .union leftCertificate rightCertificate => do
      let leftProof <- checkMode context assumptions left mode leftCertificate
      let rightProof <- checkMode context assumptions right mode rightCertificate
      pure (.union leftProof rightProof)
  | lower, mode, .subcapture upper inclusion upperCertificate => do
      let inclusionProof <- check context (.capture lower) (.capture upper)
        inclusion
      let upperProof <- checkMode context assumptions upper mode
        upperCertificate
      pure (.subcapture inclusionProof upperProof)
  | capture, .writable, .writable => some (.writable capture)
  | .readOnly capture, .readOnly, .readOnly => some (.readOnly capture)
  | _, _, _ => none

/-- Check structural capture equality. -/
def checkCaptureEquality {scope : Source.Sig} (context : Ctx scope) :
    (left right : Capture scope) -> CaptureEqualityCertificate scope ->
      Option (CaptureEquality context left right)
  | left, right, .refl =>
      if equal : left = right then
        by
          subst right
          exact some (.refl left)
      else
        none
  | left, right, .symm inner => do
      let proof <- checkCaptureEquality context right left inner
      pure (.symm proof)
  | left, right, .trans middle first second => do
      let firstProof <- checkCaptureEquality context left middle first
      let secondProof <- checkCaptureEquality context middle right second
      pure (.trans firstProof secondProof)
  | .union left₁ right₁, .union left₂ right₂,
      .union leftCertificate rightCertificate => do
      let leftProof <- checkCaptureEquality context left₁ left₂ leftCertificate
      let rightProof <- checkCaptureEquality context right₁ right₂
        rightCertificate
      pure (.union leftProof rightProof)
  | .readOnly left, .readOnly right, .readOnly inner => do
      let proof <- checkCaptureEquality context left right inner
      pure (.readOnly proof)
  | _, _, _ => none

/-- Check resource disjointness without consulting modal assumptions. -/
def checkDisjoint {scope : Source.Sig} (context : Ctx scope) :
    (left right : Capture scope) -> DisjointCertificate scope ->
      Option (Disjoint context left right)
  | .empty, right, .empty => some (.empty right)
  | left, right, .symm inner => do
      let proof <- checkDisjoint context right left inner
      pure (.symm proof)
  | .union left right, other, .union leftCertificate rightCertificate => do
      let leftProof <- checkDisjoint context left other leftCertificate
      let rightProof <- checkDisjoint context right other rightCertificate
      pure (.union leftProof rightProof)
  | replacement, other, .equality original equality disjoint => do
      let equalityProof <- checkCaptureEquality context replacement original
        equality
      let disjointProof <- checkDisjoint context original other disjoint
      pure (.equality equalityProof disjointProof)
  | _, _, _ => none

/-- Check access separation.  This subset supports structural rules,
read-only sharing, and injection of independently checked disjointness. -/
def checkSeparate {scope : Source.Sig} (context : Ctx scope)
    (assumptions : ModalAssumptions scope) :
    (left right : Capture scope) -> SeparateCertificate scope ->
      Option (Separate context assumptions left right)
  | .empty, right, .empty => some (.empty right)
  | left, right, .symm inner => do
      let proof <- checkSeparate context assumptions right left inner
      pure (.symm proof)
  | .union left right, other, .union leftCertificate rightCertificate => do
      let leftProof <- checkSeparate context assumptions left other
        leftCertificate
      let rightProof <- checkSeparate context assumptions right other
        rightCertificate
      pure (.union leftProof rightProof)
  | lower, other, .subcapture upper inclusion separation => do
      let inclusionProof <- check context (.capture lower) (.capture upper)
        inclusion
      let separationProof <- checkSeparate context assumptions upper other
        separation
      pure (.subcapture inclusionProof separationProof)
  | left, right, .readOnly leftMode rightMode => do
      let leftProof <- checkMode context assumptions left .readOnly leftMode
      let rightProof <- checkMode context assumptions right .readOnly rightMode
      pure (.readOnly leftProof rightProof)
  | left, right, .ofDisjoint certificate => do
      let proof <- checkDisjoint context left right certificate
      pure (.ofDisjoint proof)
  | _, _, _ => none

/-- Check one certificate for every finite mode-context entry. -/
def checkModeCoverage {scope : Source.Sig} (context : Ctx scope)
    (assumptions : ModalAssumptions scope) :
    {modes : List CaptureMode} -> (entries : ModeContext modes scope) ->
      ModeCoverage scope modes ->
      Option (∀ {mode : CaptureMode} {capture : Capture scope},
        ModeContext.Occurs entries mode capture ->
          Mode context assumptions capture mode)
  | [], .nil, .nil =>
      some (fun occurrence => nomatch occurrence)
  | _ :: _, .cons rest capture, .cons restCoverage newestCertificate => do
      let restProof <- checkModeCoverage context assumptions rest restCoverage
      let newestProof <- checkMode context assumptions capture _
        newestCertificate
      pure (fun occurrence =>
        match occurrence with
        | .here => newestProof
        | .there older => restProof older)

/-- Checked forward and reverse pairs between one new entry and every older
entry in a separation context. -/
structure CheckedPairs {scope : Source.Sig} (context : Ctx scope)
    (assumptions : ModalAssumptions scope) (newest : Capture scope)
    {count : Nat} (older : SeparationContext count scope) where
  forward : ∀ position : SeparationContext.Position older,
    Separate context assumptions newest position.capture
  reverse : ∀ position : SeparationContext.Position older,
    Separate context assumptions position.capture newest

/-- Check the ordered newest/older pairs represented by `PairCoverage`. -/
def checkPairs {scope : Source.Sig} (context : Ctx scope)
    (assumptions : ModalAssumptions scope) (newest : Capture scope) :
    {count : Nat} -> (older : SeparationContext count scope) ->
      PairCoverage scope count ->
      Option (CheckedPairs context assumptions newest older)
  | 0, .nil, .nil => some {
      forward := fun position => nomatch position
      reverse := fun position => nomatch position }
  | _ + 1, .cons rest older, .cons restCoverage newestToOlder
      olderToNewest => do
      let restProof <- checkPairs context assumptions newest rest restCoverage
      let forwardHead <- checkSeparate context assumptions newest older
        newestToOlder
      let reverseHead <- checkSeparate context assumptions older newest
        olderToNewest
      pure {
        forward := fun position =>
          match position with
          | .here => forwardHead
          | .there position => restProof.forward position
        reverse := fun position =>
          match position with
          | .here => reverseHead
          | .there position => restProof.reverse position }

/-- Check recursive finite coverage of every ordered distinct pair. -/
def checkSeparationCoverage {scope : Source.Sig} (context : Ctx scope)
    (assumptions : ModalAssumptions scope) :
    {count : Nat} -> (entries : SeparationContext count scope) ->
      SeparationCoverage scope count ->
      Option (∀ (left right : SeparationContext.Position entries),
        SeparationContext.Position.Distinct left right ->
          Separate context assumptions left.capture right.capture)
  | 0, .nil, .nil =>
      some (fun _ _ distinct => nomatch distinct)
  | _ + 1, .cons older newest, .cons olderCoverage newestPairs => do
      let olderProof <- checkSeparationCoverage context assumptions older
        olderCoverage
      let pairProof <- checkPairs context assumptions newest older newestPairs
      pure (fun _left right distinct =>
        match distinct with
        | .hereThere position => pairProof.forward position
        | .thereHere position => pairProof.reverse position
        | .thereThere inner => olderProof _ _ inner)

/-- Turn finite raw coverage into the source `Satisfies` judgment expected by
modal unlocking. -/
def checkSatisfies {scope : Source.Sig} (context : Ctx scope)
    (assumptions : ModalAssumptions scope)
    {separationCount : Nat} {modes : List CaptureMode}
    (requirements : ModalRequirements separationCount modes scope)
    (modeCoverage : ModeCoverage scope modes)
    (separationCoverage : SeparationCoverage scope separationCount) :
    Option (Satisfies context assumptions requirements) :=
  match requirements with
  | .mk separation modeContext => do
      let modesProof <- checkModeCoverage context assumptions modeContext
        modeCoverage
      let separationsProof <- checkSeparationCoverage context assumptions
        separation separationCoverage
      pure (.mk modesProof separationsProof)

end Evidence

end DOTCaptureToManySortedFC.CheckedFrontend
