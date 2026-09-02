import Coercions.Translation.ManySorted.RecursiveObjects.Encoding
import Coercions.Translation.ManySorted.RecursiveObjects.SourceErasure
import Coercions.Translation.ManySorted.ModalIntersections.PositiveObjectCompilation

/-!
# Ambiently checked recursive object models and packages

Recursive equality evidence supplies the two directed bounds of each exact
type member.  Capture-member bounds are first realized simultaneously by the
source's explicit concrete capture model; their resulting ordinary ambient
derivations, together with representation containment, are compiled in the
ambient context.  The resulting model is accepted by the ordinary cumulative
`ObjectContract` checker before its theory is opened, preserving
no-self-discharge.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.Model

open DOTCaptureToManySortedFC.RecursiveObjects
open DOTCaptureToManySortedFC.RecursiveObjects.Encoding
open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Evidence := ManySortedFC.Evidence
abbrev Ty := ManySortedFC.Ty
abbrev Tm := ManySortedFC.Tm

end Target

namespace Src

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev Ctx := DOTCapture.ModalIntersections.Ctx
abbrev AmbientCaptureModel :=
  DOTCaptureToManySortedFC.RecursiveObjects.Source.AmbientCaptureModel
abbrev CaptureInterface :=
  DOTCaptureToManySortedFC.RecursiveObjects.Source.CaptureInterface
abbrev Signature :=
  DOTCaptureToManySortedFC.RecursiveObjects.Source.Signature
abbrev Realization {scope : Sig} (context : Ctx scope)
    (signature : Signature scope) :=
  DOTCaptureToManySortedFC.RecursiveObjects.Source.Realization context signature

end Src

/-! ## Evidence candidates -/

/-- Both directed interval views of every exact recursive witness.  The
primitive equality has orientation `W = unfold(W)`; its symmetric inclusion
is therefore the lower bound and its forward inclusion the upper bound. -/
def exactTypeCandidates {scope : Target.Sig} {names : Nat}
    (bodies : ManySortedFC.RecBodies scope names names) :
    List (ModelEvidence scope) :=
  (List.finRange names).flatMap fun index =>
    [ .type (.equalityToInclusion (.equalitySymm (.unfoldRec bodies index))),
      .type (.equalityToInclusion (.unfoldRec bodies index)) ]

/-- Compile every simultaneously realized capture occurrence.  Raw bounds may
refer cyclically to local capture labels; the canonical source realization has
already substituted the complete concrete model into both endpoints of each
proof.  The supplied `AmbientCompiler` therefore sees only ordinary ambient
inclusions.  `checkContractedModel?` below independently checks the resulting
syntax against the instantiated generated proposition. -/
def compileCaptureCandidates? {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (ambient : AmbientCompiler core)
    {captureModel : Src.AmbientCaptureModel sourceScope} :
    {declarations : Src.CaptureInterface sourceScope} ->
    declarations.Realizes environment.bindings captureModel ->
      Option (List (ModelEvidence targetScope))
  | _, .empty => some []
  | _, .member lowerProof upperProof => do
      let lower <- ambient.compile (sort := .capture) lowerProof
      let upper <- ambient.compile (sort := .capture) upperProof
      pure [.capture lower, .capture upper]
  | _, .inter leftProof rightProof => do
      let left <- compileCaptureCandidates? ambient leftProof
      let right <- compileCaptureCandidates? ambient rightProof
      pure (left ++ right)

/-! ## Checked ambient model -/

/-- Complete contracted model provenance.  `model.checkerAcceptance` is the
standalone target check, performed under `core.target` without any assumption
from the modeled theory. -/
structure CheckedModel {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    (prepared : Encoding.Prepared core.layout signature valid realization)
    (ambient : AmbientCompiler core) where
  captureCandidates : List (ModelEvidence targetScope)
  captureCandidatesCompiled : compileCaptureCandidates? ambient
    realization.captureConstraints = some captureCandidates
  containmentEvidence : Target.Evidence (.inclusion .capture) targetScope
  containmentCompiled : ambient.compile (sort := .capture)
    realization.representationContainment = some containmentEvidence
  packageContainmentEvidence :
    Target.Evidence (.inclusion .capture) targetScope
  packageContainmentCompiled : ambient.compile (sort := .capture)
    realization.packageContainment = some packageContainmentEvidence
  candidates : List (ModelEvidence targetScope)
  candidatesEquation : candidates =
    .captureEquality (.equalityRefl
      (.capture (prepared.object.actualCapture prepared.memberSymbols))) ::
    .capture containmentEvidence ::
      exactTypeCandidates prepared.bodies ++ captureCandidates
  model : CompiledContractedModel core prepared.object
  modelChecked : checkContractedModel? core prepared.object prepared.symbols
    candidates = some model

/-- Compile all evidence and cross the ordinary target model checker. -/
def check? {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    (prepared : Encoding.Prepared core.layout signature valid realization)
    (ambient : AmbientCompiler core) :
    Option (CheckedModel core prepared ambient) :=
  match captureCandidatesCompiled : compileCaptureCandidates? ambient
      realization.captureConstraints with
  | none => none
  | some captureCandidates =>
      match containmentCompiled : ambient.compile (sort := .capture)
          realization.representationContainment with
      | none => none
      | some containmentEvidence =>
          match packageContainmentCompiled : ambient.compile (sort := .capture)
              realization.packageContainment with
          | none => none
          | some packageContainmentEvidence =>
              let candidates :=
                .captureEquality (.equalityRefl
                  (.capture (prepared.object.actualCapture
                    prepared.memberSymbols))) ::
                .capture containmentEvidence ::
                  exactTypeCandidates prepared.bodies ++ captureCandidates
              match modelChecked : checkContractedModel? core prepared.object
                  prepared.symbols candidates with
              | none => none
              | some model => some
                  { captureCandidates
                    captureCandidatesCompiled
                    containmentEvidence
                    containmentCompiled
                    packageContainmentEvidence
                    packageContainmentCompiled
                    candidates
                    candidatesEquation := rfl
                    model
                    modelChecked }

namespace CheckedModel

/-- The concrete captured representation required of a package payload after
the complete recursive model has instantiated every public member and the
distinguished `C_rep` name.  This is the target-side handoff used by the
cumulative value compiler; it does not assume a particular source payload. -/
def realizedRepresentation {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    {prepared : Encoding.Prepared core.layout signature valid realization}
    {ambient : AmbientCompiler core}
    (checkedModel : CheckedModel core prepared ambient) : Target.Ty targetScope :=
  prepared.object.representation.instantiateStatic checkedModel.model.symbols

/-- Assemble the raw existential package around an arbitrary payload.  The
caller still has to establish the value boundary and submit this term to the
standalone term checker.  Keeping assembly here ensures every cumulative
compiler uses exactly the model and containment evidence that were checked
ambiently above. -/
def packageTerm {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    {prepared : Encoding.Prepared core.layout signature valid realization}
    {ambient : AmbientCompiler core}
    (checkedModel : CheckedModel core prepared ambient)
    (payload : Target.Tm targetScope) : Target.Tm targetScope :=
  .pack prepared.object.theory prepared.object.representation
    prepared.object.outerCapture checkedModel.model.symbols
    checkedModel.model.evidence payload
      checkedModel.packageContainmentEvidence

@[simp]
theorem packageTerm_erases {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    {prepared : Encoding.Prepared core.layout signature valid realization}
    {ambient : AmbientCompiler core}
    (checkedModel : CheckedModel core prepared ambient)
    (payload : Target.Tm targetScope) :
    (checkedModel.packageTerm payload).erase = payload.erase := rfl

end CheckedModel

/-! ## Recursive-member-aware inclusion elaboration -/

/-- One source endpoint translated through the complete recursive model.
Unlike ordinary ambient preparation, this path resolves local type members to
their `recProj` witnesses and local capture members to the simultaneous
concrete capture model. -/
structure PreparedRealizedExpression {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    (prepared : Encoding.Prepared core.layout signature valid realization)
    {sort : DOTCapture.ModalIntersections.StaticSort}
    (source : DOTCapture.ModalIntersections.StaticExpr sort sourceScope) where
  target : ManySortedFC.StaticExpr
    (DOTCaptureToManySortedFC.ModalIntersections.translateSort sort)
    targetScope
  compiled : Encoding.compileRealizedStaticExpr core.layout
    realization.captures prepared.object prepared.memberSymbols source =
      .ok target

/-- Execute recursive-aware endpoint preparation once and retain its exact
equation. -/
def prepareRealizedExpression? {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    (prepared : Encoding.Prepared core.layout signature valid realization)
    {sort : DOTCapture.ModalIntersections.StaticSort}
    (source : DOTCapture.ModalIntersections.StaticExpr sort sourceScope) :
    Option (PreparedRealizedExpression prepared source) :=
  match compiled : Encoding.compileRealizedStaticExpr core.layout
      realization.captures prepared.object prepared.memberSymbols source with
  | .error _ => none
  | .ok target => some { target, compiled }

/-- A source inclusion whose exact target endpoints and certificate were all
checked after recursive-member realization. -/
structure CompiledRealizedInclusion {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    (prepared : Encoding.Prepared core.layout signature valid realization)
    {sort : DOTCapture.ModalIntersections.StaticSort}
    (lower upper : DOTCapture.ModalIntersections.StaticExpr sort sourceScope)
    where
  lowerPrepared : PreparedRealizedExpression prepared lower
  upperPrepared : PreparedRealizedExpression prepared upper
  evidence : Target.Evidence
    (.inclusion
      (DOTCaptureToManySortedFC.ModalIntersections.translateSort sort))
    targetScope
  typing : ManySortedFC.Evidence.Proves core.target evidence
    (.inclusion lowerPrepared.target upperPrepared.target)

/-- Check a candidate against the exact recursively realized endpoints. -/
def finishRealizedInclusion? {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    (prepared : Encoding.Prepared core.layout signature valid realization)
    {sort : DOTCapture.ModalIntersections.StaticSort}
    (lower upper : DOTCapture.ModalIntersections.StaticExpr sort sourceScope)
    (evidence : Target.Evidence
      (.inclusion
        (DOTCaptureToManySortedFC.ModalIntersections.translateSort sort))
      targetScope) :
    Option (CompiledRealizedInclusion prepared lower upper) := do
  let lowerPrepared <- prepareRealizedExpression? prepared lower
  let upperPrepared <- prepareRealizedExpression? prepared upper
  let checked <- ManySortedFC.Evidence.check core.target evidence
  if propositionMatches : checked.proposition =
      .inclusion lowerPrepared.target upperPrepared.target then
    pure
      { lowerPrepared
        upperPrepared
        evidence
        typing := by simpa only [propositionMatches] using checked.typing }
  else
    none

/-- Derivation-directed inclusion compilation using recursive-aware endpoint
preparation.  Ambient lookup leaves are still supplied by the ordinary
compiler and their syntax is rechecked against the recursively translated
endpoints before it is retained. -/
def compileRealizedIncludes? {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    (prepared : Encoding.Prepared core.layout signature valid realization)
    (leaves : LeafCompiler core) :
    {sort : DOTCapture.ModalIntersections.StaticSort} ->
    {lower upper : DOTCapture.ModalIntersections.StaticExpr sort sourceScope} ->
    DOTCapture.ModalIntersections.Includes environment.bindings lower upper ->
      Option (CompiledRealizedInclusion prepared lower upper)
  | _, lower, _, .refl => do
      let endpoint <- prepareRealizedExpression? prepared lower
      finishRealizedInclusion? prepared lower lower
        (.inclusionRefl endpoint.target)
  | _, lower, upper, .trans first second => do
      let firstCompiled <- compileRealizedIncludes? prepared leaves first
      let secondCompiled <- compileRealizedIncludes? prepared leaves second
      finishRealizedInclusion? prepared lower upper
        (.inclusionTrans firstCompiled.evidence secondCompiled.evidence)
  | _, _, _, .lower bound => do
      let compiled <- leaves.lower bound
      finishRealizedInclusion? prepared _ _ compiled.evidence
  | _, _, _, .upper bound => do
      let compiled <- leaves.upper bound
      finishRealizedInclusion? prepared _ _ compiled.evidence
  | .type, .type source, .type .top, .typeTop => do
      let sourcePrepared <- prepareRealizedExpression? prepared (.type source)
      let .type targetSource := sourcePrepared.target
      finishRealizedInclusion? prepared (.type source) (.type .top)
        (.typeTop targetSource)
  | .type, .type .bot, .type target, .typeBottom => do
      let targetPrepared <- prepareRealizedExpression? prepared (.type target)
      let .type targetType := targetPrepared.target
      finishRealizedInclusion? prepared (.type .bot) (.type target)
        (.typeBottom targetType)
  | .type, .type (.arr sourceDomain sourceCodomain),
      .type (.arr targetDomain targetCodomain),
      .typeArrow domain codomain => do
      let domainCompiled <- compileRealizedIncludes? prepared leaves domain
      let codomainCompiled <- compileRealizedIncludes? prepared leaves codomain
      finishRealizedInclusion? prepared
        (.type (.arr sourceDomain sourceCodomain))
        (.type (.arr targetDomain targetCodomain))
        (.typeArrow domainCompiled.evidence codomainCompiled.evidence)
  | .type, .type (.capturing sourceCaptures sourceShape),
      .type (.capturing targetCaptures targetShape),
      .typeCapturing captures shape => do
      let capturesCompiled <- compileRealizedIncludes? prepared leaves captures
      let shapeCompiled <- compileRealizedIncludes? prepared leaves shape
      finishRealizedInclusion? prepared
        (.type (.capturing sourceCaptures sourceShape))
        (.type (.capturing targetCaptures targetShape))
        (.typeCapturing capturesCompiled.evidence shapeCompiled.evidence)
  | .capture, .capture .empty, .capture target, .captureEmpty => do
      let targetPrepared <- prepareRealizedExpression? prepared (.capture target)
      let .capture targetCapture := targetPrepared.target
      finishRealizedInclusion? prepared (.capture .empty) (.capture target)
        (.captureEmpty targetCapture)
  | .capture, .capture left, .capture (.union _ right),
      .captureUnionLeft => do
      let leftPrepared <- prepareRealizedExpression? prepared (.capture left)
      let rightPrepared <- prepareRealizedExpression? prepared (.capture right)
      let .capture leftCapture := leftPrepared.target
      let .capture rightCapture := rightPrepared.target
      finishRealizedInclusion? prepared (.capture left)
        (.capture (.union left right))
        (.captureUnionLeft leftCapture rightCapture)
  | .capture, .capture right, .capture (.union left _),
      .captureUnionRight => do
      let leftPrepared <- prepareRealizedExpression? prepared (.capture left)
      let rightPrepared <- prepareRealizedExpression? prepared (.capture right)
      let .capture leftCapture := leftPrepared.target
      let .capture rightCapture := rightPrepared.target
      finishRealizedInclusion? prepared (.capture right)
        (.capture (.union left right))
        (.captureUnionRight leftCapture rightCapture)
  | .capture, .capture (.union left right), .capture target,
      .captureUnionElim fromLeft fromRight => do
      let leftCompiled <- compileRealizedIncludes? prepared leaves fromLeft
      let rightCompiled <- compileRealizedIncludes? prepared leaves fromRight
      finishRealizedInclusion? prepared (.capture (.union left right))
        (.capture target)
        (.captureUnionElim leftCompiled.evidence rightCompiled.evidence)
  | .capture, .capture (.readOnly capture), .capture _,
      .captureReadOnly => do
      let capturePrepared <- prepareRealizedExpression? prepared
        (.capture capture)
      let .capture targetCapture := capturePrepared.target
      finishRealizedInclusion? prepared (.capture (.readOnly capture))
        (.capture capture) (.captureReadOnly targetCapture)
  | .capture, .capture (.readOnly lower), .capture (.readOnly upper),
      .captureReadOnlyMono inclusion => do
      let compiled <- compileRealizedIncludes? prepared leaves inclusion
      finishRealizedInclusion? prepared (.capture (.readOnly lower))
        (.capture (.readOnly upper))
        (.captureReadOnlyMono compiled.evidence)
  | .capture, _, _, .captureVariable found => do
      let compiled <- leaves.termVariable found
      finishRealizedInclusion? prepared _ _ compiled.evidence
  | .capture, _, _, .payloadRoot exposes => do
      let compiled <- leaves.payload exposes
      finishRealizedInclusion? prepared _ _ compiled.evidence

/-! ## Stage 6A unit-package compatibility -/

/-- The unit representation made explicitly empty-captured.  It remains a
value and its adapter erases literally. -/
def capturedUnit {scope : Target.Sig} : Target.Tm scope :=
  .adapt .unit
    (.retagCapture .one .empty .one
      (.inclusionRefl (.capture .empty))
      (.inclusionRefl (.type .one)))

@[simp]
theorem capturedUnit_erases {scope : Target.Sig} :
    (capturedUnit (scope := scope)).erase = .unit := rfl

/-- A recursive package using the historical unit payload.  This helper is
kept as a Stage 6A regression surface; the general cumulative compiler uses
`CheckedModel.packageTerm` with its independently compiled value payload. -/
structure CheckedPackage {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    (prepared : Encoding.Prepared core.layout signature valid realization)
    (ambient : AmbientCompiler core)
    (checkedModel : CheckedModel core prepared ambient) where
  term : Target.Tm targetScope
  termEquation : term = checkedModel.packageTerm capturedUnit
  valueChecked : ManySortedFC.Tm.ValueChecked term
  valueAccepted : ManySortedFC.Tm.checkValue term = some valueChecked
  checked : ManySortedFC.Tm.Checked core.target term
  accepted : ManySortedFC.Tm.check core.target term = some checked
  useMatches : checked.use = .empty
  typeMatches : checked.type = prepared.object.targetType
  exactErasure : term.erase =
    DOTCaptureToManySortedFC.RecursiveObjects.Source.eraseObject signature

/-- Construct the historical unit package and retain it only when the now
general representation happens to accept that payload. -/
def package? {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    (prepared : Encoding.Prepared core.layout signature valid realization)
    (ambient : AmbientCompiler core)
    (checkedModel : CheckedModel core prepared ambient) :
    Option (CheckedPackage core prepared ambient checkedModel) :=
  let term : Target.Tm targetScope :=
    checkedModel.packageTerm capturedUnit
  match valueAccepted : ManySortedFC.Tm.checkValue term with
  | none => none
  | some valueChecked =>
      match accepted : ManySortedFC.Tm.check core.target term with
      | none => none
      | some checked =>
          if useMatches : checked.use =
              (.empty : ManySortedFC.Capture targetScope) then
            if typeMatches : checked.type = prepared.object.targetType then
              some
                { term
                  termEquation := rfl
                  valueChecked
                  valueAccepted
                  checked
                  accepted
                  useMatches
                  typeMatches
                  exactErasure := rfl }
            else none
          else none

namespace CheckedPackage

/-- Public independent checker certificate. -/
theorem checkerAccepts {sourceScope : Src.Sig}
    {environment : Src.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Src.Signature sourceScope} {valid : signature.Valid}
    {realization : Src.Realization environment.bindings signature}
    {prepared : Encoding.Prepared core.layout signature valid realization}
    {ambient : AmbientCompiler core}
    {checkedModel : CheckedModel core prepared ambient}
    (package : CheckedPackage core prepared ambient checkedModel) :
    ManySortedFC.Tm.synth core.target package.term =
      some (.empty, prepared.object.targetType) := by
  unfold ManySortedFC.Tm.synth
  rw [package.accepted]
  simp only [Option.map_some]
  rw [package.useMatches, package.typeMatches]

end CheckedPackage

end DOTCaptureToManySortedFC.RecursiveObjects.Model
