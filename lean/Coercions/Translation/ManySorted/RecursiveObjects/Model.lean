import Coercions.Translation.ManySorted.RecursiveObjects.Encoding
import Coercions.Translation.ManySorted.RecursiveObjects.SourceErasure
import Coercions.Translation.ManySorted.ModalIntersections.PositiveObjectCompilation

/-!
# Ambiently checked recursive object models and packages

Recursive equality evidence supplies the two directed bounds of each exact
type member.  Capture-member bounds and representation containment are
compiled from source derivations in the ambient context.  The resulting model
is accepted by the ordinary cumulative `ObjectContract` checker before its
theory is opened, preserving no-self-discharge.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.Model

open DOTCaptureToManySortedFC.RecursiveObjects
open DOTCaptureToManySortedFC.RecursiveObjects.Encoding
open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Evidence := ManySortedFC.Evidence
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

/-- Compile every acyclic capture occurrence.  The supplied `AmbientCompiler`
produces syntax, and `checkContractedModel?` below checks that syntax against
the instantiated generated proposition in the ambient target context. -/
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
                candidates
                candidatesEquation := rfl
                model
                modelChecked }

/-! ## Checked package -/

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

/-- A recursive package that has crossed both the theory-model checker and
the term checker.  Static recursive witnesses, evidence, and packaging erase;
the one runtime payload remains exactly `unit`. -/
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
  termEquation : term =
    .pack prepared.object.theory prepared.object.representation
      prepared.object.outerCapture checkedModel.model.symbols
      checkedModel.model.evidence capturedUnit
      checkedModel.containmentEvidence
  valueChecked : ManySortedFC.Tm.ValueChecked term
  valueAccepted : ManySortedFC.Tm.checkValue term = some valueChecked
  checked : ManySortedFC.Tm.Checked core.target term
  accepted : ManySortedFC.Tm.check core.target term = some checked
  useMatches : checked.use = .empty
  typeMatches : checked.type = prepared.object.targetType
  exactErasure : term.erase =
    DOTCaptureToManySortedFC.RecursiveObjects.Source.eraseObject signature

/-- Construct the actual `.pack` and retain it only after the standalone term
checker reproduces the strengthened cumulative object type. -/
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
    .pack prepared.object.theory prepared.object.representation
      prepared.object.outerCapture checkedModel.model.symbols
      checkedModel.model.evidence capturedUnit
      checkedModel.containmentEvidence
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
