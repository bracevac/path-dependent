import Coercions.Translation.ManySorted.ModalIntersections.IntervalMorphism
import Coercions.Translation.ManySorted.ModalIntersections.ModalTheoryMapElaboration
import Coercions.ManySortedFC.Administrative

/-!
# Derivation-directed cumulative adapter elaboration

Source adapters remain value-only.  Every recursive result retains the exact
partial translations of its source and target types, and every generated
target adapter is accepted by the standalone structural checker at those
exact endpoints.  Endpoint alignment is checked syntactically; quantified
cases do not assume an unproved static-instantiation equality.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.AdapterElaboration

open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.IntervalMorphism

namespace Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev StaticSort := DOTCapture.ModalIntersections.StaticSort
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Interval := DOTCapture.ModalIntersections.Interval
abbrev ModalRequirements := DOTCapture.ModalIntersections.ModalRequirements
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Ty := ManySortedFC.Ty
abbrev Adapter := ManySortedFC.Adapter

end Target

/-! ## Exact partial preparation -/

/-- Run cumulative type preparation once and retain its exact equation. -/
def prepareType? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (source : Source.Ty sourceScope) : Option (PreparedTerm core source) :=
  match prepared : ObjectContract.translateType core.layout source with
  | .error _ => none
  | .ok targetType => some { targetType, prepared }

/-- Run cumulative interval preparation once and retain its exact equation. -/
def prepareInterval? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort} (interval : Source.Interval sort sourceScope) :
    Option (PreparedStatic core interval) :=
  match prepared : ObjectContract.translateInterval core.layout interval with
  | .error _ => none
  | .ok theory => some { theory, prepared }

/-- Run cumulative modal-interface preparation once and retain its exact
equation. -/
def prepareModal? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {separationCount : Nat} {modes : List DOTCapture.ModalIntersections.CaptureMode}
    (requirements : Source.ModalRequirements separationCount modes
      sourceScope) : Option (PreparedModal core requirements) :=
  match prepared : Preparation.translateRequirements core.layout
      requirements with
  | .error _ => none
  | .ok targetRequirements => some
      { requirements := targetRequirements
        prepared := prepared }

/-! ## Checker-delimited artifacts -/

/-- A generated target adapter tied to both exact source preparations and to
the exact standalone-checker result.  Administrative transparency is stated
only for values, matching the source adapter judgment. -/
structure CompiledAdapter {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    (source target : Source.Ty sourceScope) where
  sourcePrepared : PreparedTerm context.core source
  targetPrepared : PreparedTerm context.core target
  adapter : Target.Adapter targetScope
  checked : ManySortedFC.Adapter.Checked context.core.target adapter
  checkerAcceptance : ManySortedFC.Adapter.check context.core.target adapter =
    some checked
  sourceExact : checked.source = sourcePrepared.targetType
  targetExact : checked.target = targetPrepared.targetType
  typing : ManySortedFC.Adapter.HasType context.core.target adapter
    sourcePrepared.targetType targetPrepared.targetType
  administrative : forall {runtimeScope : Nat}
    (term : ManySortedFC.Runtime.Tm runtimeScope),
    ManySortedFC.Runtime.IsValue term ->
      ManySortedFC.Runtime.AdministrativeEq (adapter.erase term) term

/-- Prepare both claimed endpoints, run the target checker, and retain a
candidate only if the checker synthesized those exact translations. -/
def finish? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    (source target : Source.Ty sourceScope)
    (adapter : Target.Adapter targetScope) :
    Option (CompiledAdapter context source target) := do
  let sourcePrepared <- prepareType? context.core source
  let targetPrepared <- prepareType? context.core target
  match checkerAcceptance : ManySortedFC.Adapter.check context.core.target
      adapter with
  | none => none
  | some checked =>
      if sourceExact : checked.source = sourcePrepared.targetType then
        if targetExact : checked.target = targetPrepared.targetType then
          some
            { sourcePrepared
              targetPrepared
              adapter
              checked
              checkerAcceptance
              sourceExact
              targetExact
              typing := by
                simpa only [sourceExact, targetExact] using checked.typing
              administrative := fun term value =>
                adapter.erase_admin term value }
        else
          none
      else
        none

/-! ## Derivation-directed compilation -/

/-- Negative object arrows translate to an already captured static model
abstraction.  A surrounding source capture is therefore the capture of that
abstraction, rather than a second nested target capture. -/
private def isNegativeObjectArrow {scope : Source.Sig} :
    Source.Ty scope -> Bool
  | .objectArrow _ _ => true
  | .arr (.capturing domainCapture
      (.object (.mk _ _ objectCapture))) _ =>
      decide (domainCapture = objectCapture)
  | _ => false

/-- Compile the cumulative source adapter grammar without adapter search.
Logical leaves use the cumulative evidence compiler; quantified bound changes
use the checked interval-morphism compiler in their stated variance. -/
def compile? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {source target : Source.Ty sourceScope}
    (adaptation : DOTCapture.ModalIntersections.Adapts environment
      source target) : Option (CompiledAdapter context source target) :=
  match adaptation with
  | .identity =>
      do
        let prepared <- prepareType? context.core source
        finish? context source source (.identity prepared.targetType)
  | .cast inclusion =>
      do
        let compiled <- compileIncludes? context.compiler.leaves inclusion
        finish? context source target (.cast compiled.evidence)
  | .compose first second =>
      do
        let firstCompiled <- compile? context first
        let secondCompiled <- compile? context second
        finish? context source target
          (.compose firstCompiled.adapter secondCompiled.adapter)
  | .function domain codomain =>
      do
        let domainCompiled <- compile? context domain
        let codomainCompiled <- compile? context codomain
        finish? context _ _
          (.function domainCompiled.adapter codomainCompiled.adapter)
  | @DOTCapture.ModalIntersections.Adapts.captured _ _ _ _
      sourceShape targetShape subcapture inner =>
      do
        let capturesCompiled <- compileCaptureIncludes?
          context.compiler.captures context.compiler.leaves subcapture
        let innerCompiled <- compile? context inner
        let direct :=
          .captured capturesCompiled.evidence innerCompiled.adapter
        if isNegativeObjectArrow sourceShape &&
            isNegativeObjectArrow targetShape then
            let sourceBody :=
              innerCompiled.sourcePrepared.targetType.stripCapture
            let targetBody :=
              innerCompiled.targetPrepared.targetType.stripCapture
            let introduceEmpty : Target.Adapter targetScope :=
              .retagCapture sourceBody .empty sourceBody
                (.inclusionRefl (.capture .empty))
                (.inclusionRefl (.type sourceBody))
            let exposeInner : Target.Adapter targetScope :=
              .compose introduceEmpty
                (.compose innerCompiled.adapter
                  (.forgetEmptyCapture targetBody))
            match targetBody with
            | @ManySortedFC.Ty.forallT _ symbols relations theory
                (.capturing .empty targetArrow) =>
                let innerCaptures := capturesCompiled.evidence.rename
                  (ManySortedFC.Rename.weakenStatic symbols relations)
                let closeTarget : Target.Adapter targetScope :=
                  .forallT theory
                    (.captured innerCaptures (.identity targetArrow))
                let bridged :=
                  .captured capturesCompiled.evidence
                    (.compose exposeInner closeTarget)
                match finish? context _ _ bridged with
                | some compiled => some compiled
                | none =>
                    let directClosureLift :=
                      .captured capturesCompiled.evidence
                        (.forallT theory
                          (.captured innerCaptures
                            (.identity targetArrow)))
                    finish? context _ _ directClosureLift
            | _ =>
                finish? context _ _
                  (.captured capturesCompiled.evidence exposeInner)
        else
          finish? context _ _ direct
  | @DOTCapture.ModalIntersections.Adapts.forallI _ _ sort interval
      sourceBody targetBody body =>
      do
        let preparedInterval <- prepareInterval? context.core interval
        let bodyCompiled <- compile?
          (context.extendStatic interval preparedInterval) body
        finish? context _ _
          (.forallT preparedInterval.theory bodyCompiled.adapter)
  | @DOTCapture.ModalIntersections.Adapts.existsI _ _ sort interval
      sourceBody targetBody payload =>
      do
        let preparedInterval <- prepareInterval? context.core interval
        let payloadCompiled <- compile?
          (context.extendStatic interval preparedInterval) payload
        finish? context _ _
          (.existsT preparedInterval.theory payloadCompiled.adapter)
  | @DOTCapture.ModalIntersections.Adapts.forallBounds _ _ sort
      sourceInterval targetInterval sourceBody targetBody bounds body =>
      do
        let sourcePrepared <- prepareInterval? context.core sourceInterval
        let targetPrepared <- prepareInterval? context.core targetInterval
        let constraints <- IntervalMorphism.compile? context targetPrepared
          sourcePrepared bounds
        let bodyCompiled <- compile?
          (context.extendStatic targetInterval targetPrepared) body
        finish? context _ _
          (.forallMorphism (requiredTheory sourcePrepared bounds)
            targetPrepared.theory constraints.morphism bodyCompiled.adapter)
  | @DOTCapture.ModalIntersections.Adapts.existsBounds _ _ sort
      sourceInterval targetInterval sourceBody targetBody bounds payload =>
      do
        let sourcePrepared <- prepareInterval? context.core sourceInterval
        let targetPrepared <- prepareInterval? context.core targetInterval
        let constraints <- IntervalMorphism.compile? context sourcePrepared
          targetPrepared bounds
        let payloadCompiled <- compile?
          (context.extendStatic sourceInterval sourcePrepared) payload
        finish? context _ _
          (.existsMorphism sourcePrepared.theory
            (requiredTheory targetPrepared bounds) constraints.morphism
            payloadCompiled.adapter)
  | @DOTCapture.ModalIntersections.Adapts.modal _ _ sourceCount targetCount
      sourceModes targetModes
      sourceRequirements targetRequirements sourceBody targetBody
      requirements body =>
      do
        let sourcePrepared <- prepareModal? context.core sourceRequirements
        let targetPrepared <- prepareModal? context.core targetRequirements
        let requirementsCompiled <-
          ModalTheoryMapElaboration.compile? context targetPrepared
            sourcePrepared requirements
        let pushed := context.push targetRequirements targetPrepared
        let bodyCompiled <- compile? pushed body
        finish? context _ _
          (.modal sourcePrepared.requirements targetPrepared.requirements
            requirementsCompiled.mapping bodyCompiled.adapter)

end DOTCaptureToManySortedFC.ModalIntersections.AdapterElaboration
