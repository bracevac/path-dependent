import Coercions.Translation.ManySorted.ModalIntersections.EvidenceContext
import Coercions.Translation.ManySorted.ModalIntersections.PreparationMetatheory
import Coercions.DOT.Captures.ModalIntersections.StaticTyping
import Coercions.ManySortedFC.TheoryMorphismChecker

/-!
# Checked cumulative interval morphisms

A same-shape source interval entailment is translated in its stated
direction: assumptions exported by the available interval discharge the
obligations of the required interval.  Endpoint derivations are compiled only
after opening the available interval.  The resulting identity-on-symbols
`TheoryMorphism` then crosses the standalone target checker, which likewise
opens only its source theory.

The endpoint values do not affect coordinate allocation.  The same-shape
layout and body equalities at the end of this module record that the two
intervals use the same dependent-body coordinates even when their theories
contain different propositions.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.IntervalMorphism

open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext

namespace Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev StaticSort := DOTCapture.ModalIntersections.StaticSort
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr
abbrev Interval := DOTCapture.ModalIntersections.Interval
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Theory := ManySortedFC.Theory
abbrev EvidenceArgs := ManySortedFC.EvidenceArgs

end Target

/-- View the prepared required theory at the relation-spine index selected by
the available interval.  `Interval.Entails` guarantees the same endpoint
presence shape, so every branch is definitionally just the supplied prepared
theory; no proposition or evidence is changed. -/
def requiredTheory {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {sort : Source.StaticSort}
    {available required : Source.Interval sort sourceScope}
    (prepared : PreparedStatic core required)
    (entailment : DOTCapture.ModalIntersections.Interval.Entails
      environment.bindings available required) :
    Target.Theory targetScope [translateSort sort]
      (intervalRelations available) :=
  match entailment with
  | .unbounded => prepared.theory
  | .lower _ => prepared.theory
  | .upper _ => prepared.theory
  | .between _ _ => prepared.theory

/-- Exact derivation-directed provenance for the certificate spine supplied
to the target morphism checker.  Every nonempty constructor records the
precise cumulative evidence-compiler equation for its source proof. -/
inductive EvidenceCompilation {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope) :
    {sort : Source.StaticSort} ->
    {available required : Source.Interval sort sourceScope} ->
    (preparedAvailable : PreparedStatic context.core available) ->
    (entailment : DOTCapture.ModalIntersections.Interval.Entails
      environment.bindings available required) ->
    Target.EvidenceArgs
      (ManySortedFC.StaticScope targetScope [translateSort sort]
        (intervalRelations available))
      (intervalRelations available) -> Type where
  | unbounded {sort : Source.StaticSort}
      {preparedAvailable : PreparedStatic context.core
        (.bounds .none .none : Source.Interval sort sourceScope)} :
      EvidenceCompilation (sort := sort)
        (available := .bounds .none .none)
        (required := .bounds .none .none) context preparedAvailable
        (DOTCapture.ModalIntersections.Interval.Entails.unbounded
          (context := environment.bindings))
        (.nil : Target.EvidenceArgs
          (ManySortedFC.StaticScope targetScope [translateSort sort] []) [])
  | lower {availableLower requiredLower : Source.StaticExpr sort sourceScope}
      {proof : DOTCapture.ModalIntersections.Includes
        (environment.bindings.extendStatic
          (.bounds (.some availableLower) .none))
        requiredLower.weaken
        (DOTCapture.ModalIntersections.StaticExpr.bound
          (.here : DOTCapture.ModalIntersections.BVar
            (sourceScope ▹ .static sort) (.static sort)))}
      {preparedAvailable : PreparedStatic context.core
        (.bounds (.some availableLower) .none)}
      (compiled : CompiledInclusion
        (context.extendStatic (.bounds (.some availableLower) .none)
          preparedAvailable).core
        requiredLower.weaken
        (DOTCapture.ModalIntersections.StaticExpr.bound
          (.here : DOTCapture.ModalIntersections.BVar
            (sourceScope ▹ .static sort) (.static sort))))
      (compiledEquation : compileIncludes?
        (context.extendStatic (.bounds (.some availableLower) .none)
          preparedAvailable).compiler.leaves proof = some compiled) :
      EvidenceCompilation (sort := sort)
        (available := .bounds (.some availableLower) .none)
        (required := .bounds (.some requiredLower) .none)
        context preparedAvailable
        (DOTCapture.ModalIntersections.Interval.Entails.lower proof)
        (.cons compiled.evidence .nil)
  | upper {availableUpper requiredUpper : Source.StaticExpr sort sourceScope}
      {proof : DOTCapture.ModalIntersections.Includes
        (environment.bindings.extendStatic
          (.bounds .none (.some availableUpper)))
        (DOTCapture.ModalIntersections.StaticExpr.bound
          (.here : DOTCapture.ModalIntersections.BVar
            (sourceScope ▹ .static sort) (.static sort)))
        requiredUpper.weaken}
      {preparedAvailable : PreparedStatic context.core
        (.bounds .none (.some availableUpper))}
      (compiled : CompiledInclusion
        (context.extendStatic (.bounds .none (.some availableUpper))
          preparedAvailable).core
        (DOTCapture.ModalIntersections.StaticExpr.bound
          (.here : DOTCapture.ModalIntersections.BVar
            (sourceScope ▹ .static sort) (.static sort)))
        requiredUpper.weaken)
      (compiledEquation : compileIncludes?
        (context.extendStatic (.bounds .none (.some availableUpper))
          preparedAvailable).compiler.leaves proof = some compiled) :
      EvidenceCompilation (sort := sort)
        (available := .bounds .none (.some availableUpper))
        (required := .bounds .none (.some requiredUpper))
        context preparedAvailable
        (DOTCapture.ModalIntersections.Interval.Entails.upper proof)
        (.cons compiled.evidence .nil)
  | between
      {availableLower availableUpper requiredLower requiredUpper :
        Source.StaticExpr sort sourceScope}
      {lowerProof : DOTCapture.ModalIntersections.Includes
        (environment.bindings.extendStatic
          (.bounds (.some availableLower) (.some availableUpper)))
        requiredLower.weaken
        (DOTCapture.ModalIntersections.StaticExpr.bound
          (.here : DOTCapture.ModalIntersections.BVar
            (sourceScope ▹ .static sort) (.static sort)))}
      {upperProof : DOTCapture.ModalIntersections.Includes
        (environment.bindings.extendStatic
          (.bounds (.some availableLower) (.some availableUpper)))
        (DOTCapture.ModalIntersections.StaticExpr.bound
          (.here : DOTCapture.ModalIntersections.BVar
            (sourceScope ▹ .static sort) (.static sort)))
        requiredUpper.weaken}
      {preparedAvailable : PreparedStatic context.core
        (.bounds (.some availableLower) (.some availableUpper))}
      (lowerCompiled : CompiledInclusion
        (context.extendStatic
          (.bounds (.some availableLower) (.some availableUpper))
          preparedAvailable).core
        requiredLower.weaken
        (DOTCapture.ModalIntersections.StaticExpr.bound
          (.here : DOTCapture.ModalIntersections.BVar
            (sourceScope ▹ .static sort) (.static sort))))
      (lowerEquation : compileIncludes?
        (context.extendStatic
          (.bounds (.some availableLower) (.some availableUpper))
          preparedAvailable).compiler.leaves lowerProof = some lowerCompiled)
      (upperCompiled : CompiledInclusion
        (context.extendStatic
          (.bounds (.some availableLower) (.some availableUpper))
          preparedAvailable).core
        (DOTCapture.ModalIntersections.StaticExpr.bound
          (.here : DOTCapture.ModalIntersections.BVar
            (sourceScope ▹ .static sort) (.static sort)))
        requiredUpper.weaken)
      (upperEquation : compileIncludes?
        (context.extendStatic
          (.bounds (.some availableLower) (.some availableUpper))
          preparedAvailable).compiler.leaves upperProof = some upperCompiled) :
      EvidenceCompilation (sort := sort)
        (available :=
          .bounds (.some availableLower) (.some availableUpper))
        (required :=
          .bounds (.some requiredLower) (.some requiredUpper))
        context preparedAvailable
        (DOTCapture.ModalIntersections.Interval.Entails.between
          lowerProof upperProof)
        (.cons lowerCompiled.evidence
          (.cons upperCompiled.evidence .nil))

/-- A source-indexed interval entailment whose derivation-produced candidate
has been accepted by the independently executable target checker. -/
structure CompiledMorphism {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {sort : Source.StaticSort}
    {available required : Source.Interval sort sourceScope}
    (preparedAvailable : PreparedStatic context.core available)
    (preparedRequired : PreparedStatic context.core required)
    (entailment : DOTCapture.ModalIntersections.Interval.Entails
      environment.bindings available required) where
  evidence : Target.EvidenceArgs
    (ManySortedFC.StaticScope targetScope [translateSort sort]
      (intervalRelations available))
    (intervalRelations available)
  provenance : EvidenceCompilation context preparedAvailable entailment evidence
  morphism : ManySortedFC.TheoryMorphism preparedAvailable.theory
    (requiredTheory preparedRequired entailment)
  morphismEvidence : morphism.evidence = evidence
  typing : ManySortedFC.TheoryMorphism.HasType context.core.target morphism
  checkerAcceptance : ManySortedFC.TheoryMorphism.check context.core.target
    morphism = some typing

/-- Check a derivation-produced evidence spine at the exact prepared source
and destination theories.  Only `preparedAvailable.theory` is opened by the
target checker. -/
def check? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : EvidenceContext.Context environment targetScope}
    {sort : Source.StaticSort}
    {available required : Source.Interval sort sourceScope}
    {preparedAvailable : PreparedStatic context.core available}
    {preparedRequired : PreparedStatic context.core required}
    {entailment : DOTCapture.ModalIntersections.Interval.Entails
      environment.bindings available required}
    (evidence : Target.EvidenceArgs
      (ManySortedFC.StaticScope targetScope [translateSort sort]
        (intervalRelations available))
      (intervalRelations available))
    (provenance : EvidenceCompilation context preparedAvailable entailment
      evidence) :
    Option (CompiledMorphism context preparedAvailable preparedRequired
      entailment) :=
  let morphism : ManySortedFC.TheoryMorphism preparedAvailable.theory
      (requiredTheory preparedRequired entailment) := ⟨evidence⟩
  match checkerAcceptance : ManySortedFC.TheoryMorphism.check
      context.core.target morphism with
  | none => none
  | some typing => some
      { evidence
        provenance
        morphism
        morphismEvidence := rfl
        typing
        checkerAcceptance }

/-- Compile every same-shape cumulative source interval entailment.  Required
endpoint certificates are constructed under the available interval and then
validated without ever opening the required theory. -/
def compile? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {sort : Source.StaticSort}
    {available required : Source.Interval sort sourceScope}
    (preparedAvailable : PreparedStatic context.core available)
    (preparedRequired : PreparedStatic context.core required)
    (entailment : DOTCapture.ModalIntersections.Interval.Entails
      environment.bindings available required) :
    Option (CompiledMorphism context preparedAvailable preparedRequired
      entailment) := by
  cases entailment with
  | unbounded =>
      exact check? (.nil) (.unbounded)
  | @lower availableLower requiredLower proof =>
      let extended := context.extendStatic
        (.bounds (.some availableLower) .none) preparedAvailable
      exact do
        match compiledEquation : compileIncludes? extended.compiler.leaves
            proof with
        | none => none
        | some compiled =>
            check? (.cons compiled.evidence .nil)
              (.lower compiled compiledEquation)
  | @upper availableUpper requiredUpper proof =>
      let extended := context.extendStatic
        (.bounds .none (.some availableUpper)) preparedAvailable
      exact do
        match compiledEquation : compileIncludes? extended.compiler.leaves
            proof with
        | none => none
        | some compiled =>
            check? (.cons compiled.evidence .nil)
              (.upper compiled compiledEquation)
  | @between availableLower availableUpper requiredLower requiredUpper
      lowerProof upperProof =>
      let extended := context.extendStatic
        (.bounds (.some availableLower) (.some availableUpper))
        preparedAvailable
      exact do
        match lowerEquation : compileIncludes? extended.compiler.leaves
            lowerProof with
        | none => none
        | some lowerCompiled =>
            match upperEquation : compileIncludes? extended.compiler.leaves
                upperProof with
            | none => none
            | some upperCompiled =>
                check? (.cons lowerCompiled.evidence
                  (.cons upperCompiled.evidence .nil))
                  (.between lowerCompiled lowerEquation upperCompiled
                    upperEquation)

/-! ## Same-shape coordinate agreements -/

/-- The exact layout equality selected by one same-shape entailment.  The
dependent match exposes the common target relation spine without casting
either layout. -/
def ExtendedLayoutAgreement {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {sort : Source.StaticSort}
    {available required : Source.Interval sort sourceScope}
    (entailment : DOTCapture.ModalIntersections.Interval.Entails
      environment.bindings available required) : Prop :=
  match entailment with
  | .unbounded =>
      core.layout.extendStatic
          (.bounds .none .none : Source.Interval sort sourceScope) =
        core.layout.extendStatic (.bounds .none .none)
  | @DOTCapture.ModalIntersections.Interval.Entails.lower _ _ _
      availableLower requiredLower _ =>
      core.layout.extendStatic (.bounds (.some requiredLower) .none) =
        core.layout.extendStatic (.bounds (.some availableLower) .none)
  | @DOTCapture.ModalIntersections.Interval.Entails.upper _ _ _
      availableUpper requiredUpper _ =>
      core.layout.extendStatic (.bounds .none (.some requiredUpper)) =
        core.layout.extendStatic (.bounds .none (.some availableUpper))
  | @DOTCapture.ModalIntersections.Interval.Entails.between _ _ _
      availableLower availableUpper requiredLower requiredUpper _ _ =>
      core.layout.extendStatic
          (.bounds (.some requiredLower) (.some requiredUpper)) =
        core.layout.extendStatic
          (.bounds (.some availableLower) (.some availableUpper))

/-- Replacing interval endpoints along an entailment does not change the
extended source-to-target layout. -/
def extendedLayout_eq {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {sort : Source.StaticSort}
    {available required : Source.Interval sort sourceScope}
    (entailment : DOTCapture.ModalIntersections.Interval.Entails
      environment.bindings available required) :
    ExtendedLayoutAgreement (core := core) entailment :=
  match entailment with
  | .unbounded => by simp [ExtendedLayoutAgreement]
  | @DOTCapture.ModalIntersections.Interval.Entails.lower _ _ _
      availableLower requiredLower _ => by
      simpa [ExtendedLayoutAgreement] using
        (Preparation.Layout.extendStatic_lower_eq core.layout requiredLower
          availableLower)
  | @DOTCapture.ModalIntersections.Interval.Entails.upper _ _ _
      availableUpper requiredUpper _ => by
      simpa [ExtendedLayoutAgreement] using
        (Preparation.Layout.extendStatic_upper_eq core.layout requiredUpper
          availableUpper)
  | @DOTCapture.ModalIntersections.Interval.Entails.between _ _ _
      availableLower availableUpper requiredLower requiredUpper _ _ => by
      simpa [ExtendedLayoutAgreement] using
        (Preparation.Layout.extendStatic_between_eq core.layout requiredLower
          requiredUpper availableLower availableUpper)

/-- The exact body-translation equality selected by one same-shape
entailment. -/
def BodyTranslationAgreement {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {sort : Source.StaticSort}
    {available required : Source.Interval sort sourceScope}
    (entailment : DOTCapture.ModalIntersections.Interval.Entails
      environment.bindings available required)
    (body : Source.Ty (sourceScope ▹ .static sort)) : Prop :=
  match entailment with
  | .unbounded =>
      ObjectContract.translateType
          (core.layout.extendStatic
            (.bounds .none .none : Source.Interval sort sourceScope)) body =
        ObjectContract.translateType
          (core.layout.extendStatic
            (.bounds .none .none : Source.Interval sort sourceScope)) body
  | @DOTCapture.ModalIntersections.Interval.Entails.lower _ _ _
      availableLower requiredLower _ =>
      ObjectContract.translateType
          (core.layout.extendStatic
            (.bounds (.some requiredLower) .none)) body =
        ObjectContract.translateType
          (core.layout.extendStatic
            (.bounds (.some availableLower) .none)) body
  | @DOTCapture.ModalIntersections.Interval.Entails.upper _ _ _
      availableUpper requiredUpper _ =>
      ObjectContract.translateType
          (core.layout.extendStatic
            (.bounds .none (.some requiredUpper))) body =
        ObjectContract.translateType
          (core.layout.extendStatic
            (.bounds .none (.some availableUpper))) body
  | @DOTCapture.ModalIntersections.Interval.Entails.between _ _ _
      availableLower availableUpper requiredLower requiredUpper _ _ =>
      ObjectContract.translateType
          (core.layout.extendStatic
            (.bounds (.some requiredLower) (.some requiredUpper))) body =
        ObjectContract.translateType
          (core.layout.extendStatic
            (.bounds (.some availableLower) (.some availableUpper))) body

/-- A dependent body has literally the same target translation below the
available and required intervals. -/
theorem translateBody_required_eq_available {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {sort : Source.StaticSort}
    {available required : Source.Interval sort sourceScope}
    (entailment : DOTCapture.ModalIntersections.Interval.Entails
      environment.bindings available required)
    (body : Source.Ty (sourceScope ▹ .static sort)) :
    BodyTranslationAgreement (core := core) entailment body :=
  match entailment with
  | .unbounded => by simp [BodyTranslationAgreement]
  | @DOTCapture.ModalIntersections.Interval.Entails.lower _ _ _
      availableLower requiredLower _ => by
      have layoutEq :
          core.layout.extendStatic (.bounds (.some requiredLower) .none) =
            core.layout.extendStatic
              (.bounds (.some availableLower) .none) := by
        simpa using
          (Preparation.Layout.extendStatic_lower_eq core.layout requiredLower
            availableLower)
      exact congrArg (fun layout => ObjectContract.translateType layout body)
        layoutEq
  | @DOTCapture.ModalIntersections.Interval.Entails.upper _ _ _
      availableUpper requiredUpper _ => by
      have layoutEq :
          core.layout.extendStatic (.bounds .none (.some requiredUpper)) =
            core.layout.extendStatic
              (.bounds .none (.some availableUpper)) := by
        simpa using
          (Preparation.Layout.extendStatic_upper_eq core.layout requiredUpper
            availableUpper)
      exact congrArg (fun layout => ObjectContract.translateType layout body)
        layoutEq
  | @DOTCapture.ModalIntersections.Interval.Entails.between _ _ _
      availableLower availableUpper requiredLower requiredUpper _ _ => by
      have layoutEq :
          core.layout.extendStatic
              (.bounds (.some requiredLower) (.some requiredUpper)) =
            core.layout.extendStatic
              (.bounds (.some availableLower) (.some availableUpper)) := by
        simpa using
          (Preparation.Layout.extendStatic_between_eq core.layout
            requiredLower requiredUpper availableLower availableUpper)
      exact congrArg (fun layout => ObjectContract.translateType layout body)
        layoutEq

end DOTCaptureToManySortedFC.ModalIntersections.IntervalMorphism
