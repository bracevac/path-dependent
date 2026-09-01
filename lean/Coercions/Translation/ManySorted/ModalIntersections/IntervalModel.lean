import Coercions.Translation.ManySorted.ModalIntersections.EvidenceContext
import Coercions.ManySortedFC.TheoryModelChecker
import Coercions.DOT.Captures.ModalIntersections.StaticTyping

/-!
# Checked models of cumulative lexical intervals

A source interval witness is compiled in the ambient context.  Its endpoint
derivations first cross the cumulative evidence compiler; the resulting
one-symbol model then crosses the standalone target model checker.  The
modeled interval theory is never added to the context used to prove its own
obligations.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.IntervalModel

open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext

namespace Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev StaticSort := DOTCapture.ModalIntersections.StaticSort
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr
abbrev Interval := DOTCapture.ModalIntersections.Interval
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev SymbolArgs := ManySortedFC.SymbolArgs
abbrev EvidenceArgs := ManySortedFC.EvidenceArgs

end Target

/-- The canonical one-symbol assignment supplied for a prepared interval. -/
def symbolArgs {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sort : Source.StaticSort} {witness : Source.StaticExpr sort sourceScope}
    (prepared : PreparedStaticExpr core witness) :
    Target.SymbolArgs targetScope [translateSort sort] :=
  .cons prepared.targetExpression .nil

/-- Exact evidence-compilation provenance, indexed by the source interval
derivation and the target evidence spine it produced. -/
inductive EvidenceCompilation {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (compiler : EvidenceElaboration.Compiler core)
    {sort : Source.StaticSort} {witness : Source.StaticExpr sort sourceScope} :
    {interval : Source.Interval sort sourceScope} ->
    (satisfaction : DOTCapture.ModalIntersections.Interval.SatisfiedBy
      environment.bindings witness interval) ->
    Target.EvidenceArgs targetScope (intervalRelations interval) -> Type where
  | unbounded :
      EvidenceCompilation compiler
        (DOTCapture.ModalIntersections.Interval.SatisfiedBy.unbounded)
        .nil
  | lower {lower : Source.StaticExpr sort sourceScope}
      {proof : DOTCapture.ModalIntersections.Includes environment.bindings
        lower witness}
      (compiled : CompiledInclusion core lower witness)
      (compiledEquation : compileIncludes? compiler.leaves proof =
        some compiled) :
      EvidenceCompilation compiler
        (DOTCapture.ModalIntersections.Interval.SatisfiedBy.lower proof)
        (.cons compiled.evidence .nil)
  | upper {upper : Source.StaticExpr sort sourceScope}
      {proof : DOTCapture.ModalIntersections.Includes environment.bindings
        witness upper}
      (compiled : CompiledInclusion core witness upper)
      (compiledEquation : compileIncludes? compiler.leaves proof =
        some compiled) :
      EvidenceCompilation compiler
        (DOTCapture.ModalIntersections.Interval.SatisfiedBy.upper proof)
        (.cons compiled.evidence .nil)
  | between {lower upper : Source.StaticExpr sort sourceScope}
      {lowerProof : DOTCapture.ModalIntersections.Includes
        environment.bindings lower witness}
      {upperProof : DOTCapture.ModalIntersections.Includes
        environment.bindings witness upper}
      (lowerCompiled : CompiledInclusion core lower witness)
      (lowerEquation : compileIncludes? compiler.leaves lowerProof =
        some lowerCompiled)
      (upperCompiled : CompiledInclusion core witness upper)
      (upperEquation : compileIncludes? compiler.leaves upperProof =
        some upperCompiled) :
      EvidenceCompilation compiler
        (DOTCapture.ModalIntersections.Interval.SatisfiedBy.between
          lowerProof upperProof)
        (.cons lowerCompiled.evidence
          (.cons upperCompiled.evidence .nil))

/-- The evidence spine generated from one supplied source satisfaction
derivation, retaining the exact result equation of every inclusion leaf. -/
structure CompiledEvidence {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (compiler : EvidenceElaboration.Compiler core)
    {sort : Source.StaticSort} {witness : Source.StaticExpr sort sourceScope}
    {interval : Source.Interval sort sourceScope}
    (satisfaction : DOTCapture.ModalIntersections.Interval.SatisfiedBy
      environment.bindings witness interval) where
  evidence : Target.EvidenceArgs targetScope (intervalRelations interval)
  provenance : EvidenceCompilation compiler satisfaction evidence

/-- Compile endpoint derivations in source order.  Each leaf is independently
prepared and checked by `compileIncludes?` before entering the model. -/
def compileEvidence? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (compiler : EvidenceElaboration.Compiler core)
    {sort : Source.StaticSort} {witness : Source.StaticExpr sort sourceScope}
    {interval : Source.Interval sort sourceScope}
    (satisfaction : DOTCapture.ModalIntersections.Interval.SatisfiedBy
      environment.bindings witness interval) :
    Option (CompiledEvidence compiler satisfaction) := by
  cases satisfaction with
  | unbounded =>
      exact some { evidence := .nil, provenance := .unbounded }
  | @lower lower proof =>
      exact do
        match compiledEquation : compileIncludes? compiler.leaves proof with
        | none => none
        | some compiled =>
            pure
              { evidence := .cons compiled.evidence .nil
                provenance := .lower compiled compiledEquation }
  | @upper upper proof =>
      exact do
        match compiledEquation : compileIncludes? compiler.leaves proof with
        | none => none
        | some compiled =>
            pure
              { evidence := .cons compiled.evidence .nil
                provenance := .upper compiled compiledEquation }
  | @between lower upper lowerProof upperProof =>
      exact do
        match lowerEquation : compileIncludes? compiler.leaves lowerProof with
        | none => none
        | some lowerCompiled =>
            match upperEquation : compileIncludes? compiler.leaves upperProof with
            | none => none
            | some upperCompiled =>
                pure
                  { evidence := .cons lowerCompiled.evidence
                      (.cons upperCompiled.evidence .nil)
                    provenance := .between lowerCompiled lowerEquation
                      upperCompiled upperEquation }

/-- A candidate interval model retained only after the standalone model
checker validates its exact witness and evidence spine in `core.target`.
The modeled theory is deliberately absent from that checking context. -/
structure CheckedModel {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {sort : Source.StaticSort} {interval : Source.Interval sort sourceScope}
    {witness : Source.StaticExpr sort sourceScope}
    (preparedInterval : PreparedStatic core interval)
    (preparedWitness : PreparedStaticExpr core witness)
    (evidence : Target.EvidenceArgs targetScope
      (intervalRelations interval)) where
  satisfaction : ManySortedFC.Theory.SatisfiedBy core.target
    (symbolArgs preparedWitness) preparedInterval.theory evidence
  satisfactionAcceptance : ManySortedFC.Theory.checkSatisfaction core.target
    (symbolArgs preparedWitness) preparedInterval.theory evidence =
      some satisfaction
  checked : ManySortedFC.Theory.CheckedModel core.target
    preparedInterval.theory
  checkerAcceptance : ManySortedFC.Theory.checkModel core.target
    preparedInterval.theory (symbolArgs preparedWitness) evidence =
      some checked
  symbolsExact : checked.symbols = symbolArgs preparedWitness
  evidenceExact : checked.evidence = evidence

/-- Cross the target model checker without opening the modeled theory.  This
lower-level boundary is also useful for negative checker regressions. -/
def check? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {sort : Source.StaticSort} {interval : Source.Interval sort sourceScope}
    {witness : Source.StaticExpr sort sourceScope}
    (preparedInterval : PreparedStatic core interval)
    (preparedWitness : PreparedStaticExpr core witness)
    (evidence : Target.EvidenceArgs targetScope
      (intervalRelations interval)) :
    Option (CheckedModel preparedInterval preparedWitness evidence) :=
  match satisfactionAcceptance : ManySortedFC.Theory.checkSatisfaction
      core.target (symbolArgs preparedWitness) preparedInterval.theory
      evidence with
  | none => none
  | some satisfaction =>
      let checked : ManySortedFC.Theory.CheckedModel core.target
          preparedInterval.theory :=
        { symbols := symbolArgs preparedWitness
          evidence
          satisfies := satisfaction }
      some
        { satisfaction
          satisfactionAcceptance
          checked
          checkerAcceptance := by
            simp [ManySortedFC.Theory.checkModel, satisfactionAcceptance,
              checked]
          symbolsExact := rfl
          evidenceExact := rfl }

/-- Complete source-indexed interval-model artifact. -/
structure CompiledModel {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (compiler : EvidenceElaboration.Compiler core)
    {sort : Source.StaticSort} {interval : Source.Interval sort sourceScope}
    {witness : Source.StaticExpr sort sourceScope}
    (preparedInterval : PreparedStatic core interval)
    (preparedWitness : PreparedStaticExpr core witness)
    (satisfaction : DOTCapture.ModalIntersections.Interval.SatisfiedBy
      environment.bindings witness interval) where
  compiledEvidence : CompiledEvidence compiler satisfaction
  model : CheckedModel preparedInterval preparedWitness
    compiledEvidence.evidence
  modelChecked : check? preparedInterval preparedWitness
    compiledEvidence.evidence = some model

/-- Compile a supplied source model, then independently check the completed
target model. -/
def compileWith? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (compiler : EvidenceElaboration.Compiler core)
    {sort : Source.StaticSort} {interval : Source.Interval sort sourceScope}
    {witness : Source.StaticExpr sort sourceScope}
    (preparedInterval : PreparedStatic core interval)
    (preparedWitness : PreparedStaticExpr core witness)
    (satisfaction : DOTCapture.ModalIntersections.Interval.SatisfiedBy
      environment.bindings witness interval) :
    Option (CompiledModel compiler preparedInterval preparedWitness
      satisfaction) := do
  let compiledEvidence <- compileEvidence? compiler satisfaction
  match modelChecked : check? preparedInterval preparedWitness
      compiledEvidence.evidence with
  | none => none
  | some model => some { compiledEvidence, model, modelChecked }

/-- Public executable entry point from an evidence-complete compiler context. -/
def compile? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {sort : Source.StaticSort} {interval : Source.Interval sort sourceScope}
    {witness : Source.StaticExpr sort sourceScope}
    (preparedInterval : PreparedStatic context.core interval)
    (preparedWitness : PreparedStaticExpr context.core witness)
    (satisfaction : DOTCapture.ModalIntersections.Interval.SatisfiedBy
      environment.bindings witness interval) :
    Option (CompiledModel context.compiler preparedInterval preparedWitness
      satisfaction) :=
  compileWith? context.compiler preparedInterval preparedWitness satisfaction

end DOTCaptureToManySortedFC.ModalIntersections.IntervalModel
