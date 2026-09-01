import Coercions.Translation.ManySorted.ModalIntersections.CompilerMetrics

/-!
# Certificate-study measurements

This module turns the cumulative compiler counters into explicit Stage 8
measurements.  The figures distinguish three different costs:

* annotated target syntax before erasure;
* logical certificate material checked by `ManySortedFC`;
* runtime syntax introduced specifically by structural adapters.

`eraseWithoutAdapters` is a measurement baseline, not an alternative
semantics.  It follows ordinary target erasure exactly except that an
`adapt` node erases to its operand.  Comparing it with real erasure isolates
the eta/administrative runtime syntax introduced by adapters without
pretending that those adapters preserve literal syntax.
-/

namespace DOTCaptureToManySortedFC.CertificateStudy.Metrics

open DOTCaptureToManySortedFC.ModalIntersections.CompilerMetrics

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Tm := ManySortedFC.Tm

end Target

/-! ## Adapter-free erasure baseline -/

/-- Erase a target term while treating every structural adapter as the
identity.  Static abstraction/application, packages, evidence, and modal
proof binders are forgotten exactly as in ordinary target erasure. -/
def eraseWithoutAdaptersWith {scope : Target.Sig} (term : Target.Tm scope)
    {runtimeScope : Nat}
    (rho : ManySortedFC.Erasure.Renaming scope runtimeScope) :
    ManySortedFC.Runtime.Tm runtimeScope :=
  match term with
  | .var index => .var (rho index)
  | .unit => .unit
  | .lam _ _ _ body _ =>
      .lam (eraseWithoutAdaptersWith body rho.liftTerm)
  | .app function argument =>
      .app (eraseWithoutAdaptersWith function rho)
        (eraseWithoutAdaptersWith argument rho)
  | .let' _ _ rhs body _ =>
      .let' (eraseWithoutAdaptersWith rhs rho)
        (eraseWithoutAdaptersWith body rho.liftTerm)
  | .adapt inner _ => eraseWithoutAdaptersWith inner rho
  | @ManySortedFC.Tm.lock _ separationCount modes _ _ _ body _ =>
      .suspend (eraseWithoutAdaptersWith body
        (rho.liftModal separationCount modes))
  | .unlock _ inner _ => .force (eraseWithoutAdaptersWith inner rho)
  | @ManySortedFC.Tm.slam _ symbols relations _ _ body _ =>
      eraseWithoutAdaptersWith body (rho.liftStatic symbols relations)
  | .sapp _ function _ _ => eraseWithoutAdaptersWith function rho
  | .pack _ _ _ _ _ payload _ => eraseWithoutAdaptersWith payload rho
  | @ManySortedFC.Tm.«open» _ symbols relations _ _ _ _ package body _ =>
      .let' (eraseWithoutAdaptersWith package rho)
        (eraseWithoutAdaptersWith body
          (rho.liftPayload symbols relations))
  | .use inner _ => eraseWithoutAdaptersWith inner rho

/-- Closed form of the adapter-free measurement baseline. -/
def eraseWithoutAdapters {scope : Target.Sig} (term : Target.Tm scope) :
    ManySortedFC.Runtime.Tm scope.termCount :=
  eraseWithoutAdaptersWith term (ManySortedFC.Erasure.Renaming.identity scope)

/-! ## Per-artifact overhead -/

/-- Saturating percentage, rounded down.  A zero denominator reports zero. -/
def percent (part whole : Nat) : Nat :=
  if whole = 0 then 0 else part * 100 / whole

/-- Reviewable cost summary for one emitted target artifact. -/
structure Overhead where
  annotatedTermNodes : Nat
  logicalEvidenceNodes : Nat
  theorySymbols : Nat
  theoryConstraints : Nat
  modelSymbolArguments : Nat
  modelEvidenceArguments : Nat
  adapterSites : Nat
  adapterNodes : Nat
  runtimeNodes : Nat
  runtimeNodesWithoutAdapters : Nat
  /-- Nodes present only because real adapter erasure eta-expands or inserts
  administrative runtime structure.  Saturating subtraction makes the
  measurement total even for unusual hand-written artifacts. -/
  adapterRuntimeNodeDelta : Nat
  evidencePerRuntimePercent : Nat
  annotatedPerRuntimePercent : Nat
deriving DecidableEq, Repr

/-- Measure a target term directly; no retained compiler proof is consulted. -/
def overhead {scope : Target.Sig} (term : Target.Tm scope) : Overhead :=
  let target := targetStats term
  let certificate := certificateStats term
  let runtime := runtimeStats term.erase
  let baseline := runtimeStats (eraseWithoutAdapters term)
  { annotatedTermNodes := target.termNodes
    logicalEvidenceNodes := certificate.evidenceNodes
    theorySymbols := certificate.theorySymbols
    theoryConstraints := certificate.theoryConstraints
    modelSymbolArguments := certificate.symbolArguments
    modelEvidenceArguments := certificate.evidenceArguments
    adapterSites := target.adapterSites
    adapterNodes := target.adapterNodes
    runtimeNodes := runtime.nodes
    runtimeNodesWithoutAdapters := baseline.nodes
    adapterRuntimeNodeDelta := runtime.nodes - baseline.nodes
    evidencePerRuntimePercent := percent certificate.evidenceNodes runtime.nodes
    annotatedPerRuntimePercent := percent target.termNodes runtime.nodes }

namespace Overhead

/-- Additive corpus totals.  Percentages are recomputed from the totals rather
than added artifact by artifact. -/
def add (left right : Overhead) : Overhead :=
  let evidence := left.logicalEvidenceNodes + right.logicalEvidenceNodes
  let annotated := left.annotatedTermNodes + right.annotatedTermNodes
  let runtime := left.runtimeNodes + right.runtimeNodes
  { annotatedTermNodes := annotated
    logicalEvidenceNodes := evidence
    theorySymbols := left.theorySymbols + right.theorySymbols
    theoryConstraints := left.theoryConstraints + right.theoryConstraints
    modelSymbolArguments :=
      left.modelSymbolArguments + right.modelSymbolArguments
    modelEvidenceArguments :=
      left.modelEvidenceArguments + right.modelEvidenceArguments
    adapterSites := left.adapterSites + right.adapterSites
    adapterNodes := left.adapterNodes + right.adapterNodes
    runtimeNodes := runtime
    runtimeNodesWithoutAdapters :=
      left.runtimeNodesWithoutAdapters + right.runtimeNodesWithoutAdapters
    adapterRuntimeNodeDelta :=
      left.adapterRuntimeNodeDelta + right.adapterRuntimeNodeDelta
    evidencePerRuntimePercent := percent evidence runtime
    annotatedPerRuntimePercent := percent annotated runtime }

end Overhead

/-- Fold a finite target corpus into one reproducible report. -/
def corpusOverhead {scope : Target.Sig} (terms : List (Target.Tm scope)) :
    Option Overhead :=
  match terms with
  | [] => none
  | first :: rest =>
      some (rest.foldl (fun total term => total.add (overhead term))
        (overhead first))

end DOTCaptureToManySortedFC.CertificateStudy.Metrics
