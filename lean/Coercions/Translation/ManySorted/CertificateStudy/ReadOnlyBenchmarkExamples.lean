import Coercions.Translation.ManySorted.CertificateStudy.ReadOnlyBenchmark
import Coercions.Translation.ManySorted.CertificateStudy.Metrics

/-!
# Checked regressions for the read-only separation benchmark

The program is inspired by Capybara's read-only `runParallel` example, but it
tests only static access separation and modal compilation.  Its runtime is a
sequential unit program and supplies no concurrency, mutation, allocation, or
freshness semantics.
-/

namespace DOTCaptureToManySortedFC.CertificateStudy.ReadOnlyBenchmarkExamples

open DOTCaptureToManySortedFC.CertificateStudy.ReadOnlyBenchmark
open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.Compiler
open DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.CertificateStudy.Metrics

private def success? {alpha : Type} : Except Error alpha -> Option alpha
  | .ok value => some value
  | .error _ => none

def compiled? := success? (compileTerm Context.nil Source.programTyping)
def stableUseCompiled? :=
  success? (compileTerm Context.nil Source.stableUseProgramTyping)

#guard compiled?.isSome
#guard stableUseCompiled?.isSome

def compiled := compiled?.get (by native_decide)
def stableUseCompiled := stableUseCompiled?.get (by native_decide)

theorem standalone_checker_accepts :
    ManySortedFC.Tm.check Core.nil.target compiled.term =
      some compiled.checked :=
  compiled.accepted

theorem stable_negative_use_checker_accepts :
    ManySortedFC.Tm.check Core.nil.target stableUseCompiled.term =
      some stableUseCompiled.checked :=
  stableUseCompiled.accepted

/-! ## Literal erasure and genuine execution -/

def expectedRuntime : ManySortedFC.Runtime.Tm 0 :=
  .let' .unit
    (.force
      (.app
        (.app
          (.lam
            (.lam
              (.suspend
                (.let' (.app (.var 1) .unit)
                  (.app (.var 1) .unit)))))
          (.lam .unit))
        (.lam .unit)))

theorem source_erasure_is_expected :
    Core.nil.eraseTerm Source.program = expectedRuntime := by
  native_decide

theorem target_erasure_is_expected :
    compiled.term.erase = expectedRuntime := by
  native_decide

theorem literal_exact_erasure :
    compiled.term.erase = Core.nil.eraseTerm Source.program := by
  rw [target_erasure_is_expected, source_erasure_is_expected]

theorem erased_program_executes :
    ManySortedFC.Runtime.Steps compiled.term.erase .unit := by
  rw [target_erasure_is_expected]
  exact .tail
    (.tail
      (.tail
        (.tail
          (.tail
            (.tail (.single (.zeta .unit))
              (.forceSuspension (.appFunction (.beta .lam))))
            (.forceSuspension (.beta .lam)))
          .forceBeta)
        (.letRhs (.beta .unit)))
      (.zeta .unit))
    (.beta .unit)

def expectedStableUseRuntime : ManySortedFC.Runtime.Tm 0 :=
  .let' .unit (.app (.lam .unit) (.var 0))

theorem stable_negative_use_erases_exactly :
    stableUseCompiled.term.erase = expectedStableUseRuntime ∧
      Core.nil.eraseTerm Source.stableUseProgram = expectedStableUseRuntime := by
  native_decide

theorem stable_negative_use_executes :
    ManySortedFC.Runtime.Steps stableUseCompiled.term.erase .unit := by
  rw [stable_negative_use_erases_exactly.1]
  exact .tail (.single (.zeta .unit)) (.beta .unit)

/-! ## Repeated-label identity and constraint retention -/

def normalizedSourceSignature :
    DOTCapture.Intersections.Signature
      (DOTCapture.ModalIntersections.Interface.Expr []) :=
  { entries :=
      [ DOTCapture.Intersections.Entry.type Source.typeLabel
          [⟨(DOTCapture.ModalIntersections.StaticExpr.type .one),
            (DOTCapture.ModalIntersections.StaticExpr.type .one)⟩],
        DOTCapture.Intersections.Entry.capture Source.captureLabel
          [⟨(DOTCapture.ModalIntersections.StaticExpr.capture .empty),
              (DOTCapture.ModalIntersections.StaticExpr.capture
                (.ref (.localCaptureMember Source.captureLabel)))⟩,
            ⟨(DOTCapture.ModalIntersections.StaticExpr.capture .empty),
              (DOTCapture.ModalIntersections.StaticExpr.capture
                (.ref (.localCaptureMember Source.captureLabel)))⟩] ] }

theorem repeated_capture_label_collects_once :
    Source.repeatedInterface.collect = .ok normalizedSourceSignature := by
  rfl

theorem normalized_layout_has_two_names_and_three_occurrences :
    normalizedSourceSignature.entries.length = 2 ∧
      normalizedSourceSignature.occurrenceCount = 3 ∧
      (normalizedSourceSignature.constraintsAt Source.captureLabel).length = 2 := by
  native_decide

def preparedObject? :=
  DOTCaptureToManySortedFC.ModalIntersections.ObjectContract.prepare
    Layout.empty (Source.objectType (scope := []))

#guard preparedObject?.toOption.isSome

def preparedObject := preparedObject?.toOption.get (by native_decide)

/-- `C_rep`, `A`, and one shared `C`; the repeated `C` declarations do not
allocate a second capture name. -/
theorem target_allocates_one_name_per_source_label :
    preparedObject.symbols =
      [ManySortedFC.StaticSort.capture, ManySortedFC.StaticSort.type,
        ManySortedFC.StaticSort.capture] := by
  native_decide

/-- Two representation-capture constraints, two `A` bounds, and both pairs
of repeated `C` bounds are retained. -/
theorem target_retains_every_object_constraint :
    preparedObject.relations.length = 8 := by
  native_decide

/-! ## The decisive positive and negative separation cases -/

def usesReadOnlyRule {scope : DOTCapture.ModalIntersections.Sig}
    {context : DOTCapture.ModalIntersections.Ctx scope}
    {assumptions : DOTCapture.ModalIntersections.ModalAssumptions scope}
    {left right : DOTCapture.ModalIntersections.Capture scope} :
    DOTCapture.ModalIntersections.Separate context assumptions left right → Bool
  | .readOnly _ _ => true
  | _ => false

theorem positive_overlap_uses_read_only_not_disjointness :
    usesReadOnlyRule
      (Source.sharedReadOnlySeparation
        (environment := DOTCapture.ModalIntersections.TypingEnv.nil)) = true :=
  rfl

abbrev WritableOverlapScope : ManySortedFC.Sig :=
  [] ▹ .symbol .capture

def writableOverlapContext : ManySortedFC.Ctx WritableOverlapScope :=
  ManySortedFC.Ctx.nil.extendCaptureSymbol

def abstractRoot : ManySortedFC.Capture WritableOverlapScope :=
  .cvar .here

/-- The only read-only certificate available for both sides proves the
read/read proposition, not the required read/write proposition. -/
def attemptedReadOnlyOverlap : ManySortedFC.Evidence .separate
    WritableOverlapScope :=
  .separateReadOnly (.modeReadOnly abstractRoot)
    (.modeReadOnly abstractRoot)

def writableOverlapTheory : ManySortedFC.Theory WritableOverlapScope []
    [.separate] :=
  .cons (.separate (.readOnly abstractRoot) abstractRoot) .nil

def attemptedWritableEvidence : ManySortedFC.EvidenceArgs
    WritableOverlapScope [.separate] :=
  .cons attemptedReadOnlyOverlap .nil

theorem writable_same_root_overlap_is_rejected :
    ManySortedFC.Theory.checkModel writableOverlapContext
      writableOverlapTheory .nil attemptedWritableEvidence = none := by
  native_decide

/-! ## Reviewable certificate and runtime costs -/

def benchmarkOverhead : Overhead := overhead compiled.term

theorem benchmark_overhead_snapshot :
    benchmarkOverhead =
      { annotatedTermNodes := 28
        logicalEvidenceNodes := 54
        theorySymbols := 10
        theoryConstraints := 16
        modelSymbolArguments := 5
        modelEvidenceArguments := 9
        adapterSites := 3
        adapterNodes := 5
        runtimeNodes := 19
        runtimeNodesWithoutAdapters := 19
        adapterRuntimeNodeDelta := 0
        evidencePerRuntimePercent := 284
        annotatedPerRuntimePercent := 147 } := by
  native_decide

def compilationReport :=
  DOTCaptureToManySortedFC.ModalIntersections.CompilerMetrics.ofCompiledTerm
    compiled

theorem independent_report_accepts_and_matches_erasure :
    compilationReport.checkerAccepted = true ∧
      compilationReport.checkerIndicesMatch = true ∧
      compilationReport.literalErasureMatches = true := by
  native_decide

theorem benchmark_shape_snapshot :
    compilationReport.source.objectLets = 1 ∧
      compilationReport.source.objects = 1 ∧
      compilationReport.source.staticLambdas = 2 ∧
      compilationReport.source.staticApplications = 2 ∧
      compilationReport.source.applications = 4 ∧
      compilationReport.source.modalLocks = 1 ∧
      compilationReport.source.modalUnlocks = 1 ∧
      compilationReport.target.packages = 1 ∧
      compilationReport.target.opens = 1 ∧
      compilationReport.target.staticApplications = 2 ∧
      compilationReport.target.modalLocks = 1 ∧
      compilationReport.target.modalUnlocks = 1 ∧
      compilationReport.runtime.lets = 2 ∧
      compilationReport.runtime.applications = 4 ∧
      compilationReport.runtime.suspensions = 1 ∧
      compilationReport.runtime.forces = 1 := by
  native_decide

end DOTCaptureToManySortedFC.CertificateStudy.ReadOnlyBenchmarkExamples
