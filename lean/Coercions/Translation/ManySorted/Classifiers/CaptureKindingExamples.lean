import Coercions.Translation.ManySorted.Classifiers.CaptureBounds
import Coercions.ManySortedFC.TermChecker
import Coercions.ManySortedFC.Erasure
import Coercions.ManySortedFC.TheoryModelChecker

/-!
# A checked ground-kind capture regression

This example keeps classifier kinds ground. A static abstraction binds one
ordinary target capture symbol `c` together with the checked assumption that
`c` has kind `onlyIO`. The returned function really closes over its `file`
argument, and the closure projection is justified through that opened kind
assumption rather than through an empty capture.
-/

namespace DOTCaptureToManySortedFC.Classifiers.CaptureKindingExamples

namespace Source

export DOTCaptureToManySortedFC.Classifiers.Source
  (Classifier ProjectedCapture Term Program)

end Source

open ManySortedFC

/-! ## Ground classifier tree and kind -/

def shared : Classifier := .child 0 .top
def control : Classifier := .child 0 shared
def io : Classifier := .child 1 shared

def onlyShared : Classifier.Kind := Classifier.Kind.classifier shared
def onlyControl : Classifier.Kind := Classifier.Kind.classifier control
def onlyIO : Classifier.Kind := Classifier.Kind.classifier io

/-- `only Shared except Control`: the sibling `IO` branch remains allowed. -/
def allowedKind : Classifier.Kind :=
  Classifier.Kind.subtract onlyShared onlyControl

theorem only_io_is_allowed : Classifier.Kind.Subkind onlyIO allowedKind := by
  native_decide

theorem only_control_is_not_allowed :
    ¬ Classifier.Kind.Subkind onlyControl allowedKind := by
  native_decide

/-! ## The opened kind-bounded capture -/

def captureBinder : CaptureBounds.Source.Binder where
  bound := onlyIO

def captureTheory : Theory [] [.capture] [.captureHasKind] :=
  CaptureBounds.lower captureBinder

/-! ## A nonempty model of the bound

The model checker cannot assume the proposition exported by `captureTheory`
while constructing its model. Here it receives a projected term capability
and an independently checked `captureHasKindProject` certificate.
-/

abbrev ModelScope : Sig := ([] : Sig) ▹ .term

def modelContext : Ctx ModelScope :=
  Ctx.nil.extendTerm .one

/-- The proposition being packaged is not in scope while its witness is
checked; a model cannot discharge its own kind bound. -/
theorem model_scope_has_no_kind_assumption
    (index : BVar ModelScope (.evidence .captureHasKind)) : False :=
  nomatch index

def nonemptyModelWitness : SymbolArgs ModelScope [.capture] :=
  .cons (.capture (.project (.singleton .here) onlyIO)) .nil

def nonemptyModelEvidence : EvidenceArgs ModelScope [.captureHasKind] :=
  .cons (.captureHasKindProject (.singleton .here) onlyIO) .nil

theorem nonempty_kind_bound_model_is_independently_accepted :
    (Theory.checkModel modelContext (CaptureBounds.lower captureBinder)
      nonemptyModelWitness nonemptyModelEvidence).isSome = true := by
  native_decide

/-- A true certificate for a different endpoint cannot satisfy the bound. -/
def wrongModelEvidence : EvidenceArgs ModelScope [.captureHasKind] :=
  .cons (.captureHasKindProject (.singleton .here) onlyShared) .nil

theorem wrong_kind_endpoint_is_rejected :
    Theory.checkModel modelContext (CaptureBounds.lower captureBinder)
      nonemptyModelWitness wrongModelEvidence = none := by
  native_decide

abbrev BoundScope : Sig :=
  StaticScope [] [.capture] [.captureHasKind]

abbrev FileScope : Sig := BoundScope ▹ .term
abbrev ArgumentScope : Sig := FileScope ▹ .term

def boundContext : Ctx BoundScope :=
  Ctx.nil.extendTheory captureTheory

def boundCapture : Capture BoundScope :=
  CaptureBounds.openedCapture

def capturedCallable : Ty BoundScope :=
  .capturing boundCapture (.arr .one .one)

def fileContext : Ctx FileScope :=
  boundContext.extendTerm capturedCallable

def argumentContext : Ctx ArgumentScope :=
  fileContext.extendTerm .one

def fileSingleton : Capture FileScope := .singleton .here

/-- The inner lambda advertises a genuinely nonempty, filtered free root. -/
def filteredFile : Capture FileScope :=
  .project fileSingleton allowedKind

/-! ## Evidence used by the inner lambda -/

/-- The precise `file` root is bounded by the captured type of the parameter. -/
def fileRootBelowBound : Evidence (.inclusion .capture) ArgumentScope :=
  .captureVariable (.there .here)

/-- The `c : onlyIO` premise exported by `CaptureBounds.lower`, weakened
below the two ordinary lambda binders. -/
def boundHasOnlyIO : Evidence .captureHasKind ArgumentScope :=
  (CaptureBounds.openedKindEvidence (scope := [])).weaken.weaken

/-- Ground widening is checked by recomputing `onlyIO <= allowedKind`. -/
def boundHasAllowedKind : Evidence .captureHasKind ArgumentScope :=
  .captureHasKindWiden boundHasOnlyIO onlyIO allowedKind

/-- Downward closure transfers the ground kind from `c` to the precise
singleton root of `file`. -/
def fileHasAllowedKind : Evidence .captureHasKind ArgumentScope :=
  .captureHasKindSubcapture fileRootBelowBound boundHasAllowedKind

/-- Projection completeness turns the kinded singleton into the equality
`project {file} K = {file}`. -/
def filteredFileComplete : Evidence (.equality .capture) ArgumentScope :=
  .equalityCaptureProjectComplete fileHasAllowedKind

/-- Orient projection completeness so that the real use `{file}` enters the
declared projected closure. -/
def fileRootIntoFiltered : Evidence (.inclusion .capture) ArgumentScope :=
  .equalityToInclusion (.equalitySymm filteredFileComplete)

def innerLambdaBound : Capture ArgumentScope :=
  .union filteredFile.weaken (.singleton .here)

def fileRootIntoInnerBound : Evidence (.inclusion .capture) ArgumentScope :=
  .inclusionTrans fileRootIntoFiltered
    (.captureUnionLeft filteredFile.weaken (.singleton .here))

/-- The application predicts `{file} ∪ ∅`; its nonempty branch is discharged
by the complete-projection chain above. -/
def innerBodyDischarge : Evidence (.inclusion .capture) ArgumentScope :=
  .captureUnionElim fileRootIntoInnerBound
    (.captureEmpty innerLambdaBound)

def innerBody : Tm ArgumentScope :=
  .app (.var (.there .here)) (.var .here)

def innerLambda : Tm FileScope :=
  .lam .one .one filteredFile innerBody innerBodyDischarge

theorem inner_body_discharge_is_checked :
    (Evidence.check argumentContext innerBodyDischarge).isSome = true := by
  native_decide

/-! ## Hiding the local `file` root from the outer codomain -/

/-- The projected root remains below `c`: projection first removes uses, then
`captureVariable` contracts the precise root to the parameter's capture. -/
def filteredFileBelowBound : Evidence (.inclusion .capture) FileScope :=
  .inclusionTrans
    (.captureProjectSource fileSingleton allowedKind)
    (.captureVariable .here)

def hideFileRoot : Adapter FileScope :=
  .captured filteredFileBelowBound (.identity (.arr .one .one))

def adaptedInnerLambda : Tm FileScope :=
  .adapt innerLambda hideFileRoot

theorem adapted_inner_closure_mentions_only_bound_capture :
    Tm.synth fileContext adaptedInnerLambda =
      some (.empty, capturedCallable.weaken) := by
  native_decide

/-- The codomain mentions only static `c`, never the locally bound `file`. -/
def outerLambda : Tm BoundScope :=
  .lam capturedCallable capturedCallable .empty adaptedInnerLambda
    (.captureEmpty (.union .empty (.singleton .here)))

/-- A closed target value with the interface `forall c : onlyIO` followed by
the ordinary function from `c`-captured files to `c`-captured closures. -/
def targetArtifact : Tm [] :=
  .slam captureTheory .empty outerLambda
    (.inclusionRefl (.capture .empty))

theorem target_artifact_is_independently_accepted :
    (Tm.check Ctx.nil targetArtifact).isSome = true := by
  native_decide

/-! ## Independent source erasure and runtime execution -/

def sourceCapture : Source.ProjectedCapture Unit :=
  ((Source.ProjectedCapture.base ()).only shared).except control

def sourceProgram : Source.Program Unit 0 where
  capture := sourceCapture
  term := .lam (.lam (.app (.var 1) (.var 0)))

/-- Static abstraction, kind evidence, projection annotations, and the
captured identity adapter all erase; the remaining code is exactly
`fun file => fun u => file u`. -/
theorem target_erasure_is_independently_defined_source_erasure :
    targetArtifact.erase = sourceProgram.erase := rfl

def runtimeIdentity : Runtime.Tm 0 := .lam (.var 0)

def appliedErasure : Runtime.Tm 0 :=
  .app (.app targetArtifact.erase runtimeIdentity) .unit

def afterFileBeta : Runtime.Tm 0 :=
  .app (.lam (.app (.lam (.var 0)) (.var 0))) .unit

def afterArgumentBeta : Runtime.Tm 0 :=
  .app runtimeIdentity .unit

theorem runtime_beta_file :
    Runtime.Step appliedErasure afterFileBeta :=
  .appFunction (.beta .lam)

theorem runtime_beta_argument :
    Runtime.Step afterFileBeta afterArgumentBeta :=
  .beta .unit

theorem runtime_beta_identity :
    Runtime.Step afterArgumentBeta .unit :=
  .beta .unit

theorem runtime_executes :
    Runtime.Steps appliedErasure .unit :=
  .tail
    (.tail (.single runtime_beta_file) runtime_beta_argument)
    runtime_beta_identity

/-! ## Rejected ground widening -/

/-- This premise is independently valid, so rejection isolates the false
ground side condition `onlyControl <= allowedKind`. -/
def rejectedControlWidening : Evidence .captureHasKind [] :=
  .captureHasKindWiden
    (.captureHasKindEmpty onlyControl) onlyControl allowedKind

theorem control_cannot_widen_into_allowed_kind :
    (Evidence.check Ctx.nil rejectedControlWidening).isNone = true := by
  native_decide

end DOTCaptureToManySortedFC.Classifiers.CaptureKindingExamples
