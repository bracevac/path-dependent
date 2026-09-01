import Coercions.Translation.ManySorted.CheckedFrontend.Compiler

/-!
# Checked front-end regressions

These programs begin as raw annotated syntax.  No source typing derivation is
supplied by the caller.  Successful cases run through source checking,
cumulative compilation, and the standalone target checker.  Evidence and
type failures arise before target compilation.  Unsupported sentinels test
diagnostic plumbing for forms that are outside the raw language; they do not
pretend to recognize omitted object syntax.
-/

namespace DOTCaptureToManySortedFC.CheckedFrontend.Examples

open DOTCaptureToManySortedFC.CheckedFrontend
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext

namespace Raw

def identity : RawValue [] :=
  .lam .one .one .empty .captureEmpty (.ret (.var .here))

def beta : RawTerm [] :=
  .app (.ret identity) (.ret .unit)

def zeta : RawTerm [] :=
  .letPlain .one .one .empty .refl (.ret .unit) (.ret (.var .here))

def typeInterval : Source.Interval .type [] :=
  .bounds .none .none

def typeWitness : Source.StaticExpr .type [] :=
  .type .one

def staticIdentity : RawValue [] :=
  .staticLam typeInterval .empty .refl
    (.unit : RawValue ([] ▹ .static .type))

def staticApplication : RawTerm [] :=
  .staticApp typeInterval (.one : Source.Ty ([] ▹ .static .type))
    typeWitness .unbounded (.ret staticIdentity)

/-! Bounded lexical parameters exercise context lookup rather than merely
checking an interval whose endpoints are closed expressions. -/

abbrev TypeParameterScope : Source.Sig := [] ▹ .static .type

def typeParameterInterval : Source.Interval .type [] :=
  .bounds (.some (.type .bot)) (.some (.type .top))

def typeParameterEnvironment : Source.TypingEnv TypeParameterScope :=
  DOTCapture.ModalIntersections.TypingEnv.nil.extendStatic
    typeParameterInterval

def typeParameter : Source.StaticExpr .type TypeParameterScope :=
  DOTCapture.ModalIntersections.StaticExpr.bound .here

def boundedTypeInterval : Source.Interval .type TypeParameterScope :=
  .bounds (.some (.type .bot)) (.some (.type .top))

def boundedTypeValue : RawValue TypeParameterScope :=
  .staticLam boundedTypeInterval .empty .refl
    (.unit : RawValue (TypeParameterScope ▹ .static .type))

def boundedTypeParameterApplication : RawTerm TypeParameterScope :=
  .staticApp boundedTypeInterval
    (.one : Source.Ty (TypeParameterScope ▹ .static .type))
    typeParameter
    (.between (.boundLower .here) (.boundUpper .here))
    (.ret boundedTypeValue)

/-- The requested lower endpoint is `One`, but the parameter's declared
lower endpoint is `Bottom`; `boundLower` must not accept that mismatch. -/
def mismatchedTypeInterval : Source.Interval .type TypeParameterScope :=
  .bounds (.some (.type .one)) (.some (.type .top))

def mismatchedTypeValue : RawValue TypeParameterScope :=
  .staticLam mismatchedTypeInterval .empty .refl
    (.unit : RawValue (TypeParameterScope ▹ .static .type))

def mismatchedTypeParameterApplication : RawTerm TypeParameterScope :=
  .staticApp mismatchedTypeInterval
    (.one : Source.Ty (TypeParameterScope ▹ .static .type))
    typeParameter
    (.between (.boundLower .here) (.boundUpper .here))
    (.ret mismatchedTypeValue)

abbrev CaptureParameterScope : Source.Sig := [] ▹ .static .capture

def captureParameterInterval : Source.Interval .capture [] :=
  .bounds (.some (.capture .empty)) (.some (.capture .empty))

def captureParameterEnvironment : Source.TypingEnv CaptureParameterScope :=
  DOTCapture.ModalIntersections.TypingEnv.nil.extendStatic
    captureParameterInterval

def captureParameter : Source.StaticExpr .capture CaptureParameterScope :=
  DOTCapture.ModalIntersections.StaticExpr.bound .here

def boundedCaptureInterval : Source.Interval .capture CaptureParameterScope :=
  .bounds (.some (.capture .empty)) (.some (.capture .empty))

def boundedCaptureValue : RawValue CaptureParameterScope :=
  .staticLam boundedCaptureInterval .empty .refl
    (.unit : RawValue (CaptureParameterScope ▹ .static .capture))

def boundedCaptureParameterApplication : RawTerm CaptureParameterScope :=
  .staticApp boundedCaptureInterval
    (.one : Source.Ty (CaptureParameterScope ▹ .static .capture))
    captureParameter
    (.between (.boundLower .here) (.boundUpper .here))
    (.ret boundedCaptureValue)

/-- The requested upper endpoint is read-only empty, but the parameter's
declared upper endpoint is empty; `boundUpper` must reject the mismatch. -/
def mismatchedCaptureInterval : Source.Interval .capture
    CaptureParameterScope :=
  .bounds (.some (.capture .empty))
    (.some (.capture (.readOnly .empty)))

def mismatchedCaptureValue : RawValue CaptureParameterScope :=
  .staticLam mismatchedCaptureInterval .empty .refl
    (.unit : RawValue (CaptureParameterScope ▹ .static .capture))

def mismatchedCaptureParameterApplication : RawTerm CaptureParameterScope :=
  .staticApp mismatchedCaptureInterval
    (.one : Source.Ty (CaptureParameterScope ▹ .static .capture))
    captureParameter
    (.between (.boundLower .here) (.boundUpper .here))
    (.ret mismatchedCaptureValue)

def package : RawValue [] :=
  .pack typeInterval (.one : Source.Ty ([] ▹ .static .type)) typeWitness
    .empty .unbounded .refl .unit

def packageOpen : RawTerm [] :=
  .openPackage typeInterval (.one : Source.Ty ([] ▹ .static .type))
    .one .empty .captureEmpty (.ret package) (.ret (.var .here))

/-- A nontrivial function adapter whose source and target types coincide.
The certificate requests the structural function rule rather than identity,
so the target is allowed to eta-expand and correctness remains
`AdministrativeEq`. -/
def etaAdapter : RawTerm [] :=
  .ret (.adapt (.capturing .empty (.arr .one .one))
    (.captured .refl (.function .identity .identity)) identity)

def badLambdaEvidence : RawTerm [] :=
  .ret (.lam .one .one .empty .captureUnionRight
    (.ret (.var .here)))

def badApplication : RawTerm [] :=
  .app (.ret identity) (.ret identity)

def badStaticCertificate : RawTerm [] :=
  .staticApp typeInterval (.one : Source.Ty ([] ▹ .static .type))
    typeWitness (.lower .refl) (.ret staticIdentity)

def badAdapter : RawTerm [] :=
  .ret (.adapt .top .identity .unit)

abbrev RootScope : Source.Sig := [] ▹ .term

def readOnlyRoot : Source.Capture RootScope :=
  .readOnly (.singleton (.var .here))

def readOnlySeparation :
    DOTCapture.ModalIntersections.SeparationContext 2 RootScope :=
  .cons (.cons .nil readOnlyRoot) readOnlyRoot

def readOnlyModes :
    DOTCapture.ModalIntersections.ModeContext [.readOnly, .readOnly]
      RootScope :=
  .cons (.cons .nil readOnlyRoot) readOnlyRoot

def readOnlyRequirements :
    DOTCapture.ModalIntersections.ModalRequirements 2
      [.readOnly, .readOnly] RootScope :=
  .mk readOnlySeparation readOnlyModes

def oneEntryCoverage : SeparationCoverage RootScope 1 :=
  .cons .nil .nil

def readOnlyPair : SeparateCertificate RootScope :=
  .readOnly .readOnly .readOnly

def readOnlySeparationCoverage : SeparationCoverage RootScope 2 :=
  .cons oneEntryCoverage (.cons .nil readOnlyPair readOnlyPair)

def readOnlyModeCoverage : ModeCoverage RootScope [.readOnly, .readOnly] :=
  .cons (.cons .nil .readOnly) .readOnly

def readOnlyLocked : RawValue RootScope :=
  .lock readOnlyRequirements .one .empty .refl (.ret .unit)

def readOnlyUnlocked : RawTerm RootScope :=
  .unlock readOnlyRequirements .one readOnlyModeCoverage
    readOnlySeparationCoverage (.ret readOnlyLocked)

/-- Two read-only views of the same stable root are accepted and then run
through lock/unlock in the generated target artifact. -/
def readOnlyOverlap : RawTerm [] :=
  .app
    (.ret (.lam .one .one .empty .captureEmpty readOnlyUnlocked))
    (.ret .unit)

def writableRoot : Source.Capture RootScope :=
  .singleton (.var .here)

def writableSeparation :
    DOTCapture.ModalIntersections.SeparationContext 2 RootScope :=
  .cons (.cons .nil writableRoot) writableRoot

def writableModes :
    DOTCapture.ModalIntersections.ModeContext [.writable, .writable]
      RootScope :=
  .cons (.cons .nil writableRoot) writableRoot

def writableRequirements :
    DOTCapture.ModalIntersections.ModalRequirements 2
      [.writable, .writable] RootScope :=
  .mk writableSeparation writableModes

def writableModeCoverage : ModeCoverage RootScope [.writable, .writable] :=
  .cons (.cons .nil .writable) .writable

/-- This certificate tries to justify separation by read-only sharing while
both overlapping views are writable.  Structural mode checking rejects it. -/
def falseReadOnlyPair : SeparateCertificate RootScope :=
  .readOnly .writable .writable

def writableSeparationCoverage : SeparationCoverage RootScope 2 :=
  .cons oneEntryCoverage (.cons .nil falseReadOnlyPair falseReadOnlyPair)

def writableLocked : RawValue RootScope :=
  .lock writableRequirements .one .empty .refl (.ret .unit)

def writableOverlapBody : RawTerm RootScope :=
  .unlock writableRequirements .one writableModeCoverage
    writableSeparationCoverage (.ret writableLocked)

def writableOverlap : RawTerm [] :=
  .ret (.lam .one .one .empty .captureEmpty writableOverlapBody)

def recursiveBoundary : RawTerm [] :=
  .ret (.unsupported .recursiveObjectLiteral)

def objectBoundary : RawTerm [] :=
  .ret (.unsupported .objectLiteral)

def modalBoundary : RawTerm [] :=
  .unsupported .modalLockReference

end Raw

private def exceptIsOk {error value : Type} : Except error value -> Bool
  | .ok _ => true
  | .error _ => false

private def frontendErrorIs (expected : Error) :
    Except Error (CheckedTerm DOTCapture.ModalIntersections.TypingEnv.nil) ->
      Bool
  | .error actual => decide (actual = expected)
  | .ok _ => false

private def checkedTermErrorIs {scope : Source.Sig}
    {environment : Source.TypingEnv scope} (expected : Error) :
    Except Error (CheckedTerm environment) -> Bool
  | .error actual => decide (actual = expected)
  | .ok _ => false

private def pipelineFrontendErrorIs {raw : RawTerm []} (expected : Error) :
    Except PipelineError (Compiled Context.nil raw) -> Bool
  | .error (.frontend actual) => decide (actual = expected)
  | _ => false

/-! ## Source checker -/

example : exceptIsOk
    (checkTerm DOTCapture.ModalIntersections.TypingEnv.nil Raw.beta) = true := by
  native_decide

example : exceptIsOk
    (checkTerm DOTCapture.ModalIntersections.TypingEnv.nil Raw.zeta) = true := by
  native_decide

example : exceptIsOk
    (checkTerm DOTCapture.ModalIntersections.TypingEnv.nil
      Raw.staticApplication) = true := by
  native_decide

example : exceptIsOk
    (checkTerm Raw.typeParameterEnvironment
      Raw.boundedTypeParameterApplication) = true := by
  native_decide

example : exceptIsOk
    (checkTerm Raw.captureParameterEnvironment
      Raw.boundedCaptureParameterApplication) = true := by
  native_decide

example : checkedTermErrorIs .invalidInterval
    (checkTerm Raw.typeParameterEnvironment
      Raw.mismatchedTypeParameterApplication) = true := by
  native_decide

example : checkedTermErrorIs .invalidInterval
    (checkTerm Raw.captureParameterEnvironment
      Raw.mismatchedCaptureParameterApplication) = true := by
  native_decide

example : exceptIsOk
    (checkTerm DOTCapture.ModalIntersections.TypingEnv.nil Raw.packageOpen) =
      true := by
  native_decide

example : exceptIsOk
    (checkTerm DOTCapture.ModalIntersections.TypingEnv.nil Raw.etaAdapter) =
      true := by
  native_decide

example : frontendErrorIs .invalidInclusion
    (checkTerm DOTCapture.ModalIntersections.TypingEnv.nil
      Raw.badLambdaEvidence) = true := by
  native_decide

example : frontendErrorIs .typeMismatch
    (checkTerm DOTCapture.ModalIntersections.TypingEnv.nil
      Raw.badApplication) = true := by
  native_decide

example : frontendErrorIs .invalidInterval
    (checkTerm DOTCapture.ModalIntersections.TypingEnv.nil
      Raw.badStaticCertificate) = true := by
  native_decide

example : frontendErrorIs .invalidAdapter
    (checkTerm DOTCapture.ModalIntersections.TypingEnv.nil
      Raw.badAdapter) = true := by
  native_decide

example : exceptIsOk
    (checkTerm DOTCapture.ModalIntersections.TypingEnv.nil
      Raw.readOnlyOverlap) = true := by
  native_decide

example : frontendErrorIs .invalidSeparationCoverage
    (checkTerm DOTCapture.ModalIntersections.TypingEnv.nil
      Raw.writableOverlap) = true := by
  native_decide

/-- Writable overlap is rejected by finite source evidence checking; the
cumulative compiler and target checker are never invoked. -/
example : pipelineFrontendErrorIs .invalidSeparationCoverage
    (compile Context.nil Raw.writableOverlap) = true := by
  native_decide

example : frontendErrorIs (.unsupported .recursiveObjectLiteral)
    (checkTerm DOTCapture.ModalIntersections.TypingEnv.nil
      Raw.recursiveBoundary) = true := by
  native_decide

example : frontendErrorIs (.unsupported .objectLiteral)
    (checkTerm DOTCapture.ModalIntersections.TypingEnv.nil
      Raw.objectBoundary) = true := by
  native_decide

example : frontendErrorIs (.unsupported .modalLockReference)
    (checkTerm DOTCapture.ModalIntersections.TypingEnv.nil
      Raw.modalBoundary) = true := by
  native_decide

/-! ## End-to-end checked compilation -/

def betaResult := compile Context.nil Raw.beta
def zetaResult := compile Context.nil Raw.zeta
def staticResult := compile Context.nil Raw.staticApplication
def openResult := compile Context.nil Raw.packageOpen
def etaResult := compile Context.nil Raw.etaAdapter
def readOnlyResult := compile Context.nil Raw.readOnlyOverlap

example : exceptIsOk betaResult = true := by native_decide
example : exceptIsOk zetaResult = true := by native_decide
example : exceptIsOk staticResult = true := by native_decide
example : exceptIsOk openResult = true := by native_decide
example : exceptIsOk etaResult = true := by native_decide
example : exceptIsOk readOnlyResult = true := by native_decide

def betaCompiled := betaResult.toOption.get (by native_decide)
def zetaCompiled := zetaResult.toOption.get (by native_decide)
def staticCompiled := staticResult.toOption.get (by native_decide)
def openCompiled := openResult.toOption.get (by native_decide)
def etaCompiled := etaResult.toOption.get (by native_decide)
def readOnlyCompiled := readOnlyResult.toOption.get (by native_decide)

example : checkTerm DOTCapture.ModalIntersections.TypingEnv.nil Raw.beta =
    .ok betaCompiled.checked :=
  betaCompiled.sourceAccepted

example : ManySortedFC.Tm.check Core.nil.target betaCompiled.artifact.term =
    some betaCompiled.artifact.checked :=
  betaCompiled.targetAccepted

example : ManySortedFC.Tm.check Core.nil.target openCompiled.artifact.term =
    some openCompiled.artifact.checked :=
  openCompiled.targetAccepted

example : ManySortedFC.Tm.synth Core.nil.target etaCompiled.artifact.term =
    some (etaCompiled.artifact.targetUse,
      etaCompiled.artifact.targetType) :=
  etaCompiled.targetSynthesizes

example : ManySortedFC.Runtime.AdministrativeEq
    etaCompiled.artifact.term.erase
    (Core.nil.eraseTerm etaCompiled.checked.term) :=
  etaCompiled.administrativeErasure

example : ManySortedFC.Tm.check Core.nil.target
    readOnlyCompiled.artifact.term =
      some readOnlyCompiled.artifact.checked :=
  readOnlyCompiled.targetAccepted

theorem betaErasure : betaCompiled.artifact.term.erase =
    (.app (.lam (.var 0)) .unit : ManySortedFC.Runtime.Tm 0) := by
  native_decide

theorem zetaErasure : zetaCompiled.artifact.term.erase =
    (.let' .unit (.var 0) : ManySortedFC.Runtime.Tm 0) := by
  native_decide

theorem staticErasure : staticCompiled.artifact.term.erase =
    (.unit : ManySortedFC.Runtime.Tm 0) := by
  native_decide

theorem openErasure : openCompiled.artifact.term.erase =
    (.let' .unit (.var 0) : ManySortedFC.Runtime.Tm 0) := by
  native_decide

theorem readOnlyErasure : readOnlyCompiled.artifact.term.erase =
    (.app (.lam (.force (.suspend .unit))) .unit :
      ManySortedFC.Runtime.Tm 0) := by
  native_decide

theorem betaExecutes : ManySortedFC.Runtime.Steps
    betaCompiled.artifact.term.erase .unit := by
  rw [betaErasure]
  exact .single (.beta .unit)

theorem openExecutes : ManySortedFC.Runtime.Steps
    openCompiled.artifact.term.erase .unit := by
  rw [openErasure]
  exact .single (.zeta .unit)

theorem readOnlyExecutes : ManySortedFC.Runtime.Steps
    readOnlyCompiled.artifact.term.erase .unit := by
  rw [readOnlyErasure]
  exact (ManySortedFC.Runtime.Steps.single (.beta .unit)).trans
    (ManySortedFC.Runtime.Steps.single .forceBeta)

end DOTCaptureToManySortedFC.CheckedFrontend.Examples
