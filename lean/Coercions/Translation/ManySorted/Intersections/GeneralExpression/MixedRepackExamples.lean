import Coercions.Translation.ManySorted.Intersections.GeneralExpression.RecursiveExamples

/-!
# Mixed-member open, negative application, and positive repacking

This regression keeps one payload at the model-dependent type `C · A`.
Opening the object establishes the shared `A` and `C` identities.  A negative
identity consumer receives that stable payload and returns the object
positively, which forces the compiler to repack the same payload.
-/

namespace DOTCaptureToManySortedFC.Intersections.GeneralExpression.MixedRepackExamples

open DOTCapture.Intersections.GeneralExpression
open DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler
open DOTCaptureToManySortedFC.Intersections.GeneralExpression.Recursive
open DOTCaptureToManySortedFC.Intersections.GeneralExpression.RecursiveExamples

def typeLabelA : DOTCapture.Intersections.Source.Label := 31
def captureLabelC : DOTCapture.Intersections.Source.Label := 32

def mixedInterface {scope : Scope} : Interface scope :=
  .inter
    (.typeMember typeLabelA .one .one)
    (.captureMember captureLabelC .empty .empty)

def mixedObject {scope : Scope} : ObjectType scope :=
  .mk mixedInterface
    (.capturing (.ref (.localCaptureMember captureLabelC))
      (.ref (.localTypeMember typeLabelA)))
    .empty

def mixedModel {scope : Scope} : LocalModel.Model scope where
  typeMember := fun _ => .one
  captureMember := fun _ => .empty

def mixedRealization {scope : Scope} (context : Ctx scope) :
    ObjectType.Realization context (mixedObject (scope := scope)) where
  model := mixedModel
  constraints :=
    .inter (.typeMember .refl .refl) (.captureMember .refl .refl)

def mixedValue {scope : Scope} : Value scope :=
  .object mixedObject .unit

def mixedValueTyping {scope : Scope} (context : Ctx scope) :
    Value.HasType context (mixedValue (scope := scope))
      (mixedObject (scope := scope)).formedType :=
  .object (mixedRealization context) .unit .refl .refl .refl

def identityConsumer {scope : Scope} : Value scope :=
  .objectConsumer mixedObject mixedObject.formedType (.ret (.var .here))

def identityConsumerFunction {scope : Scope} (context : Ctx scope) :
    ObjectFunction.HasType context
      (.ret (identityConsumer (scope := scope))) .empty
      (mixedObject (scope := scope))
      (mixedObject (scope := scope)).formedType .empty :=
  .returned (.ret .var) .captureEmpty

abbrev StableContext : DOTCapture.Intersections.Source.Ctx 1 :=
  DOTCapture.Intersections.Source.Ctx.nil.extendTerm
    (mixedObject (scope := 0)).formedType

def stableExposure : DOTCapture.Intersections.Source.ExposesObject
    StableContext (.var .here)
    (mixedObject (scope := 1)) :=
  .variable rfl

def stableArgument : ObjectArgument.HasType StableContext
    (.ret (.var .here)) (mixedObject (scope := 1)) :=
  .stable (name := .here) (available := mixedObject) rfl
    (ObjectType.Adapts.refl mixedObject)
    (by
      change CaptureIncludes StableContext
        (.ref (.captureMember (.var .here) captureLabelC)) .empty
      exact .source
        (.upper (.captureMember stableExposure (.right .here))))

def stableIdentityApplication : Term 1 :=
  .objectApp mixedObject (.ret identityConsumer) (.ret (.var .here))

def stableIdentityApplicationTypingRaw :
    Term.HasType StableContext stableIdentityApplication
      (.union .empty .empty) (mixedObject (scope := 1)).formedType :=
  .objectApp (identityConsumerFunction StableContext) stableArgument

def stableIdentityApplicationTyping :
    Term.HasType StableContext stableIdentityApplication .empty
      (mixedObject (scope := 1)).formedType :=
  .use stableIdentityApplicationTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

def mixedOpenApplyRepack : Term 0 :=
  .objectLet mixedObject (mixedObject.formedType) (.ret mixedValue)
    stableIdentityApplication

def mixedOpenApplyRepackTypingRaw :
    Term.HasType DOTCapture.Intersections.Source.Ctx.nil mixedOpenApplyRepack
      (.union .empty .empty)
      (mixedObject (scope := 0)).formedType :=
  .objectLet (.ret (mixedValueTyping
    DOTCapture.Intersections.Source.Ctx.nil))
    stableIdentityApplicationTyping .captureEmpty

def mixedOpenApplyRepackTyping :
    Term.HasType DOTCapture.Intersections.Source.Ctx.nil mixedOpenApplyRepack .empty
      (mixedObject (scope := 0)).formedType :=
  .use mixedOpenApplyRepackTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

#guard (compileTerm? emptyReady mixedOpenApplyRepackTyping).isSome

def mixedOpenApplyRepackCompiled :=
  (compileTerm? emptyReady mixedOpenApplyRepackTyping).get (by native_decide)

/-- Static constructors that distinguish this compilation path after target
checking and erasure have forgotten them. -/
structure ArtifactShape where
  opens : Nat := 0
  staticApplications : Nat := 0
  packages : Nat := 0
  runtimeApplications : Nat := 0
deriving DecidableEq

namespace ArtifactShape

def add (first second : ArtifactShape) : ArtifactShape where
  opens := first.opens + second.opens
  staticApplications :=
    first.staticApplications + second.staticApplications
  packages := first.packages + second.packages
  runtimeApplications :=
    first.runtimeApplications + second.runtimeApplications

end ArtifactShape

/-- Count the relevant target constructors throughout an artifact. -/
def artifactShape {scope : ManySortedFC.Sig} :
    ManySortedFC.Tm scope → ArtifactShape
  | .var _ | .unit => {}
  | .lam _ _ _ body _ => artifactShape body
  | .app function argument =>
      { (ArtifactShape.add (artifactShape function)
          (artifactShape argument)) with
        runtimeApplications :=
          (artifactShape function).runtimeApplications +
            (artifactShape argument).runtimeApplications + 1 }
  | .let' _ _ rhs body _ =>
      ArtifactShape.add (artifactShape rhs) (artifactShape body)
  | .adapt term _ => artifactShape term
  | .slam _ _ body _ => artifactShape body
  | .sapp _ function _ _ =>
      { (artifactShape function) with
        staticApplications :=
          (artifactShape function).staticApplications + 1 }
  | .pack _ _ _ _ _ payload _ =>
      { (artifactShape payload) with
        packages := (artifactShape payload).packages + 1 }
  | .«open» _ _ _ _ package body _ =>
      { (ArtifactShape.add (artifactShape package)
          (artifactShape body)) with
        opens := (artifactShape package).opens +
          (artifactShape body).opens + 1 }
  | .use term _ => artifactShape term

/-- The compiler opens the input object once, performs one negative static
and runtime application, and packages twice: once for the input literal and
once to return the same stable payload positively. -/
theorem mixed_open_apply_repack_artifact_shape :
    artifactShape mixedOpenApplyRepackCompiled.term =
      { opens := 1
        staticApplications := 1
        packages := 2
        runtimeApplications := 1 } := by
  native_decide

theorem mixed_open_apply_repack_checker_accepts :
    ManySortedFC.Tm.synth emptyReady.target mixedOpenApplyRepackCompiled.term =
      some (mixedOpenApplyRepackCompiled.targetUse,
        mixedOpenApplyRepackCompiled.targetType) :=
  mixedOpenApplyRepackCompiled.checkerAccepts

@[simp]
theorem mixed_open_apply_repack_source_erasure :
    DOTCapture.Intersections.GeneralExpression.Erasure.eraseTerm
      mixedOpenApplyRepack =
        ManySortedFC.Runtime.Tm.let' .unit
          (.app (.lam (.var 0)) (.var 0)) := by
  rfl

theorem mixed_open_apply_repack_exact_erasure :
    mixedOpenApplyRepackCompiled.term.erase =
      DOTCapture.Intersections.GeneralExpression.Erasure.eraseTerm
        mixedOpenApplyRepack := by
  simpa [Ready.eraseTerm, Ready.runtimeRenaming, emptyReady] using
    mixedOpenApplyRepackCompiled.exactErasure

theorem mixed_open_apply_repack_executes :
    ManySortedFC.Runtime.Steps mixedOpenApplyRepackCompiled.term.erase
      .unit := by
  rw [mixed_open_apply_repack_exact_erasure,
    mixed_open_apply_repack_source_erasure]
  exact .tail (.single (.zeta .unit)) (.beta .unit)

/-- One statement records the independently checked artifact, literal source
erasure, and the actual zeta/beta execution of the repacked identity result. -/
theorem mixed_open_apply_repack_end_to_end :
    ManySortedFC.Tm.synth emptyReady.target
        mixedOpenApplyRepackCompiled.term =
          some (mixedOpenApplyRepackCompiled.targetUse,
            mixedOpenApplyRepackCompiled.targetType) ∧
      mixedOpenApplyRepackCompiled.term.erase =
        DOTCapture.Intersections.GeneralExpression.Erasure.eraseTerm
          mixedOpenApplyRepack ∧
      ManySortedFC.Runtime.Steps mixedOpenApplyRepackCompiled.term.erase
        .unit :=
  ⟨mixed_open_apply_repack_checker_accepts,
    mixed_open_apply_repack_exact_erasure,
    mixed_open_apply_repack_executes⟩

end DOTCaptureToManySortedFC.Intersections.GeneralExpression.MixedRepackExamples
