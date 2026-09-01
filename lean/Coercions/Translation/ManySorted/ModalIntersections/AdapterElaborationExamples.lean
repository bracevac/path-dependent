import Coercions.Translation.ManySorted.ModalIntersections.AdapterElaboration

/-!
# Executable cumulative adapter regressions

The examples exercise every constructor family in the source grammar.  The
two bound-changing quantifier cases use a nontrivial checked interval
morphism from `One .. *` to `Bottom .. *`; the modal example crosses the
zero-requirement theory-map boundary.  Negative cases separate target-checker
failure, endpoint mismatch, and partial source preparation failure.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.AdapterElaborationExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.AdapterElaboration
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext

namespace Source

abbrev Adapts {scope : DOTCapture.ModalIntersections.Sig}
    (environment : DOTCapture.ModalIntersections.TypingEnv scope)
    (source target : DOTCapture.ModalIntersections.Ty scope) :=
  DOTCapture.ModalIntersections.Adapts environment source target
abbrev Interval := DOTCapture.ModalIntersections.Interval
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv

def oneToTop {scope : DOTCapture.ModalIntersections.Sig}
    {environment : TypingEnv scope} :
    Adapts environment (.one : Ty scope) .top :=
  .cast .typeTop

def identity : Adapts DOTCapture.ModalIntersections.TypingEnv.nil
    (.one : Ty []) .one :=
  .identity

def cast : Adapts DOTCapture.ModalIntersections.TypingEnv.nil
    (.one : Ty []) .top :=
  oneToTop

def compose : Adapts DOTCapture.ModalIntersections.TypingEnv.nil
    (.one : Ty []) .top :=
  .compose oneToTop .identity

def function : Adapts DOTCapture.ModalIntersections.TypingEnv.nil
    (.arr .top .one : Ty []) (.arr .one .top) :=
  .function oneToTop oneToTop

def captured : Adapts DOTCapture.ModalIntersections.TypingEnv.nil
    (.capturing .empty .one : Ty []) (.capturing .empty .top) :=
  .captured .refl oneToTop

def unbounded : Interval .type [] := .bounds .none .none

def forallSame : Adapts DOTCapture.ModalIntersections.TypingEnv.nil
    (.forallI unbounded .one : Ty []) (.forallI unbounded .top) :=
  .forallI oneToTop

def existsSame : Adapts DOTCapture.ModalIntersections.TypingEnv.nil
    (.existsI unbounded .one : Ty []) (.existsI unbounded .top) :=
  .existsI oneToTop

/-! A nontrivial same-shape interval entailment. -/

def one : StaticExpr .type [] := .type .one
def bottom : StaticExpr .type [] := .type .bot

def lowerAvailable : Interval .type [] :=
  .bounds (.some one) .none

def lowerRequired : Interval .type [] :=
  .bounds (.some bottom) .none

def availableBound : DOTCapture.ModalIntersections.HasLower
    (DOTCapture.ModalIntersections.Ctx.nil.extendStatic lowerAvailable)
    (.bound (.here : DOTCapture.ModalIntersections.BVar
      ([] ▹ .static .type) (.static .type))) one.weaken :=
  .bound rfl

def lowerProof : DOTCapture.ModalIntersections.Includes
    (DOTCapture.ModalIntersections.Ctx.nil.extendStatic lowerAvailable)
    bottom.weaken
    (DOTCapture.ModalIntersections.StaticExpr.bound
      (.here : DOTCapture.ModalIntersections.BVar
        ([] ▹ .static .type) (.static .type))) :=
  .trans .typeBottom (.lower availableBound)

def lowerEntails : DOTCapture.ModalIntersections.Interval.Entails
    DOTCapture.ModalIntersections.Ctx.nil lowerAvailable lowerRequired :=
  .lower lowerProof

def forallBounds : Adapts DOTCapture.ModalIntersections.TypingEnv.nil
    (.forallI lowerRequired .one : Ty [])
    (.forallI lowerAvailable .top) :=
  .forallBounds lowerEntails oneToTop

def existsBounds : Adapts DOTCapture.ModalIntersections.TypingEnv.nil
    (.existsI lowerAvailable .one : Ty [])
    (.existsI lowerRequired .top) :=
  .existsBounds lowerEntails oneToTop

/-! Modal adaptation remains value-only and contravariant in requirements. -/

def emptyRequirements :
    DOTCapture.ModalIntersections.ModalRequirements 0 [] [] :=
  .mk .nil .nil

def emptySatisfaction : DOTCapture.ModalIntersections.Satisfies
    DOTCapture.ModalIntersections.TypingEnv.nil.bindings
    (DOTCapture.ModalIntersections.TypingEnv.nil.push
      emptyRequirements).locks emptyRequirements :=
  .mk
    (fun occurrence => nomatch occurrence)
    (fun left _ _ => nomatch left)

def modal : Adapts DOTCapture.ModalIntersections.TypingEnv.nil
    (.modal emptyRequirements .one : Ty [])
    (.modal emptyRequirements .top) :=
  .modal emptySatisfaction oneToTop

end Source

/-! ## Successful derivation-directed compilation -/

def identity? := compile? Context.nil Source.identity
def cast? := compile? Context.nil Source.cast
def compose? := compile? Context.nil Source.compose
def function? := compile? Context.nil Source.function
def captured? := compile? Context.nil Source.captured
def forallSame? := compile? Context.nil Source.forallSame
def existsSame? := compile? Context.nil Source.existsSame
def forallBounds? := compile? Context.nil Source.forallBounds
def existsBounds? := compile? Context.nil Source.existsBounds
def modal? := compile? Context.nil Source.modal

example : identity?.isSome = true := by native_decide
example : cast?.isSome = true := by native_decide
example : compose?.isSome = true := by native_decide
example : function?.isSome = true := by native_decide
example : captured?.isSome = true := by native_decide
example : forallSame?.isSome = true := by native_decide
example : existsSame?.isSome = true := by native_decide
example : forallBounds?.isSome = true := by native_decide
example : existsBounds?.isSome = true := by native_decide
example : modal?.isSome = true := by native_decide

def castCompiled := cast?.get (by native_decide)
def functionCompiled := function?.get (by native_decide)
def capturedCompiled := captured?.get (by native_decide)
def forallSameCompiled := forallSame?.get (by native_decide)
def forallBoundsCompiled := forallBounds?.get (by native_decide)
def existsBoundsCompiled := existsBounds?.get (by native_decide)
def modalCompiled := modal?.get (by native_decide)

example : castCompiled.adapter =
    (.cast (.typeTop .one) : ManySortedFC.Adapter []) := by
  native_decide

example : functionCompiled.adapter =
    (.function (.cast (.typeTop .one)) (.cast (.typeTop .one)) :
      ManySortedFC.Adapter []) := by
  native_decide

example : capturedCompiled.adapter =
    (.captured (.inclusionRefl (.capture .empty))
      (.cast (.typeTop .one)) : ManySortedFC.Adapter []) := by
  native_decide

def isForall {scope : ManySortedFC.Sig} : ManySortedFC.Adapter scope -> Bool
  | .forallT _ _ => true
  | _ => false

def isForallMorphism {scope : ManySortedFC.Sig} :
    ManySortedFC.Adapter scope -> Bool
  | .forallMorphism _ _ _ _ => true
  | _ => false

def isExistsMorphism {scope : ManySortedFC.Sig} :
    ManySortedFC.Adapter scope -> Bool
  | .existsMorphism _ _ _ _ => true
  | _ => false

def isModal {scope : ManySortedFC.Sig} : ManySortedFC.Adapter scope -> Bool
  | .modal _ _ _ _ => true
  | _ => false

example : isForall forallSameCompiled.adapter = true := by native_decide
example : isForallMorphism forallBoundsCompiled.adapter = true := by
  native_decide
example : isExistsMorphism existsBoundsCompiled.adapter = true := by
  native_decide
example : isModal modalCompiled.adapter = true := by native_decide

/-! Exact preparation and checker provenance remain available on the result. -/

example : Preparation.translateType Core.nil.layout (.one : Source.Ty []) =
    .ok castCompiled.sourcePrepared.targetType :=
  castCompiled.sourcePrepared.prepared

example : Preparation.translateType Core.nil.layout (.top : Source.Ty []) =
    .ok castCompiled.targetPrepared.targetType :=
  castCompiled.targetPrepared.prepared

example : ManySortedFC.Adapter.check Core.nil.target castCompiled.adapter =
    some castCompiled.checked :=
  castCompiled.checkerAcceptance

example : castCompiled.checked.source =
    castCompiled.sourcePrepared.targetType := castCompiled.sourceExact

example : castCompiled.checked.target =
    castCompiled.targetPrepared.targetType := castCompiled.targetExact

/-! Administrative transparency is retained for every generated adapter. -/

def runtimeFunction : ManySortedFC.Runtime.Tm 0 := .lam .unit

example : ManySortedFC.Runtime.AdministrativeEq
    (functionCompiled.adapter.erase runtimeFunction) runtimeFunction :=
  functionCompiled.administrative runtimeFunction .lam

example : castCompiled.adapter.erase (.unit : ManySortedFC.Runtime.Tm 0) =
    .unit := rfl

/-! ## Rejection boundaries -/

/-- The target checker rejects composition whose intermediate endpoints do
not agree. -/
def illFormedCompose : ManySortedFC.Adapter [] :=
  .compose (.identity .one) (.identity .top)

example : ManySortedFC.Adapter.check ManySortedFC.Ctx.nil illFormedCompose =
    none := by
  native_decide

example : (finish? Context.nil (.one : Source.Ty []) .top
    illFormedCompose).isNone = true := by
  native_decide

/-- A valid target adapter is also rejected when its synthesized endpoints
do not equal the claimed source translations. -/
example : (finish? Context.nil (.top : Source.Ty []) .one
    (.cast (.typeTop .one))).isNone = true := by
  native_decide

namespace PreparationFailure

def innerObject : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk (.typeMember 0 .one .one) .one .empty

def malformedObject : DOTCapture.ModalIntersections.ObjectType [] :=
  .mk (.typeMember 0 (.object innerObject) .top) .one .empty

def malformedType : Source.Ty [] := .object malformedObject

def identity : Source.Adapts DOTCapture.ModalIntersections.TypingEnv.nil
    malformedType
    malformedType := .identity

/-- Nested object bounds hit the explicit partial preparation boundary; the
identity constructor does not receive a total fallback translation. -/
example : (compile? Context.nil identity).isNone = true := by
  native_decide

end PreparationFailure

end DOTCaptureToManySortedFC.ModalIntersections.AdapterElaborationExamples
