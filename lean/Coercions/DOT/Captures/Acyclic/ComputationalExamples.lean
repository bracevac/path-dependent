import Coercions.DOT.Captures.Acyclic.ObjectTyping
import Coercions.DOT.Captures.Acyclic.Structural

/-!
# Computational regressions for acyclic captured DOT

These examples make the object payload observably computational.  An exact
object stores the closed identity function behind `A = One → One` and
`C = {}`.  One closed program selects and returns that function; a second
selects and applies it.  The source layer therefore supports closed results
other than unit as well as genuine application and sequencing.
-/

namespace DOTCapture.Acyclic.ComputationalExamples

/-! ## A nontrivial object payload -/

/-- The closed unary payload shape. -/
def unaryShape : Ty 0 :=
  .arr .one .one

/-- Its explicitly capture-annotated closed value type. -/
def closedUnaryType : Ty 0 :=
  .capturing .empty unaryShape

/-- `λ (z : One). z`. -/
def identity : Value 0 :=
  .lam .one .one (.ret (.var .here))

def identityTyping :
    Value.HasType Ctx.nil identity closedUnaryType :=
  .lam rfl (.ret .var) .captureEmpty

/-- Exact `A = One → One` and `C = {}` bounds. -/
def functionSignature : ObjectSig 0 :=
  .bounds unaryShape unaryShape .empty .empty

/-- The identity function packaged as the fixed value member `v`. -/
def functionObject : Value 0 :=
  .object functionSignature unaryShape .empty identity

def functionObjectTyping :
    Value.HasType Ctx.nil functionObject
      (.capturing .empty (.object functionSignature)) :=
  .object .refl .refl .refl .refl identityTyping .refl .refl

/-! ## Opening, selecting, adapting, and calling -/

def objectContext : Ctx 1 :=
  Ctx.nil.extendTerm (.capturing .empty (.object functionSignature))

def receiver : Path 1 :=
  .var .here

def objectExposure :
    ExposesObject objectContext receiver functionSignature.weaken :=
  .variable rfl

/-- Selecting `x.v` and following the exact capture upper bound makes the
selection immediately pure. -/
def selectedPure :
    Term.HasType objectContext (.select receiver .v) .empty
      receiver.valueMemberType :=
  .use objectExposure.valueMember objectExposure.captureUpper

def selectedTypePlain : receiver.valueMemberType.IsPlain :=
  rfl

/-- Context after the selected payload has been bound as `f`. -/
def selectedContext : Ctx 2 :=
  objectContext.extendTerm receiver.valueMemberType

def olderReceiver : Path 2 :=
  .var (.there .here)

def olderObjectExposure :
    ExposesObject selectedContext olderReceiver
      functionSignature.weaken.weaken :=
  .variable rfl

/-- The selected `(x.A)^{x.C}` value is logically adapted through the exact
member upper bounds to the ambient closed unary-function type.  This is a
logical cast only; it does not request function eta-adaptation. -/
def selectedFunctionTyping :
    Value.HasType selectedContext (.var .here)
      closedUnaryType.weaken.weaken :=
  .adapt .var
    (.typeCapturing olderObjectExposure.captureUpper
      olderObjectExposure.typeUpper)

def selectedApplicationRaw :
    Term.HasType selectedContext (.app (.var .here) .unit)
      (.union .empty .empty) .one :=
  .app selectedFunctionTyping rfl rfl .unit

def selectedApplication :
    Term.HasType selectedContext (.app (.var .here) .unit)
      .empty .one :=
  .use selectedApplicationRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

/-! ## Closed computational programs -/

/-- Bind the object, bind its selected function payload, and return that
payload at a closed arrow type. -/
def returnSelected : Term 0 :=
  .let' closedUnaryType (.ret functionObject)
    (.let' closedUnaryType.weaken (.select receiver .v)
      (.ret (.var .here)))

private def returnSelectedInnerRaw :
    Term.HasType objectContext
      (.let' closedUnaryType.weaken (.select receiver .v)
        (.ret (.var .here)))
      (.union .empty .empty) closedUnaryType.weaken :=
  .letPlain selectedTypePlain selectedPure
    (.ret selectedFunctionTyping) .captureEmpty

private def returnSelectedInner :
    Term.HasType objectContext
      (.let' closedUnaryType.weaken (.select receiver .v)
        (.ret (.var .here)))
      .empty closedUnaryType.weaken :=
  .use returnSelectedInnerRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

private def returnSelectedRaw :
    Term.HasType Ctx.nil returnSelected (.union .empty .empty)
      closedUnaryType :=
  .letObject (signature := functionSignature)
    functionObjectTyping returnSelectedInner .captureEmpty

/-- A closed captured-DOT program whose result is a function, not unit. -/
def returnSelectedTyping :
    Term.HasType Ctx.nil returnSelected .empty closedUnaryType :=
  .use returnSelectedRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

/-- Bind the same object and selected payload, then invoke the payload. -/
def applySelected : Term 0 :=
  .let' .one (.ret functionObject)
    (.let' .one (.select receiver .v)
      (.app (.var .here) .unit))

private def applySelectedInnerRaw :
    Term.HasType objectContext
      (.let' .one (.select receiver .v)
        (.app (.var .here) .unit))
      (.union .empty .empty) .one :=
  .letPlain selectedTypePlain selectedPure
    selectedApplication .captureEmpty

private def applySelectedInner :
    Term.HasType objectContext
      (.let' .one (.select receiver .v)
        (.app (.var .here) .unit))
      .empty .one :=
  .use applySelectedInnerRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

private def applySelectedRaw :
    Term.HasType Ctx.nil applySelected (.union .empty .empty) .one :=
  .letObject (signature := functionSignature)
    functionObjectTyping applySelectedInner .captureEmpty

/-- The closed application is pure and returns `One`; its erasure will expose
two zeta steps followed by one beta step. -/
def applySelectedTyping :
    Term.HasType Ctx.nil applySelected .empty .one :=
  .use applySelectedRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

end DOTCapture.Acyclic.ComputationalExamples
