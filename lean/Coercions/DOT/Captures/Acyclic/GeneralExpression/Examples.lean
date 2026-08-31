import Coercions.DOT.Captures.Acyclic.GeneralExpression.Typing
import Coercions.DOT.Captures.Acyclic.GeneralExpression.Erasure

/-!
# General-expression captured-DOT examples

The main regression evaluates a non-value function computation, applies the
result to produce an object, opens that computed object, selects its identity
payload through a stable path, adapts the selected value through the exact
member bounds, and applies it to a separately delayed unit computation.
-/

namespace DOTCapture.Acyclic.GeneralExpression.Examples

/-! ## Reusable closed shapes and values -/

def unaryShape {scope : Scope} : Ty scope :=
  .arr .one .one

def closedUnaryType {scope : Scope} : Ty scope :=
  .capturing .empty unaryShape

def identity {scope : Scope} : Value scope :=
  .lam .one .one (.ret (.var .here))

def identityTyping {scope : Scope} (context : Ctx scope) :
    Value.HasType context (identity (scope := scope)) closedUnaryType :=
  .lam rfl (.ret .var) .captureEmpty

def functionSignature {scope : Scope} : ObjectSig scope :=
  .bounds unaryShape unaryShape .empty .empty

def formedObjectType {scope : Scope} : Ty scope :=
  .capturing .empty (.object functionSignature)

def functionObject {scope : Scope} : Value scope :=
  .object functionSignature unaryShape .empty identity

def functionObjectTyping {scope : Scope} (context : Ctx scope) :
    Value.HasType context (functionObject (scope := scope)) formedObjectType :=
  .object .refl .refl .refl .refl (identityTyping context) .refl .refl

/-! ## A computation that returns an object -/

def objectProducerType {scope : Scope} : Ty scope :=
  .capturing .empty (.arr .one formedObjectType)

/-- A function whose codomain is the exact formed-object type. -/
def objectProducer {scope : Scope} : Value scope :=
  .lam .one formedObjectType
    (.ret (functionObject (scope := scope + 1)))

def objectProducerTyping {scope : Scope} (context : Ctx scope) :
    Value.HasType context (objectProducer (scope := scope))
      objectProducerType :=
  .lam rfl (.ret (functionObjectTyping (context.extendTerm .one)))
    .captureEmpty

/-- A non-value computation returning the producer function. -/
def computedProducer : Term 0 :=
  .let' objectProducerType (.ret objectProducer) (.ret (.var .here))

private def computedProducerRaw :
    Term.HasType Ctx.nil computedProducer (.union .empty .empty)
      objectProducerType :=
  .letPlain (bound := objectProducerType) rfl
    (.ret (objectProducerTyping Ctx.nil)) (.ret .var)
    .captureEmpty

def computedProducerTyping :
    Term.HasType Ctx.nil computedProducer .empty objectProducerType :=
  .use computedProducerRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

/-- General application whose function position is itself a computation.  Its
result is an object package, not an object literal at the binding boundary. -/
def computedObject : Term 0 :=
  .app computedProducer (.ret .unit)

private def computedObjectRaw :
    Term.HasType Ctx.nil computedObject (.union .empty .empty)
      formedObjectType :=
  .app computedProducerTyping rfl (.ret .unit)

def computedObjectTyping :
    Term.HasType Ctx.nil computedObject .empty formedObjectType :=
  .use computedObjectRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

/-! ## Opening the computed object and selecting by a stable path -/

def objectContext : Ctx 1 :=
  Ctx.nil.extendTerm formedObjectType

def receiver : Path 1 :=
  .var .here

def objectExposure :
    DOTCapture.Acyclic.ExposesObject objectContext receiver
      (functionSignature (scope := 0)).weaken :=
  .variable rfl

def selectedPure :
    Term.HasType objectContext (.select receiver .v) .empty
      receiver.valueMemberType :=
  .use (ExposesObject.valueMember objectExposure)
    objectExposure.captureUpper

def selectedTypePlain : receiver.valueMemberType.IsPlain :=
  rfl

def selectedContext : Ctx 2 :=
  objectContext.extendTerm receiver.valueMemberType

def olderReceiver : Path 2 :=
  .var (.there .here)

def olderObjectExposure :
    DOTCapture.Acyclic.ExposesObject selectedContext olderReceiver
      (functionSignature (scope := 0)).weaken.weaken :=
  .variable rfl

/-- The selected `(x.A)^{x.C}` payload is adapted through the exact upper
bounds to the ambient closed unary-function type.  This remains a value-only
logical adaptation, with no evaluation hidden under the cast. -/
def selectedFunctionTyping :
    Value.HasType selectedContext (.var .here)
      (closedUnaryType (scope := 0)).weaken.weaken :=
  .adapt .var
    (.typeCapturing olderObjectExposure.captureUpper
      olderObjectExposure.typeUpper)

/-- A genuinely delayed argument: evaluating it performs a zeta step before
the selected identity can beta-reduce. -/
def delayedUnit : Term 2 :=
  .let' .one (.ret .unit) (.ret (.var .here))

private def delayedUnitRaw :
    Term.HasType selectedContext delayedUnit (.union .empty .empty) .one :=
  .letPlain (bound := .one) rfl (.ret .unit) (.ret .var) .captureEmpty

def delayedUnitTyping :
    Term.HasType selectedContext delayedUnit .empty .one :=
  .use delayedUnitRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

def selectedApplication : Term 2 :=
  .app (.ret (.var .here)) delayedUnit

private def selectedApplicationRaw :
    Term.HasType selectedContext selectedApplication
      (.union .empty .empty) .one :=
  .app (.ret selectedFunctionTyping) rfl delayedUnitTyping

def selectedApplicationTyping :
    Term.HasType selectedContext selectedApplication .empty .one :=
  .use selectedApplicationRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

/-- The computed object is opened, its payload is selected from the stable
receiver `x`, and that selected function is actually invoked on a delayed
argument. -/
def selectComputedObject : Term 0 :=
  .let' .one computedObject
    (.let' .one (.select receiver .v) selectedApplication)

private def selectionBodyRaw :
    Term.HasType objectContext
      (.let' .one (.select receiver .v) selectedApplication)
      (.union .empty .empty) .one :=
  .letPlain selectedTypePlain selectedPure selectedApplicationTyping
    .captureEmpty

private def selectionBody :
    Term.HasType objectContext
      (.let' .one (.select receiver .v) selectedApplication) .empty .one :=
  .use selectionBodyRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

private def selectComputedObjectRaw :
    Term.HasType Ctx.nil selectComputedObject (.union .empty .empty) .one :=
  .letObject (signature := functionSignature)
    (result := .one) (rhs := computedObject) (rhsUse := .empty)
    (body := .let' .one (.select receiver .v) selectedApplication)
    (bodyUse := .empty) (bodyOuterUse := .empty)
    (by
      simpa [formedObjectType, functionSignature,
        DOTCapture.Acyclic.ObjectSig.captureUpper] using computedObjectTyping)
    (by
      simpa [objectContext, formedObjectType, functionSignature,
        DOTCapture.Acyclic.ObjectSig.captureUpper] using selectionBody)
    .captureEmpty

def selectComputedObjectTyping :
    Term.HasType Ctx.nil selectComputedObject .empty .one :=
  .use selectComputedObjectRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

/-! ## Independent runtime behavior -/

namespace Runtime

export ManySortedFC.Runtime (Tm Step Steps)

def identity {scope : Nat} : Tm scope :=
  .lam (.var 0)

def producer : Tm 0 :=
  .lam (identity (scope := 1))

def initial : Tm 0 :=
  .let' (.app (.let' producer (.var 0)) .unit)
    (.let' (.var 0)
      (.app (.var 0) (.let' .unit (.var 0))))

def afterProducer : Tm 0 :=
  .let' (.app producer .unit)
    (.let' (.var 0)
      (.app (.var 0) (.let' .unit (.var 0))))

def afterApplication : Tm 0 :=
  .let' identity
    (.let' (.var 0)
      (.app (.var 0) (.let' .unit (.var 0))))

def afterObject : Tm 0 :=
  .let' identity
    (.app (.var 0) (.let' .unit (.var 0)))

def afterSelection : Tm 0 :=
  .app identity (.let' .unit (.var 0))

def afterArgument : Tm 0 :=
  .app identity .unit

/-- Count runtime lambdas, including those nested inside other terms. -/
def lambdaCount : {scope : Nat} → Tm scope → Nat
  | _, .var _ => 0
  | _, .unit => 0
  | _, .lam body => 1 + lambdaCount body
  | _, .app function argument => lambdaCount function + lambdaCount argument
  | _, .let' rhs body => lambdaCount rhs + lambdaCount body
  | _, .suspend body => lambdaCount body
  | _, .force suspension => lambdaCount suspension

/-- Count genuine runtime applications. -/
def applicationCount : {scope : Nat} → Tm scope → Nat
  | _, .var _ => 0
  | _, .unit => 0
  | _, .lam body => applicationCount body
  | _, .app function argument =>
      1 + applicationCount function + applicationCount argument
  | _, .let' rhs body => applicationCount rhs + applicationCount body
  | _, .suspend body => applicationCount body
  | _, .force suspension => applicationCount suspension

/-- Count genuine runtime sequencing nodes. -/
def letCount : {scope : Nat} → Tm scope → Nat
  | _, .var _ => 0
  | _, .unit => 0
  | _, .lam body => letCount body
  | _, .app function argument => letCount function + letCount argument
  | _, .let' rhs body => 1 + letCount rhs + letCount body
  | _, .suspend body => letCount body
  | _, .force suspension => letCount suspension

end Runtime

theorem selectComputedObject_erases_exactly :
    Erasure.eraseTerm selectComputedObject = Runtime.initial := by
  rfl

theorem selectComputedObject_zeta_producer :
    Runtime.Step Runtime.initial Runtime.afterProducer := by
  exact .letRhs (.appFunction (.zeta .lam))

theorem selectComputedObject_beta :
    Runtime.Step Runtime.afterProducer Runtime.afterApplication := by
  exact .letRhs (.beta .unit)

theorem selectComputedObject_zeta_object :
    Runtime.Step Runtime.afterApplication Runtime.afterObject := by
  exact .zeta .lam

theorem selectComputedObject_zeta_selection :
    Runtime.Step Runtime.afterObject Runtime.afterSelection := by
  exact .zeta .lam

theorem selectComputedObject_zeta_argument :
    Runtime.Step Runtime.afterSelection Runtime.afterArgument := by
  exact .appArgument .lam (.zeta .unit)

theorem selectComputedObject_beta_selected :
    Runtime.Step Runtime.afterArgument .unit := by
  exact .beta .unit

def selectComputedObjectSteps :
    Runtime.Steps Runtime.initial .unit :=
  .tail
    (.tail
      (.tail
        (.tail
          (.tail (.single selectComputedObject_zeta_producer)
            selectComputedObject_beta)
          selectComputedObject_zeta_object)
        selectComputedObject_zeta_selection)
      selectComputedObject_zeta_argument)
    selectComputedObject_beta_selected

/-! ## Nondegeneracy metrics -/

theorem selectComputedObject_runtime_lambdaCount :
    Runtime.lambdaCount Runtime.initial = 2 := by
  rfl

theorem selectComputedObject_runtime_applicationCount :
    Runtime.applicationCount Runtime.initial = 2 := by
  rfl

theorem selectComputedObject_runtime_letCount :
    Runtime.letCount Runtime.initial = 4 := by
  rfl

theorem selectComputedObject_runtime_is_not_unit :
    Runtime.initial ≠ (.unit : Runtime.Tm 0) := by
  intro equality
  cases equality

end DOTCapture.Acyclic.GeneralExpression.Examples
