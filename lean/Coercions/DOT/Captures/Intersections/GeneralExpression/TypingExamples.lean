import Coercions.DOT.Captures.Intersections.GeneralExpression.Typing

/-!
# Typed multi-member source programs

These examples use one runtime payload with several static type and capture
members. Repeated declarations share the same source label. The negative
consumer requests a one-member view of the larger object.
-/

namespace DOTCapture.Intersections.GeneralExpression.TypingExamples

open DOTCapture.Intersections.GeneralExpression
open DOTCapture.Intersections.Source

def typeLabelA : Label := 0
def captureLabelC : Label := 1
def typeLabelB : Label := 2
def captureLabelD : Label := 3

/-- Four labels and six retained interval occurrences. -/
def multiInterface {scope : Scope} : Interface scope :=
  .inter
    (.inter
      (.typeMember typeLabelA .bot .top)
      (.typeMember typeLabelA .one .one))
    (.inter
      (.inter
        (.captureMember captureLabelC .empty (.union .empty .empty))
        (.captureMember captureLabelC (.union .empty .empty) .empty))
      (.inter
        (.typeMember typeLabelB .one .one)
        (.captureMember captureLabelD .empty .empty)))

def multiObject {scope : Scope} : ObjectType scope :=
  .mk multiInterface .one .empty

/-- The independently normalized view expected by the consumer. -/
def componentInterface {scope : Scope} : Interface scope :=
  .typeMember typeLabelA .bot .top

def componentObject {scope : Scope} : ObjectType scope :=
  .mk componentInterface .one .empty

/-- One witness per label. Repeated declarations consult the same function
coordinate. -/
def multiModel {scope : Scope} : LocalModel.Model scope where
  typeMember := fun _ => .one
  captureMember := fun _ => .empty

def multiConstraints {scope : Scope} (context : Ctx scope) :
    Interface.Realizes context multiModel (multiInterface (scope := scope)) :=
  .inter
    (.inter
      (.typeMember .typeBottom .typeTop)
      (.typeMember .refl .refl))
    (.inter
      (.inter
        (.captureMember .refl .captureUnionLeft)
        (.captureMember
          (.captureUnionElim .captureEmpty .captureEmpty) .refl))
      (.inter
        (.typeMember .refl .refl)
        (.captureMember .refl .refl)))

def multiRealization {scope : Scope} (context : Ctx scope) :
    ObjectType.Realization context (multiObject (scope := scope)) where
  model := multiModel
  constraints := multiConstraints context

def objectValue {scope : Scope} : Value scope :=
  .object multiObject .unit

def objectValueTyping {scope : Scope} (context : Ctx scope) :
    Value.HasType context (objectValue (scope := scope))
      (multiObject (scope := scope)).formedType :=
  .object (multiRealization context) .unit .refl .refl .refl

/-! ## Negative consumer -/

def consumerBody {scope : Scope} : Term (scope + 1) :=
  .select (.var .here) .payload

def componentExposure {scope : Scope} (context : Ctx scope) :
    ExposesObject
      (context.extendTerm (componentObject (scope := scope)).formedType)
      (.var .here) (componentObject (scope := scope + 1)) :=
  .variable rfl

def consumerBodyTyping {scope : Scope} (context : Ctx scope) :
    Term.HasType
      (context.extendTerm (componentObject (scope := scope)).formedType)
      (consumerBody (scope := scope)) .empty .one :=
  .use (.select (componentExposure context))
    (.payloadRoot (componentExposure context))

def consumerValue {scope : Scope} : Value scope :=
  .objectConsumer componentObject .one consumerBody

def consumerValueTyping {scope : Scope} (context : Ctx scope) :
    Value.HasType context (consumerValue (scope := scope))
      (.capturing .empty
        (.arr (componentObject (scope := scope)).formedType .one)) :=
  .objectConsumer (consumerBodyTyping context) .captureEmpty

def consumerFunctionTyping {scope : Scope} (context : Ctx scope) :
    ObjectFunction.HasType context (.ret (consumerValue (scope := scope)))
      .empty (componentObject (scope := scope)) .one .empty :=
  .returned (consumerBodyTyping context) .captureEmpty

/-! ## Source-level signature projection -/

def projectedMapping {scope : Scope} : LocalModel.Mapping scope where
  typeMember := fun _ => .ref (.localTypeMember typeLabelA)
  captureMember := fun _ => .ref (.localCaptureMember captureLabelC)

def projectedModel {scope : Scope} (model : LocalModel.Model scope) :
    LocalModel.Model scope :=
  projectedMapping.apply model

/-- Project the first `A` occurrence. The runtime representation remains
`one`, and the outer capture remains empty. -/
def multiAdaptsComponent {scope : Scope} (context : Ctx scope) :
    ObjectType.Adapts context (multiObject (scope := scope))
      (componentObject (scope := scope)) where
  mapping := projectedMapping
  theory := .typeMember
    (.typeLower (.left (.left .here)))
    (.typeUpper (.left (.left .here)))
  constraints := by
    intro model realization
    cases realization with
    | inter left _right =>
        cases left with
        | inter first _second =>
            cases first with
            | typeMember lower upper =>
                exact .typeMember lower upper
  representation := by
    intro _model _realization
    exact .refl
  outerCapture := .refl

def literalArgument {scope : Scope} (context : Ctx scope) :
    ObjectArgument.HasType context (.ret (objectValue (scope := scope)))
      (componentObject (scope := scope)) :=
  .literal (multiRealization context) .unit .refl .refl .refl
    (multiAdaptsComponent context) .refl

/-! ## Direct canonical application -/

def canonicalApplication : Term 0 :=
  .objectApp componentObject (.ret consumerValue) (.ret objectValue)

def canonicalApplicationTypingRaw :
    Term.HasType Ctx.nil canonicalApplication (.union .empty .empty) .one :=
  .objectApp (consumerFunctionTyping Ctx.nil) (literalArgument Ctx.nil)

def canonicalApplicationTyping :
    Term.HasType Ctx.nil canonicalApplication .empty .one :=
  .use canonicalApplicationTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

@[simp]
theorem canonicalApplication_erasure :
    Erasure.eraseTerm canonicalApplication =
      ManySortedFC.Runtime.Tm.app (.lam (.var 0)) .unit := rfl

theorem canonicalApplication_beta :
    ManySortedFC.Runtime.Step (Erasure.eraseTerm canonicalApplication)
      .unit := by
  rw [canonicalApplication_erasure]
  exact .beta .unit

/-! ## Explicit opening and stable negative use -/

abbrev StableContext : Ctx 1 :=
  Ctx.nil.extendTerm (multiObject (scope := 0)).formedType

def stableArgument :
    ObjectArgument.HasType StableContext (.ret (.var .here))
      (componentObject (scope := 1)) :=
  .stable (name := .here) (available := multiObject) rfl
    (multiAdaptsComponent StableContext) .refl

def stableBody : Term 1 :=
  .objectApp componentObject (.ret consumerValue) (.ret (.var .here))

def stableBodyTypingRaw :
    Term.HasType StableContext stableBody (.union .empty .empty) .one :=
  .objectApp (consumerFunctionTyping StableContext) stableArgument

def stableBodyTyping :
    Term.HasType StableContext stableBody .empty .one :=
  .use stableBodyTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

def openedApplication : Term 0 :=
  .objectLet multiObject .one (.ret objectValue) stableBody

def openedApplicationTypingRaw :
    Term.HasType Ctx.nil openedApplication (.union .empty .empty) .one :=
  .objectLet (.ret (objectValueTyping Ctx.nil)) stableBodyTyping .captureEmpty

def openedApplicationTyping :
    Term.HasType Ctx.nil openedApplication .empty .one :=
  .use openedApplicationTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

@[simp]
theorem openedApplication_erasure :
    Erasure.eraseTerm openedApplication =
      ManySortedFC.Runtime.Tm.let' .unit
        (.app (.lam (.var 0)) (.var 0)) := rfl

theorem openedApplication_zeta :
    ManySortedFC.Runtime.Step (Erasure.eraseTerm openedApplication)
      (.app (.lam (.var 0)) .unit) := by
  rw [openedApplication_erasure]
  exact .zeta .unit

theorem openedApplication_then_beta :
    ManySortedFC.Runtime.Step
      ((.app (.lam (.var 0)) .unit : ManySortedFC.Runtime.Tm 0))
      .unit :=
  .beta .unit

theorem openedApplication_executes :
    ManySortedFC.Runtime.Steps (Erasure.eraseTerm openedApplication)
      .unit :=
  .tail (.single openedApplication_zeta) openedApplication_then_beta

/-! ## Negative consumption of the complete merged signature -/

def mergedConsumerExposure {scope : Scope} (context : Ctx scope) :
    ExposesObject
      (context.extendTerm (multiObject (scope := scope)).formedType)
      (.var .here) (multiObject (scope := scope + 1)) :=
  .variable rfl

def mergedConsumerBodyTyping {scope : Scope} (context : Ctx scope) :
    Term.HasType
      (context.extendTerm (multiObject (scope := scope)).formedType)
      (consumerBody (scope := scope)) .empty .one :=
  .use (.select (mergedConsumerExposure context))
    (.payloadRoot (mergedConsumerExposure context))

def mergedConsumerValue {scope : Scope} : Value scope :=
  .objectConsumer multiObject .one consumerBody

def mergedConsumerFunctionTyping {scope : Scope} (context : Ctx scope) :
    ObjectFunction.HasType context
      (.ret (mergedConsumerValue (scope := scope))) .empty
      (multiObject (scope := scope)) .one .empty :=
  .returned (mergedConsumerBodyTyping context) .captureEmpty

def mergedLiteralArgument {scope : Scope} (context : Ctx scope) :
    ObjectArgument.HasType context (.ret (objectValue (scope := scope)))
      (multiObject (scope := scope)) :=
  .literal (multiRealization context) .unit .refl .refl .refl
    (ObjectType.Adapts.refl multiObject) .refl

def mergedCanonicalApplication : Term 0 :=
  .objectApp multiObject (.ret mergedConsumerValue) (.ret objectValue)

def mergedCanonicalApplicationTypingRaw :
    Term.HasType Ctx.nil mergedCanonicalApplication
      (.union .empty .empty) .one :=
  .objectApp (mergedConsumerFunctionTyping Ctx.nil)
    (mergedLiteralArgument Ctx.nil)

def mergedCanonicalApplicationTyping :
    Term.HasType Ctx.nil mergedCanonicalApplication .empty .one :=
  .use mergedCanonicalApplicationTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

@[simp]
theorem mergedCanonicalApplication_erasure :
    Erasure.eraseTerm mergedCanonicalApplication =
      ManySortedFC.Runtime.Tm.app (.lam (.var 0)) .unit := rfl

theorem mergedCanonicalApplication_beta :
    ManySortedFC.Runtime.Step
      (Erasure.eraseTerm mergedCanonicalApplication) .unit := by
  rw [mergedCanonicalApplication_erasure]
  exact .beta .unit

def mergedStableArgument :
    ObjectArgument.HasType StableContext (.ret (.var .here))
      (multiObject (scope := 1)) :=
  .stable (name := .here) (available := multiObject) rfl
    (ObjectType.Adapts.refl multiObject) .refl

def mergedStableBody : Term 1 :=
  .objectApp multiObject (.ret mergedConsumerValue) (.ret (.var .here))

def mergedStableBodyTypingRaw :
    Term.HasType StableContext mergedStableBody
      (.union .empty .empty) .one :=
  .objectApp (mergedConsumerFunctionTyping StableContext)
    mergedStableArgument

def mergedStableBodyTyping :
    Term.HasType StableContext mergedStableBody .empty .one :=
  .use mergedStableBodyTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

def mergedOpenedApplication : Term 0 :=
  .objectLet multiObject .one (.ret objectValue) mergedStableBody

def mergedOpenedApplicationTypingRaw :
    Term.HasType Ctx.nil mergedOpenedApplication
      (.union .empty .empty) .one :=
  .objectLet (.ret (objectValueTyping Ctx.nil)) mergedStableBodyTyping
    .captureEmpty

def mergedOpenedApplicationTyping :
    Term.HasType Ctx.nil mergedOpenedApplication .empty .one :=
  .use mergedOpenedApplicationTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

@[simp]
theorem mergedOpenedApplication_erasure :
    Erasure.eraseTerm mergedOpenedApplication =
      ManySortedFC.Runtime.Tm.let' .unit
        (.app (.lam (.var 0)) (.var 0)) := rfl

theorem mergedOpenedApplication_executes :
    ManySortedFC.Runtime.Steps
      (Erasure.eraseTerm mergedOpenedApplication) .unit :=
  .tail (.single (by
    rw [mergedOpenedApplication_erasure]
    exact ManySortedFC.Runtime.Step.zeta .unit)) (.beta .unit)

/-! ## Stable-path boundary -/

def computedObject : Term 0 :=
  .objectLet multiObject (multiObject.formedType) (.ret objectValue)
    (.ret (.var .here))

def computedObjectTypingRaw :
    Term.HasType Ctx.nil computedObject (.union .empty .empty)
      (multiObject (scope := 0)).formedType := by
  simpa [computedObject] using
    (Term.HasType.objectLet
      (object := multiObject (scope := 0))
      (result := (multiObject (scope := 0)).formedType)
      (.ret (objectValueTyping Ctx.nil))
      (.ret Value.HasType.var) .captureEmpty)

def computedObjectTyping :
    Term.HasType Ctx.nil computedObject .empty
      (multiObject (scope := 0)).formedType :=
  .use computedObjectTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

/-- The computation-producing object is accepted only after an explicit
object open establishes the stable root used by the consumer. -/
def computedOpenedApplication : Term 0 :=
  .objectLet multiObject .one computedObject stableBody

def computedOpenedApplicationTypingRaw :
    Term.HasType Ctx.nil computedOpenedApplication
      (.union .empty .empty) .one :=
  .objectLet computedObjectTyping stableBodyTyping .captureEmpty

def computedOpenedApplicationTyping :
    Term.HasType Ctx.nil computedOpenedApplication .empty .one :=
  .use computedOpenedApplicationTypingRaw
    (.captureUnionElim .captureEmpty .captureEmpty)

@[simp]
theorem computedOpenedApplication_erasure :
    Erasure.eraseTerm computedOpenedApplication =
      ManySortedFC.Runtime.Tm.let'
        (.let' .unit (.var 0))
        (.app (.lam (.var 0)) (.var 0)) := rfl

theorem computedOpenedApplication_executes :
    ManySortedFC.Runtime.Steps
      (Erasure.eraseTerm computedOpenedApplication) .unit := by
  rw [computedOpenedApplication_erasure]
  exact .tail
    (.tail (.single (.letRhs (.zeta .unit))) (.zeta .unit))
    (.beta .unit)

theorem computed_object_requires_explicit_open :
    ObjectArgument.classify computedObject = .requiresExplicitOpen := rfl

theorem canonical_literal_is_direct :
    ObjectArgument.classify (.ret (objectValue (scope := 0))) =
      .canonicalLiteral := rfl

/-! ## Cross-member bounds at a stable root -/

def crossMemberInterface {scope : Scope} : Interface scope :=
  .inter
    (.typeMember typeLabelA (.ref (.localTypeMember typeLabelB)) .top)
    (.typeMember typeLabelB .bot (.ref (.localTypeMember typeLabelA)))

def crossMemberObject {scope : Scope} : ObjectType scope :=
  .mk crossMemberInterface .one .empty

abbrev CrossMemberContext : Ctx 1 :=
  Ctx.nil.extendTerm (crossMemberObject (scope := 0)).formedType

def crossMemberExposure :
    ExposesObject CrossMemberContext (.var .here)
      (crossMemberObject (scope := 1)) :=
  .variable rfl

def crossMemberALower :
    (crossMemberObject (scope := 1)).interface.HasTypeOccurrence
      typeLabelA (.ref (.localTypeMember typeLabelB)) .top :=
  .left .here

def crossMemberBUpper :
    (crossMemberObject (scope := 1)).interface.HasTypeOccurrence
      typeLabelB .bot (.ref (.localTypeMember typeLabelA)) :=
  .right .here

/-- The local lower endpoint `B` becomes the stable selection `x.B`. -/
def selectedALowerOpensAtRoot :
    HasLower CrossMemberContext
      (.typeMember (.var .here) typeLabelA)
      (.type (.ref (.typeMember (.var .here) typeLabelB))) :=
  .typeMember crossMemberExposure crossMemberALower

/-- The local upper endpoint `A` becomes the stable selection `x.A`. -/
def selectedBUpperOpensAtRoot :
    HasUpper CrossMemberContext
      (.typeMember (.var .here) typeLabelB)
      (.type (.ref (.typeMember (.var .here) typeLabelA))) :=
  .typeMember crossMemberExposure crossMemberBUpper

def crossCaptureInterface {scope : Scope} : Interface scope :=
  .inter
    (.captureMember captureLabelC
      (.ref (.localCaptureMember captureLabelD)) .empty)
    (.captureMember captureLabelD .empty
      (.ref (.localCaptureMember captureLabelC)))

def crossCaptureObject {scope : Scope} : ObjectType scope :=
  .mk crossCaptureInterface .one .empty

abbrev CrossCaptureContext : Ctx 1 :=
  Ctx.nil.extendTerm (crossCaptureObject (scope := 0)).formedType

def crossCaptureExposure :
    ExposesObject CrossCaptureContext (.var .here)
      (crossCaptureObject (scope := 1)) :=
  .variable rfl

def crossCaptureCLower :
    (crossCaptureObject (scope := 1)).interface.HasCaptureOccurrence
      captureLabelC (.ref (.localCaptureMember captureLabelD)) .empty :=
  .left .here

def crossCaptureDUpper :
    (crossCaptureObject (scope := 1)).interface.HasCaptureOccurrence
      captureLabelD .empty (.ref (.localCaptureMember captureLabelC)) :=
  .right .here

def selectedCLowerOpensAtRoot :
    HasLower CrossCaptureContext
      (.captureMember (.var .here) captureLabelC)
      (.capture (.ref (.captureMember (.var .here) captureLabelD))) :=
  .captureMember crossCaptureExposure crossCaptureCLower

def selectedDUpperOpensAtRoot :
    HasUpper CrossCaptureContext
      (.captureMember (.var .here) captureLabelD)
      (.capture (.ref (.captureMember (.var .here) captureLabelC))) :=
  .captureMember crossCaptureExposure crossCaptureDUpper

end DOTCapture.Intersections.GeneralExpression.TypingExamples
