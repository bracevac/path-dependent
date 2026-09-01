import Coercions.DOT.Captures.ModalIntersections.Typing

/-!
# Focused typing regressions for cumulative modal captured DOT

These examples exercise the access-only boundary directly.  Forming a lock
checks its body under the advertised frame but does not require that frame in
the ambient assumptions.  Unlocking does require ambient satisfaction, so an
outer lock can discharge a genuinely nontrivial requirement of an inner
modal value.
-/

namespace DOTCapture.ModalIntersections.TypingExamples

/-! ## One stable runtime root -/

abbrev OneTermScope : Sig := [] ▹ .term

def oneTermEnvironment : TypingEnv OneTermScope :=
  TypingEnv.nil.extendTerm .one

def rootCapture : Capture OneTermScope :=
  .singleton (.var .here)

/-- Requiring read-only access to a raw singleton is nontrivial: the generic
`Mode.readOnly` rule applies only to an explicitly read-only capture. -/
def singletonReadOnlyModes : ModeContext [.readOnly] OneTermScope :=
  .cons .nil rootCapture

def singletonReadOnlyRequirements :
    ModalRequirements 0 [.readOnly] OneTermScope :=
  .mk .nil singletonReadOnlyModes

/-- The top lock frame supplies the exact singleton mode occurrence. -/
def topFrameSatisfiesSingletonReadOnly :
    Satisfies oneTermEnvironment.bindings
      (.push oneTermEnvironment.locks singletonReadOnlyRequirements)
      singletonReadOnlyRequirements :=
  .mk
    (fun occurrence =>
      match occurrence with
      | .here => .lock .here .here)
    (fun left => nomatch left)

/-! The following small syntactic invariant confirms that the requirement is
not already derivable from the ordinary context.  A raw occurrence records
the distinguished root only outside `readOnly`. -/

inductive HasRawRoot : Capture OneTermScope -> Prop where
  | singleton : HasRawRoot rootCapture
  | unionLeft {left right : Capture OneTermScope} :
      HasRawRoot left -> HasRawRoot (.union left right)
  | unionRight {left right : Capture OneTermScope} :
      HasRawRoot right -> HasRawRoot (.union left right)

private theorem noCapturedTermBinding
    (name : BVar OneTermScope .term) {captures : Capture OneTermScope}
    {shape : Ty OneTermScope}
    (found : oneTermEnvironment.bindings.lookupTerm name =
      .capturing captures shape) : False := by
  cases name with
  | here => cases found
  | there older => nomatch older

private theorem noExposedObject {receiver : Path OneTermScope}
    {object : ObjectType OneTermScope}
    (exposes : ExposesObject oneTermEnvironment.bindings receiver object) :
    False := by
  cases exposes with
  | «variable» found =>
      cases ‹BVar OneTermScope .term› with
      | here => cases found
      | there older => nomatch older

private def StaticHasRawRoot : {sort : StaticSort} ->
    StaticExpr sort OneTermScope -> Prop
  | .type, _ => False
  | .capture, .capture capture => HasRawRoot capture

private theorem lowerPreservesRawRoot {sort : StaticSort}
    {reference : StaticRef sort OneTermScope}
    {endpoint : StaticExpr sort OneTermScope}
    (lower : HasLower oneTermEnvironment.bindings reference endpoint) :
    StaticHasRawRoot endpoint -> StaticHasRawRoot reference.expression := by
  cases lower with
  | bound => exact False.elim (noStaticVar (scope := 1) ‹_›)
  | typeMember => intro root; nomatch root
  | captureMember exposes _ => exact False.elim (noExposedObject exposes)

private theorem upperPreservesRawRoot {sort : StaticSort}
    {reference : StaticRef sort OneTermScope}
    {endpoint : StaticExpr sort OneTermScope}
    (upper : HasUpper oneTermEnvironment.bindings reference endpoint) :
    StaticHasRawRoot reference.expression -> StaticHasRawRoot endpoint := by
  cases upper with
  | bound => exact False.elim (noStaticVar (scope := 1) ‹_›)
  | typeMember => intro root; nomatch root
  | captureMember exposes _ => exact False.elim (noExposedObject exposes)

private def rawExpressionMonotone {sort : StaticSort}
    {lower upper : StaticExpr sort OneTermScope}
    (inclusion : Includes oneTermEnvironment.bindings lower upper) :
    StaticHasRawRoot lower -> StaticHasRawRoot upper :=
  match inclusion with
  | .refl => fun root => root
  | .trans first second =>
      fun root => rawExpressionMonotone second
        (rawExpressionMonotone first root)
  | .lower bound => lowerPreservesRawRoot bound
  | .upper bound => upperPreservesRawRoot bound
  | .typeTop => fun root => nomatch root
  | .typeBottom => fun root => nomatch root
  | .typeArrow _ _ => fun root => nomatch root
  | .typeCapturing _ _ => fun root => nomatch root
  | .captureEmpty => fun root => nomatch root
  | .captureUnionLeft => fun root => .unionLeft root
  | .captureUnionRight => fun root => .unionRight root
  | .captureUnionElim fromLeft fromRight =>
      fun root =>
        match root with
        | .unionLeft left => rawExpressionMonotone fromLeft left
        | .unionRight right => rawExpressionMonotone fromRight right
  | .captureReadOnly => fun root => nomatch root
  | .captureReadOnlyMono _ => fun root => nomatch root
  | .captureVariable found =>
      False.elim (noCapturedTermBinding _ found)
  | .payloadRoot exposes => False.elim (noExposedObject exposes)

private def rawRootMonotone {lower upper : Capture OneTermScope}
    (inclusion : CaptureIncludes oneTermEnvironment.bindings lower upper) :
    HasRawRoot lower -> HasRawRoot upper :=
  rawExpressionMonotone inclusion

private def readOnlyModeHasNoRawRoot {capture : Capture OneTermScope}
    (mode : Mode oneTermEnvironment.bindings .nil capture .readOnly) :
    HasRawRoot capture -> False :=
  match mode with
  | .empty _ => fun root => nomatch root
  | .union leftMode rightMode =>
      fun root =>
        match root with
        | .unionLeft left => readOnlyModeHasNoRawRoot leftMode left
        | .unionRight right => readOnlyModeHasNoRawRoot rightMode right
  | .subcapture inclusion upperMode =>
      fun root => readOnlyModeHasNoRawRoot upperMode
        (rawRootMonotone inclusion root)
  | .readOnly _ => fun root => nomatch root
  | .lock frame _ => nomatch frame

/-- The singleton read-only requirement cannot be unlocked with an empty
assumption stack in this ordinary one-variable context. -/
theorem singletonReadOnlyNotSatisfiedWithoutLock :
    Satisfies oneTermEnvironment.bindings .nil
      singletonReadOnlyRequirements -> False := by
  intro satisfaction
  cases satisfaction with
  | mk modesCovered _ =>
      exact readOnlyModeHasNoRawRoot (modesCovered .here) .singleton

/-! ## Formation and nested elimination -/

/-- Lock formation has no ambient-satisfaction premise. -/
def lockFormsWithoutAmbientSatisfaction :
    Value.HasType oneTermEnvironment
      (.lock singletonReadOnlyRequirements .one .empty (.ret .unit))
      (.capturing .empty (.modal singletonReadOnlyRequirements .one)) :=
  .lock (.ret .unit) .refl

/-- The inner suspension is formed while the outer frame is active. -/
def innerLockUnderOuter :
    Value.HasType
      (oneTermEnvironment.push singletonReadOnlyRequirements)
      (.lock singletonReadOnlyRequirements .one .empty (.ret .unit))
      (.capturing .empty (.modal singletonReadOnlyRequirements .one)) :=
  .lock (.ret .unit) .refl

/-- An outer lock frame discharges the inner unlock's raw-singleton
read-only requirement. -/
def outerLockDischargesInnerUnlock :
    Value.HasType oneTermEnvironment
      (.lock singletonReadOnlyRequirements .one .empty
        (.unlock singletonReadOnlyRequirements
          (.ret
            (.lock singletonReadOnlyRequirements .one .empty
              (.ret .unit)))))
      (.capturing .empty (.modal singletonReadOnlyRequirements .one)) :=
  .lock
    (.unlock (.ret innerLockUnderOuter) rfl
      topFrameSatisfiesSingletonReadOnly)
    .refl

/-! ## Separation and modal adaptation -/

/-- Two read-only views of the same root are separate.  This derivation uses
`Separate.readOnly`; it makes no `Disjoint` claim about the shared root. -/
def sharedReadOnlyOverlapSeparates :
    Separate oneTermEnvironment.bindings oneTermEnvironment.locks
      (.readOnly rootCapture) (.readOnly rootCapture) :=
  .readOnly (.readOnly rootCapture) (.readOnly rootCapture)

/-- The target modal interface requires the source read-only fact and one
additional writable fact. -/
def strongerTargetModes :
    ModeContext [.readOnly, .writable] OneTermScope :=
  .cons (.cons .nil rootCapture) rootCapture

def strongerTargetRequirements :
    ModalRequirements 0 [.readOnly, .writable] OneTermScope :=
  .mk .nil strongerTargetModes

/-- Source requirements are checked using the target frame, exhibiting the
contravariant direction of modal adaptation. -/
def strongerTargetSatisfiesSource :
    Satisfies oneTermEnvironment.bindings
      (.push oneTermEnvironment.locks strongerTargetRequirements)
      singletonReadOnlyRequirements :=
  .mk
    (fun occurrence =>
      match occurrence with
      | .here => .lock .here .here)
    (fun left => nomatch left)

def modalAdaptationUsesTargetRequirements :
    Adapts oneTermEnvironment
      (.modal singletonReadOnlyRequirements .one)
      (.modal strongerTargetRequirements .one) :=
  .modal strongerTargetSatisfiesSource .identity

/-! ## Lexical static capture inside a modal value -/

def unboundedCaptureInterval : Interval .capture [] :=
  .bounds .none .none

abbrev CaptureBinderScope : Sig := [] ▹ .static .capture

def lexicalCapture : Capture CaptureBinderScope :=
  .ref (.bound .here)

def lexicalReadOnlyRequirements :
    ModalRequirements 0 [.readOnly] CaptureBinderScope :=
  .mk .nil (.cons .nil lexicalCapture)

/-- A lexical capture abstraction returns a modal value whose interface
mentions the abstract capture. -/
def lexicalStaticModalValue :
    Value.HasType TypingEnv.nil
      (.staticLam unboundedCaptureInterval
        (.lock lexicalReadOnlyRequirements .one .empty (.ret .unit)))
      (.capturing .empty
        (.forallI unboundedCaptureInterval
          (.capturing .empty (.modal lexicalReadOnlyRequirements .one)))) :=
  .staticLam (.lock (.ret .unit) .refl) .refl

/-! ## Native positive/negative object polarity -/

def exactTypeInterface : Interface [] :=
  .typeMember 0 .one .one

/-- One static member and one runtime unit payload. -/
def exactTypeObject : ObjectType [] :=
  .mk exactTypeInterface .one .empty

/-- The positive realization chooses `One` for the abstract member. -/
def exactTypeModel : LocalModel.Model [] where
  typeMember := fun _ => .one
  captureMember := fun _ => .empty

def exactTypeRealization :
    ObjectType.Realization TypingEnv.nil.bindings exactTypeObject where
  model := exactTypeModel
  constraints := .typeMember .refl .refl

def exactTypeLiteral : Value [] :=
  .object exactTypeObject .unit

/-- Positive use retains the existential object representation. -/
def exactTypeLiteralTyping :
    Value.HasType TypingEnv.nil exactTypeLiteral exactTypeObject.formedType :=
  .object exactTypeRealization .unit .refl .refl .refl

/-- A negative result template refers to the parameter's local member. -/
def memberResultTemplate : Ty [] :=
  .ref (.localTypeMember 0)

abbrev ExactParameterScope : Sig := [] ▹ .term

def exactParameterEnvironment : TypingEnv ExactParameterScope :=
  TypingEnv.nil.extendTerm exactTypeObject.formedType

def exactParameterExposure :
    ExposesObject exactParameterEnvironment.bindings (.var .here)
      (exactTypeObject.weaken (kind := .term)) :=
  .variable rfl

/-- The exact lower member bound inhabits the dependent result selected from
the stable parameter root. -/
def exactParameterBodyTyping :
    Term.HasType exactParameterEnvironment (.ret .unit) .empty
      ((memberResultTemplate.weaken (kind := .term)).openAt (.var .here)) :=
  .ret
    (.adapt .unit
      (.cast
        (.lower
          (.typeMember exactParameterExposure
            Interface.HasTypeOccurrence.here))))

def dependentConsumer : Value [] :=
  .objectConsumer exactTypeObject memberResultTemplate (.ret .unit)

def dependentConsumerType : Ty [] :=
  .capturing .empty (.objectArrow exactTypeObject memberResultTemplate)

/-- Native negative introduction has the distinct `objectArrow` shape. -/
def dependentConsumerTyping :
    Value.HasType TypingEnv.nil dependentConsumer dependentConsumerType :=
  .objectConsumer exactParameterBodyTyping .captureEmpty

/-- Negative use exposes the expected signature's exact model without first
constructing and reopening a positive package. -/
def exactTypeLiteralArgument :
    ObjectArgument.HasType TypingEnv.nil (.ret exactTypeLiteral)
      exactTypeObject exactTypeModel := by
  simpa using
    (ObjectArgument.HasType.literal exactTypeRealization .unit
      .refl .refl .refl (ObjectType.Adapts.refl exactTypeObject)
      .refl .refl)

theorem memberResultAtExactModel :
    memberResultTemplate.realizeLocals exactTypeModel = .one :=
  rfl

theorem exactArgumentRealizesMemberResult :
    exactTypeLiteralArgument.realizeResult memberResultTemplate = .one :=
  rfl

/-- A genuine computation, rather than a returned value, occupies function
position in the native object application. -/
def computedDependentConsumer : Term [] :=
  .let' dependentConsumerType (.ret dependentConsumer) (.ret (.var .here))

def computedDependentConsumerTyping :
    Term.HasType TypingEnv.nil computedDependentConsumer
      (.union .empty .empty) dependentConsumerType :=
  .letPlain (by trivial) (.ret dependentConsumerTyping)
    (.ret Value.HasType.declaredVar) .captureEmpty

def dependentObjectApplication : Term [] :=
  .objectApp exactTypeObject computedDependentConsumer
    (.ret exactTypeLiteral)

/-- Application realizes the dependent template at the argument model, so
the result is exactly `One`; the computed consumer is evaluated once first. -/
def dependentObjectApplicationTyping :
    Term.HasType TypingEnv.nil dependentObjectApplication
      (.union (.union .empty .empty) (.union .empty .empty)) .one := by
  simpa [dependentConsumerType, memberResultAtExactModel] using
    (Term.HasType.objectApp computedDependentConsumerTyping rfl
      exactTypeLiteralArgument)

/-! An arbitrary object-producing computation remains distinct from the two
negative argument forms.  It must be opened explicitly before negative use. -/

def computedExactTypeObject : Term [] :=
  .objectLet exactTypeObject exactTypeObject.formedType
    (.ret exactTypeLiteral) (.ret (.var .here))

def computedExactTypeObjectTyping :
    Term.HasType TypingEnv.nil computedExactTypeObject
      (.union .empty .empty) exactTypeObject.formedType :=
  .objectLet (.ret exactTypeLiteralTyping)
    (.ret Value.HasType.declaredVar) .captureEmpty

theorem computedObjectRequiresExplicitOpen :
    ObjectArgument.classify computedExactTypeObject =
      .requiresExplicitOpen :=
  rfl

theorem computedObjectHasNoNegativeArgumentDerivation
    {model : LocalModel.Model []} :
    ObjectArgument.HasType TypingEnv.nil computedExactTypeObject
      exactTypeObject model -> False := by
  intro typing
  cases typing

end DOTCapture.ModalIntersections.TypingExamples
